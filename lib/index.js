require('es6-shim');

var json = require('../package.json');

var domino = require('domino');
var fs = require('fs');
var guard = require('when/guard');
var linewrap = require('linewrap');
var path = require('path');
var stream = require('stream');
var tmp = require('tmp');
var url = require('url');
var when = require('when');
tmp.setGracefulCleanup();

// node 0.8 compatibility
if (!stream.Writable) {
	stream = require('readable-stream');
}

var Db = require('./db');
var DomUtil = require('./domutil');
var P = require('./p');
var Polyglossia = require('./polyglossia');
var StatusReporter = require('./status');


// Convert plain text (with HTML whitespace semantics) to an appropriately
// simplified string
var textEscape = function(str) {
	// compress multiple newlines (and use unix-style newlines exclusively)
	str = str.replace(/\r\n?/g, '\n').replace(/\n\n+/g, '\n');
	// trim leading and trailing newlines for consistent output.
	str = str.replace(/^\n+/, '').replace(/\n$/, '');
	// replace smart quotes with plain quotes
	// XXX only in en locales?
	str = str.replace(/[\u201C\u201D]/g, '"');
	str = str.replace(/[\u2018\u2019]/g, "'");
	return str;
};

// Special predicate for some image templates used on enwiki
// XXX restrict to enwiki content?
var isMultipleImageTemplate = function(node) {
	if (node.getAttribute('typeof') === 'mw:Transclusion') {
		try {
			var data = JSON.parse(node.getAttribute('data-mw'));
			var href = data.parts[0].template.target.href;
			if (href === './Template:Triple_image' ||
				href === './Template:Double_image') {
				return true;
			}
		} catch (e) { /* ignore */ }
	}
	return false;
};

// Predicate to distinguish 'nonprintable' content.
var isHidden = function(node) {
	if (isMultipleImageTemplate(node)) {
		return false;
	}
	if (node.classList.contains('noprint')) {
		return true;
	}
	if (/(^|;)\s*display\s*:\s*none\s*(;|$)/i.test
		(node.getAttribute('style') || '')) {
		return true;
	}
	// bit of a hack: hide infobox / navbox / rellink / dablink / metadata
	// XXX restrict to enwiki or localize?
	if (['infobox', 'navbox', 'rellink', 'dablink', 'toplink', 'metadata'].some(function(c) {
		return node.classList.contains(c);
	})) {
		return true;
	}
	return false;
};

/** Formatter helper.
 * This class encapsulates all the formatting logic.
 */
var Formatter = function(outStream, options) {
	this.options = options;
	this.columns = options.column || 75;
	this.tabWidth = options.tabWidth || 2;
	this.buffer = [];
	this.outStream = outStream;
	this.newLine = this.newPara = true;
	this.stateStack = [];
	this.state = {
		indent: 0,
		wrap: this._makeWrap(0)
	};
};
Formatter.prototype._makeWrap = function(indent, tag) {
	if (this.options.noWrap) {
		if (tag) { indent -= this.tabWidth; }
		var spc = (function mkspace(n) {
			if (n<=1) { return (n===1) ? ' ' : ''; }
			var m = (n/2)|0;
			return mkspace(m) + mkspace(n-m);
		})(indent); /* make a string `n` spaces long */
		return (function(t) { return spc + t.replace(/\s+/g, ' ').trim(); });
	}
	var opts = {
		whitespace: 'collapse',
		respectLineBreaks: 'none',
		tabWidth: this.tabWidth
	};
	if (indent + 20 >= this.columns) {
		indent = this.columns - 20;
	}
	if (tag) {
		opts.wrapLineIndent = this.tabWidth;
		return linewrap(this.columns, indent - this.tabWidth, opts);
	}
	return linewrap(this.columns, indent, opts);
};
Formatter.prototype._write = function(text) {
	this.outStream.write(text, 'utf8');
};
Formatter.prototype._writeWrap = function(text) {
	this._write(this.state.wrap(text));
};
Formatter.prototype.flush = function() {
	var deferred = when.defer();
	this.lineBreak();
	this.outStream.write('', 'utf8', function() {
		deferred.resolve();
	});
	return deferred.promise;
};

Formatter.prototype.writeTitle = function(title, subtitle) {
	this.write(title.trim());
	this.lineBreak();
	if (subtitle) {
		this.write(subtitle.trim());
		this.lineBreak();
	}
	this.paragraphBreak();
};
Formatter.prototype.writeSummary = function(summary) {
	this.paragraphBreak();
	this.indent();
	this.write(summary.trim());
	this.dedent();
	this.paragraphBreak();
};
Formatter.prototype.writeHeading = function(level, heading) {
	this.paragraphBreak();
	this.write(heading.trim());
	this.paragraphBreak();
};
Formatter.prototype.indent = function(tag) {
	this.lineBreak();
	this.stateStack.push(this.state);
	var nIndent = this.state.indent + this.tabWidth;
	this.state = {
		indent: nIndent,
		wrap: this._makeWrap(nIndent, tag)
	};
	if (tag) {
		this.write(tag);
		this.write(' ');
	}
};
Formatter.prototype.dedent = function() {
	this.lineBreak();
	this.state = this.stateStack.pop();
};

Formatter.prototype.paragraphBreak = function() {
	if (this.newPara) { return; }
	if (!this.newLine) {
		this.lineBreak();
	}
	this._write('\n'); // turn line break into paragraph break
	this.newPara = true;
	return;
};
Formatter.prototype.lineBreak = function() {
	if (this.newLine) { return; }
	this._writeWrap(this.buffer.join(''));
	this._write('\n');
	this.buffer.length = 0;
	this.newLine = true;
};

// accumulate text in buffer until the next linebreak or paragraph break.
Formatter.prototype.write = function(text) {
	if (this.newLine || this.newPara) {
		text = text.replace(/^\s+/, ''); // kill leading space after nl
		if (!text.length) { return; }
		this.newLine = this.newPara = false;
	}
	// the given text shouldn't have line breaks, and should have all the
	// spaces compressed... but the linewrap module should take care of
	// that for us.
	this.buffer.push(text);
};

/* Document node visitor class.  Collects LaTeX output as it traverses the
 * document tree. */
var Visitor = function(document, format, options) {
	this.document = document;
	this.format = format;
	this.options = options;
	this.templates = Object.create(null);
	this.base = options.base || '';
	this.currentLanguage = this.tocLanguage = options.lang || 'en';
	this.currentDirectionality = options.dir || 'ltr';
	this.usedLanguages = new Set();
	this.listInfo = { depth: 0 };
};

// Helper function -- collect all text from the children of `node` as
// HTML non-block/TeX non-paragraph content.  Invoke `f` with the result,
// suitable for inclusion in a TeX non-paragraph context.
Visitor.prototype.collect = function(node, f) {
	var wasFormat = this.format;
	var b = [];
	this.format = {
		newLine: true,
		newPara: true,
		write: function(text) {
			this.newLine = this.newPara = false;
			b.push(text);
		},
		lineBreak: function() {
			if (!this.newLine) { b.push(' '); this.newLine = true; }
		},
		paragraphBreak: function() {
			if (!this.newPara) { this.lineBreak(); this.newPara = true; }
		},
		indent: function(tag) {
			this.lineBreak();
			if (tag) { b.push(tag); b.push(' '); }
		},
		dedent: function() {
			this.lineBreak();
		}
	};
	this.visitChildren(node);
	// combine lines, compress paragraphs
	var text = b.join('').replace(/\s+/g, ' ');
	this.format = wasFormat;
	return f.call(this, text);
};

// Generic node visitor.  Dispatches to specialized visitors based on
// element typeof/rel attributes or tag name.
Visitor.prototype.visit = function(node) {
	var name = node.nodeName, type = node.nodeType;
	switch(type) {
	case node.ELEMENT_NODE:
		if (isHidden(node)) {
			return;
		}
		// handle LANG attributes (which override everything else)
		var lang = node.getAttribute('lang') || this.currentLanguage;
		// in addition to eliminating no-ops, this condition allows us
		// to recursively invoke visit() inside the LANG handler.
		if (lang !== this.currentLanguage) {
			this.usedLanguages.add(lang);
			return this['visitLANG='].apply(this, arguments);
		}
		// directionality should be set by language handling.  if it isn't...
		var dir = node.getAttribute('dir') || this.currentDirectionality;
		if (dir==='auto') { dir = this.currentDirectionality; /* hack */ }
		if (dir !== this.currentDirectionality) {
			return this['visitDIR='].apply(this, arguments);
		}
		// xxx look at lang and dir from css styling xxx
		// use typeof property if possible
		if (node.hasAttribute('typeof')) {
			var typeo = node.getAttribute('typeof');
			if (this['visitTYPEOF=' + typeo]) {
				return this['visitTYPEOF=' + typeo].apply(this, arguments);
			}
		}
		// use rel property if possible
		if (node.hasAttribute('rel')) {
			var rel = node.getAttribute('rel');
			if (this['visitREL=' + rel]) {
				return this['visitREL=' + rel].apply(this, arguments);
			}
		}
		// use tag name
		if (this['visit' + name]) {
			return this['visit' + name].apply(this, arguments);
		}
		//console.error('UNKNOWN TAG', name);
		return this.visitChildren.apply(this, arguments);

	case node.TEXT_NODE:
	case node.CDATA_SECTION_NODE:
		var text = textEscape(node.data);
		if (text) {
			this.format.write(text);
		}
		break;

	//case node.PROCESSING_INSTRUCTION_NODE:
	//case node.DOCUMENT_TYPE_NODE:
	//case node.COMMENT_NODE:
	default:
		// swallow it up.
		break;
	}
};

// Generic helper to recurse into the children of the given node.
Visitor.prototype.visitChildren = function(node) {
	for (var i = 0, n = node.childNodes.length; i < n; i++) {
		this.visit(node.childNodes[i]);
	}
};

Visitor.prototype.visitBODY = function(node) {
	var title = this.document.title;
	// use dc:isVersionOf if present
	var ivo = this.document.querySelector('link[rel="dc:isVersionOf"]');
	if (ivo && ivo.hasAttribute('href')) {
		title = ivo.getAttribute('href').replace(/^.*\//, '');
	}
	// titles use _ instead of ' '
	title = title.replace(/_/g, ' ');
	this.visitChildren(node);
};

Visitor.prototype.visitA = function(node) {
	var href = node.getAttribute('href');
	// ignore the href
	this.visitChildren(node);
};

Visitor.prototype.visitP = function(node) {
	this.format.paragraphBreak();
	this.visitChildren(node);
	this.format.paragraphBreak();
};

var submap = {
	'0': '\u2080',
	'1': '\u2081',
	'2': '\u2082',
	'3': '\u2083',
	'4': '\u2084',
	'5': '\u2085',
	'6': '\u2086',
	'7': '\u2087',
	'8': '\u2088',
	'9': '\u2089',
	'+': '\u208a',
	'-': '\u208b',
	'=': '\u208c',
	'(': '\u208d',
	')': '\u208e',
	'a': '\u2090',
	'e': '\u2091',
	'o': '\u2092',
	'x': '\u2093',
	'h': '\u2095',
	'k': '\u2096',
	'l': '\u2097',
	'm': '\u2098',
	'n': '\u2099',
	'p': '\u209a',
	's': '\u209b',
	't': '\u209c',
	// and whitespace
	' ': ' ',
	'\u00A0': '\u00A0'
};

var supmap = {
	'2': '\u00B2',
	'3': '\u00B3',
	'1': '\u00B9',
	'0': '\u2070',
	'i': '\u2071',
	'4': '\u2074',
	'5': '\u2075',
	'6': '\u2076',
	'7': '\u2077',
	'8': '\u2078',
	'9': '\u2079',
	'+': '\u207a',
	'-': '\u207b',
	'=': '\u207c',
	'(': '\u207d',
	')': '\u207e',
	'n': '\u207f',
	// and whitespace
	' ': ' ',
	'\u00A0': '\u00A0'
};
var subre =
	new RegExp('^['+Object.keys(submap).join('').replace(/(-)/g, '\\$1')+']+$');
var supre =
	new RegExp('^['+Object.keys(supmap).join('').replace(/(-)/g, '\\$1')+']+$');

Visitor.prototype.visitSUB = function(node) {
	return this.collect(node, function(contents) {
		if (subre.test(contents)) {
			this.format.write(contents.replace(/[\s\S]/g, function(c) {
				return submap[c];
			}));
		} else {
			// throw the subscript away
			/* jshint noempty: false */
		}
	});
};

Visitor.prototype.visitSUP = function(node) {
	return this.collect(node, function(contents) {
		if (supre.test(contents)) {
			this.format.write(contents.replace(/[\s\S]/g, function(c) {
				return supmap[c];
			}));
		} else {
			// throw the superscript away
			/* jshint noempty: false */
		}
	});
};

Visitor.prototype.visitCENTER = function(node) {
	this.format.lineBreak();
	this.visitChildren(node); // XXX implement this properly?
	this.format.lineBreak();
};

Visitor.prototype.visitBR = function(node) {
	/* jshint unused: vars */
	this.format.lineBreak();
};

// H1s are "at the same level as the page title".
// Don't allow them in single item collections, as the article class doesn't
// allow \chapters
Visitor.prototype.visitHn = function(node, n) {
	if (!this.options.hasChapters) { n -= 1; }
	if (this.options.singleItem && n === 0) {
		/* the article class doesn't allow chapters */
		return;
	}
	return this.collect(node, function(contents) {
		this.format.writeHeading(n, contents);
	});
};

Visitor.prototype.visitH1 = function(node) { return this.visitHn(node, 1); };
Visitor.prototype.visitH2 = function(node) { return this.visitHn(node, 2); };
Visitor.prototype.visitH3 = function(node) { return this.visitHn(node, 3); };
Visitor.prototype.visitH4 = function(node) { return this.visitHn(node, 4); };
Visitor.prototype.visitH5 = function(node) { return this.visitHn(node, 5); };
Visitor.prototype.visitH6 = function(node) { return this.visitHn(node, 6); };

Visitor.prototype['visitREL=dc:references'] = function(node) {
	if (this.options.noRefs) { return; /* skip references */ }
	return this.visitSUP(node);
};

Visitor.prototype.visitUL =
Visitor.prototype.visitOL = function(node) {
	if (!DomUtil.first_child(node)) { return; /* no items */ }
	var wasListInfo = this.listInfo;
	this.listInfo = {
		type: node.nodeName,
		num: 0,
		depth: wasListInfo.depth + 1
	};
	this.visitChildren(node);
	this.listInfo = wasListInfo;
};

Visitor.prototype.visitLI = function(node) {
	var depth = (this.listInfo.depth % 3);
	var tag = "*-+".charAt(depth);
	if (this.listInfo === 'OL') {
		tag = (++this.listInfo.num) + (".)]".charAt(depth));
	}
	this.format.indent(tag);
	this.visitChildren(node);
	this.format.dedent();
};

Visitor.prototype.visitDL = function(node) {
	var child = DomUtil.first_child(node); // first non-ws child node
	// LaTeX requires that a description have at least one item.
	if (child === null) { return; /* no items */ }

	// recognize DL/DD used for quotations/indentation
	// node.querySelector('dl:scope > dt') !== null
	// special case DL used to indent math
	// node.querySelector('dl:scope > dd:only-child > *[typeof=...]:only-child')
	// (but domino/zest doesn't support :scope yet)
	var dd = node.firstElementChild, sawDT = false, allMath = true;
	for ( ; dd && !sawDT; dd = dd.nextElementSibling) {
		sawDT = (dd.nodeName === 'DT');
		var math = dd.firstElementChild;
		if (!(math && !math.nextElementSibling &&
			  math.getAttribute('typeof') === 'mw:Extension/math')) {
			allMath = false;
		}
	}
	if (allMath && !sawDT) {
		var v = this['visitTYPEOF=mw:Extension/math'].bind(this);
		for (dd = node.firstElementChild; dd; dd = dd.nextElementSibling) {
			v(dd.firstElementChild, "display");
		}
		return;
	}

	var wasListInfo = this.listInfo;
	this.listInfo = {
		type: sawDT ? node.nodeName : 'BLOCKQUOTE',
		num: 0,
		depth: wasListInfo.depth + 1
	};
	this.visitChildren(node);
	if (this.listInfo.sawDT) {
		this.format.dedent();
	}
	this.listInfo = wasListInfo;
};

Visitor.prototype.visitDT = function(node) {
	if (this.listInfo.sawDT) {
		this.format.dedent();
		this.listInfo.sawDT = false;
	}
	return this.collect(node, function(contents) {
		this.format.indent(contents);
		this.listInfo.sawDT = true;
	});
};

Visitor.prototype.visitDD = function(node) {
	// verify that previous line was the DT, otherwise add blank DT
	if (!this.listInfo.sawDT) {
		this.format.indent();
		this.listInfo.sawDT = true;
	}
	this.visitChildren(node);
};

Visitor.prototype.visitBLOCKQUOTE = function(node) {
	this.format.indent();
	this.visitChildren(node);
	this.format.dedent();
};

Visitor.prototype['visitREL=mw:referencedBy'] = function(node) {
	// hide this span
	/* jshint unused: vars */
};

Visitor.prototype['visitTYPEOF=mw:Extension/references'] = function(node) {
	if (this.options.noRefs) { return; /* skip references */ }

	for (var i = 0, n = node.childNodes.length; i < n; i++) {
		var ref = node.childNodes[i];
		var name = textEscape('[' + (i+1) + ']');
		this.format.indent(name);
		this.visitChildren(ref);
		this.format.dedent();
	}
};

// tables
Visitor.prototype.visitTABLE = function(node) {
	if (node.getAttribute('about') in this.templates) {
		return;
	}
	// xxx hide all tables for now
};

// images!
Visitor.prototype.visitFIGURE = function(node, extraCaption) {
	// skip all figures.
	return;
};

Visitor.prototype['visitTYPEOF=mw:Extension/math'] = function(node, display) {
	// xxx: sanitize this string the same way the math extension does

	var math = JSON.parse(node.getAttribute('data-mw')).body.extsrc;
	var m = /^(\s*\\begin\s*\{\s*(?:eqnarray|equation|align|gather|falign|multiline|alignat))[*]?(\s*\}[\s\S]*\\end\s*\{[^\}*]+)[*]?(\}\s*)$/.exec(math);
	if (m) {
		// math expression contains its own environment
		// ensure we're using the * form so we don't get equation numbers
		this.output.push(m[1]+'*'+m[2]+'*'+m[3]);
		return;
	}
	var delimit = display ? '$$' : '$';
	var eol = display ? '' : '%';
	this.output.push(delimit + math + delimit + eol);
};

Visitor.prototype['visitLANG='] = function(node) {
	var r;
	var savedLanguage = this.currentLanguage;
	var savedDirectionality = this.currentDirectionality;
	var lang = node.getAttribute('lang');
	var poly = Polyglossia.lookup(lang);
	this.currentLanguage = lang;
	this.currentDirectionality = poly.dir;
	// XXX emit an explicit directionality cue
	r = this.visit(node);
	// XXX pop the directionality cue
	this.currentLanguage = savedLanguage;
	this.currentDirectionality = savedDirectionality;
	return r;
};

Visitor.prototype['visitDIR='] = function(node) {
	var r;
	var savedDirectionality = this.currentDirectionality;
	var dir = node.getAttribute('dir');
	console.warn("Using non-standard DIR", this.currentLanguage, this.currentDirectionality, '->', dir);
	this.currentDirectionality = dir;
	// XXX emit an explicit directionality cue
	r = this.visit(node);
	// XXX pop the directionality cue
	this.currentDirectionality = savedDirectionality;
	return r;
};

Visitor.prototype['visitTYPEOF=mw:Image'] =
Visitor.prototype['visitTYPEOF=mw:Image/Thumb'] = function(node) {
	return this.visitFIGURE(node);
};

// hack to support double/triple image template
Visitor.prototype.visitMultipleImage = function(node) {
	var about = node.getAttribute('about');
	this.templates[about] = true;
	node = node.parentElement; // hop up one level so we can see siblings
	var sel = 'table[about="' + about + '"] tr ';
	var images = node.querySelectorAll(sel + '> td > *[typeof="mw:Image"]');
	var captions = node.querySelectorAll(sel + '+ tr > td > *[class="thumbcaption"]');
	for (var i=0, n=images.length; i < n ; i++) {
		this.visitFIGURE(images[i], captions[i]);
	}
};


// hack to support triple image template
Visitor.prototype.visitDIV = function(node) {
	if (isMultipleImageTemplate(node)) {
		return this.visitMultipleImage(node);
	}
	this.format.lineBreak();
	var r = this.visitChildren(node);
	this.format.lineBreak();
	return r;
};

// ---------------------------------------------------------------------
// Bundle and file processing

// return a promise for the builddir and control file contents
// (after the bundle has been unpacked)
var unpackBundle = function(options) {
	var metabook, builddir, status = options.status;

	status.createStage(0, 'Unpacking content bundle');

	// first create a temporary directory
	return P.call(tmp.dir, tmp, {
		prefix: json.name,
		unsafeCleanup: !(options.debug || options.latex)
	}).then(function(_builddir) {
		builddir = _builddir;
		// make bundle and output subdirs
		return when.join(
			P.call(fs.mkdir, fs, path.join(builddir, 'bundle')),
			P.call(fs.mkdir, fs, path.join(builddir, 'output'))
		);
	}).then(function() {
		// now unpack the zip archive
		var bundledir = path.join(builddir, 'bundle');
		return P.spawn('unzip', [ path.resolve( options.bundle ) ], {
			cwd: bundledir
		});
	}).then(function() {
		// now read in the main metabook.json file
		return P.call(
			fs.readFile, fs, path.join(builddir, 'bundle', 'metabook.json')
		).then(function(data) {
			metabook = JSON.parse(data);
		});
	}).then(function() {
		return { metabook: metabook, builddir: builddir };
	});
};

// count total # of items (used for status reporting)
var countItems = function(item) {
	return (item.items || []).reduce(function(sum, item) {
		return sum + countItems(item);
	}, 1);
};

// Return an empty promise after the output.txt file has been written.
var generateOutput = function(metabook, builddir, options) {
	var status = options.status;
	status.createStage(countItems(metabook), 'Processing collection');
	status.report(null, metabook.title);

	// create output stream
	var writeStream;
	if (options.output) {
		writeStream = fs.createWriteStream(options.output);
	} else {
		// trivially wrap process.stdout so we don't get an error when
		// pipe() tries to close it (stdout can't be closed w/o throwing)
		writeStream = new stream.Writable({ decodeStrings: true });
		writeStream._write = function(chunk, encoding, callback) {
			return process.stdout.write(chunk, callback);
		};
	}

	// book or article?
	var hasChapters =
		metabook.items.some(function(it) { return it.type === 'chapter'; });
	var singleItem = (!hasChapters) && metabook.items.length <= 1;
	// default language (for chapter headings, page numbers, etc)
	// CLI --lang option overrides
	var collectionLanguage = options.lang || metabook.lang || 'en';
	var usedLanguages = new Set();
	usedLanguages.add(collectionLanguage);

	var format = new Formatter(writeStream, options);

	// emit title, subtitle, etc.
	var title = metabook.title;
	if (!title && metabook.items.length === 1) {
		title = metabook.items[0].title;
	}
	format.writeTitle(
		textEscape(title).replace(/\s+/g, ' '),
		metabook.subtitle ? textEscape(metabook.subtitle).replace(/\s+/g, ' ')
			: null
	);

	if (metabook.summary) {
		format.writeSummary(textEscape(metabook.summary).replace(/\s+/g, ' '));
	}

	var pdb = new Db(
		path.join(builddir, 'bundle', 'parsoid.db'), { readonly: true }
	);
	var sidb = new Db(
		path.join(builddir, 'bundle', 'siteinfo.db'), { readonly: true }
	);
	var write = {};
	write.article = function(item) {
		console.assert(item.type === 'article');
		status.report('Processing article', item.title);
		var revid = item.revision;
		var document, base = '', articleLanguage;
		var key = (item.wiki ? (item.wiki+'|') : '') + revid;
		return pdb.get(key, 'nojson').then(function(data) {
			document = domino.createDocument(data);
			var baseElem = document.querySelector('head > base[href]');
			if (baseElem) {
				base = baseElem.getAttribute('href').
					replace(/^\/\//, 'https://');
			}
		}).then(function() {
			// get the siteinfo for the article's wiki
			return sidb.get(metabook.wikis[item.wiki].baseurl);
		}).then(function(siteinfo) {
			articleLanguage = siteinfo.general.lang || collectionLanguage;
		}).then(function() {
			var visitor = new Visitor(document, format, {
				base: base,
				noWrap: options.noWrap,
				noRefs: options.noRefs,
				singleItem: singleItem,
				hasChapters: hasChapters,
				lang: collectionLanguage,
				dir: Polyglossia.lookup(collectionLanguage).dir
			});
			var h1 = document.createElement('h1');
			var span = document.createElement('span');
			h1.appendChild(span);
			span.textContent = item.title;
			span.lang = articleLanguage;
			visitor.visit(h1); // emit document title!
			document.body.lang = document.body.lang || articleLanguage;
			visitor.visit(document.body);
			visitor.usedLanguages.forEach(function(l){ usedLanguages.add(l); });
			format.paragraphBreak();
			// wait for buffer to empty before continuing
			// (ensure we don't end up buffering the entire collection!)
			return format.flush();
		});
	};
	write.chapter = function(item) {
		console.assert(item.type === 'chapter');
		status.report('Processing chapter', item.title);
		format.writeHeading(0, textEscape(item.title));
		return P.forEachSeq(item.items, write.article);
	};

	return P.forEachSeq(metabook.items, function(item) {
		return write[item.type](item);
	}).then(function() {
		return format.flush();
	}).then(function() {
		return P.call(writeStream.end, writeStream, '');
	});
};

// Return a promise for an exit status (0 for success) after the bundle
// specified in the options has been converted.
var convert = function(options) {
	var status = options.status = new StatusReporter(2, function(msg) {
		if (options.log && options.output) {
			var file = msg.file ? (': ' + msg.file) : '';
			options.log('['+msg.percent.toFixed()+'%]', msg.status + file);
		}
	});
	var metabook, builddir;
	return when.resolve().then(function() {
		// unpack the bundle
		return unpackBundle(options);
	}).then(function(args) {
		metabook = args.metabook;
		builddir = args.builddir;
	}).then(function() {
		// generate the plaintext
		return generateOutput(metabook, builddir, options);
	}).then(function() {
		status.createStage(0, 'Done');
		return 0; // success!
	}, function(err) {
		// xxx clean up?
		if (options.debug) {
			throw err;
		}
		// xxx send this error to parent process?
		console.error('Error:', err);
		return 1;
	});
};

module.exports = {
	version: json.version, // version # for this code
	convert: convert
};
