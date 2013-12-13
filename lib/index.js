require('es6-shim');

var json = require('../package.json');

var domino = require('domino');
var fs = require('fs');
var guard = require('when/guard');
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

/* Document node visitor class.  Collects LaTeX output as it traverses the
 * document tree. */
var Visitor = function(document, options) {
	this.document = document;
	this.options = options;
	this.output = [];
	this.templates = Object.create(null);
	this.base = options.base || '';
	this.currentLanguage = this.tocLanguage = options.lang || 'en';
	this.currentDirectionality = options.dir || 'ltr';
	this.usedLanguages = new Set();
	this.insideParagraph = false;
};

// Helper function -- collect all text from the children of `node` as
// HTML non-block/TeX non-paragraph content.  Invoke `f` with the result,
// suitable for inclusion in a TeX non-paragraph context.
Visitor.prototype.collect = function(node, f) {
	var o = this.output, inside = this.insideParagraph;
	this.output = [];
	this.insideParagraph = false;
	this.visitChildren(node);
	// combine lines, compress paragraphs
	var text = this.output.join('\n').
		replace(/(^|\n)%[^\n]*(\n|$)/g, '$1'). // remove comments
		replace(/%\n\s*/g, ''). // remove escaped newlines
		replace(/%$/, '').
		replace(/^\{\}/, ''). // remove escape for start of line whitespace
		replace(/\n\n+/g, '\n'); // remove paragraphs
	this.output = o;
	this.insideParagraph = inside;
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
			this.output.push(text);
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
	this.output.push("");
	var o = this.output;
	this.output = []; // make sure we don't emit a linebreak immediately
	this.visitChildren(node);
	// ok, emit this entire section as a paragraph.
	var para = this.output.join(' ').replace(/\s+/g, ' ').trim() + '\n';
	this.output = o;
	this.output.push(para);
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
	'1': '\u2090',
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
			this.output.push(contents.replace(/[\s\S]/g, function(c) {
				return submap[c];
			}));
		} else {
			// throw the subscript away
		}
	});
};

Visitor.prototype.visitSUP = function(node) {
	return this.collect(node, function(contents) {
		if (supre.test(contents)) {
			this.output.push(contents.replace(/[\s\S]/g, function(c) {
				return supmap[c];
			}));
		} else {
			// throw the superscript away
		}
	});
};

/*
Visitor.prototype.visitCENTER = function(node) {
	this.output.push('\\begin{center}');
	this.visitChildren(node);
	this.output.push('\\end{center}');
};
*/

Visitor.prototype.visitBR = function(node) {
	/* jshint unused: vars */
	this.output.push("\n");
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
		this.output.push("\n" + contents + "\n");
	});
};

Visitor.prototype.visitH1 = function(node) { return this.visitHn(node, 1); };
Visitor.prototype.visitH2 = function(node) { return this.visitHn(node, 2); };
Visitor.prototype.visitH3 = function(node) { return this.visitHn(node, 3); };
Visitor.prototype.visitH4 = function(node) { return this.visitHn(node, 4); };
Visitor.prototype.visitH5 = function(node) { return this.visitHn(node, 5); };
Visitor.prototype.visitH6 = function(node) { return this.visitHn(node, 6); };

Visitor.prototype['visitREL=dc:references'] = function(node) {
	return this.visitSUP(node);
};

Visitor.prototype.visitUL = function(node) {
	if (!DomUtil.first_child(node)) { return; /* no items */ }
	this.output.push('\\begin{itemize}');
	this.visitChildren(node);
	this.output.push('\\end{itemize}');
};

Visitor.prototype.visitOL = function(node) {
	if (!DomUtil.first_child(node)) { return; /* no items */ }
	this.output.push('\\begin{enumerate}');
	this.visitChildren(node);
	this.output.push('\\end{enumerate}');
};

Visitor.prototype.visitLI = function(node) {
	this.output.push('\\item %');
	this.insideParagraph = true;
	this.visitChildren(node);
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

	// ok, generate description or quotation environment
	var envName = sawDT ? 'description' :
		this.options.parindent ? 'quotation' : 'quote';
	var wasBlockQuote = this.inBlockQuote;
	this.inBlockQuote = !sawDT;
	this.output.push('\\begin{'+envName+'}');
	// ensure that there's an item before any contents
	if (sawDT &&
		!(child.nodeType === node.ELEMENT_NODE && child.nodeName === 'DT')) {
		this.output.push('\\item');
	}
	this.visitChildren(node);
	this.output.push('\\end{'+envName+'}');
	this.inBlockQuote = wasBlockQuote;
};

Visitor.prototype.visitDT = function(node) {
	return this.collect(node, function(contents) {
		this.output.push('\\item[' + contents + '] %');
		this.insideParagraph = true;
	});
};

Visitor.prototype.visitDD = function(node) {
	if (this.inBlockQuote) {
		return this.visitP(node);
	}
	// verify that previous line was the DT, otherwise add blank DT
	var prev = DomUtil.node_before(node);
	if (!(prev === null || prev.nodeName === 'DT')) {
		this.output.push('\\item');
		this.insideParagraph = true;
	}
	this.visitChildren(node);
};

Visitor.prototype.visitLI = function(node) {
	this.output.push('\\item %');
	this.insideParagraph = true;
	this.visitChildren(node);
};

Visitor.prototype.visitBLOCKQUOTE = function(node) {
	this.output.push('\\begin{quotation}');
	this.visitChildren(node);
	this.output.push('\\end{quotation}');
};

Visitor.prototype['visitREL=mw:referencedBy'] = function(node) {
	// hide this span
	/* jshint unused: vars */
};

Visitor.prototype['visitTYPEOF=mw:Extension/references'] = function(node) {
	if (!node.childNodes.length) { return; /* no items */ }
	this.insideParagraph = false;
	this.output.push('\\begin{enumerate}\\small');
	for (var i = 0, n = node.childNodes.length; i < n; i++) {
		var ref = node.childNodes[i];
		var name = textEscape('[' + (i+1) + ']');
		if (ref.id) {
			name = '\\hypertarget{' + ref.id + '}{' + name + '}';
		}
		this.output.push('\\item[' + name + ']');
		this.visitChildren(ref);
	}
	this.output.push('\\end{enumerate}');
	this.insideParagraph = false;
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
	// xxx enforce line breaks before?
	var r = this.visitChildren(node);
	this.visitBR(node); // enforce line break after
	return r;
};

// ---------------------------------------------------------------------
// Bundle, image, and file processing

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

	var output = fs.createWriteStream(path.join(builddir, 'output.txt'), {
		encoding: 'utf8'
	});
	// book or article?
	var hasChapters =
		metabook.items.some(function(it) { return it.type === 'chapter'; });
	var singleItem = (!hasChapters) && metabook.items.length <= 1;
	// default language (for chapter headings, page numbers, etc)
	// CLI --lang option overrides
	var collectionLanguage = options.lang || metabook.lang || 'en';
	var usedLanguages = new Set();
	usedLanguages.add(collectionLanguage);

	// emit title, subtitle, etc.
	var title = metabook.title;
	if (!title && metabook.items.length === 1) {
		title = metabook.items[0].title;
	}
	output.write(textEscape(title) + '\n');
	if (metabook.subtitle) {
		output.write(textEscape(metabook.subtitle) + '\n');
	}
	output.write('\n');

	if (metabook.summary) {
		// XXX do something with metabook.summary
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
		var outfile = path.join(
			builddir, 'output', item.wiki + '-' + revid + '.txt'
		);
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
			var visitor = new Visitor(document, {
				base: base,
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
			var result = visitor.output.join(''); // XXX?
			visitor.usedLanguages.forEach(function(l){ usedLanguages.add(l); });
			return P.call(fs.writeFile, fs, outfile, result, 'utf8');
		});
	};
	write.chapter = function(item) {
		console.assert(item.type === 'chapter');
		status.report('Processing chapter', item.title);
		if ('columns' in item && columns !== item.columns) {
			columns = item.columns;
			output.write(columns === 1 ? '\\onecolumn\n' : '\\twocolumn\n');
		}
		output.write('\\chapter{' + textEscape(item.title) + '}\n');
		return P.forEachSeq(item.items, write.article);
	};

	return P.forEachSeq(metabook.items, function(item) {
		return write[item.type](item);
	}).then(function() {
		return P.call(output.end, output, '');
	});
};

// Return a promise for an exit status (0 for success) after the bundle
// specified in the options has been converted.
var convert = function(options) {
	var status = options.status = new StatusReporter(2, function(msg) {
		if (options.log) {
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
