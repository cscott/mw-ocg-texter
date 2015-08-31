"use strict";
require('core-js/shim');
var Promise = require('prfun');
var main = require('./');
var bundler = require('mw-ocg-bundler');

var convert = module.exports.convert = function(options) {
	// make metabook.
	return bundler.metabook.fromArticles([{
		prefix: options.prefix,
		domain: options.domain,
		title: options.title
	}], options).then(function(metabook) {
		var item = metabook.items[0];
		var Parsoid = new bundler.parsoid(
			metabook.wikis, options.apiVersion, options.log
		);
		var siteinfo = options.siteinfo || new bundler.siteinfo(
			metabook.wikis, options.log
		);
		return siteinfo.fetch(item.wiki).then(function(si) {
			return Parsoid.fetch(si, item.wiki, item.title, null, 2).then(function(pr) {
				var opts = Object.create(options);
				item.wiki = pr.wiki;
				item.title = pr.title;
				item.revision = pr.getRevisionId();
				// fake a db
				opts.pdb = {
					get: function(key, nojson) {
						return Promise.resolve({ document: pr.document });
					}
				};
				opts.sidb = {
					get: function(key, nojson) {
						return Promise.resolve(si);
					}
				};
				opts.status = {
					createStage: function(){},
					report: function(){},
				};
				return main.generateOutput(metabook, '/dont/use/this', opts);
			});
		});
	});
};
