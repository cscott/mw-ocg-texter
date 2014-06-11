/* global describe, it */
"use strict";
require('es6-shim');
require('prfun');

var assert = require('assert');
var fs = require('fs');
var path = require('path');

var texter = require('../');

// ensure that we don't crash on any of our sample inputs
describe("Basic crash test", function() {
	['tao.zip', 'us.zip', 'std_dev.zip'].forEach(function(bundle) {
		describe(bundle, function() {
			it('should compile to plaintext', function(done) {
				this.timeout(0);
				var filename = path.join(__dirname, '..', 'samples', bundle);
				return texter.convert({
					bundle: filename,
					output: filename + '.txt',
					log: function() { /* suppress logging */ }
				}).then(function(statusCode) {
					assert.equal(statusCode, 0);
				}).finally(function() {
					try {
						fs.unlinkSync(filename + '.txt');
					} catch (e) { }
				}).done(
					function() { done(); },
					function(err) { done(err); }
				);
			});
		});
	});
});
