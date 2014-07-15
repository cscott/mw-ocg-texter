# mw-ocg-texter
[![NPM][NPM1]][NPM2]

[![Build Status][1]][2] [![dependency status][3]][4] [![dev dependency status][5]][6]

Converts mediawiki collection bundles (as generated by [mw-ocg-bundler]) to
stripped plaintext.

This is a proof-of-concept, but it could be used to archive or embed the
textual content of wikipedia in a minimal amount of space.

## Installation

Node version 0.8 and 0.10 are tested to work.

Install the node package dependencies.
```
npm install
```

Install other system dependencies.
```
apt-get install unzip
```

## Generating bundles

You may wish to install the [mw-ocg-bundler] npm package to create bundles
from wikipedia articles.  The below text assumes that you have done
so; ignore the `mw-ocg-bundler` references if you have bundles from
some other source.

## Running

To generate a plaintext file named `out.txt` from the English
(`enwiki`) wikipedia article "United States":
```
mw-ocg-bundler -o us.zip --prefix enwiki "United States"
bin/mw-ocg-texter -o out.txt us.zip
```

The default format does 80-column word wrap.  If you would like to
use "semantic" new lines (that is, newlines end paragraphs and there
are no newlines within paragraphs) use the `--no-wrap`
option:
```
bin/mw-ocg-texter --no-wrap -o out.txt us.zip
```

For other options, see:
```
bin/mw-ocg-texter --help
```

## Related Projects

* [mw-ocg-bundler][]
* [mw-ocg-latexer][]

## License

GPLv2

(c) 2013-2014 by C. Scott Ananian

[mw-ocg-bundler]: https://github.com/wikimedia/mediawiki-extensions-Collection-OfflineContentGenerator-bundler
[mw-ocg-latexer]: https://github.com/wikimedia/mediawiki-extensions-Collection-OfflineContentGenerator-latex_renderer

[NPM1]: https://nodei.co/npm/mw-ocg-texter.svg
[NPM2]: https://nodei.co/npm/mw-ocg-texter/

[1]: https://travis-ci.org/cscott/mw-ocg-texter.svg
[2]: https://travis-ci.org/cscott/mw-ocg-texter
[3]: https://david-dm.org/wikimedia/mediawiki-extensions-Collection-OfflineContentGenerator-text_renderer.svg
[4]: https://david-dm.org/wikimedia/mediawiki-extensions-Collection-OfflineContentGenerator-text_renderer
[5]: https://david-dm.org/wikimedia/mediawiki-extensions-Collection-OfflineContentGenerator-text_renderer/dev-status.svg
[6]: https://david-dm.org/wikimedia/mediawiki-extensions-Collection-OfflineContentGenerator-text_renderer#info=devDependencies
