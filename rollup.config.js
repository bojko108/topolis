import git from 'git-rev-sync';
import replace from 'rollup-plugin-replace';
import babel from 'rollup-plugin-babel';
import resolve from 'rollup-plugin-node-resolve';
import commonjs from 'rollup-plugin-commonjs';
import uglify from 'rollup-plugin-uglify';

var pjson = require('./package.json');

const banner = `// topolis. See https://github.com/bojko108/topolis`;

export default {
  entry: 'src/topolis.js',
  format: 'umd',
  moduleName: 'topolis',
  banner,
  plugins: [
    replace({
      npm_package_version: pjson.version,
      git_hash: git.short()
    }),
    resolve(),
    commonjs(),
    babel({
      presets: [
        [
          'env',
          {
            modules: false,
            targets: {
              browsers: ['> 2%']
            }
          }
        ]
      ],
      plugins: ['external-helpers'],
      babelrc: false
    }),
    uglify({
      output: {
        comments: (node, token) => token.line < 4
      }
    })
  ]
};
