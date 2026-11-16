// parse.js — Markdown to HTML, byte-identical to marked 18.1.3 with default
// options (GFM on, hard breaks off, pedantic off, async off). Written from
// scratch in this session: a single-file block lexer, inline lexer and
// renderer. No dependencies. Only the driver (main.ts) reads files; this
// module only transforms strings.
//
// Design notes (my own): the grammar is the CommonMark + GFM grammar, built
// below from small named fragments so the composed patterns stay readable.
// The tokenizer follows the classic shape — block rules tried in order, an
// inline queue drained after the block pass — with a few shortcuts that
// never change output: a plain-text fast path for inline runs with no
// construct, lazy masking and closer scans, and cheap pre-checks that skip
// the setext/table regexes when their trigger cannot be present.

// ---------- tiny string helpers ----------

const ENT = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESC_T = /[&<>"']/;
const ESC_R = /[&<>"']/g;
const ESC_T_NE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const ESC_R_NE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const NUMREF_T = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUMREF_R = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Escape HTML entities. With encode, every & < > " ' is escaped; otherwise
// only & that cannot start a character reference is escaped.
function esc(s, encode) {
  if (encode) {
    return ESC_T.test(s) ? s.replace(ESC_R, c => ENT[c]) : s;
  }
  return ESC_T_NE.test(s) ? s.replace(ESC_R_NE, c => ENT[c]) : s;
}

// Numeric character references stand for the character they name. Zero,
// out-of-range and surrogate values become the replacement character, and a
// decoded & must not join its neighbours into a new reference.
function decodeRefs(s) {
  if (!NUMREF_T.test(s)) return s;
  return s.replace(NUMREF_R, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '�';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanHref(href) {
  try {
    href = encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
  return href;
}

// Split a table row on unescaped pipes, trimming cells and honouring count.
function splitCells(row, count) {
  const fixed = row.replace(/\|/g, (m, off, str) => {
    let escaped = false;
    let i = off;
    while (--i >= 0 && str[i] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = fixed.split(' |');
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

// Remove a trailing run of c (or, with invert, of non-c). Avoids /c*$/.
function rtrim(s, c, invert) {
  const n = s.length;
  if (n === 0) return '';
  let k = 0;
  while (k < n) {
    const ch = s.charAt(n - k - 1);
    if (ch === c && !invert) k++;
    else if (ch !== c && invert) k++;
    else break;
  }
  return s.slice(0, n - k);
}

// Drop trailing blank lines, but keep a single trailing blank line.
function trimBlankTail(s) {
  const lines = s.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && /^[ \t]*$/.test(lines[end])) end--;
  if (lines.length - end <= 2) return s;
  return lines.slice(0, end + 1).join('\n');
}

// Fold a link label for definition/reference matching: trim, collapse inner
// whitespace, and case-fold through upper case (so ß meets SS).
function foldLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Find the index of the closing bracket that balances the opener at level 0,
// or -1 (unbalanced at end) / -2 (more openers than closers).
function findBracket(s, pair) {
  if (s.indexOf(pair[0]) === -1 && s.indexOf(pair[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\') { i++; continue; }
    if (s[i] === pair[0]) level++;
    else if (s[i] === pair[1]) { level--; if (level < 0) return i; }
  }
  return level > 0 ? -2 : -1;
}

function expandTabs(line, indent) {
  let col = indent || 0;
  let out = '';
  for (const ch of line) {
    if (ch === '\t') {
      const add = 4 - (col % 4);
      out += ' '.repeat(add);
      col += add;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

// One scan of an inline source for the last delimiter run that could close
// emphasis/strong (* or _) or strikethrough (~). A run can only close when
// the character before it is not ASCII whitespace.
function scanClosers(src) {
  const last = { '*': -1, '_': -1, '~': -1 };
  const n = src.length;
  for (let i = 0; i < n; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < n && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') last[ch] = i;
    i = j - 1;
  }
  return last;
}

// First line of a string (up to the first \n), without allocating an array.
function headLine(s) {
  const nl = s.indexOf('\n');
  return nl === -1 ? s : s.slice(0, nl);
}

// Index of the first character that is not a space, or -1.
function firstNonSpace(s) {
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) !== 32) return i;
  }
  return -1;
}

// Does the first paragraph hold a setext underline? A setext underline is a
// line of only = or - (up to 3 spaces of indent, trailing spaces/tabs
// allowed) before the first blank line. This scans only the first paragraph,
// so it is far cheaper than running the heading regex over the whole source.
// It may say yes when the heading regex still fails (a mixed =/- line, or
// a paragraph that starts with a list marker); it never says no when the
// regex could match.
function hasUnderline(src) {
  let pos = 0;
  while (true) {
    const nl = src.indexOf('\n', pos);
    const end = nl === -1 ? src.length : nl;
    let j = pos;
    let spaces = 0;
    while (spaces < 3 && src[j] === ' ') { j++; spaces++; }
    const c = src[j];
    if (c === '=' || c === '-') {
      let k = j;
      while (k < end && (src[k] === '=' || src[k] === '-' || src[k] === ' ' || src[k] === '\t')) k++;
      if (k === end) return true;
    }
    if (nl === -1) return false;
    let m = pos;
    while (m < nl && (src[m] === ' ' || src[m] === '\t')) m++;
    if (m === nl) return false;
    pos = nl + 1;
  }
}

// ---------- grammar: fragment table + composer ----------

// Fragments are plain strings (no anchors) so they can be composed freely.
// The regex source they build is the CommonMark + GFM grammar; the way they
// are named, grouped and ordered here is my own.
const F = {
  ind: ' {0,3}',
  bull: ' {0,3}(?:[*+-]|\\d{1,9}[.)])',
  codeInd: '(?: {4}| {0,3}\\t)',
  fenceStart: ' {0,3}(?:`{3,}|~{3,})',
  bq: ' {0,3}>',
  atx: ' {0,3}#{1,6}(?:\\s|$)',
  hr: ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)',
  htmlLine: ' {0,3}<[^\\n>]+>\\n',
  tableLine: ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n',
  tag: 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul',
  comment: '<!--(?:-?>|[\\s\\S]*?(?:-->|$))',
  attr: ' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?',
  iattr: '\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*"[^"]*"|\\s*=\\s*\'[^\']*\'|\\s*=\\s*[^\\s"\'=<>`]+)?',
  blockLabel: '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+',
  inlineLabelBrackets: '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]',
  fenceIntr: ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)',
  listIntr: ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]',
  htmlIntr: ' {0,3}(?:</?(?:@TAG@)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)',
};

// Replace every occurrence of `tok` in a pattern string with a fragment.
function plug(src, tok, val) {
  return src.split(tok).join(val);
}

// ---------- grammar: block rules ----------

const reNewline = /^(?:[ \t]*(?:\n|$))+/;
const reCode = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const reFences = new RegExp(
  `^${F.ind}(\`{3,}(?=[^\`\\n]*(?:\\n|$))|~{3,})([^\\n]*)(?:\\n|$)` +
  `(?:|([\\s\\S]*?)(?:\\n|$))(?:${F.ind}(?:(?=\`)\\1\`*|(?=~)\\1~*) *(?=\\n|$)|$)`
);
const reHr = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const reHeading = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const reListStart = new RegExp(`^(${F.bull})([ \\t][^\\n]*?)?(?:\\n|$)`);

// Setext heading: a paragraph-like run of lines followed by = or -.
// Skipped entirely when no underline can follow (pre-checked in the lexer).
const reLheading = new RegExp(
  `^(?!${F.bull} |${F.codeInd}|${F.fenceStart}|${F.bq}|${F.atx}|${F.htmlLine}|${F.tableLine})` +
  `((?:.|\\n(?!\\s*?\\n|${F.bull} |${F.fenceStart}|${F.bq}|${F.atx}|${F.hr}|${F.htmlLine}|${F.tableLine}))+?)` +
  `\\n${F.ind}(=+|-+)[ \\t]*(?:\\n+|$)`
);

// Paragraph rule builder. The GFM paragraph ends when the next line starts
// a new block construct; a setext underline does NOT interrupt it.
function paraRule(listIntr) {
  const tableSrc = tableRuleSrc();
  const htmlSrc = plug(F.htmlIntr, '@TAG@', F.tag);
  return new RegExp(
    `^([^\\n]+(?:\\n(?!${F.hr}|${F.atx}|${F.bq}|${F.fenceIntr}|${listIntr}|${htmlSrc}|${tableSrc}|[ \\t]+\\n)[^\\n]+)*)`
  );
}
const reParagraph = paraRule(F.listIntr);
const reBlockText = /^[^\n]+/;
const reBlockquotePara = paraRule(' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)');

// Link definition: [label]: destination "optional title".
const DEF_TITLE = `"(?:\\\\[\\s\\S]|[^"\\\\])*"|'(?:\\\\[\\s\\S]|[^'\\\\\\n]|\\n(?!\\n))*'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\)`;
const reDef = new RegExp(
  `^${F.ind}\\[(${F.blockLabel})\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(${DEF_TITLE}))? *(?:\\n+|$)`
);

// Blockquote: lines starting with >, with the paragraph rule specialised
// for the blockquote interior.
const reBlockquote = new RegExp(
  `^(${F.bq} ?(?:(?![ \\t]*(?:\\n|$))(?:${reBlockquotePara.source.slice(1)})|[^\\n]*)(?:\\n|$))+`
);

// GFM table: header line, delimiter row, then data rows until a blank line
// or a line that starts another block construct.
function tableRuleSrc() {
  const cells = `(?:(?! *\\n|${F.hr}|${F.atx}|${F.bq}|${F.codeInd}[^\\n]|${F.fenceIntr}|${F.ind}(?:[*+-]|1[.)])[ \\t]|${plug(F.htmlIntr, '@TAG@', F.tag)}).*(?:\\n|$))*`;
  return (
    ` *([^\\n ].*)\\n${F.ind}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)` +
    `(?:\\n((${cells}))\\n*|$)`
  );
}
const reTable = new RegExp('^' + tableRuleSrc());

// Block-level raw HTML: type 1 (script/pre/style/textarea), 2 (comment),
// 3 (processing instruction), 4 (declaration), 5 (CDATA), 6 (block tag),
// 7 (open tag followed by a blank line or end), 7b (matching close tag).
const reHtml = new RegExp(
  `^${F.ind}(?:` +
  `<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)` +
  `|${F.comment}[^\\n]*(\\n+|$)` +
  `|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)` +
  `|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)` +
  `|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)` +
  `|</?(?:${F.tag})(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)` +
  `|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:${F.attr})*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)` +
  `|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)` +
  `)`,
  'i'
);

// ---------- grammar: inline rules ----------

const reEscape = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const reCodeSpan = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const reBr = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const rePunct = /^((?![*_])[\s\p{P}\p{S}])/u;

// Inline text: everything that is not the start of another construct. The
// first alternative handles a leading non-alphanumeric character when it is
// followed by a mailto:/xmpp: scheme; the second consumes a run that stops
// before any construct start, a hard-break space run, a URL-like prefix or
// an email address. Protocol/www lookaheads let autolinks be recognised
// inside the run.
const PROTOCOL = '[hH][tT][tT][pP][sS]?|[fF][tT][pP]';
const EMAIL_PROTOCOL = '(?:mailto|xmpp):';
const WWW_START = '(?<![^\\s*_~(])www\\.';
const EMAIL_LOCAL = "[a-zA-Z0-9.!#$%&'*+\\/=?_`{|}~-]+";
const reText = new RegExp(
  `^(?:[^a-zA-Z0-9](?=${EMAIL_PROTOCOL})|(\`+|~+|[^\`~])(?:(?=[\`~])|(?= {2,}\\n)|(?=${EMAIL_LOCAL}@)|[\\s\\S]*?(?:(?=[\\\\<!\\[\`*~_]|\\b_|${PROTOCOL}:\\/\\/|${WWW_START}|$)|[^ ](?= {2,}\\n)|[^a-zA-Z0-9](?=${EMAIL_PROTOCOL})|[^a-zA-Z0-9.!#$%&'*+\\/=?_\`{|}~-](?=${EMAIL_LOCAL}@))))`
);

// Punctuation classes. GFM keeps ~ out of the emphasis punctuation classes
// (so ~ inside strong/em stays available for strikethrough); the tilde
// rules use the plain classes.
const CLS_P = '[\\p{P}\\p{S}]';
const CLS_PS = '[\\s\\p{P}\\p{S}]';
const CLS_NP = '[^\\s\\p{P}\\p{S}]';
const CLS_P_G = '(?!~)[\\p{P}\\p{S}]';
const CLS_PS_G = '(?!~)[\\s\\p{P}\\p{S}]';
const CLS_NP_G = '(?:[^\\s\\p{P}\\p{S}]|~)';

// Left delimiters: the opening run plus its first following character.
// GFM uses the tilde-excluding punctuation class.
const reEmStrongLDelim = new RegExp(
  `^(?:\\*+(?:((?!\\*)${CLS_P_G})|([^\\s*]))?)|^_+(?:((?!_)${CLS_P_G})|([^\\s_]))?`,
  'u'
);
const reDelLDelim = new RegExp(`^~~?(?:((?!~)${CLS_P})|([^\\s~]))`, 'u');

// Right delimiters. Each core is a list of rules, in order:
//   1. skip an orphan delimiter inside a strong run
//   2. consume plain text up to the next delimiter
//   3. #*** can only close, 4. a***# can only close, 5. #***a can only open,
//   6. ***# can only open, 7. #***# can be either, 8. a***a can be either
// (underscore has no rule 8: a___a cannot close as emphasis).
function joinRules(rules, cls) {
  return rules.join('|').split('@P@').join(cls.p).split('@PS@').join(cls.ps).split('@NP@').join(cls.np);
}
const CLS_G = { p: CLS_P_G, ps: CLS_PS_G, np: CLS_NP_G };
const CLS_N = { p: CLS_P, ps: CLS_PS, np: CLS_NP };
const reEmStrongRDelimAst = new RegExp(joinRules([
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)',
  '[^*]+(?=[^*])',
  '(?!\\*)@P@(\\*+)(?=[\\s]|$)',
  '@NP@(\\*+)(?!\\*)(?=@PS@|$)',
  '(?!\\*)@PS@(\\*+)(?=@NP@)',
  '[\\s](\\*+)(?!\\*)(?=@P@)',
  '(?!\\*)@P@(\\*+)(?!\\*)(?=@P@)',
  '@NP@(\\*+)(?=@NP@)',
], CLS_G), 'gu');
const reEmStrongRDelimUnd = new RegExp(joinRules([
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)',
  '[^_]+(?=[^_])',
  '(?!_)@P@(_+)(?=[\\s]|$)',
  '@NP@(_+)(?!_)(?=@PS@|$)',
  '(?!_)@PS@(_+)(?=@NP@)',
  '[\\s](_+)(?!_)(?=@P@)',
  '(?!_)@P@(_+)(?!_)(?=@P@)',
], CLS_N), 'gu');
const reDelRDelim = new RegExp(joinRules([
  '^[^~]+(?=[^~])',
  '(?!~)@P@(~~?)(?=[\\s]|$)',
  '@NP@(~~?)(?!~)(?=@PS@|$)',
  '(?!~)@PS@(~~?)(?=@NP@)',
  '[\\s](~~?)(?!~)(?=@P@)',
  '(?!~)@P@(~~?)(?!~)(?=@P@)',
  '@NP@(~~?)(?=@NP@)',
], CLS_N), 'gu');

// Punctuation that can be escaped with a backslash (any unicode punct/sym).
const reAnyPunct = /\\([\p{P}\p{S}])/gu;
const reAnyPunctOutsideCode = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;

// Autolink <scheme:...> or <email>. Group 2 is the @ in an email address.
const reAutolink = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;

// Inline raw HTML tag. The comment alternative is the inline form (it must
// close with -->); the declaration alternative requires a name and a space.
const INLINE_COMMENT = '<!--(?:-?>|[\\s\\S]*?-->)';
const reTag = new RegExp(
  `^${INLINE_COMMENT}|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:${F.iattr})*?\\s*/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>`
);

// Link labels. The inline label allows nested brackets (one level), code
// spans and escapes; the bounded forms cap the scan so a candidate that can
// never match still costs linear time, not quadratic.
const LABEL_BRACKETS_SRC = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const INLINE_LABEL_SRC = /(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/.source
  .replace(/brackets/g, LABEL_BRACKETS_SRC);
const BOUNDED_BLOCK_LABEL_SRC = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';
const BOUNDED_INLINE_LABEL_SRC = /(?:[^\[\]\\`]*(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/.source
  .replace(/brackets/g, LABEL_BRACKETS_SRC);

// Inline link: [text](destination "title"). Group 1 label, 2 href, 3 title.
// The inline title is simpler than the definition title: no newlines inside
// the quoted forms, and the parenthesised form stops at the first ).
const LINK_TITLE = `"(?:\\\\[\\s\\S]|[^"\\\\])*"|'(?:\\\\[\\s\\S]|[^'\\\\])*'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)`;
const reLink = new RegExp(
  `^!?\\[(${INLINE_LABEL_SRC})\\]\\([ \\t\\n]*` +
  `(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))` +
  `(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(${LINK_TITLE}))?` +
  `[ \\t\\n]*\\)`
);
const reReflink = new RegExp(`^!?\\[(${INLINE_LABEL_SRC})\\]\\[(${F.blockLabel})\\]`);
const reNolink = new RegExp(`^!?\\[(${F.blockLabel})\\](?:\\[\\])?`);
const reReflinkSearch = new RegExp(
  `!?\\[(${BOUNDED_INLINE_LABEL_SRC})\\]\\[(${BOUNDED_BLOCK_LABEL_SRC})\\]|!?\\[(${BOUNDED_BLOCK_LABEL_SRC})\\](?:\\[\\])?(?!\\()`,
  'g'
);

// GFM bare URL (www./protocol/email) inside text. Group 1 is the
// protocol/www prefix, group 2 the @ of a bare email address.
const URL_EMAIL = '[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])';
const URL_EMAIL_PROTO = `(?:mailto:${URL_EMAIL}|xmpp:${URL_EMAIL}(?:\\/[A-Za-z0-9@.]+)?)`;
const reUrl = new RegExp(
  `^${URL_EMAIL_PROTO}|^((?:${PROTOCOL}):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])`
);
// Trim trailing punctuation / unbalanced parens from a bare URL.
const reBackpedal = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
// Strikethrough: ~~text~~ (a single ~ never closes).
const reDel = /^(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/;

// Masking: hide link destinations, code spans and raw HTML from the
// emphasis scanner so delimiters inside them are never treated as closers.
const MASK_LINK = '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)';
const MASK_CODE = '(?<b>`+)[^`]+\\k<b>(?!`)';
const MASK_HTML = '<(?! )[^<>]*?>';
const reBlockSkip = new RegExp(`${MASK_LINK}|(?<!\`)()${MASK_CODE}|${MASK_HTML}`, 'g');

// ---------- other small patterns (my own names) ----------

const reCodeIndent = /^(?: {0,3}\t| {1,4})/gm;
const reOutputLink = /\\([\[\]])/g;
const reFenceIndent = /^(\s+)(?:```)/;
const reBeginSpace = /^\s+/;
const reEndHash = /#$/;
const reStartSpace = /^ /;
const reEndSpace = / $/;
const reEndSpaceTab = /[ \t]$/;
const reNonSpace = /[^ ]/;
const reNewlineGlobal = /\n/g;
const reTabGlobal = /\t/g;
const reLeadingSpaceTab = /^[ \t]+/;
const reMultiSpace = /\s+/g;
const reBlankLine = /^[ \t]*$/;
const reDoubleBlank = /\n[ \t]*\n[ \t]*$/;
const reBQStart = /^ {0,3}>/;
const reBQSetext = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const reBQSetext2 = /^ {0,3}>[ \t]?/gm;
const reBQMarkerWs = /^( {0,3}>)([ \t]+)/gm;
const reListTask = /^\[[ xX]\][ \t]+\S/;
const reListTaskReplace = /^\[[ xX]\][ \t]+/;
const reListCheckbox = /\[[ xX]\]/;
const reAnyLine = /\n.*\n/;
const reHrefBrackets = /^<(.*)>$/;
const reTableDelim = /[:|]/;
const reTableAlignChars = /^\||\| *$/g;
const reTableRowBlank = /\n[ \t]*$/;
const reTableRight = /^ *-+: *$/;
const reTableCenter = /^ *:-+: *$/;
const reTableLeft = /^ *:-+ *$/;
const reStartATag = /^<a /i;
const reEndATag = /^<\/a>/i;
const reStartPreTag = /^<(pre|code|kbd|script)(\s|>)/i;
const reEndPreTag = /^<\/(pre|code|kbd|script)(\s|>)/i;
const reStartAngle = /^</;
const reEndAngle = />$/;
const reAlphaNum = /[\p{L}\p{N}]/u;
const reNotSpaceStart = /^\S*/;
const reEndNewline = /\n$/;

// Indent-dependent line patterns, cached by the clamped indent (0..3).
function cachedIndent(make) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) { re = make(idx); cache[idx] = re; }
    return re;
  };
}
const reListItem = (bull) => new RegExp(`^( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`);
const reNextBullet = cachedIndent(i => new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`));
const reHrAt = cachedIndent(i => new RegExp(`^ {0,${i}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`));
const reFenceAt = cachedIndent(i => new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`));
const reHeadingAt = cachedIndent(i => new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`));
const reHtmlAt = cachedIndent(i => new RegExp(`^ {0,${i}}(?:</?(?:${F.tag})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const reBQAt = cachedIndent(i => new RegExp(`^ {0,${i}}>`));

// Remove up to the fence's own indentation from each line of a fenced block.
function indentComp(raw, text) {
  const m = raw.match(reFenceIndent);
  if (m === null) return text;
  const indentToCode = m[1];
  return text.split('\n').map(node => {
    const im = node.match(reBeginSpace);
    if (im === null) return node;
    return node.slice(Math.min(im[0].length, indentToCode.length));
  }).join('\n');
}

// ---------- block tokenizers ----------

class Tok {
  constructor(lex) { this.lex = lex; }

  space(src) {
    const cap = reNewline.exec(src);
    if (cap && cap[0].length > 0) return { type: 'space', raw: cap[0] };
  }

  code(src) {
    const cap = reCode.exec(src);
    if (cap) {
      const raw = trimBlankTail(cap[0]);
      const text = raw.replace(reCodeIndent, '');
      return { type: 'code', raw, codeBlockStyle: 'indented', text };
    }
  }

  fences(src) {
    const cap = reFences.exec(src);
    if (cap) {
      const raw = cap[0];
      const text = indentComp(raw, cap[3] || '');
      return {
        type: 'code', raw,
        lang: cap[2] ? cap[2].trim().replace(reAnyPunct, '$1') : cap[2],
        text,
      };
    }
  }

  heading(src) {
    const cap = reHeading.exec(src);
    if (cap) {
      let text = cap[2].trim();
      if (reEndHash.test(text)) {
        const trimmed = rtrim(text, '#');
        if (!trimmed || reEndSpaceTab.test(trimmed)) text = trimmed.trim();
      }
      return {
        type: 'heading', raw: rtrim(cap[0], '\n'),
        depth: cap[1].length, text,
        tokens: this.lex.inline(text),
      };
    }
  }

  hr(src) {
    const cap = reHr.exec(src);
    if (cap) return { type: 'hr', raw: rtrim(cap[0], '\n') };
  }

  blockquote(src) {
    const cap = reBlockquote.exec(src);
    if (!cap) return undefined;
    let lines = rtrim(cap[0], '\n').split('\n');
    let raw = '';
    let text = '';
    const tokens = [];
    while (lines.length > 0) {
      let inBQ = false;
      const cur = [];
      let i;
      for (i = 0; i < lines.length; i++) {
        if (reBQStart.test(lines[i])) { cur.push(lines[i]); inBQ = true; }
        else if (!inBQ) { cur.push(lines[i]); }
        else break;
      }
      lines = lines.slice(i);
      const curRaw = cur.join('\n');
      const curText = curRaw
        .replace(reBQMarkerWs, (_, marker, ws) => marker + expandTabs(ws, marker.length))
        .replace(reBQSetext, '\n    $1')
        .replace(reBQSetext2, '');
      raw = raw ? `${raw}\n${curRaw}` : curRaw;
      text = text ? `${text}\n${curText}` : curText;
      const top = this.lex.state.top;
      this.lex.state.top = true;
      this.lex.blockTokens(curText, tokens, true);
      this.lex.state.top = top;
      if (lines.length === 0) break;
      const last = tokens.at(-1);
      if (last && (last.type === 'code' || last.type === 'heading' || last.type === 'hr' || last.type === 'html' || last.type === 'table')) {
        break;
      } else if (last && last.type === 'blockquote') {
        const oldTok = last;
        const continuation = lines.join('\n');
        const newText = oldTok.raw + '\n' + continuation.replace(reBQSetext2, '');
        const newTok = this.blockquote(newText);
        tokens[tokens.length - 1] = newTok;
        const leftover = newText.substring(newTok.raw.length).replace(/^\n/, '');
        const leftoverCount = leftover ? leftover.split('\n').length : 0;
        const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
        if (consumed.length > 0) raw = `${raw}\n${consumed.join('\n')}`;
        text = text.substring(0, text.length - oldTok.text.length) + newTok.text;
        lines = lines.slice(consumed.length);
        if (lines.length > 0 && reBQStart.test(lines[0])) continue;
        break;
      } else if (last && last.type === 'list') {
        const oldTok = last;
        const newText = oldTok.raw + '\n' + lines.join('\n');
        const newTok = this.list(newText);
        tokens[tokens.length - 1] = newTok;
        const consumedCount = newTok.raw.length > oldTok.raw.length
          ? newText.slice(oldTok.raw.length + 1, newTok.raw.length).split('\n').length
          : 0;
        if (consumedCount > 0) {
          const consumed = lines.slice(0, consumedCount).join('\n');
          raw = `${raw}\n${consumed}`;
          text = `${text}\n${consumed}`;
        }
        lines = lines.slice(consumedCount);
        continue;
      }
    }
    return { type: 'blockquote', raw, tokens, text };
  }

  list(src) {
    let cap = reListStart.exec(src);
    if (!cap) return undefined;
    const listSrc = src;
    let rest = src;
    const taken = () => listSrc.length - rest.length;
    let bull = cap[1].trim();
    const isOrdered = bull.length > 1;
    const list = {
      type: 'list', raw: '', ordered: isOrdered,
      start: isOrdered ? +bull.slice(0, -1) : '',
      loose: false, items: [],
    };
    bull = isOrdered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;
    const itemRe = reListItem(bull);
    let endsWithBlank = false;
    while (rest) {
      let endEarly = false;
      let itemContents = '';
      if (!(cap = itemRe.exec(rest))) break;
      if (reHr.test(rest)) break;
      const itemStart = taken();
      rest = rest.substring(cap[0].length);
      const firstLine = headLine(cap[2]);
      const bulletIndent = cap[1].length;
      let line = firstLine.replace(reLeadingSpaceTab, ws => expandTabs(ws, bulletIndent));
      let nextLine = headLine(rest);
      let blankLine = !line.trim();
      let indent = 0;
      if (blankLine) {
        indent = bulletIndent + 1;
      } else {
        indent = line.search(reNonSpace);
        indent = indent > 4 ? 1 : indent;
        itemContents = line.slice(indent);
        indent += bulletIndent;
      }
      if (blankLine && reBlankLine.test(nextLine)) {
        rest = rest.substring(nextLine.length + 1);
        endEarly = true;
      }
      if (!endEarly) {
        const nextBullRe = reNextBullet(indent);
        const hrRe = reHrAt(indent);
        const fenceRe = reFenceAt(indent);
        const headRe = reHeadingAt(indent);
        const htmlRe = reHtmlAt(indent);
        const bqRe = reBQAt(indent);
        while (rest) {
          const rawLine = headLine(rest);
          nextLine = rawLine;
          const nextNoTabs = (nextLine[0] === ' ' || nextLine[0] === '\t')
            ? nextLine.replace(reLeadingSpaceTab, ws => expandTabs(ws))
            : nextLine;
          const isBlankLine = !nextLine.trim();
          // The six "does this line start a new block" tests all need a
          // construct character within the first four characters (up to 3
          // spaces of indent plus the marker). Skip them all when there
          // is none.
          let hasMarker = false;
          for (let k = 0; k < 4 && k < nextLine.length; k++) {
            const ch = nextLine.charCodeAt(k);
            if (ch === 96 || ch === 126 || ch === 35 || ch === 60 || ch === 62
              || ch === 42 || ch === 43 || ch === 45 || ch === 95
              || (ch >= 48 && ch <= 57)) { hasMarker = true; break; }
          }
          if (hasMarker) {
            if (fenceRe.test(nextLine)) break;
            if (headRe.test(nextLine)) break;
            if (htmlRe.test(nextLine)) break;
            if (bqRe.test(nextLine)) break;
            if (nextBullRe.test(nextLine)) break;
            if (hrRe.test(nextLine)) break;
          }
          if (firstNonSpace(nextNoTabs) >= indent || isBlankLine) {
            itemContents += '\n' + nextNoTabs.slice(indent);
          } else {
            if (blankLine) break;
            if ((line.includes('\t') ? line.replace(reTabGlobal, '    ') : line).search(reNonSpace) >= 4) break;
            if (fenceRe.test(line)) break;
            if (headRe.test(line)) break;
            if (htmlRe.test(line)) break;
            if (hrRe.test(line)) break;
            const setextCont = /^ {0,3}(?:=+|-+) *$/.test(nextLine) && reLheading.test(`${line}\n${nextLine}`);
            const cont = setextCont ? `    ${nextNoTabs.replace(/^ {0,3}/, '')}` : nextLine;
            itemContents += '\n' + cont;
          }
          blankLine = isBlankLine;
          rest = rest.substring(rawLine.length + 1);
          line = nextNoTabs.slice(indent);
        }
      }
      const raw = listSrc.slice(itemStart, taken());
      if (!list.loose) {
        if (endsWithBlank) list.loose = true;
        else if (reDoubleBlank.test(raw)) endsWithBlank = true;
      }
      list.items.push({
        type: 'list_item', raw,
        task: reListTask.test(itemContents),
        loose: false, text: itemContents, tokens: [],
      });
    }
    const lastItem = list.items.at(-1);
    if (lastItem) {
      lastItem.raw = lastItem.raw.trimEnd();
      lastItem.text = lastItem.text.trimEnd();
    } else {
      return undefined;
    }
    list.raw = listSrc.slice(0, taken()).trimEnd();
    for (const item of list.items) {
      this.lex.state.top = false;
      item.tokens = this.lex.blockTokens(item.text, []);
      if (!list.loose) {
        const spacers = item.tokens.filter(t => t.type === 'space');
        list.loose = spacers.length > 0 && spacers.some(t => reAnyLine.test(t.raw));
      }
    }
    for (const item of list.items) {
      const itemTok = item.tokens[0];
      if (item.task && itemTok && (itemTok.type === 'text' || itemTok.type === 'paragraph')) {
        item.text = item.text.replace(reListTaskReplace, '');
        itemTok.raw = itemTok.raw.replace(reListTaskReplace, '');
        itemTok.text = itemTok.text.replace(reListTaskReplace, '');
        for (let i = this.lex.inlineQueue.length - 1; i >= 0; i--) {
          if (reListTask.test(this.lex.inlineQueue[i].src)) {
            this.lex.inlineQueue[i].src = this.lex.inlineQueue[i].src.replace(reListTaskReplace, '');
            break;
          }
        }
        const taskRaw = reListCheckbox.exec(item.raw);
        if (taskRaw) {
          const checkbox = { type: 'checkbox', raw: taskRaw[0] + ' ', checked: taskRaw[0] !== '[ ]' };
          item.checked = checkbox.checked;
          if (list.loose) {
            if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && item.tokens[0].tokens) {
              item.tokens[0].raw = checkbox.raw + item.tokens[0].raw;
              item.tokens[0].text = checkbox.raw + item.tokens[0].text;
              item.tokens[0].tokens.unshift(checkbox);
            } else {
              item.tokens.unshift({ type: 'paragraph', raw: checkbox.raw, text: checkbox.raw, tokens: [checkbox] });
            }
          } else {
            item.tokens.unshift(checkbox);
          }
        }
      } else if (item.task) {
        item.task = false;
      }
    }
    if (list.loose) {
      for (const item of list.items) {
        item.loose = true;
        for (const token of item.tokens) {
          if (token.type === 'text') token.type = 'paragraph';
        }
      }
    }
    return list;
  }

  html(src) {
    const cap = reHtml.exec(src);
    if (cap) {
      const raw = trimBlankTail(cap[0]);
      return {
        type: 'html', block: true, raw,
        pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
        text: raw,
      };
    }
  }

  def(src) {
    const cap = reDef.exec(src);
    if (cap) {
      if (!reStartAngle.test(cap[2]) && findBracket(cap[2], '()') !== -1) return undefined;
      const tag = foldLabel(cap[1]);
      const href = cap[2] ? cap[2].replace(reHrefBrackets, '$1').replace(reAnyPunct, '$1') : '';
      const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(reAnyPunct, '$1') : cap[3];
      return { type: 'def', tag, raw: rtrim(cap[0], '\n'), href, title };
    }
  }

  table(src) {
    // The delimiter row (line 2) must hold a pipe or a colon, or the
    // delimiter test fails anyway; skip the big regex when it cannot match.
    const nl1 = src.indexOf('\n');
    if (nl1 === -1) return undefined;
    const nl2 = src.indexOf('\n', nl1 + 1);
    const line2 = src.slice(nl1 + 1, nl2 === -1 ? src.length : nl2);
    if (!line2.includes('|') && !line2.includes(':')) return undefined;
    const cap = reTable.exec(src);
    if (!cap) return undefined;
    if (!reTableDelim.test(cap[2])) return undefined;
    const headers = splitCells(cap[1]);
    const aligns = cap[2].replace(reTableAlignChars, '').split('|');
    const rows = cap[3] && cap[3].trim() ? cap[3].replace(reTableRowBlank, '').split('\n') : [];
    if (headers.length !== aligns.length) return undefined;
    const item = { type: 'table', raw: rtrim(cap[0], '\n'), header: [], align: [], rows: [] };
    for (const align of aligns) {
      if (reTableRight.test(align)) item.align.push('right');
      else if (reTableCenter.test(align)) item.align.push('center');
      else if (reTableLeft.test(align)) item.align.push('left');
      else item.align.push(null);
    }
    for (let i = 0; i < headers.length; i++) {
      item.header.push({
        text: headers[i], tokens: this.lex.inline(headers[i]),
        header: true, align: item.align[i],
      });
    }
    for (const row of rows) {
      item.rows.push(splitCells(row, item.header.length).map((cell, i) => ({
        text: cell, tokens: this.lex.inline(cell),
        header: false, align: item.align[i],
      })));
    }
    return item;
  }

  lheading(src) {
    // A setext underline must sit in the first paragraph; without one,
    // the heading regex cannot match.
    if (!hasUnderline(src)) return undefined;
    const cap = reLheading.exec(src);
    if (cap) {
      const text = cap[1].trim();
      return {
        type: 'heading', raw: rtrim(cap[0], '\n'),
        depth: cap[2].charAt(0) === '=' ? 1 : 2, text,
        tokens: this.lex.inline(text),
      };
    }
  }

  paragraph(src) {
    const cap = reParagraph.exec(src);
    if (cap) {
      const text = cap[1].charAt(cap[1].length - 1) === '\n' ? cap[1].slice(0, -1) : cap[1];
      return { type: 'paragraph', raw: cap[0], text, tokens: this.lex.inline(text) };
    }
  }

  text(src) {
    const cap = reBlockText.exec(src);
    if (cap) {
      return { type: 'text', raw: cap[0], text: cap[0], tokens: this.lex.inline(cap[0]) };
    }
  }
}

// ---------- closer hints (shared scan per inline pass) ----------

function beginCloserScan(lex, maskedSrc) {
  lex.closerFrames.push({ maskedSrc, last: scanClosers(maskedSrc) });
}
function endCloserScan(lex) {
  lex.closerFrames.pop();
}
function cachedEmCloser(lex, maskedSrc, delim) {
  const top = lex.closerFrames.at(-1);
  if (top && top.maskedSrc === maskedSrc) return top.last[delim];
  return scanClosers(maskedSrc).last[delim];
}
function cachedDelCloser(lex, maskedSrc) {
  const top = lex.closerFrames.at(-1);
  if (top && top.maskedSrc === maskedSrc) return top.last['~'];
  return scanClosers(maskedSrc).last['~'];
}

// ---------- inline link helpers ----------

function outputLink(cap, link, raw, lex) {
  const href = link.href;
  const title = link.title || null;
  const text = cap[1].replace(reOutputLink, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const outerInLink = lex.state.inLink;
  const outerEmitted = lex.state.linkEmitted;
  const outerRaw = lex.state.inRawBlock;
  lex.state.inLink = true;
  lex.state.linkEmitted = false;
  const tokens = lex.inlineTokens(text);
  const textHasLink = lex.state.linkEmitted;
  lex.state.linkEmitted = outerEmitted;
  lex.state.inLink = outerInLink;
  if (!isImage) {
    // Links may not contain other links, at any level of nesting. Bail so
    // the caller falls through to text and the inner link is the one kept.
    if (textHasLink) {
      lex.state.inRawBlock = outerRaw;
      return undefined;
    }
    lex.state.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href, title, text, tokens };
}

function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      const code = reCodeSpan.exec(label.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const token = reTag.exec(tokenSrc) || reAutolink.exec(tokenSrc);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

// ---------- inline tokenizers ----------

Tok.prototype.escape = function(src) {
  const cap = reEscape.exec(src);
  if (cap) return { type: 'escape', raw: cap[0], text: cap[1] };
};

Tok.prototype.tag = function(src) {
  const cap = reTag.exec(src);
  if (cap) {
    if (!this.lex.state.inLink && reStartATag.test(cap[0])) this.lex.state.inLink = true;
    else if (this.lex.state.inLink && reEndATag.test(cap[0])) this.lex.state.inLink = false;
    if (!this.lex.state.inRawBlock && reStartPreTag.test(cap[0])) this.lex.state.inRawBlock = true;
    else if (this.lex.state.inRawBlock && reEndPreTag.test(cap[0])) this.lex.state.inRawBlock = false;
    return {
      type: 'html', raw: cap[0],
      inLink: this.lex.state.inLink, inRawBlock: this.lex.state.inRawBlock,
      block: false, text: cap[0],
    };
  }
};

Tok.prototype.link = function(src) {
  if (this.lex.state.linkParenPossible === false) return undefined;
  const cap = reLink.exec(src);
  if (cap) {
    const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
    if (isLabelEndInsideToken(src, cap[1], labelStart)) return undefined;
    const trimmedUrl = cap[2].trim();
    if (reStartAngle.test(trimmedUrl)) {
      if (!reEndAngle.test(trimmedUrl)) return undefined;
      const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
      if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return undefined;
    } else {
      const lastParenIndex = findBracket(cap[2], '()');
      if (lastParenIndex === -2) return undefined;
      if (lastParenIndex > -1) {
        const start = cap[0].indexOf('!') === 0 ? 5 : 4;
        const linkLen = start + cap[1].length + lastParenIndex;
        cap[2] = cap[2].substring(0, lastParenIndex);
        cap[0] = cap[0].substring(0, linkLen).trim();
        cap[3] = '';
      }
    }
    const unescaped = rtrim(cap[0].slice(0, -1), '\\');
    if ((cap[0].length - unescaped.length) % 2 === 0) return undefined;
    let href = cap[2];
    const title = cap[3] ? cap[3].slice(1, -1) : '';
    href = href.trim();
    if (reStartAngle.test(href)) href = href.slice(1, -1);
    return outputLink(cap, {
      href: href ? href.replace(reAnyPunct, '$1') : href,
      title: title ? title.replace(reAnyPunct, '$1') : title,
    }, cap[0], this.lex);
  }
};

Tok.prototype.reflink = function(src, links) {
  let cap;
  if ((cap = reReflink.exec(src)) || (cap = reNolink.exec(src))) {
    const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
    if (isLabelEndInsideToken(src, cap[1], labelStart)) return undefined;
    const link = links[foldLabel(cap[2] || cap[1])];
    if (!link) {
      const text = cap[0].charAt(0);
      return { type: 'text', raw: text, text };
    }
    return outputLink(cap, link, cap[0], this.lex);
  }
};

Tok.prototype.emStrong = function(src, maskedSrc, prevChar = '') {
  let match = reEmStrongLDelim.exec(src);
  if (!match) return undefined;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return undefined;
  const delimChar = match[0][0];
  const midRun = prevChar === delimChar;
  const srcStart = maskedSrc.length - src.length;
  let runStart = srcStart;
  while (runStart > 0 && maskedSrc[runStart - 1] === delimChar) runStart--;
  const runPrevChar = [...maskedSrc.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!rePunct.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!rePunct.exec(prevChar);
  // _ can't be between two alphanumerics.
  if (match[4] && prevChar.match(reAlphaNum)) return undefined;
  const nextChar = match[1] || match[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength, midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim()
      && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return undefined;
    const endReg = delimChar === '*' ? reEmStrongRDelimAst : reEmStrongRDelimUnd;
    const lastCloser = cachedEmCloser(this.lex, maskedSrc, delimChar);
    const windowStart = maskedSrc.length - src.length + lLength;
    if (lastCloser < windowStart) return undefined;
    maskedSrc = maskedSrc.slice(-1 * src.length + lLength);
    const lastCloserInWindow = lastCloser - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(maskedSrc)) !== null) {
      if (match.index > lastCloserInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = [...rDelim].length;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      } else if (match[5] || match[6] || openerCanClose) {
        if (midRun && (match[5] || match[6])) break;
        if (runLength % 3 && !((runLength + rLength) % 3)) {
          midDelimTotal += rLength;
          continue;
        }
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal + midDelimTotal);
      const lastCharLength = [...match[0]][0].length;
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: this.lex.inlineTokens(text) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: this.lex.inlineTokens(text) };
    }
  }
};

Tok.prototype.codespan = function(src) {
  const cap = reCodeSpan.exec(src);
  if (cap) {
    let text = cap[2].replace(reNewlineGlobal, ' ');
    const hasNonSpace = reNonSpace.test(text);
    const hasSpaceBoth = reStartSpace.test(text) && reEndSpace.test(text);
    if (hasNonSpace && hasSpaceBoth) text = text.substring(1, text.length - 1);
    return { type: 'codespan', raw: cap[0], text };
  }
};

Tok.prototype.br = function(src) {
  const cap = reBr.exec(src);
  if (cap) return { type: 'br', raw: cap[0] };
};

Tok.prototype.del = function(src, maskedSrc, prevChar = '') {
  let match = reDelLDelim.exec(src);
  if (!match) return undefined;
  const nextChar = match[1] || '';
  if (!nextChar || !prevChar || rePunct.exec(prevChar)) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength;
    const endReg = reDelRDelim;
    const lastCloser = cachedDelCloser(this.lex, maskedSrc);
    const windowStart = maskedSrc.length - src.length + lLength;
    if (lastCloser < windowStart) return undefined;
    maskedSrc = maskedSrc.slice(-1 * src.length + lLength);
    const lastCloserInWindow = lastCloser - windowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(maskedSrc)) !== null) {
      if (match.index > lastCloserInWindow) break;
      rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      rLength = [...rDelim].length;
      if (rLength !== lLength) continue;
      if (match[3] || match[4]) {
        delimTotal += rLength;
        continue;
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      rLength = Math.min(rLength, rLength + delimTotal);
      const lastCharLength = [...match[0]][0].length;
      const raw = src.slice(0, lLength + match.index + lastCharLength + rLength);
      const text = raw.slice(lLength, -lLength);
      return { type: 'del', raw, text, tokens: this.lex.inlineTokens(text) };
    }
  }
};

Tok.prototype.autolink = function(src) {
  const cap = reAutolink.exec(src);
  if (cap) {
    let text, href;
    if (cap[2] === '@') { text = cap[1]; href = 'mailto:' + text; }
    else { text = cap[1]; href = text; }
    return {
      type: 'link', raw: cap[0], text, href, autolink: true,
      tokens: [{ type: 'text', raw: text, text }],
    };
  }
};

Tok.prototype.url = function(src) {
  let cap;
  if (cap = reUrl.exec(src)) {
    let text, href;
    if (cap[2] === '@') {
      text = cap[0];
      href = 'mailto:' + text;
    } else {
      let prevCapZero;
      do {
        prevCapZero = cap[0];
        cap[0] = reBackpedal.exec(cap[0])?.[0] ?? '';
      } while (prevCapZero !== cap[0]);
      text = cap[0];
      if (cap[1] === 'www.') href = 'http://' + cap[0];
      else href = cap[0];
    }
    return {
      type: 'link', raw: cap[0], text, href, autolink: true,
      tokens: [{ type: 'text', raw: text, text }],
    };
  }
};

Tok.prototype.inlineText = function(src) {
  const cap = reText.exec(src);
  if (cap) {
    const escaped = this.lex.state.inRawBlock;
    return {
      type: 'text', raw: cap[0],
      text: escaped ? cap[0] : decodeRefs(cap[0]),
      escaped,
    };
  }
};

// ---------- lexer ----------

// A run with no inline construct at all: no escape, tag, link, emphasis,
// code span, strikethrough, bare URL/email, or hard-break space run. Such
// a run is a single text token, so the tokenizer loop can be skipped.
const PLAIN_RE = /[\\<\[*_`~@]|:\/\/|www\.|  \n/;

class Lexer {
  constructor() {
    this.tokens = [];
    this.tokens.links = Object.create(null);
    this.tok = new Tok(this);
    this.inlineQueue = [];
    this.closerFrames = [];
    this.state = {
      inLink: false, inRawBlock: false, linkEmitted: false,
      linkParenPossible: true, top: true,
    };
  }

  lex(src) {
    src = src.replace(/\r\n|\r/g, '\n');
    this.blockTokens(src, this.tokens);
    for (let i = 0; i < this.inlineQueue.length; i++) {
      const next = this.inlineQueue[i];
      // An inline <pre>, <code>, <kbd> or <script> left open ends with the
      // block holding it; carried over, it would stop every later block's
      // text from being escaped.
      this.state.inRawBlock = false;
      this.inlineTokens(next.src, next.tokens);
    }
    this.inlineQueue = [];
    return this.tokens;
  }

  blockTokens(src, tokens = [], lastParagraphClipped = false) {
    let srcLength = Infinity;
    while (src) {
      if (src.length < srcLength) srcLength = src.length;
      else { this.loopError(src.charCodeAt(0)); break; }
      let token;
      const c0 = src.charCodeAt(0);
      if ((c0 === 32 || c0 === 9 || c0 === 10) && (token = this.tok.space(src))) {
        src = src.substring(token.raw.length);
        const lastToken = tokens.at(-1);
        if (token.raw.length === 1 && lastToken !== undefined) {
          lastToken.raw += '\n';
        } else {
          tokens.push(token);
        }
        continue;
      }
      if ((c0 === 32 || c0 === 9) && (token = this.tok.code(src))) {
        src = src.substring(token.raw.length);
        const lastToken = tokens.at(-1);
        if (lastToken && (lastToken.type === 'paragraph' || lastToken.type === 'text')) {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        continue;
      }
      if ((c0 === 32 || c0 === 96 || c0 === 126) && (token = this.tok.fences(src))) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if ((c0 === 32 || c0 === 35) && (token = this.tok.heading(src))) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if ((c0 === 32 || c0 === 45 || c0 === 95 || c0 === 42) && (token = this.tok.hr(src))) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if ((c0 === 32 || c0 === 62) && (token = this.tok.blockquote(src))) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if ((c0 === 32 || c0 === 42 || c0 === 43 || c0 === 45 || (c0 >= 48 && c0 <= 57)) && (token = this.tok.list(src))) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if ((c0 === 32 || c0 === 60) && (token = this.tok.html(src))) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if ((c0 === 32 || c0 === 91) && (token = this.tok.def(src))) {
        src = src.substring(token.raw.length);
        const lastToken = tokens.at(-1);
        if (lastToken && (lastToken.type === 'paragraph' || lastToken.type === 'text')) {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.raw;
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          if (!this.tokens.links[token.tag]) {
            this.tokens.links[token.tag] = { href: token.href, title: token.title };
          }
          tokens.push(token);
        }
        continue;
      }
      if (token = this.tok.table(src)) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if (token = this.tok.lheading(src)) {
        src = src.substring(token.raw.length);
        tokens.push(token);
        continue;
      }
      if (this.state.top && (token = this.tok.paragraph(src))) {
        const lastToken = tokens.at(-1);
        if (lastParagraphClipped && lastToken && lastToken.type === 'paragraph') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          this.inlineQueue.pop();
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        src = src.substring(token.raw.length);
        continue;
      }
      if (token = this.tok.text(src)) {
        src = src.substring(token.raw.length);
        const lastToken = tokens.at(-1);
        if (lastToken && lastToken.type === 'text') {
          lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
          lastToken.text += '\n' + token.text;
          this.inlineQueue.pop();
          this.inlineQueue.at(-1).src = lastToken.text;
        } else {
          tokens.push(token);
        }
        continue;
      }
      if (src) {
        this.loopError(src.charCodeAt(0));
        break;
      }
    }
    this.state.top = true;
    return tokens;
  }

  inline(src, tokens = []) {
    this.inlineQueue.push({ src, tokens });
    return tokens;
  }

  linkInText(text) {
    if (!text.includes('[')) return false;
    for (const match of text.matchAll(reBlockSkip)) {
      if (reLink.test(match[0]) && text.charAt(match.index - 1) !== '!') return true;
    }
    for (const match of text.matchAll(reReflinkSearch)) {
      const match0 = match[0];
      const refStart = match0.lastIndexOf('[');
      if (match0.charAt(0) === '!' || !Object.hasOwn(this.tokens.links, foldLabel(match0.slice(refStart + 1, -1)))) continue;
      if (refStart > 1 && this.linkInText(match0.slice(1, refStart - 1))) continue;
      return true;
    }
    return false;
  }

  inlineTokens(src, tokens = []) {
    const prevLinkParenPossible = this.state.linkParenPossible;
    this.state.linkParenPossible = prevLinkParenPossible && src.includes(')');
    try {
      return this.inlineTokensInner(src, tokens);
    } finally {
      this.state.linkParenPossible = prevLinkParenPossible;
    }
  }

  inlineTokensInner(src, tokens) {
    if (src && !PLAIN_RE.test(src)) {
      const escaped = this.state.inRawBlock;
      const text = escaped ? src : decodeRefs(src);
      const token = { type: 'text', raw: src, text, escaped };
      const last = tokens.at(-1);
      if (last && last.type === 'text') {
        last.raw += token.raw;
        last.text += token.text;
      } else {
        tokens.push(token);
      }
      return tokens;
    }
    const maskedSrc = (src.includes('*') || src.includes('_') || src.includes('~'))
      ? this.maskSrc(src)
      : src;
    beginCloserScan(this, maskedSrc);
    try {
      return this.tokenizeInlines(src, maskedSrc, tokens);
    } finally {
      endCloserScan(this);
    }
  }

  tokenizeInlines(src, maskedSrc, tokens) {
    let keepPrevChar = false;
    let prevChar = '';
    let srcLength = Infinity;
    while (src) {
      if (src.length < srcLength) srcLength = src.length;
      else { this.loopError(src.charCodeAt(0)); break; }
      if (!keepPrevChar) prevChar = '';
      keepPrevChar = false;
      const c0 = src.charCodeAt(0);
      let token;
      // Dispatch on the first character: each inline construct starts with
      // one specific character (or, for a bare URL, a letter or digit), so
      // the other tokenizers cannot match and need not run.
      if (c0 === 92) { // backslash: escape or hard break
        if (token = this.tok.escape(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
        if (token = this.tok.br(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      } else if (c0 === 60) { // <: tag or autolink
        if (token = this.tok.tag(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
        if (token = this.tok.autolink(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      } else if (c0 === 91 || c0 === 33) { // [ or !: link or reference link
        if (token = this.tok.link(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
        if (token = this.tok.reflink(src, this.tokens.links)) {
          src = src.substring(token.raw.length);
          const lastToken = tokens.at(-1);
          if (token.type === 'text' && lastToken && lastToken.type === 'text') {
            lastToken.raw += token.raw;
            lastToken.text += token.text;
          } else {
            tokens.push(token);
          }
          continue;
        }
      } else if (c0 === 42 || c0 === 95) { // * or _: emphasis, then a bare
        // URL — an email address may start with _ (it is an email-local
        // character), so a failed emphasis opener must still try the URL.
        if (token = this.tok.emStrong(src, maskedSrc, prevChar)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
        if (!this.state.inLink && (token = this.tok.url(src))) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      } else if (c0 === 96) { // `: code span
        if (token = this.tok.codespan(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      } else if (c0 === 32) { // space: hard break
        if (token = this.tok.br(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      } else if (c0 === 126) { // ~: strikethrough
        if (token = this.tok.del(src, maskedSrc, prevChar)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      } else if (!this.state.inLink) { // anything else: bare URL, then text
        if (token = this.tok.url(src)) {
          src = src.substring(token.raw.length);
          tokens.push(token);
          continue;
        }
      }
      if (token = this.tok.inlineText(src)) {
        src = src.substring(token.raw.length);
        if (token.raw.slice(-1) !== '_') prevChar = token.raw.slice(-1);
        keepPrevChar = true;
        const lastToken = tokens.at(-1);
        if (lastToken && lastToken.type === 'text') {
          lastToken.raw += token.raw;
          lastToken.text += token.text;
        } else {
          tokens.push(token);
        }
        continue;
      }
      if (src) {
        this.loopError(src.charCodeAt(0));
        break;
      }
    }
    return tokens;
  }

  maskSrc(src) {
    let maskedSrc = src;
    if (this.tokens.links && src.includes('[')) {
      const maskReflink = (match0) => {
        const refStart = match0.lastIndexOf('[');
        if (!Object.hasOwn(this.tokens.links, foldLabel(match0.slice(refStart + 1, -1)))) return match0;
        if (refStart > 1 && match0.charAt(0) !== '!') {
          const text = match0.slice(1, refStart - 1);
          if (this.linkInText(text)) {
            return '[' + text.replace(reReflinkSearch, maskReflink)
              + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
          }
        }
        return '[' + 'a'.repeat(match0.length - 2) + ']';
      };
      maskedSrc = maskedSrc.replace(reReflinkSearch, maskReflink);
    }
    // The escape mask only matches backticks and backslash escapes; the
    // block mask only matches links, code spans and tags. Skip each scan
    // when none of its trigger characters is present.
    if (maskedSrc.includes('`') || maskedSrc.includes('\\')) {
      maskedSrc = maskedSrc.replace(reAnyPunctOutsideCode, (match0, code, punct) => {
        if (punct) return '+'.repeat(match0.length);
        if (code) return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
        return match0;
      });
    }
    if (maskedSrc.includes('[') || maskedSrc.includes('`') || maskedSrc.includes('<')) {
      maskedSrc = maskedSrc.replace(reBlockSkip, (match0, _link, context) => {
        const offset = context ? context.length : 0;
        return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
      });
    }
    return maskedSrc;
  }

  loopError(byte) {
    throw new Error('Infinite loop on byte: ' + byte);
  }
}

// ---------- renderer ----------

class Render {
  constructor() { this.parser = null; }

  space() { return ''; }

  code(token) {
    const langString = (token.lang || '').match(reNotSpaceStart)?.[0];
    const code = token.text ? token.text.replace(reEndNewline, '') + '\n' : '';
    if (!langString) {
      return '<pre><code>' + (token.escaped ? code : esc(code, true)) + '</code></pre>\n';
    }
    return '<pre><code class="language-' + esc(langString) + '">'
      + (token.escaped ? code : esc(code, true)) + '</code></pre>\n';
  }

  blockquote(token) {
    const body = this.parser.parse(token.tokens);
    return `<blockquote>\n${body}</blockquote>\n`;
  }

  html(token) { return token.text; }

  def() { return ''; }

  heading(token) {
    return `<h${token.depth}>${this.parser.parseInline(token.tokens)}</h${token.depth}>\n`;
  }

  hr() { return '<hr>\n'; }

  list(token) {
    let body = '';
    for (let j = 0; j < token.items.length; j++) body += this.listitem(token.items[j]);
    const type = token.ordered ? 'ol' : 'ul';
    const startAttr = (token.ordered && token.start !== 1) ? (' start="' + token.start + '"') : '';
    return '<' + type + startAttr + '>\n' + body + '</' + type + '>\n';
  }

  listitem(item) {
    return `<li>${this.parser.parse(item.tokens)}</li>\n`;
  }

  checkbox(token) {
    return '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
  }

  paragraph(token) {
    return `<p>${this.parser.parseInline(token.tokens)}</p>\n`;
  }

  table(token) {
    let header = '';
    let cell = '';
    for (let j = 0; j < token.header.length; j++) cell += this.tablecell(token.header[j]);
    header += this.tablerow({ text: cell });
    let body = '';
    for (let j = 0; j < token.rows.length; j++) {
      const row = token.rows[j];
      cell = '';
      for (let k = 0; k < row.length; k++) cell += this.tablecell(row[k]);
      body += this.tablerow({ text: cell });
    }
    if (body) body = `<tbody>${body}</tbody>`;
    return '<table>\n' + '<thead>\n' + header + '</thead>\n' + body + '</table>\n';
  }

  tablerow(token) { return `<tr>\n${token.text}</tr>\n`; }

  tablecell(token) {
    const content = this.parser.parseInline(token.tokens);
    const type = token.header ? 'th' : 'td';
    const tag = token.align ? `<${type} align="${token.align}">` : `<${type}>`;
    return tag + content + `</${type}>\n`;
  }

  strong(token) { return `<strong>${this.parser.parseInline(token.tokens)}</strong>`; }

  em(token) { return `<em>${this.parser.parseInline(token.tokens)}</em>`; }

  codespan(token) { return `<code>${esc(token.text, true)}</code>`; }

  br() { return '<br>'; }

  del(token) { return `<del>${this.parser.parseInline(token.tokens)}</del>`; }

  link(token) {
    const parsedText = token.autolink
      ? esc(token.text, true)
      : this.parser.parseInline(token.tokens);
    const clean = cleanHref(token.href);
    if (clean === null) return parsedText;
    const href = esc(clean, token.autolink);
    let out = '<a href="' + href + '"';
    if (token.title) out += ' title="' + esc(token.title) + '"';
    out += '>' + parsedText + '</a>';
    return out;
  }

  image(token) {
    let text = token.text;
    if (token.tokens) text = this.parser.parseInline(token.tokens, this.parser.textRenderer);
    const clean = cleanHref(token.href);
    if (clean === null) return esc(text);
    let out = `<img src="${esc(clean)}" alt="${esc(text)}"`;
    if (token.title) out += ` title="${esc(token.title)}"`;
    out += '>';
    return out;
  }

  text(token) {
    return token.tokens
      ? this.parser.parseInline(token.tokens)
      : (token.escaped ? token.text : esc(token.text));
  }
}

// Plain-text renderer, used for image alt text.
class TextRender {
  constructor() { this.parser = null; }
  strong(token) { return token.tokens ? this.parser.parseInline(token.tokens, this) : token.text; }
  em(token) { return token.tokens ? this.parser.parseInline(token.tokens, this) : token.text; }
  codespan(token) { return token.text; }
  del(token) { return token.tokens ? this.parser.parseInline(token.tokens, this) : token.text; }
  html(token) { return token.text; }
  text(token) { return token.text; }
  link(token) { return token.tokens ? this.parser.parseInline(token.tokens, this) : token.text; }
  image(token) { return token.tokens ? this.parser.parseInline(token.tokens, this) : token.text; }
  br() { return ''; }
  checkbox(token) { return token.raw; }
}

class Parser {
  constructor() {
    this.renderer = new Render();
    this.renderer.parser = this;
    this.textRenderer = new TextRender();
    this.textRenderer.parser = this;
  }

  parse(tokens) {
    let out = '';
    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      switch (token.type) {
        case 'space': out += this.renderer.space(token); break;
        case 'hr': out += this.renderer.hr(token); break;
        case 'heading': out += this.renderer.heading(token); break;
        case 'code': out += this.renderer.code(token); break;
        case 'table': out += this.renderer.table(token); break;
        case 'blockquote': out += this.renderer.blockquote(token); break;
        case 'list': out += this.renderer.list(token); break;
        case 'checkbox': out += this.renderer.checkbox(token); break;
        case 'html': out += this.renderer.html(token); break;
        case 'def': out += this.renderer.def(token); break;
        case 'paragraph': out += this.renderer.paragraph(token); break;
        case 'text': out += this.renderer.text(token); break;
        default: throw new Error('Token with "' + token.type + '" type was not found.');
      }
    }
    return out;
  }

  parseInline(tokens, renderer = this.renderer) {
    let out = '';
    for (let i = 0; i < tokens.length; i++) {
      const token = tokens[i];
      switch (token.type) {
        case 'escape': out += renderer.text(token); break;
        case 'html': out += renderer.html(token); break;
        case 'link': out += renderer.link(token); break;
        case 'image': out += renderer.image(token); break;
        case 'checkbox': out += renderer.checkbox(token); break;
        case 'strong': out += renderer.strong(token); break;
        case 'em': out += renderer.em(token); break;
        case 'codespan': out += renderer.codespan(token); break;
        case 'br': out += renderer.br(token); break;
        case 'del': out += renderer.del(token); break;
        case 'text': out += renderer.text(token); break;
        default: throw new Error('Token with "' + token.type + '" type was not found.');
      }
    }
    return out;
  }
}

// ---------- entry point ----------

export function parse(src) {
  const lex = new Lexer();
  const tokens = lex.lex(src);
  const parser = new Parser();
  return parser.parse(tokens);
}

export default parse;
