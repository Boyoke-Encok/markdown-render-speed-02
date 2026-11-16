// parse.js — a fast drop-in for marked 18.1.3's marked.parse(markdown) with its
// default options (gfm on, breaks off, pedantic off, async off).
//
// Re-authored from scratch in this session. It renders exactly what marked
// does — block structure, inline spans, and every output quirk of its default
// renderer — but as a single cursor-based scanner: the input string is never
// copied per token, the block and inline grammars run as sticky patterns
// anchored at a cursor, and rendering appends into one output string per
// case. No dependencies, no network, no cache between cases: parse() keeps
// nothing from an earlier call.

/* ------------------------------------------------------------------ */
/* Small string helpers                                                */
/* ------------------------------------------------------------------ */

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

// Escape HTML entities. With encode=true every & < > " ' is replaced.
// Otherwise < > " ' are replaced, and & only when it cannot start a valid
// entity or numeric character reference.
const RE_ESC_TEST = /[&<>"']/;
const RE_ESC_REPLACE = /[&<>"']/g;
const RE_ESC_TEST_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const RE_ESC_REPLACE_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

function escHtml(html, encode) {
  if (encode) {
    return RE_ESC_TEST.test(html) ? html.replace(RE_ESC_REPLACE, (ch) => ESCAPES[ch]) : html;
  }
  return RE_ESC_TEST_NOENC.test(html) ? html.replace(RE_ESC_REPLACE_NOENC, (ch) => ESCAPES[ch]) : html;
}

const RE_NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const RE_NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// A numeric character reference stands for the character it names; zero, an
// out-of-range value, or a surrogate becomes the replacement character. A
// bare & that starts no reference is escaped, so a decoded character cannot
// join its neighbours into a new reference.
function decodeNumericRefs(text) {
  if (!RE_NUM_REF.test(text)) return text;
  return text.replace(RE_NUM_REF_OR_AMP, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

// Encode a link destination the way marked's cleanUrl does; null when the
// destination cannot be encoded.
const RE_PCT25 = /%25/g;
function cleanUrl(href) {
  try {
    href = encodeURI(href).replace(RE_PCT25, '%');
  } catch {
    return null;
  }
  return href;
}

// Split a table row on unescaped pipes, trimming cells and dropping empty
// edge cells. `count` pads or truncates to a fixed column count.
const RE_FIND_PIPE = /\|/g;
const RE_SPLIT_PIPE = / \|/;
const RE_SLASH_PIPE = /\\\|/g;
function splitCells(row, count) {
  const withSpaces = row.replace(RE_FIND_PIPE, (match, offset, str) => {
    let escaped = false;
    let i = offset;
    while (--i >= 0 && str[i] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = withSpaces.split(RE_SPLIT_PIPE);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(RE_SLASH_PIPE, '|');
  }
  return cells;
}

// Remove a trailing run of `c` (or, with invert, of characters other than c).
function rtrim(str, c, invert) {
  const len = str.length;
  if (len === 0) return '';
  let n = 0;
  while (n < len) {
    const ch = str.charAt(len - n - 1);
    if (ch === c && !invert) n++;
    else if (ch !== c && invert) n++;
    else break;
  }
  return str.slice(0, len - n);
}

const RE_BLANK_LINE = /^[ \t]*$/;

// Drop trailing blank lines, keeping at most one trailing blank line.
function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && RE_BLANK_LINE.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

const RE_MULTI_SPACE = /\s+/g;

// Normalize a link label for definition/reference matching: trim, collapse
// inner whitespace runs to one space, and fold case through upper case (so
// that e.g. ß and SS meet, which toLowerCase alone does not reach).
function normalizeLabel(label) {
  return label.trim().replace(RE_MULTI_SPACE, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Find the index of the closing bracket that balances the brackets in str,
// skipping escaped characters. -1 when there is none, -2 when opens remain.
function findClosingBracket(str, pair) {
  if (str.indexOf(pair[0]) === -1 && str.indexOf(pair[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === pair[0]) level++;
    else if (str[i] === pair[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  return level > 0 ? -2 : -1;
}

// Expand tabs to the next multiple-of-4 column, starting from `indent`.
function expandTabs(line, indent) {
  let col = indent || 0;
  let out = '';
  for (const ch of line) {
    if (ch === '\t') {
      const added = 4 - (col % 4);
      out += ' '.repeat(added);
      col += added;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

/* ------------------------------------------------------------------ */
/* Grammar: shared fragments and block patterns                        */
/* ------------------------------------------------------------------ */

// The block-level tag names that can start or interrupt a block.
const TAG = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

// Small building blocks, written once and reused by the larger patterns.
const HR_SRC = /((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/.source;
const HR_START = ` {0,3}${HR_SRC}`;
const HR_INTERRUPT = ' {0,3}' + HR_SRC.replace(/^\(\(\?:/, '(?:(?:');
const HEADING_START = / {0,3}#{1,6}(?:\s|$)/.source;
const FENCES_LINE = / {0,3}(?:`{3,}(?=[^`\n]*(?:\n|$))|~~~)[^\n]*(?:\n|$)/.source;
const FENCES_OPEN = / {0,3}(?:`{3,}|~{3,})/.source;
const BLOCKQUOTE_START = / {0,3}>/.source;
const CODE_START = /(?: {4}| {0,3}	)[^\n]/.source;
const BULL = / {0,3}(?:[*+-]|\d{1,9}[.)])/.source;
const HTML_START = String.raw` {0,3}(?:<\/?(?:${TAG})(?: +|\n|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)`;

// The GFM table pattern, used both as a block of its own and inside the
// paragraph lookahead (a table can interrupt a paragraph).
const TABLE_SRC = String.raw` *([^\n ].*)\n {0,3}((?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?)(?:\n((?:(?! *\n|${HR_START}|${HEADING_START}|${BLOCKQUOTE_START}|${CODE_START}|${FENCES_LINE}| {0,3}(?:[*+-]|1[.)])[ \t]|${HTML_START}).*(?:\n|$))*)\n*|$)`;
const TABLE = new RegExp(TABLE_SRC, 'y');

// The paragraph body, with the lookahead that stops it before any block that
// can interrupt a paragraph. The blockquote variant uses a different list
// interruption (any number, even a bare marker, starts a sibling list).
const PARA_BODY = (listInterrupt, includeTable = true) => {
  const parts = [HR_START, HEADING_START, BLOCKQUOTE_START, FENCES_LINE, listInterrupt, HTML_START];
  if (includeTable) parts.push(TABLE_SRC);
  parts.push('[ \\t]+\\n');
  return `([^\\n]+(?:\\n(?!${parts.join('|')})[^\\n]+)*)`;
};
const PARA_GFM_SRC = PARA_BODY(/ {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]/.source);
const PARA_BQ_SRC = PARA_BODY(/ {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/.source, false);

// Block patterns. Every one is sticky: it must match exactly at the cursor,
// which is what the ^ anchor did in marked's grammar.
const RE_NEWLINE = /(?:[ \t]*(?:\n|$))+/y;
const RE_CODE = /((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/y;
const RE_FENCES = / {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/y;
const RE_HEADING = / {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/y;
const RE_HR = new RegExp(HR_START, 'y');
const RE_LIST = /( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/y;
const ATTR_SRC = / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/.source;
const RE_HTML = new RegExp(String.raw` {0,3}(?:<(script|pre|style|textarea)[\s>][\s\S]*?(?:<\/\1>[^\n]*\n*|$)|<!--(?:-?>|[\s\S]*?(?:-->|$))[^\n]*(\n+|$)|<\?[\s\S]*?(?:\?>[^\n]*\n*|$)|<![A-Z][\s\S]*?(?:>[^\n]*\n*|$)|<!\[CDATA\[[\s\S]*?(?:\]\]>[^\n]*\n*|$)|<\/?(${TAG})(?:[ \t]+|\n|\/?>|$)[\s\S]*?(?:(?:\n[ 	]*)+\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:${ATTR_SRC})*? *\/?>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ 	]*)+\n|$)|<\/[a-z][a-z0-9-]*\s*>(?=[ \t]*(?:\n|$))[\s\S]*?(?:(?:\n[ 	]*)+\n|$))`, 'iy');
const RE_DEF = / {0,3}\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)((?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))))? *(?:\n+|$)/y;
const RE_LHEADING = new RegExp(String.raw`(?!${BULL} |(?: {4}| {0,3}\t)|${FENCES_OPEN}|${BLOCKQUOTE_START}|${HEADING_START}| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n)((?:.|\n(?!\s*?\n|${BULL} |${FENCES_OPEN}|${BLOCKQUOTE_START}|${HEADING_START}|${HR_INTERRUPT}| {0,3}<[^\n>]+>\n| {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)`, 'y');
const RE_PARAGRAPH = new RegExp(PARA_GFM_SRC, 'y');
const RE_TEXT = /[^\n]+/y;
const RE_BLOCKQUOTE = new RegExp(String.raw`( {0,3}> ?(?:(?![ \t]*(?:\n|$))(${PARA_BQ_SRC})|[^\n]*)(?:\n|$))+`, 'y');

// Indent-dependent line checks used inside list items, cached per indent
// exactly the way marked caches them (index clamps to 0..3).
function cachedLineCheck(make) {
  const cache = [];
  return (indent) => {
    const idx = Math.max(0, Math.min(3, indent - 1));
    let re = cache[idx];
    if (!re) {
      re = make(idx);
      cache[idx] = re;
    }
    return re;
  };
}
const NEXT_BULLET = cachedLineCheck((i) => new RegExp(`^ {0,${i}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`));
const HR_LINE = cachedLineCheck((i) => new RegExp(`^ {0,${i}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`));
const FENCES_BEGIN = cachedLineCheck((i) => new RegExp(`^ {0,${i}}(?:\`\`\`|~~~)`));
const HEADING_BEGIN = cachedLineCheck((i) => new RegExp(`^ {0,${i}}#{1,6}(?:\\s|$)`));
const HTML_BEGIN = cachedLineCheck((i) => new RegExp(String.raw`^ {0,${i}}(?:<\/?(?:${TAG})(?: +|$|\/?>)|<(?:(?:script|pre|style|textarea)(?:[\s>]|$)|!--)|<\?|<![A-Za-z]|<!\[CDATA\[)`, 'i'));
const BLOCKQUOTE_BEGIN = cachedLineCheck((i) => new RegExp(`^ {0,${i}}>`));

const RE_LIST_ITEM = (bull) => new RegExp(`( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`, 'y');

// Index of the '\n' at or after `from`, or the string length when there is
// none. Lets list scanning find a line end without copying the remainder.
function lineEnd(str, from) {
  const i = str.indexOf('\n', from);
  return i === -1 ? str.length : i;
}

// True when the string is empty or contains only spaces and tabs.
function isBlankStr(s) {
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

/* ------------------------------------------------------------------ */
/* Grammar: small block helpers                                        */
/* ------------------------------------------------------------------ */

const RE_CODE_REMOVE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const RE_OUTPUT_LINK = /\\([\[\]])/g;
const RE_INDENT_CODE_COMP = /^(\s+)(?:```)/;
const RE_BEGIN_SPACE = /^\s+/;
const RE_END_HASH = /#$/;
const RE_START_SPACE = /^ /;
const RE_END_SPACE = / $/;
const RE_END_SPACE_TAB = /[ \t]$/;
const RE_NON_SPACE = /[^ ]/;
const RE_NEWLINE_GLOBAL = /\n/g;
const RE_TAB_GLOBAL = /\t/g;
const RE_LEADING_SPACE_TAB = /^[ \t]+/;
const RE_DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const RE_BQ_START = /^ {0,3}>/;
const RE_BQ_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const RE_BQ_SETEXT2 = /^ {0,3}>[ \t]?/gm;
const RE_BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const RE_LIST_NESTING = /^ {1,4}(?=( {4})*[^ ])/g;
const RE_LIST_TASK = /^\[[ xX]\][ \t]+\S/;
const RE_LIST_TASK_REPLACE = /^\[[ xX]\][ \t]+/;
const RE_LIST_CHECKBOX = /\[[ xX]\]/;
const RE_ANY_LINE = /\n.*\n/;
const RE_HREF_BRACKETS = /^<(.*)>$/;
const RE_TABLE_DELIM = /[:|]/;
const RE_TABLE_ALIGN_CHARS = /^\||\| *$/g;
const RE_TABLE_ROW_BLANK = /\n[ \t]*$/;
const RE_TABLE_ALIGN_RIGHT = /^ *-+: *$/;
const RE_TABLE_ALIGN_CENTER = /^ *:-+: *$/;
const RE_TABLE_ALIGN_LEFT = /^ *:-+ *$/;
const RE_START_A = /^<a /i;
const RE_END_A = /^<\/a>/i;
const RE_START_PRE = /^<(pre|code|kbd|script)(\s|>)/i;
const RE_END_PRE = /^<\/(pre|code|kbd|script)(\s|>)/i;
const RE_START_ANGLE = /^</;
const RE_END_ANGLE = />$/;
const RE_UNICODE_ALNUM = /[\p{L}\p{N}]/u;
const RE_SPACE_LINE = /^ +$/gm;
const RE_NOT_SPACE_START = /^\S*/;
const RE_END_NEWLINE = /\n$/;
const RE_SETEXT_CONT = /^ {0,3}(?:=+|-+) *$/;

/* ------------------------------------------------------------------ */
/* Grammar: inline patterns                                            */
/* ------------------------------------------------------------------ */

// A link label, as it appears inside [text](...) and [text][ref]: one level
// of nested brackets, escapes, code spans, or plain characters.
const INLINE_LABEL = String.raw`(?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|` + '`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?';
const BLOCK_LABEL = String.raw`(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+`;
// Bounded labels for the reflink search pass: the label itself is capped at
// 999 items, which is every label CommonMark allows.
const BOUNDED_BLOCK_LABEL = String.raw`(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}`;
const BT = '`';
const BOUNDED_INLINE_LABEL = String.raw`(?:[^\[\]\\${BT}]*(?:\[(?:\[(?:\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|` + '`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?';

const RE_ESCAPE = /\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/y;
const RE_CODE_SPAN = /(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/y;
const RE_BR = /( {2,}|\\)\n(?!\s*$)[ \t]*/y;
const RE_INLINE_TEXT = /(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\/\/|(?<![^\s*_~(])www\.|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/y;

// Fast text scan, used only when the inline string holds no bare-URL,
// email or hard-break marker (S.state.noMarkers): a text run then ends at
// the next special character, so a plain negated-class scan replaces the
// lookahead-heavy RE_INLINE_TEXT. Only called with a non-special first char.
const RE_TEXT_SIMPLE = /[^\\<!\[`*~_]+/y;
const RE_PUNCT = /((?![*_])[\s\p{P}\p{S}])/yu;
const RE_EM_LDELIM = /(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?/yu;
const RE_EM_RDELIM_AST = /^[^_*]*?__[^_*]*?\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?=[\s]|$)|(?:[^\s\p{P}\p{S}]|~)(\*+)(?!\*)(?=(?!~)[\s\p{P}\p{S}]|$)|(?!\*)(?!~)[\s\p{P}\p{S}](\*+)(?=(?:[^\s\p{P}\p{S}]|~))|[\s](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?:[^\s\p{P}\p{S}]|~)(\*+)(?=(?:[^\s\p{P}\p{S}]|~))/gu;
const RE_EM_RDELIM_UND = /^[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)|[^_]+(?=[^_])|(?!_)[\p{P}\p{S}](_+)(?=[\s]|$)|[^\s\p{P}\p{S}](_+)(?!_)(?=[\s\p{P}\p{S}]|$)|(?!_)[\s\p{P}\p{S}](_+)(?=[^\s\p{P}\p{S}])|[\s](_+)(?!_)(?=[\p{P}\p{S}])|(?!_)[\p{P}\p{S}](_+)(?!_)(?=[\p{P}\p{S}])/gu;
const RE_DEL_LDELIM = /~~?(?:((?!~)[\p{P}\p{S}])|[^\s~])/yu;
const RE_DEL_RDELIM = /^[^~]+(?=[^~])|(?!~)[\p{P}\p{S}](~~?)(?=[\s]|$)|[^\s\p{P}\p{S}](~~?)(?!~)(?=[\s\p{P}\p{S}]|$)|(?!~)[\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])|[\s](~~?)(?!~)(?=[\p{P}\p{S}])|(?!~)[\p{P}\p{S}](~~?)(?!~)(?=[\p{P}\p{S}])|[^\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])/gu;
const RE_DEL = /(~~?)(?=[^\s~])((?:\\[\s\S]|[^\\])*?(?:\\[\s\S]|[^\s~\\]))\1(?=[^~]|$)/y;
const RE_AUTOLINK = /<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/y;
const RE_TAG = /<!--(?:-?>|[\s\S]*?-->)|<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*?\s*\/?>|<\?[\s\S]*?\?>|<![a-zA-Z]+\s[\s\S]*?>|<!\[CDATA\[[\s\S]*?\]\]>/y;
const RE_LINK = new RegExp(String.raw`!?\[(${INLINE_LABEL})\]\([ \t\n]*(<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\)))(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)("(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)))?[ \t\n]*\)`, 'y');
const RE_REFLINK = new RegExp(String.raw`!?\[(${INLINE_LABEL})\]\[(${BLOCK_LABEL})\]`, 'y');
const RE_NOLINK = new RegExp(String.raw`!?\[(${BLOCK_LABEL})\](?:\[\])?`, 'y');
const RE_REFLINK_SEARCH = new RegExp(String.raw`!?\[(${BOUNDED_INLINE_LABEL})\]\[(${BOUNDED_BLOCK_LABEL})\]|!?\[(${BOUNDED_BLOCK_LABEL})\](?:\[\])?(?!\()`, 'g');
const RE_BLOCKSKIP = /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)()(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g;
const RE_ANY_PUNCT = /\\([\p{P}\p{S}])/gu;
const RE_ANY_PUNCT_OUTSIDE_CODE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;
const RE_URL = /(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?)|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/y;
const RE_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

/* ------------------------------------------------------------------ */
/* Closer hints (one scan of maskedSrc per inline pass)                */
/* ------------------------------------------------------------------ */

// Scan maskedSrc once for the last `*` / `_` run that can close emphasis
// or strong and the last `~` run that can close strikethrough. A run can
// close only when it is not preceded by ASCII whitespace or the start of
// the string.
function scanClosers(src) {
  const frame = { '*': -1, '_': -1, '~': -1 };
  const len = src.length;
  for (let i = 0; i < len; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    while (j < len && src[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      frame[ch] = i;
    }
    i = j - 1;
  }
  return frame;
}

// The hint stack lives on the parse state; nested inline passes push a
// frame and pop it when they finish, so maskedSrc is not retained.
function beginCloserScan(S, maskedSrc) {
  S.hintStack.push({ src: maskedSrc, frame: scanClosers(maskedSrc) });
}
function endCloserScan(S) {
  S.hintStack.pop();
}
function lastCloser(S, maskedSrc, delim) {
  const top = S.hintStack[S.hintStack.length - 1];
  if (top && top.src === maskedSrc) return top.frame[delim];
  return scanClosers(maskedSrc)[delim];
}

/* ------------------------------------------------------------------ */
/* Shared tokenizer helpers                                            */
/* ------------------------------------------------------------------ */

// Queue inline content for later tokenizing; returns the token array that
// will be filled when the queue is processed.
function queueInline(S, text) {
  const tokens = [];
  S.inlineQueue.push({ src: text, tokens });
  return tokens;
}

// Compensate for fence indentation: up to the fence's own indentation is
// removed from each line of a fenced code block.
function indentCodeCompensation(raw, text) {
  const m = raw.match(RE_INDENT_CODE_COMP);
  if (m === null) return text;
  const indentToCode = m[1];
  return text.split('\n').map((node) => {
    const mn = node.match(RE_BEGIN_SPACE);
    if (mn === null) return node;
    return node.slice(Math.min(mn[0].length, indentToCode.length));
  }).join('\n');
}

// True when a link label's closing `]` sits inside an inline tag or
// autolink that started inside the label (so the label does not end there).
function isLabelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      RE_CODE_SPAN.lastIndex = 0;
      const code = RE_CODE_SPAN.exec(label.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    RE_TAG.lastIndex = 0;
    const token = RE_TAG.exec(tokenSrc) || (() => { RE_AUTOLINK.lastIndex = 0; return RE_AUTOLINK.exec(tokenSrc); })();
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

// Build a link/image token from a matched label + destination. The label
// text is tokenized inline (recursively); a link whose text already holds
// a link is not a link (the inner one is kept instead).
function outputLink(S, cap, href, title, raw) {
  const text = cap[1].replace(RE_OUTPUT_LINK, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const outerInLink = S.state.inLink;
  const outerLinkEmitted = S.state.linkEmitted;
  const outerInRawBlock = S.state.inRawBlock;
  S.state.inLink = true;
  S.state.linkEmitted = false;
  const tokens = inlineTokens(S, text);
  const textHasLink = S.state.linkEmitted;
  S.state.linkEmitted = outerLinkEmitted;
  S.state.inLink = outerInLink;
  if (!isImage) {
    if (textHasLink) {
      S.state.inRawBlock = outerInRawBlock;
      return undefined;
    }
    S.state.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href, title, text, tokens };
}

/* ------------------------------------------------------------------ */
/* Block tokenizers (each takes the parse state, the source string and */
/* a cursor; returns a token or undefined). Sticky patterns match only */
/* exactly at the cursor.                                              */
/* ------------------------------------------------------------------ */

function tokSpace(S, src, pos) {
  RE_NEWLINE.lastIndex = pos;
  const cap = RE_NEWLINE.exec(src);
  if (cap && cap[0].length > 0) return { type: 'space', raw: cap[0] };
}
function tokCode(S, src, pos) {
  RE_CODE.lastIndex = pos;
  const cap = RE_CODE.exec(src);
  if (cap) {
    const raw = trimTrailingBlankLines(cap[0]);
    const text = raw.replace(RE_CODE_REMOVE_INDENT, '');
    return { type: 'code', raw, codeBlockStyle: 'indented', text };
  }
}
function tokFences(S, src, pos) {
  RE_FENCES.lastIndex = pos;
  const cap = RE_FENCES.exec(src);
  if (cap) {
    const raw = cap[0];
    const text = indentCodeCompensation(raw, cap[3] || '');
    return {
      type: 'code',
      raw,
      lang: cap[2] ? cap[2].trim().replace(RE_ANY_PUNCT, '$1') : cap[2],
      text,
    };
  }
}
function tokHeading(S, src, pos) {
  RE_HEADING.lastIndex = pos;
  const cap = RE_HEADING.exec(src);
  if (cap) {
    let text = cap[2].trim();
    if (RE_END_HASH.test(text)) {
      const trimmed = rtrim(text, '#');
      if (!trimmed || RE_END_SPACE_TAB.test(trimmed)) text = trimmed.trim();
    }
    return {
      type: 'heading',
      raw: rtrim(cap[0], '\n'),
      depth: cap[1].length,
      text,
      tokens: queueInline(S, text),
    };
  }
}
function tokHr(S, src, pos) {
  RE_HR.lastIndex = pos;
  const cap = RE_HR.exec(src);
  if (cap) return { type: 'hr', raw: rtrim(cap[0], '\n') };
}
function tokHtml(S, src, pos) {
  RE_HTML.lastIndex = pos;
  const cap = RE_HTML.exec(src);
  if (cap) {
    const raw = trimTrailingBlankLines(cap[0]);
    return {
      type: 'html',
      block: true,
      raw,
      pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
      text: raw,
    };
  }
}
function tokDef(S, src, pos) {
  RE_DEF.lastIndex = pos;
  const cap = RE_DEF.exec(src);
  if (cap) {
    if (!RE_START_ANGLE.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) return;
    const tag = normalizeLabel(cap[1]);
    const href = cap[2] ? cap[2].replace(RE_HREF_BRACKETS, '$1').replace(RE_ANY_PUNCT, '$1') : '';
    const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(RE_ANY_PUNCT, '$1') : cap[3];
    return { type: 'def', tag, raw: rtrim(cap[0], '\n'), href, title };
  }
}
function tokTable(S, src, pos) {
  // Fast pre-check: a table's delimiter row is the second line and always
  // contains at least one '-'. No '-' there means no table can start here.
  const nl1 = src.indexOf('\n', pos);
  if (nl1 === -1) return;
  const nl2 = src.indexOf('\n', nl1 + 1);
  const delimEnd = nl2 === -1 ? src.length : nl2;
  const dash = src.indexOf('-', nl1 + 1);
  if (dash === -1 || dash >= delimEnd) return;
  TABLE.lastIndex = pos;
  const cap = TABLE.exec(src);
  if (!cap) return;
  if (!RE_TABLE_DELIM.test(cap[2])) return;
  const headers = splitCells(cap[1]);
  const aligns = cap[2].replace(RE_TABLE_ALIGN_CHARS, '').split('|');
  const rows = cap[3] && cap[3].trim() ? cap[3].replace(RE_TABLE_ROW_BLANK, '').split('\n') : [];
  if (headers.length !== aligns.length) return;
  const item = { type: 'table', raw: rtrim(cap[0], '\n'), header: [], align: [], rows: [] };
  for (const align of aligns) {
    if (RE_TABLE_ALIGN_RIGHT.test(align)) item.align.push('right');
    else if (RE_TABLE_ALIGN_CENTER.test(align)) item.align.push('center');
    else if (RE_TABLE_ALIGN_LEFT.test(align)) item.align.push('left');
    else item.align.push(null);
  }
  for (let i = 0; i < headers.length; i++) {
    item.header.push({
      text: headers[i],
      tokens: queueInline(S, headers[i]),
      header: true,
      align: item.align[i],
    });
  }
  for (const row of rows) {
    item.rows.push(splitCells(row, item.header.length).map((cell, i) => ({
      text: cell,
      tokens: queueInline(S, cell),
      header: false,
      align: item.align[i],
    })));
  }
  return item;
}
function tokLheading(S, src, pos) {
  // Fast pre-check: a setext underline must appear on some line before the
  // next blank line. If none does, the big regex below cannot match.
  let scan = pos;
  let found = false;
  while (scan < src.length) {
    const le = lineEnd(src, scan);
    // Setext underline: up to 3 spaces, then =+ or -+, then spaces/tabs.
    let i = scan;
    while (i < le && src.charCodeAt(i) === 32) i++;
    if (i < le && (src.charCodeAt(i) === 61 || src.charCodeAt(i) === 45)) {
      const mark = src.charCodeAt(i);
      let j = i;
      while (j < le && src.charCodeAt(j) === mark) j++;
      let k = j;
      while (k < le && (src.charCodeAt(k) === 32 || src.charCodeAt(k) === 9)) k++;
      if (k === le && i - scan <= 3) { found = true; break; }
    }
    // Blank line: only spaces/tabs on this line.
    let blank = true;
    for (let b = scan; b < le; b++) {
      const bc = src.charCodeAt(b);
      if (bc !== 32 && bc !== 9) { blank = false; break; }
    }
    if (blank) break;
    scan = le + 1;
  }
  if (!found) return;
  RE_LHEADING.lastIndex = pos;
  const cap = RE_LHEADING.exec(src);
  if (cap) {
    const text = cap[1].trim();
    return {
      type: 'heading',
      raw: rtrim(cap[0], '\n'),
      depth: cap[2].charAt(0) === '=' ? 1 : 2,
      text,
      tokens: queueInline(S, text),
    };
  }
}
function tokParagraph(S, src, pos) {
  RE_PARAGRAPH.lastIndex = pos;
  const cap = RE_PARAGRAPH.exec(src);
  if (cap) {
    const text = cap[1].charAt(cap[1].length - 1) === '\n' ? cap[1].slice(0, -1) : cap[1];
    return { type: 'paragraph', raw: cap[0], text, tokens: queueInline(S, text) };
  }
}
function tokText(S, src, pos) {
  RE_TEXT.lastIndex = pos;
  const cap = RE_TEXT.exec(src);
  if (cap) {
    return { type: 'text', raw: cap[0], text: cap[0], tokens: queueInline(S, cap[0]) };
  }
}

function tokBlockquote(S, src, pos) {
  RE_BLOCKQUOTE.lastIndex = pos;
  const cap = RE_BLOCKQUOTE.exec(src);
  if (!cap) return;
  let lines = rtrim(cap[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const tokens = [];
  while (lines.length > 0) {
    let inBlockquote = false;
    const currentLines = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (RE_BQ_START.test(lines[i])) {
        currentLines.push(lines[i]);
        inBlockquote = true;
      } else if (!inBlockquote) {
        currentLines.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);
    const currentRaw = currentLines.join('\n');
    const currentText = currentRaw
      .replace(RE_BQ_MARKER_WS, (_, marker, whitespace) => marker + expandTabs(whitespace, marker.length))
      .replace(RE_BQ_SETEXT, '\n    $1')
      .replace(RE_BQ_SETEXT2, '');
    raw = raw ? `${raw}\n${currentRaw}` : currentRaw;
    text = text ? `${text}\n${currentText}` : currentText;
    const top = S.state.top;
    S.state.top = true;
    blockTokens(S, currentText, tokens, true);
    S.state.top = top;
    if (lines.length === 0) break;
    const lastToken = tokens[tokens.length - 1];
    if (lastToken && (lastToken.type === 'code' || lastToken.type === 'heading' || lastToken.type === 'hr' || lastToken.type === 'html' || lastToken.type === 'table')) {
      break;
    } else if (lastToken && lastToken.type === 'blockquote') {
      const oldToken = lastToken;
      const continuation = lines.join('\n');
      const newText = oldToken.raw + '\n' + continuation.replace(RE_BQ_SETEXT2, '');
      const newToken = tokBlockquote(S, newText, 0);
      tokens[tokens.length - 1] = newToken;
      const leftover = newText.substring(newToken.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = `${raw}\n${consumed.join('\n')}`;
      text = text.substring(0, text.length - oldToken.text.length) + newToken.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && RE_BQ_START.test(lines[0])) continue;
      break;
    } else if (lastToken && lastToken.type === 'list') {
      const oldToken = lastToken;
      const newText = oldToken.raw + '\n' + lines.join('\n');
      const newToken = tokList(S, newText, 0);
      tokens[tokens.length - 1] = newToken;
      const consumedCount = newToken.raw.length > oldToken.raw.length
        ? newText.slice(oldToken.raw.length + 1, newToken.raw.length).split('\n').length
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

function tokList(S, src, pos) {
  RE_LIST.lastIndex = pos;
  let cap = RE_LIST.exec(src);
  if (!cap) return;
  const listSrc = src.slice(pos);
  let cur = 0; // cursor within listSrc
  const taken = () => cur;
  let bull = cap[1].trim();
  const isordered = bull.length > 1;
  const list = {
    type: 'list',
    raw: '',
    ordered: isordered,
    start: isordered ? +bull.slice(0, -1) : '',
    loose: false,
    items: [],
  };
  bull = isordered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;
  const itemRegex = RE_LIST_ITEM(bull);
  let endsWithBlankLine = false;
  while (cur < listSrc.length) {
    let endEarly = false;
    let itemContents = '';
    itemRegex.lastIndex = cur;
    const m = itemRegex.exec(listSrc);
    if (!m) break;
    cap = m;
    RE_HR.lastIndex = cur;
    if (RE_HR.test(listSrc)) break;
    const itemStart = taken();
    cur += cap[0].length;
    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    let line = firstLine.replace(RE_LEADING_SPACE_TAB, (whitespace) => expandTabs(whitespace, bulletIndent));
    let nextLine = listSrc.slice(cur, lineEnd(listSrc, cur));
    let blankLine = !line.trim();
    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = line.search(RE_NON_SPACE);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }
    if (blankLine && RE_BLANK_LINE.test(nextLine)) {
      const leN = lineEnd(listSrc, cur);
      cur = leN + (leN < listSrc.length ? 1 : 0);
      endEarly = true;
    }
    if (!endEarly) {
      const nextBulletRegex = NEXT_BULLET(indent);
      const hrRegex = HR_LINE(indent);
      const fencesBeginRegex = FENCES_BEGIN(indent);
      const headingBeginRegex = HEADING_BEGIN(indent);
      const htmlBeginRegex = HTML_BEGIN(indent);
      const blockquoteBeginRegex = BLOCKQUOTE_BEGIN(indent);
      while (cur < listSrc.length) {
        const le = lineEnd(listSrc, cur);
        const rawLine = listSrc.slice(cur, le);
        nextLine = rawLine;
        // Only expand leading tabs when the line actually has a tab.
        const nextLineWithoutTabs = nextLine.includes('\t')
          ? nextLine.replace(RE_LEADING_SPACE_TAB, (whitespace) => expandTabs(whitespace))
          : nextLine;
        // Cheap first-char dispatch: the six break conditions below can only
        // match when the line (after up to `indent` spaces) starts with one
        // of these characters. Skip all six regex tests otherwise.
        let c = 0;
        while (c < indent && c < nextLine.length && nextLine.charCodeAt(c) === 32) c++;
        const ch = c < nextLine.length ? nextLine.charCodeAt(c) : -1;
        const canBreak = ch === 96 || ch === 126 || ch === 35 || ch === 60 || ch === 62
          || ch === 42 || ch === 45 || ch === 43 || ch === 95 || (ch >= 48 && ch <= 57) || ch === 124;
        if (canBreak) {
          if (fencesBeginRegex.test(nextLine)) break;
          if (headingBeginRegex.test(nextLine)) break;
          if (htmlBeginRegex.test(nextLine)) break;
          if (blockquoteBeginRegex.test(nextLine)) break;
          if (nextBulletRegex.test(nextLine)) break;
          if (hrRegex.test(nextLine)) break;
        }
        // Index of the first non-space char (-1 when the line is all spaces).
        let firstNonSpace = -1;
        for (let i = 0; i < nextLineWithoutTabs.length; i++) {
          if (nextLineWithoutTabs.charCodeAt(i) !== 32) { firstNonSpace = i; break; }
        }
        if (firstNonSpace >= indent || isBlankStr(nextLine)) {
          itemContents += '\n' + nextLineWithoutTabs.slice(indent);
        } else {
          if (blankLine) break;
          if (line.replace(RE_TAB_GLOBAL, '    ').search(RE_NON_SPACE) >= 4) break;
          // Dispatch on the previous line's own first non-space char.
          let lc = 0;
          while (lc < line.length && line.charCodeAt(lc) === 32) lc++;
          const lch = lc < line.length ? line.charCodeAt(lc) : -1;
          const lineCanBreak = lch === 96 || lch === 126 || lch === 35 || lch === 60
            || lch === 42 || lch === 45 || lch === 43 || lch === 95 || (lch >= 48 && lch <= 57) || lch === 124;
          if (lineCanBreak) {
            if (fencesBeginRegex.test(line)) break;
            if (headingBeginRegex.test(line)) break;
            if (htmlBeginRegex.test(line)) break;
            if (hrRegex.test(line)) break;
          }
          const setextContinuation = RE_SETEXT_CONT.test(nextLine)
            && (() => { RE_LHEADING.lastIndex = 0; return RE_LHEADING.test(`${line}\n${nextLine}`); })();
          const continuation = setextContinuation
            ? `    ${nextLineWithoutTabs.replace(/^ {0,3}/, '')}`
            : nextLine;
          itemContents += '\n' + continuation;
        }
        blankLine = !nextLine.trim();
        cur = le + (le < listSrc.length ? 1 : 0);
        line = nextLineWithoutTabs.slice(indent);
      }
    }
    const raw = listSrc.slice(itemStart, taken());
    if (!list.loose) {
      if (endsWithBlankLine) list.loose = true;
      else if (RE_DOUBLE_BLANK.test(raw)) endsWithBlankLine = true;
    }
    list.items.push({
      type: 'list_item',
      raw,
      task: RE_LIST_TASK.test(itemContents),
      loose: false,
      text: itemContents,
      tokens: [],
    });
  }
  const lastItem = list.items[list.items.length - 1];
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else {
    return;
  }
  list.raw = listSrc.slice(0, taken()).trimEnd();
  for (const item of list.items) {
    S.state.top = false;
    item.tokens = blockTokens(S, item.text, []);
    if (!list.loose) {
      const spacers = item.tokens.filter((t) => t.type === 'space');
      const hasMultipleLineBreaks = spacers.length > 0 && spacers.some((t) => RE_ANY_LINE.test(t.raw));
      list.loose = hasMultipleLineBreaks;
    }
  }
  for (const item of list.items) {
    const itemToken = item.tokens[0];
    if (item.task && (itemToken && (itemToken.type === 'text' || itemToken.type === 'paragraph'))) {
      item.text = item.text.replace(RE_LIST_TASK_REPLACE, '');
      itemToken.raw = itemToken.raw.replace(RE_LIST_TASK_REPLACE, '');
      itemToken.text = itemToken.text.replace(RE_LIST_TASK_REPLACE, '');
      for (let i = S.inlineQueue.length - 1; i >= 0; i--) {
        if (RE_LIST_TASK.test(S.inlineQueue[i].src)) {
          S.inlineQueue[i].src = S.inlineQueue[i].src.replace(RE_LIST_TASK_REPLACE, '');
          break;
        }
      }
      const taskRaw = RE_LIST_CHECKBOX.exec(item.raw);
      if (taskRaw) {
        const checkboxToken = {
          type: 'checkbox',
          raw: taskRaw[0] + ' ',
          checked: taskRaw[0] !== '[ ]',
        };
        item.checked = checkboxToken.checked;
        if (list.loose) {
          if (item.tokens[0] && ['paragraph', 'text'].includes(item.tokens[0].type) && 'tokens' in item.tokens[0] && item.tokens[0].tokens) {
            item.tokens[0].raw = checkboxToken.raw + item.tokens[0].raw;
            item.tokens[0].text = checkboxToken.raw + item.tokens[0].text;
            item.tokens[0].tokens.unshift(checkboxToken);
          } else {
            item.tokens.unshift({
              type: 'paragraph',
              raw: checkboxToken.raw,
              text: checkboxToken.raw,
              tokens: [checkboxToken],
            });
          }
        } else {
          item.tokens.unshift(checkboxToken);
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

/* ------------------------------------------------------------------ */
/* Block lexer: the main block loop                                    */
/* ------------------------------------------------------------------ */

function blockTokens(S, src, tokens = [], lastParagraphClipped = false) {
  let pos = 0;
  let lastPos = -1;
  while (pos < src.length) {
    if (pos === lastPos) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    lastPos = pos;
    let token;
    if ((token = tokSpace(S, src, pos))) {
      pos += token.raw.length;
      const lastToken = tokens[tokens.length - 1];
      if (token.raw.length === 1 && lastToken !== undefined) {
        lastToken.raw += '\n';
      } else {
        tokens.push(token);
      }
      continue;
    }
    if ((token = tokCode(S, src, pos))) {
      pos += token.raw.length;
      const lastToken = tokens[tokens.length - 1];
      if (lastToken && (lastToken.type === 'paragraph' || lastToken.type === 'text')) {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        S.inlineQueue[S.inlineQueue.length - 1].src = lastToken.text;
      } else {
        tokens.push(token);
      }
      continue;
    }
    if ((token = tokFences(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokHeading(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokHr(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokBlockquote(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokList(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokHtml(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokDef(S, src, pos))) {
      pos += token.raw.length;
      const lastToken = tokens[tokens.length - 1];
      if (lastToken && (lastToken.type === 'paragraph' || lastToken.type === 'text')) {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.raw;
        S.inlineQueue[S.inlineQueue.length - 1].src = lastToken.text;
      } else {
        if (!S.links[token.tag]) {
          S.links[token.tag] = { href: token.href, title: token.title };
        }
        tokens.push(token);
      }
      continue;
    }
    if ((token = tokTable(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokLheading(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if (S.state.top && (token = tokParagraph(S, src, pos))) {
      const lastToken = tokens[tokens.length - 1];
      if (lastParagraphClipped && lastToken && lastToken.type === 'paragraph') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        S.inlineQueue.pop();
        S.inlineQueue[S.inlineQueue.length - 1].src = lastToken.text;
      } else {
        tokens.push(token);
      }
      lastParagraphClipped = false; // no extensions clip the source
      pos += token.raw.length;
      continue;
    }
    if ((token = tokText(S, src, pos))) {
      pos += token.raw.length;
      const lastToken = tokens[tokens.length - 1];
      if (lastToken && lastToken.type === 'text') {
        lastToken.raw += (lastToken.raw.endsWith('\n') ? '' : '\n') + token.raw;
        lastToken.text += '\n' + token.text;
        S.inlineQueue.pop();
        S.inlineQueue[S.inlineQueue.length - 1].src = lastToken.text;
      } else {
        tokens.push(token);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  S.state.top = true;
  return tokens;
}

/* ------------------------------------------------------------------ */
/* Inline tokenizers                                                   */
/* ------------------------------------------------------------------ */

function tokEscape(S, src, pos) {
  RE_ESCAPE.lastIndex = pos;
  const cap = RE_ESCAPE.exec(src);
  if (cap) return { type: 'escape', raw: cap[0], text: cap[1] };
}
function tokTag(S, src, pos) {
  RE_TAG.lastIndex = pos;
  const cap = RE_TAG.exec(src);
  if (cap) {
    if (!S.state.inLink && RE_START_A.test(cap[0])) S.state.inLink = true;
    else if (S.state.inLink && RE_END_A.test(cap[0])) S.state.inLink = false;
    if (!S.state.inRawBlock && RE_START_PRE.test(cap[0])) S.state.inRawBlock = true;
    else if (S.state.inRawBlock && RE_END_PRE.test(cap[0])) S.state.inRawBlock = false;
    return {
      type: 'html',
      raw: cap[0],
      inLink: S.state.inLink,
      inRawBlock: S.state.inRawBlock,
      block: false,
      text: cap[0],
    };
  }
}
function tokLink(S, src, pos) {
  if (S.state.linkParenPossible === false) return;
  RE_LINK.lastIndex = pos;
  const cap = RE_LINK.exec(src);
  if (!cap) return;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src.slice(pos), cap[1], labelStart)) return;
  const trimmedUrl = cap[2].trim();
  if (RE_START_ANGLE.test(trimmedUrl)) {
    if (!RE_END_ANGLE.test(trimmedUrl)) return;
    const rtrimSlash = rtrim(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rtrimSlash.length) % 2 === 0) return;
  } else {
    const lastParenIndex = findClosingBracket(cap[2], '()');
    if (lastParenIndex === -2) return;
    if (lastParenIndex > -1) {
      const start = cap[0].indexOf('!') === 0 ? 5 : 4;
      const linkLen = start + cap[1].length + lastParenIndex;
      cap[2] = cap[2].substring(0, lastParenIndex);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  const unescaped = rtrim(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return;
  let href = cap[2];
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (RE_START_ANGLE.test(href)) href = href.slice(1, -1);
  return outputLink(S, cap, href ? href.replace(RE_ANY_PUNCT, '$1') : href, title ? title.replace(RE_ANY_PUNCT, '$1') : title, cap[0]);
}
function tokReflink(S, src, pos) {
  RE_REFLINK.lastIndex = pos;
  let cap = RE_REFLINK.exec(src);
  if (!cap) {
    RE_NOLINK.lastIndex = pos;
    cap = RE_NOLINK.exec(src);
  }
  if (!cap) return;
  const labelStart = cap[0].charAt(0) === '!' ? 2 : 1;
  if (isLabelEndInsideToken(src.slice(pos), cap[1], labelStart)) return;
  const link = S.links[normalizeLabel(cap[2] || cap[1])];
  if (!link) {
    const text = cap[0].charAt(0);
    return { type: 'text', raw: text, text };
  }
  return outputLink(S, cap, link.href, link.title, cap[0]);
}
// Punctuation test for a single character. RE_PUNCT is sticky, so its
// lastIndex must be reset before every use (a stale lastIndex makes the
// test fail and silently disables emphasis after a space or punctuation).
function isPunct(ch) {
  RE_PUNCT.lastIndex = 0;
  return !!RE_PUNCT.exec(ch);
}

function tokEmStrong(S, src, pos, maskedSrc, prevChar = '') {
  RE_EM_LDELIM.lastIndex = pos;
  let match = RE_EM_LDELIM.exec(src);
  if (!match) return;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return;
  const delimChar = match[0][0];
  const midRun = prevChar === delimChar;
  const srcStart = pos;
  let runStart = srcStart;
  while (runStart > 0 && maskedSrc[runStart - 1] === delimChar) runStart--;
  const runPrevChar = [...maskedSrc.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || isPunct(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : isPunct(prevChar);
  if (match[4] && prevChar.match(RE_UNICODE_ALNUM)) return;
  const nextChar = match[1] || match[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength, midDelimTotal = 0;
    const runLength = srcStart - runStart + lLength;
    const openerCanClose = !!runPrevChar.trim() && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    if (delimChar !== '*' && delimChar !== '_') return;
    const endReg = delimChar === '*' ? RE_EM_RDELIM_AST : RE_EM_RDELIM_UND;
    const lastPossibleEmStrongCloserIndex = lastCloser(S, maskedSrc, delimChar);
    const emStrongCloserWindowStart = pos + lLength;
    if (lastPossibleEmStrongCloserIndex < emStrongCloserWindowStart) return;
    const clipped = maskedSrc.slice(pos + lLength);
    const lastPossibleEmStrongCloserIndexInWindow = lastPossibleEmStrongCloserIndex - emStrongCloserWindowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(clipped)) !== null) {
      if (match.index > lastPossibleEmStrongCloserIndexInWindow) break;
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
      const raw = src.slice(pos, pos + lLength + match.index + lastCharLength + rLength);
      if (Math.min(lLength, rLength) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: inlineTokens(S, text) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: inlineTokens(S, text) };
    }
  }
}

function tokCodespan(S, src, pos) {
  RE_CODE_SPAN.lastIndex = pos;
  const cap = RE_CODE_SPAN.exec(src);
  if (cap) {
    let text = cap[2].replace(RE_NEWLINE_GLOBAL, ' ');
    const hasNonSpaceChars = RE_NON_SPACE.test(text);
    const hasSpaceCharsOnBothEnds = RE_START_SPACE.test(text) && RE_END_SPACE.test(text);
    if (hasNonSpaceChars && hasSpaceCharsOnBothEnds) text = text.substring(1, text.length - 1);
    return { type: 'codespan', raw: cap[0], text };
  }
}
function tokBr(S, src, pos) {
  RE_BR.lastIndex = pos;
  const cap = RE_BR.exec(src);
  if (cap) return { type: 'br', raw: cap[0] };
}
function tokDel(S, src, pos, maskedSrc, prevChar = '') {
  RE_DEL_LDELIM.lastIndex = pos;
  let match = RE_DEL_LDELIM.exec(src);
  if (!match) return;
  const nextChar = match[1] || '';
  if (!nextChar || !prevChar || isPunct(prevChar)) {
    const lLength = [...match[0]].length - 1;
    let rDelim, rLength, delimTotal = lLength;
    const endReg = RE_DEL_RDELIM;
    const lastPossibleDelCloserIndex = lastCloser(S, maskedSrc, '~');
    const delCloserWindowStart = pos + lLength;
    if (lastPossibleDelCloserIndex < delCloserWindowStart) return;
    const clipped = maskedSrc.slice(pos + lLength);
    const lastPossibleDelCloserIndexInWindow = lastPossibleDelCloserIndex - delCloserWindowStart;
    endReg.lastIndex = 0;
    while ((match = endReg.exec(clipped)) !== null) {
      if (match.index > lastPossibleDelCloserIndexInWindow) break;
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
      const raw = src.slice(pos, pos + lLength + match.index + lastCharLength + rLength);
      const text = raw.slice(lLength, -lLength);
      return { type: 'del', raw, text, tokens: inlineTokens(S, text) };
    }
  }
}
function tokAutolink(S, src, pos) {
  RE_AUTOLINK.lastIndex = pos;
  const cap = RE_AUTOLINK.exec(src);
  if (cap) {
    let text, href;
    if (cap[2] === '@') {
      text = cap[1];
      href = 'mailto:' + text;
    } else {
      text = cap[1];
      href = text;
    }
    return {
      type: 'link',
      raw: cap[0],
      text,
      href,
      autolink: true,
      tokens: [{ type: 'text', raw: text, text }],
    };
  }
}
function tokUrl(S, src, pos) {
  RE_URL.lastIndex = pos;
  let cap = RE_URL.exec(src);
  if (cap) {
    let text, href;
    if (cap[2] === '@') {
      text = cap[0];
      href = 'mailto:' + text;
    } else {
      let prevCapZero;
      do {
        prevCapZero = cap[0];
        cap[0] = RE_BACKPEDAL.exec(cap[0])?.[0] ?? '';
      } while (prevCapZero !== cap[0]);
      text = cap[0];
      if (cap[1] === 'www.') href = 'http://' + cap[0];
      else href = cap[0];
    }
    return {
      type: 'link',
      raw: cap[0],
      text,
      href,
      autolink: true,
      tokens: [{ type: 'text', raw: text, text }],
    };
  }
}
function tokInlineText(S, src, pos) {
  // Fast scan first: a text run that does not start on a special character
  // ends at the next special character. That scan is exact unless a
  // bare-URL / email / hard-break marker intervenes before the next special
  // char, so test the chunk for a marker and only then fall through to the
  // full lookahead pattern (which can also open a run on a lone ` or ~, or
  // on a special character left by a failed construct).
  const ch = src.charCodeAt(pos);
  if (ch !== 92 && ch !== 60 && ch !== 33 && ch !== 91 && ch !== 96
    && ch !== 42 && ch !== 126 && ch !== 95) {
    RE_TEXT_SIMPLE.lastIndex = pos;
    const simple = RE_TEXT_SIMPLE.exec(src);
    if (simple && (S.state.noMarkers || !RE_MARKER.test(simple[0]))) {
      const escaped = S.state.inRawBlock;
      return {
        type: 'text',
        raw: simple[0],
        text: escaped ? simple[0] : decodeNumericRefs(simple[0]),
        escaped,
      };
    }
  }
  RE_INLINE_TEXT.lastIndex = pos;
  const cap = RE_INLINE_TEXT.exec(src);
  if (cap) {
    const escaped = S.state.inRawBlock;
    return {
      type: 'text',
      raw: cap[0],
      text: escaped ? cap[0] : decodeNumericRefs(cap[0]),
      escaped,
    };
  }
}

/* ------------------------------------------------------------------ */
/* Inline lexer                                                        */
/* ------------------------------------------------------------------ */

function linkInText(S, text) {
  if (!text.includes('[')) return false;
  for (const match of text.matchAll(RE_BLOCKSKIP)) {
    RE_LINK.lastIndex = 0;
    if (RE_LINK.test(match[0]) && text.charAt(match.index - 1) !== '!') return true;
  }
  for (const match of text.matchAll(RE_REFLINK_SEARCH)) {
    const match0 = match[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(S.links, normalizeLabel(match0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(S, match0.slice(1, refStart - 1))) continue;
    return true;
  }
  return false;
}

function maskSrc(S, src) {
  let maskedSrc = src;
  if (src.includes('[')) {
    const maskReflink = (match0) => {
      const refStart = match0.lastIndexOf('[');
      if (!Object.hasOwn(S.links, normalizeLabel(match0.slice(refStart + 1, -1)))) return match0;
      if (refStart > 1 && match0.charAt(0) !== '!') {
        const text = match0.slice(1, refStart - 1);
        if (linkInText(S, text)) {
          return '[' + text.replace(RE_REFLINK_SEARCH, maskReflink)
            + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match0.length - 2) + ']';
    };
    maskedSrc = maskedSrc.replace(RE_REFLINK_SEARCH, maskReflink);
  }
  // Mask out escaped characters and code spans. Skip the pass entirely
  // when there is no backtick or backslash to mask (the common case).
  if (maskedSrc.includes('`') || maskedSrc.includes('\\')) {
    maskedSrc = maskedSrc.replace(RE_ANY_PUNCT_OUTSIDE_CODE, (match0, code, punct) => {
      if (punct) return '+'.repeat(match0.length);
      if (code) return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
      return match0;
    });
  }
  // Mask out links, code spans and html. Skip when none can occur.
  if (maskedSrc.includes('[') || maskedSrc.includes('<') || maskedSrc.includes('`')) {
    maskedSrc = maskedSrc.replace(RE_BLOCKSKIP, (match0, _link, context) => {
      const offset = context ? context.length : 0;
      return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
    });
  }
  return maskedSrc;
}

function inlineTokens(S, src, tokens = []) {
  const prevLinkParenPossible = S.state.linkParenPossible;
  S.state.linkParenPossible = prevLinkParenPossible && src.includes(')');
  try {
    return inlineTokensInner(S, src, tokens);
  } finally {
    S.state.linkParenPossible = prevLinkParenPossible;
  }
}

// Any character or marker that forces the full inline path: an inline
// construct starter, an entity, a bare URL, an email, or a hard break.
const RE_PLAIN_BLOCKER = /[\\<\[*_`~@&]|:\/\/|www\.|mailto:|xmpp:|  \n/;
// A bare-URL / email / hard-break marker. When none is present, a text run
// can only end at a special character (see RE_TEXT_SIMPLE).
const RE_MARKER = /:\/\/|www\.|@|mailto:|xmpp:|  \n/;

function inlineTokensInner(S, src, tokens) {
  // Fast path: plain text with no inline construct at all. Skip the masking,
  // the closer scan and the whole token loop; the renderer escapes the text.
  // A construct needs one of \ < [ * _ ` ~, a bare URL (:// or www.) or an
  // email (@), or a hard break (two spaces before a newline). An & must also
  // go through the full path: entities are decoded while lexing, so a raw
  // &#35; must become '#' and not survive as an entity reference.
  if (src.length > 0 && !RE_PLAIN_BLOCKER.test(src)) {
    tokens.push({ type: 'text', raw: src, text: src });
    return tokens;
  }
  // Whether this inline string contains any bare-URL / email / hard-break
  // marker. When it does not, a text run can only end at a special char, so
  // tokInlineText may use a plain negated-class scan instead of the full
  // lookahead regex. Saved/restored because link text tokenizes recursively.
  const prevNoMarkers = S.state.noMarkers;
  S.state.noMarkers = !RE_MARKER.test(src);
  // Masking only matters when something can be masked: a code span
  // (backtick), a link ([), raw HTML (<) or an escape (\). With none of
  // those, the masked source is the source itself — skip the three passes.
  const maskedSrc = (src.includes('*') || src.includes('_') || src.includes('~'))
    && (src.includes('`') || src.includes('[') || src.includes('<') || src.includes('\\'))
    ? maskSrc(S, src)
    : src;
  beginCloserScan(S, maskedSrc);
  try {
    return tokenizeInlines(S, src, maskedSrc, tokens);
  } finally {
    endCloserScan(S);
    S.state.noMarkers = prevNoMarkers;
  }
}

function tokenizeInlines(S, src, maskedSrc, tokens) {
  let keepPrevChar = false;
  let prevChar = '';
  let pos = 0;
  let lastPos = -1;
  while (pos < src.length) {
    if (pos === lastPos) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    lastPos = pos;
    if (!keepPrevChar) prevChar = '';
    keepPrevChar = false;
    let token;
    if ((token = tokEscape(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokTag(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokLink(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokReflink(S, src, pos))) {
      pos += token.raw.length;
      const lastToken = tokens[tokens.length - 1];
      if (token.type === 'text' && lastToken && lastToken.type === 'text') {
        lastToken.raw += token.raw;
        lastToken.text += token.text;
      } else {
        tokens.push(token);
      }
      continue;
    }
    if ((token = tokEmStrong(S, src, pos, maskedSrc, prevChar))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokCodespan(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokBr(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokDel(S, src, pos, maskedSrc, prevChar))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokAutolink(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if (!S.state.inLink && (token = tokUrl(S, src, pos))) {
      pos += token.raw.length;
      tokens.push(token);
      continue;
    }
    if ((token = tokInlineText(S, src, pos))) {
      pos += token.raw.length;
      if (token.raw.slice(-1) !== '_') prevChar = token.raw.slice(-1);
      keepPrevChar = true;
      const lastToken = tokens[tokens.length - 1];
      if (lastToken && lastToken.type === 'text') {
        lastToken.raw += token.raw;
        lastToken.text += token.text;
      } else {
        tokens.push(token);
      }
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  return tokens;
}

/* ------------------------------------------------------------------ */
/* Renderer                                                            */
/* ------------------------------------------------------------------ */

const RE_CARRIAGE_RETURN = /\r\n|\r/g;

// Render inline tokens to HTML. When textOnly is set, render plain text
// (the image alt-text path).
function renderInline(tokens, textOnly = false) {
  let out = '';
  for (const token of tokens) {
    switch (token.type) {
      case 'escape':
      case 'text': {
        if (token.tokens) {
          out += renderInline(token.tokens, textOnly);
        } else if (textOnly) {
          out += token.text;
        } else if (token.escaped) {
          out += token.text;
        } else {
          out += escHtml(token.text);
        }
        break;
      }
      case 'html': {
        out += token.text;
        break;
      }
      case 'link': {
        if (textOnly) {
          out += token.tokens ? renderInline(token.tokens, true) : token.text;
          break;
        }
        const parsedText = token.autolink
          ? escHtml(token.text, true)
          : renderInline(token.tokens);
        const cleanHref = cleanUrl(token.href);
        if (cleanHref === null) {
          out += parsedText;
          break;
        }
        const href = escHtml(cleanHref, token.autolink);
        let linkOut = '<a href="' + href + '"';
        if (token.title) linkOut += ' title="' + escHtml(token.title) + '"';
        linkOut += '>' + parsedText + '</a>';
        out += linkOut;
        break;
      }
      case 'image': {
        if (textOnly) {
          out += token.tokens ? renderInline(token.tokens, true) : token.text;
          break;
        }
        const text = token.tokens ? renderInline(token.tokens, true) : token.text;
        const cleanHref = cleanUrl(token.href);
        if (cleanHref === null) {
          out += escHtml(text);
          break;
        }
        let imgOut = `<img src="${escHtml(cleanHref)}" alt="${escHtml(text)}"`;
        if (token.title) imgOut += ` title="${escHtml(token.title)}"`;
        imgOut += '>';
        out += imgOut;
        break;
      }
      case 'checkbox': {
        if (textOnly) out += token.raw;
        else out += '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      }
      case 'strong': {
        out += textOnly
          ? (token.tokens ? renderInline(token.tokens, true) : token.text)
          : `<strong>${renderInline(token.tokens)}</strong>`;
        break;
      }
      case 'em': {
        out += textOnly
          ? (token.tokens ? renderInline(token.tokens, true) : token.text)
          : `<em>${renderInline(token.tokens)}</em>`;
        break;
      }
      case 'codespan': {
        out += textOnly ? token.text : `<code>${escHtml(token.text, true)}</code>`;
        break;
      }
      case 'br': {
        if (!textOnly) out += '<br>';
        break;
      }
      case 'del': {
        out += textOnly
          ? (token.tokens ? renderInline(token.tokens, true) : token.text)
          : `<del>${renderInline(token.tokens)}</del>`;
        break;
      }
      default:
        throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

function renderTokens(tokens) {
  let out = '';
  for (const token of tokens) {
    switch (token.type) {
      case 'space':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading':
        out += `<h${token.depth}>${renderInline(token.tokens)}</h${token.depth}>\n`;
        break;
      case 'code': {
        const langString = (token.lang || '').match(RE_NOT_SPACE_START)?.[0];
        const code = token.text ? token.text.replace(RE_END_NEWLINE, '') + '\n' : '';
        if (!langString) {
          out += '<pre><code>' + escHtml(code, true) + '</code></pre>\n';
        } else {
          out += '<pre><code class="language-' + escHtml(langString) + '">'
            + escHtml(code, true) + '</code></pre>\n';
        }
        break;
      }
      case 'table': {
        let header = '';
        let cell = '';
        for (const h of token.header) cell += renderTableCell(h);
        header += `<tr>\n${cell}</tr>\n`;
        let body = '';
        for (const row of token.rows) {
          cell = '';
          for (const c of row) cell += renderTableCell(c);
          body += `<tr>\n${cell}</tr>\n`;
        }
        if (body) body = `<tbody>${body}</tbody>`;
        out += '<table>\n<thead>\n' + header + '</thead>\n' + body + '</table>\n';
        break;
      }
      case 'blockquote':
        out += `<blockquote>\n${renderTokens(token.tokens)}</blockquote>\n`;
        break;
      case 'list': {
        let body = '';
        for (const item of token.items) body += renderListItem(item);
        const type = token.ordered ? 'ol' : 'ul';
        const startAttr = (token.ordered && token.start !== 1) ? (' start="' + token.start + '"') : '';
        out += '<' + type + startAttr + '>\n' + body + '</' + type + '>\n';
        break;
      }
      case 'checkbox':
        out += '<input ' + (token.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'html':
        out += token.text;
        break;
      case 'def':
        break;
      case 'paragraph':
        out += `<p>${renderInline(token.tokens)}</p>\n`;
        break;
      case 'text':
        out += renderInline(token.tokens);
        break;
      default:
        throw new Error('Token with "' + token.type + '" type was not found.');
    }
  }
  return out;
}

function renderTableCell(token) {
  const content = renderInline(token.tokens);
  const type = token.header ? 'th' : 'td';
  const tag = token.align ? `<${type} align="${token.align}">` : `<${type}>`;
  return tag + content + `</${type}>\n`;
}

function renderListItem(item) {
  return `<li>${renderTokens(item.tokens)}</li>\n`;
}

/* ------------------------------------------------------------------ */
/* Entry point                                                         */
/* ------------------------------------------------------------------ */

// Render markdown to HTML, exactly as marked 18.1.3's marked.parse does
// with its default options (gfm on, breaks off, pedantic off, async off).
export function parse(markdown) {
  const src = markdown.replace(RE_CARRIAGE_RETURN, '\n');
  // Two phases: the block pass lexes structure and queues inline strings
  // (their token arrays are filled in the second phase), so link reference
  // definitions — which may appear after their uses — are known before any
  // inline text is tokenized.
  const S = {
    links: Object.create(null),
    inlineQueue: [],
    state: {
      inLink: false,
      inRawBlock: false,
      linkEmitted: false,
      linkParenPossible: true,
      top: true,
    },
    hintStack: [],
  };
  const tokens = blockTokens(S, src, []);
  for (const next of S.inlineQueue) {
    S.state.inRawBlock = false;
    inlineTokens(S, next.src, next.tokens);
  }
  S.inlineQueue = [];
  return renderTokens(tokens);
}
