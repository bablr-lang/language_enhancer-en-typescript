import { spam as m, re } from '@bablr/helpers/shorthand';
import { o, eat, eatMatch, exec, match } from '@bablr/helpers/grammar';
import * as productions from '@bablr/helpers/productions';
import { triviaEnhancer } from '@bablr/helpers/trivia';
import { List } from '@bablr/helpers/productions';
import { Matcher } from '@bablr/agast-vm-helpers/symbols';
import { get } from '@bablr/agast-helpers/path';
import { reifyExpression } from '@bablr/agast-vm-helpers';
import { printSource } from '@bablr/agast-helpers/tree';

const matchVerbs = new Set(['eat', 'match', 'eatMatch', 'shift', 'shiftMatch']);

let getMatcher = (instr) => {
  if (matchVerbs.has(instr.verb) && instr.arguments[0].type === Matcher) {
    return instr.arguments[0];
  }
  return null;
};

let getReferenceName = (matcher) => {
  if (matcher == null) return null;
  return reifyExpression(get(['refMatcher', 'name'], matcher.value));
};

let execAtrivial = (s, m, value = o({})) => exec(s, m, value, (g) => g.atrivial);

const atrivial = class TypescriptGrammar {
  constructor() {
    this.literals = new Set(['Punctuator', 'Keyword', 'Literal']);
    this.attributes = new Map(
      Object.entries({
        OpenTag: { balanced: undefined, balancedSpan: undefined },
        CloseTag: { balancer: true },
      }),
    );
  }

  *DeclarationStatement() {
    yield eat(m`sigilToken*: <*Keyword 'declare' />`);

    yield eat(m`declaration*: <_Declaration />`);
  }

  *Declaration() {
    let kw = yield match(re`/function|var|let|const|type|interface|class/`);

    switch (printSource(kw)) {
      case 'function':
        yield eat(m`<FunctionDeclaration />`);
        break;
      case 'var':
      case 'let':
      case 'const':
        break;
      case 'type':
        break;
      case 'interface':
        break;
      case 'class':
        break;
    }
  }

  *FunctionDeclaration({ s }) {
    for (let instr of execAtrivial(s, m`:..: <__FunctionStatement />`)) {
      let refName = getReferenceName(getMatcher(instr));
      if (refName === 'id') {
        yield instr;
        yield eatMatch(m`<TypeParametersDeclaration '<' />`);
      } else if (refName !== 'body') {
        yield instr;
      }
    }
  }

  *TypeParametersDeclaration() {
    yield eat(m`openToken*: <*Punctuator '<' { balanced: '>' } />`);
    yield* List({
      element: m`params[]$: <TypeParameterDeclaration />`,
      allowTrailingSeparator: true,
      separator: m`#separatorTokens[]: <*Punctuator ',' />`,
    });
    yield eat(m`closeToken*: <*Punctuator '>' { balancer: true } />`);
  }

  *TypeParameterDeclaration() {
    yield eat(m`name$: :..: <Identifier />`);
    if (yield eatMatch(m`extendsToken*: <*Keyword 'extends' />`)) {
      yield eatMatch(m`constraint$: <Identifier />`);
    }
  }

  *TypeParameters() {
    yield eat(m`openToken*: <*Punctuator '<' { balanced: '>' } />`);
    yield* List({
      element: m`elements[]$: <_Type />`,
      allowTrailingSeparator: true,
      separator: m`#separatorTokens[]: <*Punctuator ',' />`,
    });
    yield eat(m`closeToken*: <*Punctuator '>' { balancer: true } />`);
  }

  *NeverType() {
    yield eat(m`sigilToken*: <Keyword 'never' />`);
  }

  *VoidType() {
    yield eat(m`sigilToken*: <Keyword 'void' />`);
  }

  *NullType() {
    yield eat(m`sigilToken*: <Keyword 'null' />`);
  }

  *ReferenceType() {
    yield eat(m`name$: :..: <Identifier />`);

    yield eatMatch(m`params[]$: <TypeParameters '<' />`);
  }

  *Type() {
    let kw = yield match(re`/void|null|never/`);
    switch (printSource(kw)) {
      case 'void':
        yield eat(m`<VoidType />`);
        break;
      case 'null':
        yield eat(m`<NullType />`);
        break;
      case 'never':
        yield eat(m`<NeverType />`);
        break;
      default:
        yield eat(m`<ReferenceType />`);
        break;
    }
  }

  List(args) {
    return productions.List(args);
  }
};

export const TypescriptGrammar = triviaEnhancer(
  {
    triviaIsAllowed: (s) => ['Bare'].includes(s.span),
    triviaMatcher: m`#: :..: <__Trivia /[ \n\r\t]|\/\/|\/\*/ />`,
  },
  atrivial,
);

let tsLanguage = Object.freeze({
  canonicalURL: 'https://bablr.org/languages/universe/typescript',
  dependencies: Object.freeze({}),
  grammar: TypescriptGrammar,
});

export const enhanceLanguageWithTypescript = (language) => {
  if (language.dependencies.TS) throw new Error();

  return Object.freeze({
    ...language,
    dependencies: Object.freeze({ ...language.dependencies, TS: tsLanguage }),
    grammar: triviaEnhancer(
      {
        triviaIsAllowed: (s) => s.span === 'Bare',
        triviaMatcher: m`#: <__Trivia /[ \n\r\t]|\/\/|\/\*/ />`,
      },
      class extends language.grammar.atrivial {
        *Expression(args) {
          let {
            s,
            props: { power },
          } = args;
          // if (!s.held) {
          //   if (yield eatMatch(m`:JSX: <Node />`)) {
          //     return r(shiftMatch(m`<_Expression />`, o({ power })));
          //   } else {
          //     return yield* super.Expression(args);
          //   }
          // } else {
          return yield* super.Expression(args);
          // }
        }

        *Statement(args) {
          if (yield eatMatch(m`:TS: <DeclarationStatement />`)) {
          } else {
            yield* super.Statement(args);
          }
        }
      },
    ),
  });
};

export default enhanceLanguageWithTypescript;
