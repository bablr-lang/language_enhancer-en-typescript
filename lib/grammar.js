import { spam as m, re } from '@bablr/helpers/shorthand';
import {
  o,
  r,
  eat,
  eatMatch,
  shiftMatch,
  exec,
  match,
  getInstrMatcher,
} from '@bablr/helpers/grammar';
import * as BTree from '@bablr/agast-helpers/btree';
import { triviaEnhancer } from '@bablr/helpers/trivia';
import { List } from '@bablr/helpers/productions';
import { printSource } from '@bablr/agast-helpers/tree';
import { Coroutine } from '@bablr/coroutine';
import { reifyMatcherReferenceName } from '@bablr/agast-vm-helpers';

let runCo = (generator) => new Coroutine(generator).advance();

let execAtrivial = (s, m, value = o({})) => exec(s, m, value, (g) => g.atrivial);

const atrivial = class TypescriptGrammar {
  constructor() {
    this.literals = new Set(['Keyword', 'Literal']);
    this.attributes = new Map();
  }

  *DeclarationStatement() {
    yield eat(m`declaration$: <_Declaration />`);

    yield eatMatch(m`endToken*: <* ';' />`);
  }

  *Declaration() {
    let kw = yield match(re`/function|var|let|const|type|enum|interface|class/`);

    switch (printSource(kw)) {
      case 'function':
        yield eat(m`<FunctionDeclaration />`);
        break;
      case 'var':
      case 'let':
      case 'const':
        yield eat(m`<VariableDeclaration />`);
        break;
      case 'type':
        yield eat(m`<TypeDeclaration />`);
        break;
      case 'enum':
        yield eat(m`<EnumDeclaration />`);
        break;
      case 'interface':
        yield eat(m`<InterfaceDeclaration />`);
        break;
      case 'class':
        yield eat(m`<ClassDeclaration />`);
        break;
    }
  }

  *FunctionDeclaration({ s }) {
    let co = runCo(execAtrivial(s, m`:..: <__FunctionDeclaration />`));

    while (!co.done) {
      let instr = co.value;
      let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
      if (refName !== 'body') {
        co.advance(yield instr);
      } else {
        co.advance(null);
      }
    }
  }

  *VariableDeclaration({ s }) {
    let co = runCo(execAtrivial(s, m`:..: <__VariableDeclaration />`));
    while (!co.done) {
      let instr = co.value;
      let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
      if (refName !== 'value' && refName !== 'assignmentToken') {
        co.advance(yield instr);
      } else {
        co.advance(null);
      }
    }
  }

  *ClassDeclaration({ s }) {
    yield* execAtrivial(s, m`:..: <__ClassDeclaration />`);
  }

  *TypeAnnotation() {
    yield eat(m`sigilToken*: <* ':' />`);

    yield eat(m`type+$: <_Type />`);
  }

  *TypeDeclaration() {
    yield eat(m`sigilToken*: <*Keyword 'type' />`);
    yield eat(m`name$: :..: <Identifier />`);
    yield eatMatch(m`params$: <TypeParametersDeclaration '<' />`);
    yield eat(m`assignmentToken*: <*Keyword '=' />`);
    yield eat(m`type+$: <_Type />`);
  }

  *TypeParametersDeclaration() {
    yield eat(m`openToken*: <* '<' />`);
    yield* List({
      element: m`params[]$: <TypeParameterDeclaration />`,
      allowTrailingSeparator: true,
      separator: m`#separatorTokens: <* ',' />`,
    });
    yield eat(m`closeToken*: <* '>' />`);
  }

  *TypeParameterDeclaration() {
    yield eat(m`name$: :..: <Identifier />`);
    if (yield eatMatch(m`extendsToken*: <*Keyword 'extends' />`)) {
      yield eatMatch(m`constraint$: <_Type />`);
    }
  }

  *TypeParameters() {
    yield eat(m`openToken*: <* '<' />`);
    yield* List({
      element: m`elements[]$: <_Type />`,
      allowTrailingSeparator: true,
      separator: m`#separatorTokens: <* ',' />`,
    });
    yield eat(m`closeToken*: <* '>' />`);
  }

  *NeverType() {
    yield eat(m`sigilToken*: <*Keyword 'never' />`);
  }

  *VoidType() {
    yield eat(m`sigilToken*: <*Keyword 'void' />`);
  }

  *NullType() {
    yield eat(m`sigilToken*: <*Keyword 'null' />`);
  }

  *NumberType() {
    yield eat(m`sigilToken*: <*Keyword 'number' />`);
  }

  *BooleanType() {
    yield eat(m`sigilToken*: <*Keyword 'boolean' />`);
  }

  *StringType() {
    yield eat(m`sigilToken*: <*Keyword 'string' />`);
  }

  *TrueType() {
    yield eat(m`sigilToken*: <*Keyword 'true' />`);
  }

  *FalseType() {
    yield eat(m`sigilToken*: <*Keyword 'false' />`);
  }

  *AnyType() {
    yield eat(m`sigilToken*: <*Keyword 'any' />`);
  }

  *UnionType({ s }) {
    if (!s().held) throw new Error();
    yield eat(m`types[]+$: <_Type />`);
    yield eat(m`#separators[]: <* '|' />`);
    let sep;
    do {
      yield eat(m`types[]+$: <_Type />`);
      sep = yield eatMatch(m`#separators[]: <* '|' />`);
    } while (sep);
  }

  *IntersectionType({ s }) {
    if (!s().held) throw new Error();
    yield eat(m`types[]+$: <_Type />`);
    yield eat(m`#separators[]: <* '&' />`);
    let sep;
    do {
      yield eat(m`types[]+$: <_Type />`);
      sep = yield eatMatch(m`#separators[]: <* '&' />`);
    } while (sep);
  }

  *ObjectType({ getState }) {
    yield eat(m`openToken*: <* '{' />`);

    let getPreviousTrivia = (s) => {
      // TODO turn this into getPreviousTrivias (pl) and use it the other place too
      let triviaProp = BTree.getAt(0, s.result.value.property.node.value.bounds[1]);

      if (triviaProp.node.value.flags.token && !triviaProp.reference.type !== '#') {
        triviaProp = BTree.getAt(1, s.result.value.property.node.value.bounds[1]);
      }

      return triviaProp.reference.type === '#' ? triviaProp?.node : null;
    };

    let sep;
    while (yield eatMatch(m`signatures$: <_Signature />`)) {
      sep = yield eatMatch(m`#separators[]: <* /[;,]/ />`);
      let trivia;
      if (!sep) {
        trivia =
          getPreviousTrivia(getState()) ||
          (yield eatMatch(m`#: <__Trivia /[ \n\r\t]|\/\/|\/\*/ />`))?.node;
        sep = !!trivia && printSource(trivia).includes('\n');
      }

      if (!sep) break;
    }

    yield eat(m`closeToken*: <* '}' />`);
  }

  *Signature() {
    let chr = yield match(re`/\[|new/`);
    switch (chr) {
      case '[':
        if (yield eatMatch(m`<MethodSignature />`)) {
        } else {
          if (yield eat(m`<PropertySignature />`)) {
          }
        }
        break;
      default:
        yield eat(m`<PropertySignature />`);
        break;
    }
  }

  *PropertySignature({ s }) {
    let co = runCo(execAtrivial(s, m`:..: <__Property />`));
    while (!co.done) {
      let instr = co.value;

      let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
      if (refName === 'value') {
        co.advance(yield eat(m`value+$: <_Type />`));
      } else if (refName === 'key') {
        co.advance(yield eat(m`key+$: <_PropertySignatureKey />`));
      } else {
        co.advance(yield instr);
      }
    }
  }

  *PropertySignatureKey() {
    if (yield eatMatch(m`:..: <String /['"]/ />`)) {
    } else if (yield eatMatch(m`:..: <UnsignedInteger /\d/ />`)) {
    } else if (yield eatMatch(m`<ComputedPropertyKey '[' />`)) {
    } else {
      yield eat(m`:..: <Identifier />`, o({ scoped: false }));
    }
  }

  *MethodSignature() {}

  *ComputedPropertyKey() {
    yield eat(m`openToken*: <* '[' />`);
    yield eat(m`name+$: :..: <_Expression />`);
    if (yield eatMatch(m`typeToken*: <* ':' />`)) {
      yield eat(m`type+$: <_Type />`);
    }
    yield eat(m`closeToken*: <* ']' />`);
  }

  *CallSignatureDeclaration() {}

  *ConstructSignatureDeclaration() {}

  *EnumDeclaration() {
    yield eat(m`sigilToken*: <*Keyword 'enum' />`);
    yield eat(m`name$: :..: <Identifier />`);
    yield eat(m`openMembers*: <* '{' />`);

    yield* List({
      element: m`members[]$: <EnumMember />`,
      allowTrailingSeparator: true,
      separator: m`#separatorTokens: <* ',' />`,
    });

    yield eat(m`closeMembers*: <* '}' />`);
  }

  *EnumMember() {
    yield eat(m`name$: :..: <Identifier />`);

    if (yield eatMatch(m`assignmentOperator*: <* '=' />`)) {
      yield eat(m`initializer+$: :..: <_Expression />`, o({ power: 32 }));
    }
  }

  *TypeQuery() {}

  *ImportType() {}

  *TypeOperator() {}

  *ModuleDeclaration() {}

  *ModuleBlock() {}

  *ImportEqualsDeclaration() {}

  *ExportAssignment() {}

  *NamespaceExportDeclaration() {}

  *IndexedAccessType() {}

  *AsExpression() {
    yield eat(m`expression+$: <Expression />`);
    yield eat(m`sigilToken*: <* 'as' />`);
    yield eat(m`type$: `);
  }

  *QualifiedName() {}

  *TypeCastExpression() {}

  *SatisfiesExpression() {}

  *NonNullExpression() {}

  *BigIntType() {}

  *OptionalType() {}

  *RestType() {}

  *MappedType() {
    yield eat(m`openToken*: <* '{' />`);

    yield eat(m`openIndexToken*: <* '[' />`);

    yield eat(m`key*: :..: <Identifier />`);

    yield eat(m`inToken*: <*Keyword 'in' />`);

    yield eat(m`keys+$: <_Type />`);

    yield eat(m`closeIndexToken*: <* ']' />`);
    yield eat(m`mapOperator*: <Punctuator ':' />`);

    yield eat(m`value+$: <_Type />`);

    yield eat(m`closeToken*: <* '}' />`);
  }

  *ReferenceType() {
    yield eat(m`name$: :..: <Identifier />`);

    yield eatMatch(m`params[]$: <TypeParameters '<' />`);
  }

  *Type({ s }) {
    if (s().held) {
      yield eatMatch(m`<UnionType '|' />`);
      yield eatMatch(m`<IntersectionType '&' />`);
    } else {
      let kw = yield match(re`/void|null|never|true|false|boolean|any|string|\{/`);
      switch (printSource(kw)) {
        case 'void':
          yield eat(m`<VoidType />`);
          break;
        case 'null':
          yield eat(m`<NullType />`);
          break;
        case 'true':
          yield eat(m`<TrueType />`);
          break;
        case 'false':
          yield eat(m`<FalseType />`);
          break;
        case 'any':
          yield eat(m`<AnyType />`);
          break;
        case 'boolean':
          yield eat(m`<BooleanType />`);
          break;
        case 'string':
          yield eat(m`<StringType />`);
          break;
        case 'never':
          yield eat(m`<NeverType />`);
          break;
        case '{':
          if (yield eatMatch(m`<MappedType />`)) {
          } else {
            yield eat(m`<ObjectType />`);
          }
          break;
        default:
          yield eat(m`<ReferenceType />`);
          break;
      }

      return r(shiftMatch(m`<_Type />`));
    }
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
          // if (!s().held) {
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
          if (yield eatMatch(m`:TS: <DeclarationStatement /declare|type|enum/ />`)) {
          } else {
            yield* super.Statement(args);
          }
        }

        *FunctionDeclaration(args) {
          let co = runCo(super.FunctionDeclaration(args));
          while (!co.done) {
            let instr = co.value;
            let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
            if (refName === 'name') {
              co.advance(yield instr);
              yield eatMatch(m`typeParams[]$: :TS: <TypeParametersDeclaration '<' />`);
            } else if (refName === 'params') {
              co.advance(yield instr);
              yield eatMatch(m`paramTypes[]$: :TS: <TypeAnnotation ':' />`);
            } else if (refName === 'body') {
              yield eatMatch(m`returnType$: :TS: <TypeAnnotation ':' />`);

              co.advance(yield instr);
            } else {
              co.advance(yield instr);
            }
          }
        }

        *ClassDeclaration(args) {
          let co = runCo(super.ClassDeclaration(args));
          while (!co.done) {
            let instr = co.value;
            let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
            if (refName === 'name') {
              co.advance(yield instr);
              yield eatMatch(m`typeParams$: :TS: <TypeParametersDeclaration '<' />`);
            } else {
              co.advance(yield instr);
            }
          }
        }

        *Method(args) {
          let co = runCo(super.Method(args));
          while (!co.done) {
            let instr = co.value;
            let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
            if (refName === 'isSyncMethod') {
              co.advance(
                yield match(m`isSyncMethod*: <All />`, [m`<* 'async' />`, m`<* /[(<]/ />`]),
              );
            } else if (refName === 'name') {
              co.advance(yield instr);
              yield eatMatch(m`typeParams[]$: :TS: <TypeParametersDeclaration '<' />`);
            } else if (refName === 'body') {
              yield eatMatch(m`returnType$: :TS: <TypeAnnotation ':' />`);

              co.advance(yield instr);
            } else {
              co.advance(yield instr);
            }
          }
        }

        *VariableDeclarator(args) {
          let co = runCo(super.VariableDeclarator(args));

          while (!co.done) {
            let instr = co.value;
            let refName = reifyMatcherReferenceName(getInstrMatcher(instr));
            if (refName === 'receiver') {
              co.advance(yield instr);
              yield eatMatch(m`type+$: :TS: <TypeAnnotation ':' />`);
            } else {
              co.advance(yield instr);
            }
          }
        }
      },
    ),
  });
};

export default enhanceLanguageWithTypescript;
