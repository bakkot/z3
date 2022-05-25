// see the Python API: https://github.com/Z3Prover/z3/blob/a90b66134d74fa2e6b36968955d306902ccc3cc6/src/api/python/z3/z3.py

import type {
  Z3_context,
  Z3_solver,
  Z3_model,
  Z3_ast,
  Z3_sort,
  Z3_symbol,
  Z3_func_interp,
  Z3_func_decl,
  Z3_app,
  Z3_decl_kind,
} from '../build/wrapper';
import {
  Z3_ast_print_mode,
  Z3_ast_kind,
  Z3_error_code,
  Z3_lbool,
  Z3_sort_kind,
  Z3_symbol_kind,
} from '../build/wrapper';

/*
# Notes

## This API is incomplete

You can help by expanding it!

Currently it covers only a small fraction of the underlying Z3 API.
When expanding this file, the Python API is a good starting point, but it lacks types.
The dotnet API has better types.


## Initialization

This file is only consumed by end users for its types.
The actual initialiation happens in `wrapper.ts`, just after initializing the underlying API.
That file imports `makeAPI` from this file and passes it the underlying API.

This is a bit convoluted. Better designs are possible. This was just the first thing I thought of.

If TypeScript's support for es modules were better, top-level await would be a reasonable solution to this mess.


## Branding

TypeScript's types are _structural_ rather than nominal.
So we use a phantom `__brand` property to make all classes structurally distinct.
See https://www.typescriptlang.org/play#example/nominal-typing
To make subtyping work, the superclass's `__brand` must be a supertype of all of its subclass's `__brand`s.
So either every subclass needs a distinct property, or the superclass must list the brands of its immediate subclasses.
Since this class heirarchy isn't really intended to be extended by users, we've taken the second approach.


## Method vs Function types

Methods are declared as function types, rather than methods.
This avoids the unsound method bivariance issue: https://github.com/Microsoft/TypeScript/wiki/FAQ#why-are-function-parameters-bivariant
But only applies to function types: https://www.typescriptlang.org/tsconfig#strictFunctionTypes


## Top-level vs nested declarations

The actual implementations of classes want to close over the Z3 parameter to the init function.
But that requires they be declared inside of a function.
We also want to export the types, so types need to be declared separately.


## ContextName type parameter

The ContextName type parameter exists to prevent users, at a type level, from mixing values from different contexts.

### Use of `interface`

Because we want classes to be generic, we are basically forced to use interfaces for the type declarations
- there's no way to refer to the type of a generic class, just its instances.

### Use of _three_ interfaces

TypeScript does not have a way to refer to the type of a generic class, so we have to use interfaces.
https://github.com/microsoft/TypeScript/issues/49234

Extending an interface only adds methods, rather than replacing them, so we can't extension for interface which defines the constructor.
But we still want derived clases to inherit static methods.
So we need seperate interfaces for the constructor, for other static methods, and for the prototype/instances.

## FinalizationRegistry

JavaScript doesn't have destructors per se, but it does have FinalizationRegistry,
which allows you to specify a function to be called when an object is GC'd.
For this to work it is essential that the callback not hold a reference to the object being GC'd,
since that will create a loop which can never be collected.
In particular, as used below, the callback must not refer to `this`.

*/

interface Context<ContextName extends string = 'main'> {
  __brand: 'Context';
  name: ContextName;
  readonly ptr: Z3_context;
}

export interface Solver<ContextName extends string = 'main'> {
  __brand: 'Solver';
  readonly ptr: Z3_solver;
  add: (...args: BoolExpr<ContextName>[]) => void;
  assertExprs: (...args: BoolExpr<ContextName>[]) => void;
  check: (...assumptions: BoolExpr<ContextName>[]) => Promise<'sat' | 'unsat' | 'unknown'>;
  model: () => Model<ContextName>;
  help: () => string;
  toString: () => string;
}
export interface SolverCtor<ContextName extends string = 'main'> {
  new (): Solver<ContextName>;
}

export interface Model<ContextName extends string = 'main'> extends Iterable<FuncDecl<ContextName>> {
  __brand: 'Model';
  readonly ptr: Z3_model;
  length: () => number;
  [Symbol.iterator]: () => Iterator<FuncDecl<ContextName>>;
  getInterp: (decl: FuncDecl<ContextName>) => Expr<ContextName> | FuncInterp<ContextName> | null;
  evaluate: (t: Expr<ContextName>, modelCompletion?: boolean) => ArithExpr<ContextName>;
}
export interface ModelCtor<ContextName extends string = 'main'> {
  new (m: Z3_model): Model<ContextName>;
}

export interface FuncInterp<ContextName extends string = 'main'> {
  __brand: 'FuncInterp';
  readonly ptr: Z3_func_interp;
  readonly ctx: Context<ContextName>;
}
export interface FuncInterpCtor<ContextName extends string = 'main'> {
  new (f: Z3_func_interp): FuncInterp<ContextName>;
}

export interface AST<ContextName extends string = 'main'> {
  __brand:
    | 'AST'
    | FuncDecl<ContextName>['__brand']
    | Expr<ContextName>['__brand']
    | Sort<ContextName>['__brand'];
  readonly ptr: Z3_ast;
  readonly ctx: Context<ContextName>;
  toString: () => string;
  astKind: () => Z3_ast_kind;
}
export interface ASTCtor<ContextName extends string = 'main'> {
  new (ast: Z3_ast): AST<ContextName>;
}

export interface FuncDecl<ContextName extends string = 'main'> extends AST<ContextName> {
  __brand: 'FuncDecl';
  readonly ptr: Z3_func_decl;
  arity: () => number;
  name: () => string;
  declKind: () => Z3_decl_kind;
}
export interface FuncDeclCtor<ContextName extends string = 'main'> {
  // TODO it would be good to have specialized sub-types for the AST pointers
  new (ast: Z3_ast): FuncDecl<ContextName>;
}

export interface Expr<ContextName extends string = 'main'> extends AST<ContextName> {
  __brand: 'Expr' | ArithExpr<ContextName>['__brand'];
  eq: (other: CoercibleToExpr<ContextName>) => BoolExpr<ContextName>;
  neq: (other: CoercibleToExpr<ContextName>) => BoolExpr<ContextName>;
  sort: () => Sort<ContextName>;
  decl: () => FuncDecl<ContextName>;
  numArgs: () => number;
  arg: (idx: number) => Expr<ContextName>;
  children: () => Expr<ContextName>[];
}
export interface ExprStatics<ContextName extends string = 'main'> {
  from(a: boolean): BoolExpr<ContextName>;
  from(a: number): IntNumeralExpr<ContextName>;
  from(a: CoercibleToExpr<ContextName>): Expr<ContextName>;
}
export interface ExprCtor<ContextName extends string = 'main'> extends ExprStatics<ContextName> {
  new (ast: Z3_ast): Expr<ContextName>;
}

export interface ArithExpr<ContextName extends string = 'main'> extends Expr<ContextName> {
  __brand: 'ArithExpr' | IntNumeralExpr<ContextName>['__brand'] | BoolExpr<ContextName>['__brand'];
  neg: () => ArithExpr<ContextName>;
  add: (other: ArithExpr<ContextName> | number) => ArithExpr<ContextName>;
  sub: (other: ArithExpr<ContextName> | number) => ArithExpr<ContextName>;
  mul: (other: ArithExpr<ContextName> | number) => ArithExpr<ContextName>;
  div: (other: ArithExpr<ContextName> | number) => ArithExpr<ContextName>;
  mod: (other: ArithExpr<ContextName> | number) => ArithExpr<ContextName>;
  pow: (other: ArithExpr<ContextName> | number) => ArithExpr<ContextName>;
  le: (other: ArithExpr<ContextName> | number) => BoolExpr<ContextName>;
  lt: (other: ArithExpr<ContextName> | number) => BoolExpr<ContextName>;
  ge: (other: ArithExpr<ContextName> | number) => BoolExpr<ContextName>;
  gt: (other: ArithExpr<ContextName> | number) => BoolExpr<ContextName>;
  toString: () => string;
}
export interface ArithExprStatics<ContextName extends string = 'main'> extends ExprStatics<ContextName> {}
export interface ArithExprCtor<ContextName extends string = 'main'> extends ArithExprStatics<ContextName> {
  new (ast: Z3_ast): ArithExpr<ContextName>;
}

export interface IntNumeralExpr<ContextName extends string = 'main'> extends ArithExpr<ContextName> {
  __brand: 'IntNumeralExpr';
}
export interface IntNumeralExprStatics<ContextName extends string = 'main'>
  extends ArithExprStatics<ContextName> {}
export interface IntNumeralExprCtor<ContextName extends string = 'main'>
  extends IntNumeralExprStatics<ContextName> {
  new (ast: Z3_ast): IntNumeralExpr<ContextName>;
}

export interface BoolExpr<ContextName extends string = 'main'> extends ArithExpr<ContextName> {
  __brand: 'BoolExpr';
  not: () => BoolExpr<ContextName>;
  iff: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  implies: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  xor: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  and: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  or: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
}
export interface BoolExprStatics<ContextName extends string = 'main'>
  extends ArithExprStatics<ContextName> {}
export interface BoolExprCtor<ContextName extends string = 'main'> extends BoolExprStatics<ContextName> {
  new (ast: Z3_ast): BoolExpr<ContextName>;
}

export interface Sort<ContextName extends string = 'main'> extends AST<ContextName> {
  __brand: 'Sort' | BoolSort<ContextName>['__brand'] | ArithSort<ContextName>['__brand'];
  readonly ptr: Z3_sort;
  eq: (other: Sort<ContextName>) => boolean;
}
export interface SortCtor<ContextName extends string = 'main'> {
  new (ast: Z3_sort): Sort<ContextName>;
}

export interface ArithSort<ContextName extends string = 'main'> extends Sort<ContextName> {
  __brand: 'ArithSort' | IntSort<ContextName>['__brand'];
}
export interface ArithSortCtor<ContextName extends string = 'main'> {
  new (ast: Z3_ast): ArithSort<ContextName>;
}

// todo why does this not extend ArithSort?
export interface BoolSort<ContextName extends string = 'main'> extends Sort<ContextName> {
  __brand: 'BoolSort';
}
export interface BoolSortCtor<ContextName extends string = 'main'> {
  new (ast: Z3_ast): BoolSort<ContextName>;
}

export interface IntSort<ContextName extends string = 'main'> extends ArithSort<ContextName> {
  __brand: 'IntSort';
}
export interface IntSortCtor<ContextName extends string = 'main'> {
  new (ast: Z3_ast): IntSort<ContextName>;
}

export type CoercibleToExpr<ContextName extends string = 'main'> = boolean | number | Expr<ContextName>;

type API<ContextName extends string = 'main'> = {
  Solver: SolverCtor<ContextName>;
  Model: ModelCtor<ContextName>;
  Expr: ExprCtor<ContextName>;
  Int: (name: string) => ArithExpr<ContextName>;
  FreshInt: (name: string) => ArithExpr<ContextName>;
  Bool: (name: string) => BoolExpr<ContextName>;
  Distinct: (...args: CoercibleToExpr<ContextName>[]) => BoolExpr<ContextName>;
  If: (
    test: BoolExpr<ContextName>,
    consequent: ArithExpr<ContextName>,
    alternate: ArithExpr<ContextName>,
  ) => ArithExpr<ContextName>;
  evalSmtlib2String: (command: string) => Promise<string>;
};

type Z3 = Awaited<ReturnType<typeof import('../build/wrapper')['init']>>['Z3'];
export function makeAPI(
  Z3: Z3,
): <ContextName extends string>(name: ContextName) => API<ContextName> {
  return <ContextName extends string>(contextName: ContextName) => {
    // @ts-ignore I promise FinalizationRegistry is a thing
    let cleanupRegistry = new FinalizationRegistry<() => void>(thunk => {
      // console.log('cleaning up');
      thunk();
    });

    // call this after every nontrivial call to the underlying API
    function throwIfError() {
      if (Z3.get_error_code(ctx.ptr) !== Z3_error_code.Z3_OK) {
        throw new Error(Z3.get_error_msg(ctx.ptr, Z3.get_error_code(ctx.ptr)));
      }
    }

    function enforceContextConsistency(a: { ctx: { name: string } }) {
      if (a.ctx !== ctx) {
        throw new Error(
          `contexts do not match: attempting to use value from context ${a.ctx.name} with class from context ${contextName}`,
        );
      }
    }

    // we use `const X = class X` everywhere to avoid shadowing the `X` type in the primary scope
    const Context = class Context {
      declare __brand: 'Context';
      declare ptr: Z3_context;
      name: ContextName = contextName;
      constructor() {
        let conf = Z3.mk_config();
        Z3.set_param_value(conf, 'auto_config', 'true');
        let ptr = Z3.mk_context_rc(conf);
        this.ptr = ptr;

        Z3.set_ast_print_mode(ptr, Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
        Z3.del_config(conf);

        // TODO lint rule against `this` in the thunk
        cleanupRegistry.register(this, () => Z3.del_context(ptr));
      }
    };
    const ctx = new Context();

    const Solver = class Solver {
      declare __brand: 'Solver';

      declare ctx: Context<ContextName>;
      declare ptr: Z3_solver;
      constructor() {
        let solver = Z3.mk_solver(ctx.ptr);
        Z3.solver_inc_ref(ctx.ptr, solver);

        this.ctx = ctx;
        this.ptr = solver;
        cleanupRegistry.register(this, () => Z3.solver_dec_ref(ctx.ptr, solver));
      }

      add(...args: BoolExpr<ContextName>[]) {
        this.assertExprs(...args);
      }

      assertExprs(...args: BoolExpr<ContextName>[]) {
        args.forEach(enforceContextConsistency);
        for (let arg of args) {
          Z3.solver_assert(ctx.ptr, this.ptr, arg.ptr);
          throwIfError();
        }
      }

      async check(...assumptions: BoolExpr<ContextName>[]) {
        assumptions.forEach(enforceContextConsistency);
        let r = await Z3.solver_check_assumptions(
          ctx.ptr,
          this.ptr,
          assumptions.map(a => a.ptr),
        );
        throwIfError();
        if (r === Z3_lbool.Z3_L_FALSE) {
          return 'unsat';
        } else if (r === Z3_lbool.Z3_L_TRUE) {
          return 'sat';
        } else if (r === Z3_lbool.Z3_L_UNDEF) {
          return 'unknown';
        } else {
          throw new Error('unknown lbool value ' + r);
        }
      }

      model() {
        let m = Z3.solver_get_model(ctx.ptr, this.ptr);
        throwIfError();
        if ((m as unknown as number) === 0) {
          throw new Error('failed to get model');
        }
        return new Model(m);
      }

      help() {
        return Z3.solver_get_help(ctx.ptr, this.ptr);
      }

      toString() {
        return Z3.solver_to_string(ctx.ptr, this.ptr);
      }
    };

    const Model = class Model {
      declare __brand: 'Model';

      declare ptr: Z3_model;
      declare ctx: Context<ContextName>;
      constructor(m: Z3_model) {
        this.ptr = m;
        this.ctx = ctx;
        Z3.model_inc_ref(ctx.ptr, this.ptr);
        cleanupRegistry.register(this, () => Z3.model_dec_ref(ctx.ptr, m));
      }

      length() {
        let a = Z3.model_get_num_consts(ctx.ptr, this.ptr);
        throwIfError();
        let b = Z3.model_get_num_funcs(ctx.ptr, this.ptr);
        throwIfError();
        return a + b;
      }

      *[Symbol.iterator]() {
        let num_consts = Z3.model_get_num_consts(ctx.ptr, this.ptr);
        throwIfError();
        for (let i = 0; i < num_consts; ++i) {
          let decl = Z3.model_get_const_decl(ctx.ptr, this.ptr, i);
          throwIfError();
          yield new FuncDecl(decl);
        }
        let num_funcs = Z3.model_get_num_funcs(ctx.ptr, this.ptr);
        throwIfError();
        for (let i = 0; i < num_funcs; ++i) {
          let decl = Z3.model_get_func_decl(ctx.ptr, this.ptr, i);
          throwIfError();
          yield new FuncDecl(decl);
        }
      }

      getInterp(decl: FuncDecl<ContextName>): Expr<ContextName> | FuncInterp<ContextName> | null {
        enforceContextConsistency(decl);
        if (decl.arity() === 0) {
          let _r = Z3.model_get_const_interp(ctx.ptr, this.ptr, decl.ptr);
          throwIfError();
          if (_r == null) {
            throw new Error('npe in getInterp');
          }
          let r = astPtrToExpr(_r);
          if (isAsArray(r)) {
            throw new Error('unimplement: getInterp of as_array');
          } else {
            return r;
          }
        } else {
          let interp = Z3.model_get_func_interp(ctx.ptr, this.ptr, decl.ptr);
          throwIfError();
          if (interp == null) {
            return null;
          }
          return new FuncInterp(interp);
        }
      }

      evaluate(t: Expr<ContextName>, modelCompletion = false) {
        enforceContextConsistency(t);
        let out = Z3.model_eval(ctx.ptr, this.ptr, t.ptr, modelCompletion);
        throwIfError();
        if (out == null) {
          throw new Error('failed to evaluate expression in the model');
        }
        return astPtrToExpr(out);
      }
    };

    const FuncInterp = class FuncInterp {
      declare __brand: 'FuncInterp';

      declare ptr: Z3_func_interp;
      declare ctx: Context<ContextName>;
      constructor(f: Z3_func_interp) {
        this.ptr = f;
        this.ctx = ctx;
      }
    };

    const AST = class AST {
      declare __brand:
        | 'AST'
        | FuncDecl<ContextName>['__brand']
        | Expr<ContextName>['__brand']
        | Sort<ContextName>['__brand'];

      declare ptr: Z3_ast;
      declare ctx: Context<ContextName>;
      constructor(ast: Z3_ast) {
        Z3.inc_ref(ctx.ptr, ast);
        this.ptr = ast;
        this.ctx = ctx;
        cleanupRegistry.register(this, () => Z3.dec_ref(ctx.ptr, ast));
      }

      valueOf() {
        throw new Error('attempting to take value of ref; this is almost certainly a mistake');
      }

      toString() {
        let str = Z3.ast_to_string(ctx.ptr, this.ptr);
        throwIfError();
        return str;
      }

      astKind() {
        let out = Z3.get_ast_kind(ctx.ptr, this.ptr);
        throwIfError();
        return out;
      }
    };

    const FuncDecl = class FuncDecl extends AST {
      declare __brand: 'FuncDecl';

      declare ptr: Z3_func_decl;
      constructor(ast: Z3_func_decl) {
        super(ast);
      }

      arity() {
        let out = Z3.get_arity(ctx.ptr, this.ptr);
        throwIfError();
        return out;
      }

      name() {
        let name = Z3.get_decl_name(ctx.ptr, this.ptr);
        throwIfError();
        return symbolToJsValue(name);
      }

      declKind() {
        let kind = Z3.get_decl_kind(ctx.ptr, this.ptr);
        throwIfError();
        return kind;
      }
    };

    type _Expr<ContextName extends string = 'main'> = Expr<ContextName>;
    const Expr = class Expr extends AST {
      declare __brand: 'Expr' | ArithExpr<ContextName>['__brand'];

      static from(a: boolean): BoolExpr<ContextName>;
      static from(a: number): IntNumeralExpr<ContextName>;
      static from(a: CoercibleToExpr<ContextName>): _Expr<ContextName>;
      static from(a: CoercibleToExpr<ContextName>): _Expr<ContextName> {
        if (typeof a === 'boolean') {
          return new BoolExpr((a ? Z3.mk_false : Z3.mk_true)(ctx.ptr));
        } else if (typeof a === 'number') {
          if (Math.floor(a) !== a || !Number.isFinite(a)) {
            throw new Error('unimplemented: Expr.from support for non-integer values');
          }
          let numeral = Z3.mk_numeral(ctx.ptr, toIntStr(a), IntSort.from().ptr);
          throwIfError();
          return new IntNumeralExpr(numeral);
        } else if (a instanceof Expr) {
          return a;
        } else {
          if (typeof a === 'object' && typeof a.ctx === 'object') {
            enforceContextConsistency(a);
          }
          throw new Error(`unimplemented: Expr.from support for ${typeof a}`);
        }
      }

      eq(other: CoercibleToExpr<ContextName>) {
        let [a, b] = coerceExprs([this, other]);
        let eq = Z3.mk_eq(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(eq);
      }

      neq(other: CoercibleToExpr<ContextName>) {
        let [a, b] = coerceExprs([this, other]);
        let distinct = Z3.mk_distinct(ctx.ptr, [a.ptr, b.ptr]);
        throwIfError();
        return new BoolExpr(distinct);
      }

      sort(): Sort<ContextName> {
        throw new Error(`unimplemented: sort on ${this.constructor.name}`);
      }

      decl() {
        if (!isApp(this)) {
          throw new Error('decl called on non-app');
        }
        let decl = Z3.get_app_decl(ctx.ptr, this.ptr as unknown as Z3_app);
        throwIfError();
        return new FuncDecl(decl);
      }

      numArgs() {
        if (!isApp(this)) {
          throw new Error('num_args called on non-app');
        }
        let out = Z3.get_app_num_args(ctx.ptr, this.ptr as unknown as Z3_app);
        throwIfError();
        return out;
      }

      arg(idx: number): _Expr<ContextName> {
        if (!isApp(this)) {
          throw new Error('arg called on non-app');
        }
        let ptr = Z3.get_app_arg(ctx.ptr, this.ptr as Z3_app, idx);
        throwIfError();
        return astPtrToExpr(ptr);
      }

      children(): _Expr<ContextName>[] {
        if (!isApp(this)) {
          return [];
        }
        let length = this.numArgs();
        let out = [];
        for (let i = 0; i < length; ++i) {
          out.push(this.arg(i));
        }
        return out;
      }
    };

    type _ArithExpr<ContextName extends string = 'main'> = ArithExpr<ContextName>;
    const ArithExpr = class ArithExpr extends Expr {
      declare __brand:
        | 'ArithExpr'
        | IntNumeralExpr<ContextName>['__brand']
        | BoolExpr<ContextName>['__brand'];

      sort(): Sort<ContextName> {
        let sort = Z3.get_sort(ctx.ptr, this.ptr);
        throwIfError();
        return new ArithSort(sort);
      }

      neg() {
        let r = Z3.mk_unary_minus(ctx.ptr, this.ptr);
        throwIfError();
        return new ArithExpr(r);
      }

      add(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_add(ctx.ptr, [a.ptr, b.ptr]);
        throwIfError();
        return new ArithExpr(r);
      }

      sub(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_sub(ctx.ptr, [a.ptr, b.ptr]);
        throwIfError();
        return new ArithExpr(r);
      }

      mul(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_mul(ctx.ptr, [a.ptr, b.ptr]);
        throwIfError();
        return new ArithExpr(r);
      }

      div(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_div(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new ArithExpr(r);
      }

      mod(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_mod(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new ArithExpr(r);
      }

      pow(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_power(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new ArithExpr(r);
      }

      le(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_le(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      lt(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_lt(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      ge(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_ge(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      gt(other: _ArithExpr<ContextName> | number) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_gt(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }
    };

    const IntNumeralExpr = class IntNumeralExpr extends ArithExpr {
      declare __brand: 'IntNumeralExpr';

      toString() {
        let out = Z3.get_numeral_string(ctx.ptr, this.ptr);
        throwIfError();
        return out;
      }
    };

    type _BoolExpr<ContextName extends string = 'main'> = BoolExpr<ContextName>;
    const BoolExpr = class BoolExpr extends ArithExpr {
      declare __brand: 'BoolExpr';

      sort() {
        let sort = Z3.get_sort(ctx.ptr, this.ptr);
        throwIfError();
        return new BoolSort(sort);
      }

      not() {
        let r = Z3.mk_not(ctx.ptr, this.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      iff(other: _BoolExpr<ContextName> | boolean) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_iff(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      implies(other: _BoolExpr<ContextName> | boolean) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_implies(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      xor(other: _BoolExpr<ContextName> | boolean) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_xor(ctx.ptr, a.ptr, b.ptr);
        throwIfError();
        return new BoolExpr(r);
      }

      and(other: _BoolExpr<ContextName> | boolean) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_and(ctx.ptr, [a.ptr, b.ptr]);
        throwIfError();
        return new BoolExpr(r);
      }

      or(other: _BoolExpr<ContextName> | boolean) {
        let [a, b] = coerceExprs([this, other]);
        let r = Z3.mk_or(ctx.ptr, [a.ptr, b.ptr]);
        throwIfError();
        return new BoolExpr(r);
      }
    };

    let Sort: SortCtor<ContextName> = class Sort extends AST {
      declare __brand: 'Sort' | ArithSort['__brand'];

      declare ptr: Z3_sort;
      constructor(sort: Z3_sort) {
        super(sort);
      }

      eq(other: Sort) {
        enforceContextConsistency(other);
        let out = Z3.is_eq_sort(ctx.ptr, this.ptr, other.ptr);
        throwIfError();
        return out;
      }
    };

    class ArithSort extends Sort {
      declare __brand: 'ArithSort' | BoolSort['__brand'] | IntSort['__brand'];
    }

    // TODO maybe just have a single BoolSort value?
    class BoolSort extends Sort {
      declare __brand: 'BoolSort';

      // TODO why does this exist
      static from(sort = Z3.mk_bool_sort(ctx.ptr)) {
        return new BoolSort(sort);
      }
    }

    class IntSort extends Sort {
      declare __brand: 'IntSort';

      // TODO why does this exist
      static from(sort = Z3.mk_int_sort(ctx.ptr)) {
        return new IntSort(sort);
      }
    }

    function jsValueToSymbol(s: number | string) {
      if (typeof s === 'number') {
        assertInt(s);
        let out = Z3.mk_int_symbol(ctx.ptr, s);
        throwIfError();
        return out;
      } else if (typeof s === 'string') {
        let out = Z3.mk_string_symbol(ctx.ptr, s);
        throwIfError();
        return out;
      } else {
        throw new Error(`unreachable: to_symbol called with ${typeof s}`);
      }
    }

    function symbolToJsValue(s: Z3_symbol) {
      let kind = Z3.get_symbol_kind(ctx.ptr, s);
      throwIfError();
      if (kind === Z3_symbol_kind.Z3_INT_SYMBOL) {
        let int = Z3.get_symbol_int(ctx.ptr, s);
        throwIfError();
        return `k!${int}`;
      } else {
        let out = Z3.get_symbol_string(ctx.ptr, s);
        throwIfError();
        return out;
      }
    }

    function isApp(a: Expr<ContextName>) {
      enforceContextConsistency(a);
      let kind = a.astKind();
      return kind == Z3_ast_kind.Z3_NUMERAL_AST || kind == Z3_ast_kind.Z3_APP_AST;
    }

    let isConst = (a: Expr<ContextName>) => isApp(a) && a.numArgs() === 0;

    function isAsArray(n: Expr<ContextName>) {
      enforceContextConsistency(n);
      let out = Z3.is_as_array(ctx.ptr, n.ptr);
      throwIfError();
      return out;
    }

    function astPtrToExpr(a: Z3_ast): ArithExpr<ContextName> {
      let k = Z3.get_ast_kind(ctx.ptr, a);
      throwIfError();
      let sort = Z3.get_sort(ctx.ptr, a);
      throwIfError();
      let sk = Z3.get_sort_kind(ctx.ptr, sort);
      throwIfError();

      if (sk === Z3_sort_kind.Z3_BOOL_SORT) {
        return new BoolExpr(a);
      }
      if (sk === Z3_sort_kind.Z3_INT_SORT) {
        if (k === Z3_ast_kind.Z3_NUMERAL_AST) {
          return new IntNumeralExpr(a);
        }
        return new ArithExpr(a);
      }
      throw new Error(`unknown sort kind ${sk}`);
    }

    function coerceExprs(exprs: CoercibleToExpr<ContextName>[]) {
      if (exprs.length === 0) {
        return [];
      }
      let coerced = exprs.map(e => Expr.from(e));
      let sort = coerced[0].sort();
      if (coerced.some(e => !e.sort().eq(sort))) {
        throw new Error('unimplemented: coerceExprs with unequal sorts');
      }
      return coerced;
    }

    function assertInt(val: number) {
      if (Math.floor(val) !== val || !Number.isFinite(val)) {
        throw new Error('unimplemented: support for non-integer values');
      }
    }

    function toIntStr(val: boolean | number) {
      if (typeof val === 'boolean') {
        return val ? '1' : '0';
      } else if (typeof val === 'number') {
        assertInt(val);
        return '' + BigInt(val); // bigint cast avoids scientific notation for large numbers
      }
      throw new Error(`unimplemented: toIntStr for ${typeof val}`);
    }

    function Int(name: string) {
      let c = Z3.mk_const(ctx.ptr, jsValueToSymbol(name), IntSort.from().ptr);
      throwIfError();
      return new ArithExpr(c);
    }

    function FreshInt(name: string) {
      let c = Z3.mk_fresh_const(ctx.ptr, name, IntSort.from().ptr);
      throwIfError();
      return new ArithExpr(c);
    }

    function Bool(name: string) {
      let c = Z3.mk_const(ctx.ptr, jsValueToSymbol(name), BoolSort.from().ptr);
      throwIfError();
      return new BoolExpr(c);
    }

    function Distinct(...args: CoercibleToExpr<ContextName>[]) {
      let coerced = coerceExprs(args);
      let d = Z3.mk_distinct(
        ctx.ptr,
        coerced.map(c => c.ptr),
      );
      throwIfError();
      return new BoolExpr(d);
    }

    function If(
      test: BoolExpr<ContextName>,
      consequent: ArithExpr<ContextName>,
      alternate: ArithExpr<ContextName>,
    ) {
      // TODO checks for context equality, here and elsewhere
      let ite = Z3.mk_ite(ctx.ptr, test.ptr, consequent.ptr, alternate.ptr);
      throwIfError();
      return new ArithExpr(ite);
    }

    async function evalSmtlib2String(command: string) {
      let out = await Z3.eval_smtlib2_string(ctx.ptr, command);
      throwIfError();
      return out;
    }

    return {
      Context,
      Solver,
      Model,
      Expr,
      Int,
      FreshInt,
      Bool,
      Distinct,
      If,
      evalSmtlib2String,
    };
  };
}
