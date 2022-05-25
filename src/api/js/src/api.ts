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


### `export declare class C {}` vs `declare class C {}; export type { C }`

If we put `export declare class C {}` at the top level, TypeScript would think we are actually exporting that class.
Which would allow it to be used as a value, which would break at runtime.
We aren't actually exporting the class from the top level; we just want to make its type available.
So we declare the class internally and only export its type.


## FinalizationRegistry

JavaScript doesn't have destructors per se, but it does have FinalizationRegistry,
which allows you to specify a function to be called when an object is GC'd.
For this to work it is essential that the callback not hold a reference to the object being GC'd,
since that will create a loop which can never be collected.
In particular, as used below, the callback must not refer to `this`.

*/

export interface Context<ContextName extends string> {
  __brand: 'Context';
  readonly ptr: Z3_context;
}
export interface ContextCtor<ContextName extends string> {
  new (): Context<ContextName>;
}

export interface Solver<ContextName extends string> {
  __brand: 'Solver';
  readonly ptr: Z3_solver;
  add: (...args: BoolExpr<ContextName>[]) => void;
  assertExprs: (...args: BoolExpr<ContextName>[]) => void;
  check: (...assumptions: BoolExpr<ContextName>[]) => Promise<'sat' | 'unsat' | 'unknown'>;
  model: () => Model<ContextName>;
  help: () => string;
  toString: () => string;
}
export interface SolverCtor<ContextName extends string> {
  new (ctx?: Context<ContextName>): Solver<ContextName>;
}

export interface Model<ContextName extends string> extends Iterable<FuncDecl<ContextName>> {
  __brand: 'Model';
  readonly ptr: Z3_model;
  length: () => number;
  [Symbol.iterator]: () => Iterator<FuncDecl<ContextName>>;
  getInterp: (decl: FuncDecl<ContextName>) => Expr<ContextName> | FuncInterp<ContextName> | null;
  evaluate: (t: Expr<ContextName>, modelCompletion?: boolean) => ArithExpr<ContextName>;
}
export interface ModelCtor<ContextName extends string> {
  new (m: Z3_model, ctx?: Context<ContextName>): Model<ContextName>;
}

export interface FuncInterp<ContextName extends string> {
  __brand: 'FuncInterp';
  readonly ptr: Z3_func_interp;
  readonly ctx: Context<ContextName>;
}
export interface FuncInterpCtor<ContextName extends string> {
  new (f: Z3_func_interp, ctx?: Context<ContextName>): FuncInterp<ContextName>;
}

export interface AST<ContextName extends string> {
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
export interface ASTCtor<ContextName extends string> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): AST<ContextName>;
}

export interface FuncDecl<ContextName extends string> extends AST<ContextName> {
  __brand: 'FuncDecl';
  readonly ptr: Z3_func_decl;
  arity: () => number;
  name: () => string;
  declKind: () => Z3_decl_kind;
}
export interface FuncDeclCtor<ContextName extends string> {
  // TODO it would be good to have specialized sub-types for the AST pointers
  new (ast: Z3_ast, ctx?: Context<ContextName>): FuncDecl<ContextName>;
}

export interface Expr<ContextName extends string> extends AST<ContextName> {
  __brand: 'Expr' | ArithExpr<ContextName>['__brand'];
  eq: (other: CoercibleToExpr<ContextName>) => BoolExpr<ContextName>;
  neq: (other: CoercibleToExpr<ContextName>) => BoolExpr<ContextName>;
  sort: () => Sort<ContextName>;
  decl: () => FuncDecl<ContextName>;
  numArgs: () => number;
  arg: (idx: number) => Expr<ContextName>;
  children: () => Expr<ContextName>[];
}
export interface ExprStatics<ContextName extends string> {
  from(a: boolean, ctx?: Context<ContextName>): BoolExpr<ContextName>;
  from(a: number, ctx?: Context<ContextName>): IntNumeralExpr<ContextName>;
  from(a: CoercibleToExpr<ContextName>, ctx?: Context<ContextName>): Expr<ContextName>;
}
export interface ExprCtor<ContextName extends string> extends ExprStatics<ContextName> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): Expr<ContextName>;
}

export interface ArithExpr<ContextName extends string> extends Expr<ContextName> {
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
export interface ArithExprCtor<ContextName extends string> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): ArithExpr<ContextName>;
}

export interface IntNumeralExpr<ContextName extends string> extends ArithExpr<ContextName> {
  __brand: 'IntNumeralExpr';
}
export interface IntNumeralExprCtor<ContextName extends string> extends ArithExprCtor<ContextName> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): IntNumeralExpr<ContextName>;
}
type _IntNumeralExpr<ContextName extends string> = IntNumeralExpr<ContextName>;

export interface BoolExpr<ContextName extends string> extends ArithExpr<ContextName> {
  __brand: 'BoolExpr';
  not: () => BoolExpr<ContextName>;
  iff: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  implies: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  xor: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  and: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
  or: (other: BoolExpr<ContextName> | boolean) => BoolExpr<ContextName>;
}
export interface BoolExprCtor<ContextName extends string> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): BoolExpr<ContextName>;
}
type _BoolExpr<ContextName extends string> = BoolExpr<ContextName>;

export interface Sort<ContextName extends string> extends AST<ContextName> {
  __brand: 'Sort' | BoolSort<ContextName>['__brand'] | ArithSort<ContextName>['__brand'];
  readonly ptr: Z3_sort;
  eq: (other: Sort<ContextName>) => boolean;
}
export interface SortCtor<ContextName extends string> {
  new (ast: Z3_sort, ctx?: Context<ContextName>): Sort<ContextName>;
}

export interface ArithSort<ContextName extends string> extends Sort<ContextName> {
  __brand: 'ArithSort' | IntSort<ContextName>['__brand'];
}
export interface ArithSortCtor<ContextName extends string> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): ArithSort<ContextName>;
}

// todo why does this not extend ArithSort?
export interface BoolSort<ContextName extends string> extends Sort<ContextName> {
  __brand: 'BoolSort';
}
export interface BoolSortCtor<ContextName extends string> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): BoolSort<ContextName>;
}

export interface IntSort<ContextName extends string> extends ArithSort<ContextName> {
  __brand: 'IntSort';
}
export interface IntSortCtor<ContextName extends string> {
  new (ast: Z3_ast, ctx?: Context<ContextName>): IntSort<ContextName>;
}

export type CoercibleToExpr<ContextName extends string> = boolean | number | Expr<ContextName>;

type API<ContextName extends string> = {
  Context: ContextCtor<ContextName>;
  Solver: SolverCtor<ContextName>;
  Model: ModelCtor<ContextName>;
  Expr: ExprCtor<ContextName>;
  Int: (name: string, ctx?: Context<ContextName>) => ArithExpr<ContextName>;
  FreshInt: (name: string, ctx?: Context<ContextName>) => ArithExpr<ContextName>;
  Bool: (name: string, ctx?: Context<ContextName>) => BoolExpr<ContextName>;
  Distinct: (...args: CoercibleToExpr<ContextName>[]) => BoolExpr<ContextName>;
  If: (
    test: BoolExpr<ContextName>,
    consequent: ArithExpr<ContextName>,
    alternate: ArithExpr<ContextName>,
  ) => ArithExpr<ContextName>;
  evalSmtlib2String: (command: string, ctx?: Context<ContextName>) => Promise<string>;
};

type Z3 = Awaited<ReturnType<typeof import('../build/wrapper')['init']>>['Z3'];
export function makeAPI(Z3: Z3): API<'TODO'> {
  // @ts-ignore I promise FinalizationRegistry is a thing
  let cleanupRegistry = new FinalizationRegistry<() => void>(thunk => {
    // console.log('cleaning up');
    thunk();
  });

  // Global Z3 context
  let _mainCtx: Context<'TODO'> | null = null;

  function mainCtx() {
    if (_mainCtx === null) {
      _mainCtx = new Context();
    }
    return _mainCtx;
  }

  // call this after every nontrivial call to the underlying API
  function throwIfError(ctx: Context<'TODO'>) {
    if (Z3.get_error_code(ctx.ptr) !== Z3_error_code.Z3_OK) {
      throw new Error(Z3.get_error_msg(ctx.ptr, Z3.get_error_code(ctx.ptr)));
    }
  }

  const Context = class Context {
    declare __brand: 'Context';
    declare ptr: Z3_context;
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

  const Solver = class Solver {
    declare __brand: 'Solver';

    declare ctx: Context<'TODO'>;
    declare ptr: Z3_solver;
    constructor(ctx = mainCtx()) {
      let solver = Z3.mk_solver(ctx.ptr);
      Z3.solver_inc_ref(ctx.ptr, solver);

      this.ctx = ctx;
      this.ptr = solver;
      cleanupRegistry.register(this, () => Z3.solver_dec_ref(ctx.ptr, solver));
    }

    add(...args: BoolExpr<'TODO'>[]) {
      this.assertExprs(...args);
    }

    assertExprs(...args: BoolExpr<'TODO'>[]) {
      for (let arg of args) {
        Z3.solver_assert(this.ctx.ptr, this.ptr, arg.ptr);
        throwIfError(this.ctx);
      }
    }

    async check(...assumptions: BoolExpr<'TODO'>[]) {
      let r = await Z3.solver_check_assumptions(
        this.ctx.ptr,
        this.ptr,
        assumptions.map(a => a.ptr),
      );
      throwIfError(this.ctx);
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
      let m = Z3.solver_get_model(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      if ((m as unknown as number) === 0) {
        throw new Error('failed to get model');
      }
      return new Model(m, this.ctx);
    }

    help() {
      return Z3.solver_get_help(this.ctx.ptr, this.ptr);
    }

    toString() {
      return Z3.solver_to_string(this.ctx.ptr, this.ptr);
    }
  };

  const Model = class Model {
    declare __brand: 'Model';

    declare ptr: Z3_model;
    declare ctx: Context<'TODO'>;
    constructor(m: Z3_model, ctx = mainCtx()) {
      this.ptr = m;
      this.ctx = ctx;
      Z3.model_inc_ref(this.ctx.ptr, this.ptr);
      cleanupRegistry.register(this, () => Z3.model_dec_ref(ctx.ptr, m));
    }

    length() {
      let a = Z3.model_get_num_consts(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      let b = Z3.model_get_num_funcs(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return a + b;
    }

    *[Symbol.iterator]() {
      let num_consts = Z3.model_get_num_consts(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      for (let i = 0; i < num_consts; ++i) {
        let decl = Z3.model_get_const_decl(this.ctx.ptr, this.ptr, i);
        throwIfError(this.ctx);
        yield new FuncDecl(decl, this.ctx);
      }
      let num_funcs = Z3.model_get_num_funcs(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      for (let i = 0; i < num_funcs; ++i) {
        let decl = Z3.model_get_func_decl(this.ctx.ptr, this.ptr, i);
        throwIfError(this.ctx);
        yield new FuncDecl(decl, this.ctx);
      }
    }

    getInterp(decl: FuncDecl<'TODO'>): Expr<'TODO'> | FuncInterp<'TODO'> | null {
      if (decl.arity() === 0) {
        let _r = Z3.model_get_const_interp(this.ctx.ptr, this.ptr, decl.ptr);
        throwIfError(this.ctx);
        if (_r == null) {
          throw new Error('npe in getInterp');
        }
        let r = astPtrToExpr(_r, this.ctx);
        if (isAsArray(r)) {
          throw new Error('unimplement: getInterp of as_array');
        } else {
          return r;
        }
      } else {
        let interp = Z3.model_get_func_interp(this.ctx.ptr, this.ptr, decl.ptr);
        throwIfError(this.ctx);
        if (interp == null) {
          return null;
        }
        return new FuncInterp(interp, this.ctx);
      }
    }

    evaluate(t: Expr<'TODO'>, modelCompletion = false) {
      let out = Z3.model_eval(this.ctx.ptr, this.ptr, t.ptr, modelCompletion);
      throwIfError(this.ctx);
      if (out == null) {
        throw new Error('failed to evaluate expression in the model');
      }
      return astPtrToExpr(out, this.ctx);
    }
  };

  const FuncInterp = class FuncInterp {
    declare __brand: 'FuncInterp';

    declare ptr: Z3_func_interp;
    declare ctx: Context<'TODO'>;
    constructor(f: Z3_func_interp, ctx = mainCtx()) {
      this.ptr = f;
      this.ctx = ctx;
    }
  };

  const AST = class AST {
    declare __brand:
      | 'AST'
      | FuncDecl<'TODO'>['__brand']
      | Expr<'TODO'>['__brand']
      | Sort<'TODO'>['__brand'];

    declare ptr: Z3_ast;
    declare ctx: Context<'TODO'>;
    constructor(ast: Z3_ast, ctx: Context<'TODO'> = mainCtx()) {
      Z3.inc_ref(ctx.ptr, ast);
      this.ptr = ast;
      this.ctx = ctx;
      cleanupRegistry.register(this, () => Z3.dec_ref(ctx.ptr, ast));
    }

    valueOf() {
      throw new Error('attempting to take value of ref; this is almost certainly a mistake');
    }

    toString() {
      let str = Z3.ast_to_string(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return str;
    }

    astKind() {
      let out = Z3.get_ast_kind(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return out;
    }
  };

  const FuncDecl = class FuncDecl extends AST {
    declare __brand: 'FuncDecl';

    declare ptr: Z3_func_decl;
    constructor(ast: Z3_func_decl, ctx = mainCtx()) {
      super(ast, ctx);
    }

    arity() {
      let out = Z3.get_arity(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return out;
    }

    name() {
      let name = Z3.get_decl_name(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return symbolToJsValue(this.ctx, name);
    }

    declKind() {
      let kind = Z3.get_decl_kind(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return kind;
    }
  };

  type _Expr<ContextName extends string> = Expr<ContextName>;
  const Expr = class Expr extends AST {
    declare __brand: 'Expr' | ArithExpr<'TODO'>['__brand'];

    static from(a: boolean, ctx?: Context<'TODO'>): BoolExpr<'TODO'>;
    static from(a: number, ctx?: Context<'TODO'>): _IntNumeralExpr<'TODO'>;
    static from(a: CoercibleToExpr<'TODO'>, ctx?: Context<'TODO'>): _Expr<'TODO'>;
    static from(a: CoercibleToExpr<'TODO'>, ctx = mainCtx()): _Expr<'TODO'> {
      if (typeof a === 'boolean') {
        return new BoolExpr((a ? Z3.mk_false : Z3.mk_true)(ctx.ptr), ctx);
      } else if (typeof a === 'number') {
        if (Math.floor(a) !== a || !Number.isFinite(a)) {
          throw new Error('unimplemented: Expr.from support for non-integer values');
        }
        let numeral = Z3.mk_numeral(ctx.ptr, toIntStr(a), IntSort.from({ ctx }).ptr);
        throwIfError(ctx);
        return new IntNumeralExpr(numeral, ctx);
      } else if (a instanceof Expr) {
        return a;
      } else {
        throw new Error(`unimplemented: Expr.from support for ${typeof a}`);
      }
    }

    eq(other: CoercibleToExpr<'TODO'>) {
      let [a, b] = coerceExprs([this, other]);
      let eq = Z3.mk_eq(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(eq, this.ctx);
    }

    neq(other: CoercibleToExpr<'TODO'>) {
      let [a, b] = coerceExprs([this, other]);
      let distinct = Z3.mk_distinct(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new BoolExpr(distinct, this.ctx);
    }

    sort(): Sort<'TODO'> {
      throw new Error(`unimplemented: sort on ${this.constructor.name}`);
    }

    decl() {
      if (!isApp(this)) {
        throw new Error('decl called on non-app');
      }
      let decl = Z3.get_app_decl(this.ctx.ptr, this.ptr as unknown as Z3_app);
      throwIfError(this.ctx);
      return new FuncDecl(decl, this.ctx);
    }

    numArgs() {
      if (!isApp(this)) {
        throw new Error('num_args called on non-app');
      }
      let out = Z3.get_app_num_args(this.ctx.ptr, this.ptr as unknown as Z3_app);
      throwIfError(this.ctx);
      return out;
    }

    arg(idx: number): _Expr<'TODO'> {
      if (!isApp(this)) {
        throw new Error('arg called on non-app');
      }
      let ptr = Z3.get_app_arg(this.ctx.ptr, this.ptr as Z3_app, idx);
      throwIfError(this.ctx);
      return astPtrToExpr(ptr, this.ctx);
    }

    children(): _Expr<'TODO'>[] {
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

  type _ArithExpr<ContextName extends string> = ArithExpr<ContextName>;
  const ArithExpr = class ArithExpr extends Expr {
    declare __brand: 'ArithExpr' | IntNumeralExpr<'TODO'>['__brand'] | BoolExpr<'TODO'>['__brand'];

    sort(): Sort<'TODO'> {
      let sort = Z3.get_sort(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return new ArithSort(sort, this.ctx);
    }

    neg() {
      let r = Z3.mk_unary_minus(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    add(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_add(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    sub(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_sub(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    mul(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_mul(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    div(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_div(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    mod(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_mod(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    pow(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_power(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    le(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_le(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    lt(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_lt(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    ge(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_ge(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    gt(other: _ArithExpr<'TODO'> | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_gt(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }
  };

  const IntNumeralExpr = class IntNumeralExpr extends ArithExpr {
    declare __brand: 'IntNumeralExpr';

    toString() {
      let out = Z3.get_numeral_string(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return out;
    }
  };

  const BoolExpr = class BoolExpr extends ArithExpr {
    declare __brand: 'BoolExpr';

    sort() {
      let sort = Z3.get_sort(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return new BoolSort(sort, this.ctx);
    }

    not() {
      let r = Z3.mk_not(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    iff(other: _BoolExpr<'TODO'> | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_iff(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    implies(other: _BoolExpr<'TODO'> | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_implies(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    xor(other: _BoolExpr<'TODO'> | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_xor(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    and(other: _BoolExpr<'TODO'> | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_and(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    or(other: _BoolExpr<'TODO'> | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_or(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }
  };

  let Sort: SortCtor<'TODO'> = class Sort extends AST {
    declare __brand: 'Sort' | ArithSort['__brand'];

    declare ptr: Z3_sort;
    constructor(sort: Z3_sort, ctx = mainCtx()) {
      super(sort, ctx);
    }

    eq(other: Sort) {
      let out = Z3.is_eq_sort(this.ctx.ptr, this.ptr, other.ptr);
      throwIfError(this.ctx);
      return out;
    }
  };

  class ArithSort extends Sort {
    declare __brand: 'ArithSort' | BoolSort['__brand'] | IntSort['__brand'];
  }

  class BoolSort extends Sort {
    declare __brand: 'BoolSort';

    static from({ ctx = mainCtx(), sort = Z3.mk_bool_sort(ctx.ptr) } = {}) {
      return new BoolSort(sort, ctx);
    }
  }

  class IntSort extends Sort {
    declare __brand: 'IntSort';

    static from({ ctx = mainCtx(), sort = Z3.mk_int_sort(ctx.ptr) } = {}) {
      return new IntSort(sort, ctx);
    }
  }

  function jsValueToSymbol(s: number | string, ctx = mainCtx()) {
    if (typeof s === 'number') {
      assertInt(s);
      let out = Z3.mk_int_symbol(ctx.ptr, s);
      throwIfError(ctx);
      return out;
    } else if (typeof s === 'string') {
      let out = Z3.mk_string_symbol(ctx.ptr, s);
      throwIfError(ctx);
      return out;
    } else {
      throw new Error(`unreachable: to_symbol called with ${typeof s}`);
    }
  }

  function symbolToJsValue(ctx: Context<'TODO'>, s: Z3_symbol) {
    let kind = Z3.get_symbol_kind(ctx.ptr, s);
    throwIfError(ctx);
    if (kind === Z3_symbol_kind.Z3_INT_SYMBOL) {
      let int = Z3.get_symbol_int(ctx.ptr, s);
      throwIfError(ctx);
      return `k!${int}`;
    } else {
      let out = Z3.get_symbol_string(ctx.ptr, s);
      throwIfError(ctx);
      return out;
    }
  }

  function isApp(a: Expr<'TODO'>) {
    let kind = a.astKind();
    return kind == Z3_ast_kind.Z3_NUMERAL_AST || kind == Z3_ast_kind.Z3_APP_AST;
  }

  let isConst = (a: Expr<'TODO'>) => isApp(a) && a.numArgs() === 0;

  function isAsArray(n: Expr<'TODO'>) {
    let out = Z3.is_as_array(n.ctx.ptr, n.ptr);
    throwIfError(n.ctx);
    return out;
  }

  function astPtrToExpr(a: Z3_ast, ctx: Context<'TODO'>): ArithExpr<'TODO'> {
    let k = Z3.get_ast_kind(ctx.ptr, a);
    throwIfError(ctx);
    let sort = Z3.get_sort(ctx.ptr, a);
    throwIfError(ctx);
    let sk = Z3.get_sort_kind(ctx.ptr, sort);
    throwIfError(ctx);

    if (sk === Z3_sort_kind.Z3_BOOL_SORT) {
      return new BoolExpr(a, ctx);
    }
    if (sk === Z3_sort_kind.Z3_INT_SORT) {
      if (k === Z3_ast_kind.Z3_NUMERAL_AST) {
        return new IntNumeralExpr(a, ctx);
      }
      return new ArithExpr(a, ctx);
    }
    throw new Error(`unknown sort kind ${sk}`);
  }

  function coerceExprs(exprs: CoercibleToExpr<'TODO'>[], ctx?: Context<'TODO'> | null) {
    if (exprs.length === 0) {
      return [];
    }
    ctx ??= contextFromArgs(exprs) ?? mainCtx();
    let coerced = exprs.map(e => Expr.from(e, ctx!));
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

  function contextFromArgs(args: CoercibleToExpr<'TODO'>[]): Context<'TODO'> | null {
    let ctx: Context<'TODO'> | null = null;
    for (let a of args) {
      if (a instanceof AST /* || is_probe(a) */) {
        if (ctx == null) {
          ctx = (a as AST<'TODO'>).ctx;
        } else if (ctx !== (a as AST<'TODO'>).ctx) {
          throw new Error('args are from different contexts');
        }
      }
    }
    return ctx;
  }

  function Int(name: string, ctx = mainCtx()) {
    let c = Z3.mk_const(ctx.ptr, jsValueToSymbol(name, ctx), IntSort.from({ ctx }).ptr);
    throwIfError(ctx);
    return new ArithExpr(c, ctx);
  }

  function FreshInt(name: string, ctx = mainCtx()) {
    let c = Z3.mk_fresh_const(ctx.ptr, name, IntSort.from({ ctx }).ptr);
    throwIfError(ctx);
    return new ArithExpr(c, ctx);
  }

  function Bool(name: string, ctx = mainCtx()) {
    let c = Z3.mk_const(ctx.ptr, jsValueToSymbol(name, ctx), BoolSort.from({ ctx }).ptr);
    throwIfError(ctx);
    return new BoolExpr(c, ctx);
  }

  function Distinct(...args: CoercibleToExpr<'TODO'>[]) {
    let ctx = contextFromArgs(args);
    if (ctx == null) {
      throw new Error('at least one argument to Distinct must be a Z3 expression');
    }
    let coerced = coerceExprs(args, ctx);
    let d = Z3.mk_distinct(
      ctx.ptr,
      coerced.map(c => c.ptr),
    );
    throwIfError(ctx);
    return new BoolExpr(d, ctx);
  }

  function If(test: BoolExpr<'TODO'>, consequent: ArithExpr<'TODO'>, alternate: ArithExpr<'TODO'>) {
    let ctx = contextFromArgs([test, consequent, alternate])!;
    let ite = Z3.mk_ite(ctx.ptr, test.ptr, consequent.ptr, alternate.ptr);
    throwIfError(ctx);
    return new ArithExpr(ite, ctx);
  }

  async function evalSmtlib2String(command: string, ctx = mainCtx()) {
    let out = await Z3.eval_smtlib2_string(ctx.ptr, command);
    throwIfError(ctx);
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
}
