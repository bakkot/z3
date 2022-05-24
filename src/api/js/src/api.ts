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

export interface Context {
  __brand: 'Context';
  readonly ptr: Z3_context;
}
export interface ContextCtor {
  new (): Context;
}

export interface Solver {
  __brand: 'Solver';
  readonly ptr: Z3_solver;
  add: (...args: BoolExpr[]) => void;
  assertExprs: (...args: BoolExpr[]) => void;
  check: (...assumptions: BoolExpr[]) => Promise<'sat' | 'unsat' | 'unknown'>;
  model: () => Model;
  help: () => string;
  toString: () => string;
}
export interface SolverCtor {
  new (ctx?: Context): Solver;
}

export interface Model extends Iterable<FuncDecl> {
  __brand: 'Model';
  readonly ptr: Z3_model;
  length: () => number;
  [Symbol.iterator]: () => Iterator<FuncDecl>;
  getInterp: (decl: FuncDecl) => Expr | FuncInterp | null;
  evaluate: (t: Expr, modelCompletion?: boolean) => ArithExpr;
}
export interface ModelCtor {
  new (m: Z3_model, ctx?: Context): Model;
}

export interface FuncInterp {
  __brand: 'FuncInterp';
  readonly ptr: Z3_func_interp;
  readonly ctx: Context;
}
export interface FuncInterpCtor {
  new (f: Z3_func_interp, ctx?: Context): FuncInterp;
}

export interface AST {
  __brand: 'AST' | FuncDecl['__brand'] | Expr['__brand'] | Sort['__brand'];
  readonly ptr: Z3_ast;
  readonly ctx: Context;
  toString: () => string;
  astKind: () => Z3_ast_kind;
}
export interface ASTCtor {
  new (ast: Z3_ast, ctx?: Context): AST;
}

export interface FuncDecl extends AST {
  __brand: 'FuncDecl';
  readonly ptr: Z3_func_decl;
  arity: () => number;
  name: () => string;
  declKind: () => Z3_decl_kind;
}
export interface FuncDeclCtor extends ASTCtor {
  // TODO it would be good to have specialized sub-types for the AST pointers
  new (ast: Z3_ast, ctx?: Context): FuncDecl;
}

export interface Expr extends AST {
  __brand: 'Expr' | ArithExpr['__brand'];
  eq: (other: CoercibleToExpr) => BoolExpr;
  neq: (other: CoercibleToExpr) => BoolExpr;
  sort: () => Sort;
  decl: () => FuncDecl;
  numArgs: () => number;
  arg: (idx: number) => Expr;
  children: () => Expr[];
}
export interface ExprCtor extends ASTCtor {
  from(a: boolean, ctx?: Context): BoolExpr;
  from(a: number, ctx?: Context): IntNumeralExpr;
  from(a: CoercibleToExpr, ctx?: Context): Expr;
  new (ast: Z3_ast, ctx?: Context): Expr;
}
type _Expr = Expr;

export interface ArithExpr extends Expr {
  __brand: 'ArithExpr' | IntNumeralExpr['__brand'] | BoolExpr['__brand'];
  neg: () => ArithExpr;
  add: (other: ArithExpr | number) => ArithExpr;
  sub: (other: ArithExpr | number) => ArithExpr;
  mul: (other: ArithExpr | number) => ArithExpr;
  div: (other: ArithExpr | number) => ArithExpr;
  mod: (other: ArithExpr | number) => ArithExpr;
  pow: (other: ArithExpr | number) => ArithExpr;
  le: (other: ArithExpr | number) => BoolExpr;
  lt: (other: ArithExpr | number) => BoolExpr;
  ge: (other: ArithExpr | number) => BoolExpr;
  gt: (other: ArithExpr | number) => BoolExpr;
  toString: () => string;
}
export interface ArithExprCtor extends ExprCtor {
  new (ast: Z3_ast, ctx?: Context): ArithExpr;
}
type _ArithExpr = ArithExpr;

export interface IntNumeralExpr extends ArithExpr {
  __brand: 'IntNumeralExpr';
}
export interface IntNumeralExprCtor extends ArithExprCtor {
  new (ast: Z3_ast, ctx?: Context): IntNumeralExpr;
}

export interface BoolExpr extends ArithExpr {
  __brand: 'BoolExpr';
  not: () => BoolExpr;
  iff: (other: BoolExpr | boolean) => BoolExpr;
  implies: (other: BoolExpr | boolean) => BoolExpr;
  xor: (other: BoolExpr | boolean) => BoolExpr;
  and: (other: BoolExpr | boolean) => BoolExpr;
  or: (other: BoolExpr | boolean) => BoolExpr;
}
export interface BoolExprCtor extends ArithExprCtor {
  new (ast: Z3_ast, ctx?: Context): BoolExpr;
}
type _BoolExpr = BoolExpr;

export interface Sort extends AST {
  __brand: 'Sort' | BoolSort['__brand'] | ArithSort['__brand'];
  readonly ptr: Z3_sort;
  eq: (other: Sort) => boolean;
}
export interface SortCtor extends ASTCtor {
  new (ast: Z3_ast, ctx?: Context): Sort;
}

export interface ArithSort extends Sort {
  __brand: 'ArithSort' | IntSort['__brand'];
}
export interface ArithSortCtor extends ASTCtor {
  new (ast: Z3_ast, ctx?: Context): ArithSort;
}

export interface BoolSort extends Sort {
  // todo why not ArithSort?
  __brand: 'BoolSort';
}
export interface BoolSortCtor extends SortCtor {
  new (ast: Z3_ast, ctx?: Context): BoolSort;
}

export interface IntSort extends ArithSort {
  __brand: 'IntSort';
}
export interface IntSortCtor extends ArithSortCtor {
  new (ast: Z3_ast, ctx?: Context): IntSort;
}

export type CoercibleToExpr = boolean | number | Expr;

type API = {
  Context: ContextCtor;
  Solver: SolverCtor;
  Model: ModelCtor;
  Expr: ExprCtor;
  Int: (name: string, ctx?: Context) => ArithExpr;
  FreshInt: (name: string, ctx?: Context) => ArithExpr;
  Bool: (name: string, ctx?: Context) => BoolExpr;
  Distinct: (...args: CoercibleToExpr[]) => BoolExpr;
  If: (test: BoolExpr, consequent: ArithExpr, alternate: ArithExpr) => ArithExpr;
  evalSmtlib2String: (command: string, ctx?: Context) => Promise<string>;
};

type Z3 = Awaited<ReturnType<typeof import('../build/wrapper')['init']>>['Z3'];
export function makeAPI(Z3: Z3): API {
  // @ts-ignore I promise FinalizationRegistry is a thing
  let cleanupRegistry = new FinalizationRegistry<() => void>(thunk => {
    // console.log('cleaning up');
    thunk();
  });

  // Global Z3 context
  let _mainCtx: Context | null = null;

  function mainCtx() {
    if (_mainCtx === null) {
      _mainCtx = new Context();
    }
    return _mainCtx;
  }

  // call this after every nontrivial call to the underlying API
  function throwIfError(ctx: Context) {
    if (Z3.get_error_code(ctx.ptr) !== Z3_error_code.Z3_OK) {
      throw new Error(Z3.get_error_msg(ctx.ptr, Z3.get_error_code(ctx.ptr)));
    }
  }

  class Context {
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
  }

  class Solver {
    declare __brand: 'Solver';

    declare ctx: Context;
    declare ptr: Z3_solver;
    constructor(ctx = mainCtx()) {
      let solver = Z3.mk_solver(ctx.ptr);
      Z3.solver_inc_ref(ctx.ptr, solver);

      this.ctx = ctx;
      this.ptr = solver;
      cleanupRegistry.register(this, () => Z3.solver_dec_ref(ctx.ptr, solver));
    }

    add(...args: _BoolExpr[]) {
      this.assertExprs(...args);
    }

    assertExprs(...args: _BoolExpr[]) {
      for (let arg of args) {
        Z3.solver_assert(this.ctx.ptr, this.ptr, arg.ptr);
        throwIfError(this.ctx);
      }
    }

    async check(...assumptions: _BoolExpr[]) {
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
  }

  class Model {
    declare __brand: 'Model';

    declare ptr: Z3_model;
    declare ctx: Context;
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

    getInterp(decl: FuncDecl): Expr | FuncInterp | null {
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

    evaluate(t: _Expr, modelCompletion = false) {
      let out = Z3.model_eval(this.ctx.ptr, this.ptr, t.ptr, modelCompletion);
      throwIfError(this.ctx);
      if (out == null) {
        throw new Error('failed to evaluate expression in the model');
      }
      return astPtrToExpr(out, this.ctx);
    }
  }

  class FuncInterp {
    declare __brand: 'FuncInterp';

    declare ptr: Z3_func_interp;
    declare ctx: Context;
    constructor(f: Z3_func_interp, ctx = mainCtx()) {
      this.ptr = f;
      this.ctx = ctx;
    }
  }

  class AST {
    declare __brand: 'AST' | FuncDecl['__brand'] | Expr['__brand'] | Sort['__brand'];

    declare ptr: Z3_ast;
    declare ctx: Context;
    constructor(ast: Z3_ast, ctx: Context = mainCtx()) {
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
  }

  class FuncDecl extends AST {
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
  }

  class Expr extends AST {
    declare __brand: 'Expr' | ArithExpr['__brand'];

    static from(a: boolean, ctx?: Context): BoolExpr;
    static from(a: number, ctx?: Context): IntNumeralExpr;
    static from(a: CoercibleToExpr, ctx?: Context): Expr;
    static from(a: CoercibleToExpr, ctx = mainCtx()): Expr {
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

    eq(other: CoercibleToExpr) {
      let [a, b] = coerceExprs([this, other]);
      let eq = Z3.mk_eq(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(eq, this.ctx);
    }

    neq(other: CoercibleToExpr) {
      let [a, b] = coerceExprs([this, other]);
      let distinct = Z3.mk_distinct(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new BoolExpr(distinct, this.ctx);
    }

    sort(): Sort {
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

    arg(idx: number): Expr {
      if (!isApp(this)) {
        throw new Error('arg called on non-app');
      }
      let ptr = Z3.get_app_arg(this.ctx.ptr, this.ptr as Z3_app, idx);
      throwIfError(this.ctx);
      return astPtrToExpr(ptr, this.ctx);
    }

    children(): Expr[] {
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
  }

  class ArithExpr extends Expr {
    declare __brand: 'ArithExpr' | IntNumeralExpr['__brand'] | BoolExpr['__brand'];

    sort(): Sort {
      let sort = Z3.get_sort(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return new ArithSort(sort, this.ctx);
    }

    neg() {
      let r = Z3.mk_unary_minus(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    add(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_add(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    sub(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_sub(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    mul(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_mul(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    div(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_div(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    mod(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_mod(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    pow(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_power(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new ArithExpr(r, this.ctx);
    }

    le(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_le(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    lt(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_lt(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    ge(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_ge(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    gt(other: _ArithExpr | number) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_gt(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }
  }

  class IntNumeralExpr extends ArithExpr {
    declare __brand: 'IntNumeralExpr';

    toString() {
      let out = Z3.get_numeral_string(this.ctx.ptr, this.ptr);
      throwIfError(this.ctx);
      return out;
    }
  }

  class BoolExpr extends ArithExpr {
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

    iff(other: _BoolExpr | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_iff(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    implies(other: _BoolExpr | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_implies(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    xor(other: _BoolExpr | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_xor(this.ctx.ptr, a.ptr, b.ptr);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    and(other: _BoolExpr | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_and(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }

    or(other: _BoolExpr | boolean) {
      let [a, b] = coerceExprs([this, other]);
      let r = Z3.mk_or(this.ctx.ptr, [a.ptr, b.ptr]);
      throwIfError(this.ctx);
      return new BoolExpr(r, this.ctx);
    }
  }

  class Sort extends AST {
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
  }

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

  function symbolToJsValue(ctx: Context, s: Z3_symbol) {
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

  function isApp(a: Expr) {
    let kind = a.astKind();
    return kind == Z3_ast_kind.Z3_NUMERAL_AST || kind == Z3_ast_kind.Z3_APP_AST;
  }

  let isConst = (a: Expr) => isApp(a) && a.numArgs() === 0;

  function isAsArray(n: Expr) {
    let out = Z3.is_as_array(n.ctx.ptr, n.ptr);
    throwIfError(n.ctx);
    return out;
  }

  function astPtrToExpr(a: Z3_ast, ctx: Context): ArithExpr {
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

  function coerceExprs(exprs: CoercibleToExpr[], ctx?: Context | null) {
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

  function contextFromArgs(args: CoercibleToExpr[]): Context | null {
    let ctx: Context | null = null;
    for (let a of args) {
      if (a instanceof AST /* || is_probe(a) */) {
        if (ctx == null) {
          ctx = (a as AST).ctx;
        } else if (ctx !== (a as AST).ctx) {
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

  function Distinct(...args: CoercibleToExpr[]) {
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

  function If(test: _BoolExpr, consequent: _ArithExpr, alternate: _ArithExpr) {
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
