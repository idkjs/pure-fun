/*
    Original source code in SML from:

      Purely Functional Data Structures
      Chris Okasaki
      Cambridge University Press, 1998
      Copyright (c) 1998 Cambridge University Press

    Translation from SML to OCAML (this file):

      Copyright (C) 1999, 2000, 2001  Markus Mottl
      email:  markus.mottl@gmail.com
      www:    http://www.ocaml.info

    Licensed under the Apache License, Version 2.0 (the "License"); you may
    not use this file except in compliance with the License.  You may obtain
    a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
    License for the specific language governing permissions and limitations
    under the License.
 */

/***********************************************************************/
/*                              Chapter 2                              */
/***********************************************************************/

exception Empty;
exception Subscript;

module type STACK = {
  type stack('a);

  let empty: stack('a);
  let is_empty: stack('a) => bool;
  let cons: ('a, stack('a)) => stack('a);
  let head: stack('a) => 'a; /* raises Empty if stack is empty */
  let tail: stack('a) => stack('a); /* raises Empty if stack is empty */
  let (++): (stack('a), stack('a)) => stack('a);
};

module ListStack: STACK = {
  type stack('a) = list('a);

  let empty = [];
  let is_empty = s => s == [];
  let cons = (x, s) => [x, ...s];
  let head =
    fun
    | [] => raise(Empty)
    | [h, ..._] => h;
  let tail =
    fun
    | [] => raise(Empty)
    | [_, ...t] => t;
  let (++) = (@);
};

module CustomStack: STACK = {
  type stack('a) =
    | Nil
    | Cons('a, stack('a));

  let cons = (x, s) =>  Cons(x, s);
  let empty = Nil;

  let is_empty = s => s == Nil;
  let head =
    fun
    | Nil => raise(Empty)
    |  Cons(x, _) => x;
  let tail =
    fun
    | Nil => raise(Empty)
    |  Cons(_, s) => s;

  let rec (++) = (xs, ys) =>
    if (is_empty(xs)) {
      ys;
    } else {
      cons(head(xs), tail(xs) ++ ys);
    };
};

let rec (++) = (xs, ys) =>
  switch (xs) {
  | [] => ys
  | [xh, ...xt] => [xh, ...xt ++ ys]
  };

let rec update = (lst, i, y) =>
  switch (lst, i) {
  | ([], _) => raise(Subscript)
  | ([_, ...xs], 0) => [y, ...xs]
  | ([x, ...xs], _) => [x, ...update(xs, i - 1, y)]
  };

module type SET = {
  type elem;
  type set;

  let empty: set;
  let insert: (elem, set) => set;
  let member: (elem, set) => bool;
};

/* A totally ordered type and its comparison functions */
module type ORDERED = {
  type t;

  let eq: (t, t) => bool;
  let lt: (t, t) => bool;
  let leq: (t, t) => bool;
};

module UnbalancedSet = (Element: ORDERED) : (SET with type elem = Element.t) => {
  type elem = Element.t;
  type tree =
    | E
    | T(tree, elem, tree);
  type set = tree;

  let empty = E;

  let rec member = x =>
    fun
    | E => false
    |  T(a, y, b) =>
      if (Element.lt(x, y)) {
        member(x, a);
      } else if (Element.lt(y, x)) {
        member(x, b);
      } else {
        true;
      };

  let rec insert = x =>
    fun
    | E =>  T(E, x, E)
    |  T(a, y, b) as s =>
      if (Element.lt(x, y)) {
         T(insert(x, a), y, b);
      } else if (Element.lt(y, x)) {
         T(a, y, insert(x, b));
      } else {
        s;
      };
};

module type FINITE_MAP = {
  type key;
  type map('a);

  let empty: map('a);
  let bind: (key, 'a, map('a)) => map('a);
  let lookup: (key, map('a)) => 'a; /* raise Not_found if key is not found */
};
