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
/*                              Chapter 3                              */
/***********************************************************************/

exception Empty;
exception Impossible_pattern(string);

let impossible_pat = x => raise(Impossible_pattern(x));

/* A totally ordered type and its comparison functions */
module type ORDERED = {
  type t;

  let eq: (t, t) => bool;
  let lt: (t, t) => bool;
  let leq: (t, t) => bool;
};

module type HEAP = {
  module Elem: ORDERED;

  type heap;

  let empty: heap;
  let is_empty: heap => bool;

  let insert: (Elem.t, heap) => heap;
  let merge: (heap, heap) => heap;

  let find_min: heap => Elem.t; /* raises Empty if heap is empty */
  let delete_min: heap => heap; /* raises Empty if heap is empty */
};

module LeftistHeap = (Element: ORDERED) : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type heap =
    | E
    | T(int, Elem.t, heap, heap);

  let rank =
    fun
    | E => 0
    |  T(r, _, _, _) => r;

  let makeT = (x, a, b) =>
    if (rank(a) >= rank(b)) {
       T(rank(b) + 1, x, a, b);
    } else {
       T(rank(a) + 1, x, b, a);
    };

  let empty = E;
  let is_empty = h => h == E;

  let rec merge = (h1, h2) =>
    switch (h1, h2) {
    | (_, E) => h1
    | (E, _) => h2
    | ( T(_, x, a1, b1),  T(_, y, a2, b2)) =>
      if (Elem.leq(x, y)) {
        makeT(x, a1, merge(b1, h2));
      } else {
        makeT(y, a2, merge(h1, b2));
      }
    };

  let insert = (x, h) => merge( T(1, x, E, E), h);
  let find_min =
    fun
    | E => raise(Empty)
    |  T(_, x, _, _) => x;
  let delete_min =
    fun
    | E => raise(Empty)
    |  T(_, _, a, b) => merge(a, b);
};

module BinomialHeap = (Element: ORDERED) : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type tree =
    | Node(int, Elem.t, list(tree));
  type heap = list(tree);

  let empty = [];
  let is_empty = ts => ts == [];

  let rank = ( Node(r, _, _)) => r;
  let root = ( Node(_, x, _)) => x;

  let link =
      (
         Node(r, x1, c1) as t1,
         Node(_, x2, c2) as t2,
      ) =>
    if (Elem.leq(x1, x2)) {
       Node(r + 1, x1, [t2, ...c1]);
    } else {
       Node(r + 1, x2, [t1, ...c2]);
    };

  let rec ins_tree = t =>
    fun
    | [] => [t]
    | [t', ...ts'] as ts =>
      if (rank(t) < rank(t')) {
        [t, ...ts];
      } else {
        ins_tree(link(t, t'), ts');
      };

  let insert = (x, ts) => ins_tree( Node(0, x, []), ts);

  let rec merge = (ts1, ts2) =>
    switch (ts1, ts2) {
    | (_, []) => ts1
    | ([], _) => ts2
    | ([t1, ...ts1'], [t2, ...ts2']) =>
      if (rank(t1) < rank(t2)) {
        [t1, ...merge(ts1', ts2)];
      } else if (rank(t2) < rank(t1)) {
        [t2, ...merge(ts1, ts2')];
      } else {
        ins_tree(link(t1, t2), merge(ts1', ts2'));
      }
    };

  let rec remove_min_tree =
    fun
    | [] => raise(Empty)
    | [t] => (t, [])
    | [t, ...ts] => {
        let (t', ts') = remove_min_tree(ts);
        if (Elem.leq(root(t), root(t'))) {
          (t, ts);
        } else {
          (t', [t, ...ts']);
        };
      };

  let find_min = ts => root(fst(remove_min_tree(ts)));

  let delete_min = ts => {
    let ( Node(_, _, ts1), ts2) = remove_min_tree(ts);
    merge(List.rev(ts1), ts2);
  };
};

module type SET = {
  type elem;
  type set;

  let empty: set;
  let insert: (elem, set) => set;
  let member: (elem, set) => bool;
};

module RedBlackSet = (Element: ORDERED) : (SET with type elem = Element.t) => {
  type elem = Element.t;

  type color =
    | R
    | B;
  type tree =
    | E
    | T(color, tree, elem, tree);
  type set = tree;

  let empty = E;

  let rec member = x =>
    fun
    | E => false
    |  T(_, a, y, b) =>
      if (Element.lt(x, y)) {
        member(x, a);
      } else if (Element.lt(y, x)) {
        member(x, b);
      } else {
        true;
      };

  let balance =
    fun
    | (
        B,
         T(R,  T(R, a, x, b), y, c),
        z,
        d,
      )
    | (
        B,
         T(R, a, x,  T(R, b, y, c)),
        z,
        d,
      )
    | (
        B,
        a,
        x,
         T(R,  T(R, b, y, c), z, d),
      )
    | (
        B,
        a,
        x,
         T(R, b, y,  T(R, c, z, d)),
      ) =>

      T(
        R,
         T(B, a, x, b),
        y,
         T(B, c, z, d),
      )
    | (a, b, c, d) =>  T(a, b, c, d);

  let insert = (x, s) => {
    let rec ins =
      fun
      | E =>  T(R, E, x, E)
      |  T(color, a, y, b) as s =>
        if (Element.lt(x, y)) {
          balance((color, ins(a), y, b));
        } else if (Element.lt(y, x)) {
          balance((color, a, y, ins(b)));
        } else {
          s;
        };
    switch (ins(s)) {
    /* guaranteed to be non-empty */
    |  T(_, a, y, b) =>  T(B, a, y, b)
    | _ => impossible_pat("insert")
    };
  };
};
