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

/************************************************************************/
/*                              Chapter 9                               */
/************************************************************************/

exception Empty;
exception Subscript;
exception Impossible_pattern(string);

let impossible_pat = x => raise(Impossible_pattern(x));

module Dense = {
  type digit =
    | Zero
    | One;
  type nat = list(digit); /* increasing order of significance */

  let rec inc =
    fun
    | [] => [One]
    | [Zero, ...ds] => [One, ...ds]
    | [One, ...ds] => [Zero, ...inc(ds)]; /* carry */

  let rec dec =
    fun
    | [One] => []
    | [One, ...ds] => [Zero, ...ds]
    | [Zero, ...ds] => [One, ...dec(ds)] /* borrow */
    | [] => impossible_pat("dec");

  let rec add = (d1, d2) =>
    switch (d1, d2) {
    | (ds, []) => ds
    | ([], ds) => ds
    | ([d, ...ds1], [Zero, ...ds2]) => [d, ...add(ds1, ds2)]
    | ([Zero, ...ds1], [d, ...ds2]) => [d, ...add(ds1, ds2)]
    | ([One, ...ds1], [One, ...ds2]) => [Zero, ...inc(add(ds1, ds2))]
    }; /* carry */
};

module SparseByWeight = {
  type nat = list(int); /* increasing list of weights, each a power of two */

  let rec carry = w =>
    fun
    | [] => [w]
    | [w', ...ws'] as ws =>
      if (w < w') {
        [w, ...ws];
      } else {
        carry(2 * w, ws');
      };

  let rec borrow = w =>
    fun
    | [w', ...ws'] as ws =>
      if (w == w') {
        ws';
      } else {
        [w, ...borrow(2 * w, ws)];
      }
    | [] => impossible_pat("borrow");

  let inc = ws => carry(1, ws);
  let dec = ws => borrow(1, ws);

  let rec add = (m, n) =>
    switch (m, n) {
    | (_, []) => m
    | ([], _) => n
    | ([w1, ...ws1], [w2, ...ws2]) =>
      if (w1 < w2) {
        [w1, ...add(ws1, n)];
      } else if (w2 < w1) {
        [w2, ...add(m, ws2)];
      } else {
        carry(2 * w1, add(ws1, ws2));
      }
    };
};

module type RANDOM_ACCESS_LIST = {
  type ra_list('a);

  let empty: ra_list('a);
  let is_empty: ra_list('a) => bool;

  let cons: ('a, ra_list('a)) => ra_list('a);
  let head: ra_list('a) => 'a;
  let tail: ra_list('a) => ra_list('a);
  /* head and tail raise Empty if list is empty */

  let lookup: (int, ra_list('a)) => 'a;
  let update: (int, 'a, ra_list('a)) => ra_list('a);
  /* lookup and update raise Subscript if index is out of bounds */
};

module BinaryRandomAccessList: RANDOM_ACCESS_LIST = {
  type tree('a) =
    | Leaf('a)
    | Node(int, tree('a), tree('a));
  type digit('a) =
    | Zero
    | One(tree('a));
  type ra_list('a) = list(digit('a));

  let empty = [];
  let is_empty = ts => ts == [];

  let size =
    fun
    | Leaf(_) => 1
    |  Node(w, _, _) => w;

  let link = (t1, t2) =>
     Node(size(t1) + size(t2), t1, t2);

  let rec cons_tree = t =>
    fun
    | [] => [One(t)]
    | [Zero, ...ts] => [One(t), ...ts]
    | [One(t'), ...ts] => [Zero, ...cons_tree(link(t, t'), ts)];

  let rec uncons_tree =
    fun
    | [] => raise(Empty)
    | [One(t)] => (t, [])
    | [One(t), ...ts] => (t, [Zero, ...ts])
    | [Zero, ...ts] =>
      switch (uncons_tree(ts)) {
      | ( Node(_, t1, t2), ts') => (
          t1,
          [One(t2), ...ts'],
        )
      | _ => impossible_pat("uncons_tree")
      };

  let cons = (x, ts) => cons_tree(Leaf(x), ts);

  let head = ts =>
    switch (uncons_tree(ts)) {
    | (Leaf(x), _) => x
    | _ => impossible_pat("head")
    };

  let tail = ts => snd(uncons_tree(ts));

  let rec lookup_tree = (i, t) =>
    switch (i, t) {
    | (0, Leaf(x)) => x
    | (_, Leaf(_)) => raise(Subscript)
    | (i,  Node(w, t1, t2)) =>
      if (i < w / 2) {
        lookup_tree(i, t1);
      } else {
        lookup_tree(i - w / 2, t2);
      }
    };

  let rec update_tree = (i, y, t) =>
    switch (i, t) {
    | (0, Leaf(_)) => Leaf(y)
    | (_, Leaf(_)) => raise(Subscript)
    | (_,  Node(w, t1, t2)) =>
      if (i < w / 2) {
         Node(w, update_tree(i, y, t1), t2);
      } else {
         Node(w, t1, update_tree(i - w / 2, y, t2));
      }
    };

  let rec lookup = i =>
    fun
    | [] => raise(Subscript)
    | [Zero, ...ts] => lookup(i, ts)
    | [One(t), ...ts] =>
      if (i < size(t)) {
        lookup_tree(i, t);
      } else {
        lookup(i - size(t), ts);
      };

  let rec update = (i, y) =>
    fun
    | [] => raise(Subscript)
    | [Zero, ...ts] => [Zero, ...update(i, y, ts)]
    | [One(t), ...ts] =>
      if (i < size(t)) {
        [One(update_tree(i, y, t)), ...ts];
      } else {
        [One(t), ...update(i - size(t), y, ts)];
      };
};

module SkewBinaryRandomAccessList: RANDOM_ACCESS_LIST = {
  type tree('a) =
    | Leaf('a)
    | Node('a, tree('a), tree('a));
  type ra_list('a) = list((int, tree('a))); /* integer is the weight of the tree */

  let empty = [];
  let is_empty = ts => ts == [];

  let cons = x =>
    fun
    | [(w1, t1), (w2, t2), ...ts'] as ts =>
      if (w1 == w2) {
        [(1 + w1 + w2,  Node(x, t1, t2)), ...ts'];
      } else {
        [(1, Leaf(x)), ...ts];
      }
    | ts => [(1, Leaf(x)), ...ts];

  let head =
    fun
    | [] => raise(Empty)
    | [(1, Leaf(x)), ..._] => x
    | [(_,  Node(x, _, _)), ..._] => x
    | _ => impossible_pat("head");

  let tail =
    fun
    | [] => raise(Empty)
    | [(1, Leaf(_)), ...ts] => ts
    | [(w,  Node(_, t1, t2)), ...ts] => [
        (w / 2, t1),
        (w / 2, t2),
        ...ts,
      ]
    | _ => impossible_pat("tail");

  let rec lookup_tree = (w, i, t) =>
    switch (w, i, t) {
    | (1, 0, Leaf(x)) => x
    | (1, _, Leaf(_)) => raise(Subscript)
    | (_, 0,  Node(x, _, _)) => x
    | (_, _,  Node(_, t1, t2)) =>
      if (i <= w / 2) {
        lookup_tree(w / 2, i - 1, t1);
      } else {
        lookup_tree(w / 2, i - 1 - w / 2, t2);
      }
    | _ => impossible_pat("lookup_tree")
    };

  let rec update_tree =
    fun
    | (1, 0, y, Leaf(_)) => Leaf(y)
    | (1, _, _, Leaf(_)) => raise(Subscript)
    | (_, 0, y,  Node(_, t1, t2)) =>
       Node(y, t1, t2)
    | (w, i, y,  Node(x, t1, t2)) =>
      if (i <= w / 2) {
         Node(x, update_tree((w / 2, i - 1, y, t1)), t2);
      } else {

        Node(x, t1, update_tree((w / 2, i - 1 - w / 2, y, t2)));
      }
    | _ => impossible_pat("update_tree");

  let rec lookup = i =>
    fun
    | [] => raise(Subscript)
    | [(w, t), ...ts] =>
      if (i < w) {
        lookup_tree(w, i, t);
      } else {
        lookup(i - w, ts);
      };

  let rec update = (i, y) =>
    fun
    | [] => raise(Subscript)
    | [(w, t), ...ts] =>
      if (i < w) {
        [(w, update_tree((w, i, y, t))), ...ts];
      } else {
        [(w, t), ...update(i - w, y, ts)];
      };
};

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

module SkewBinomialHeap =
       (Element: ORDERED)
       : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type tree =
    | Node(int, Elem.t, list(Elem.t), list(tree));
  type heap = list(tree);

  let empty = [];
  let is_empty = ts => ts == [];

  let rank = ( Node(r, _, _, _)) => r;
  let root = ( Node(_, x, _, _)) => x;

  let link =
      (
         Node(r, x1, xs1, c1) as t1,
         Node(_, x2, xs2, c2) as t2,
      ) =>
    if (Elem.leq(x1, x2)) {
       Node(r + 1, x1, xs1, [t2, ...c1]);
    } else {
       Node(r + 1, x2, xs2, [t1, ...c2]);
    };

  let skew_link = (x, t1, t2) => {
    let  Node(r, y, ys, c) = link(t1, t2);
    if (Elem.leq(x, y)) {
       Node(r, x, [y, ...ys], c);
    } else {
       Node(r, y, [x, ...ys], c);
    };
  };

  let rec ins_tree = t =>
    fun
    | [] => [t]
    | [t', ...ts] =>
      if (rank(t) < rank(t')) {
        [t, t', ...ts];
      } else {
        ins_tree(link(t, t'), ts);
      };

  let rec merge_trees = (ts1, ts2) =>
    switch (ts1, ts2) {
    | (_, []) => ts1
    | ([], _) => ts2
    | ([t1, ...ts1'], [t2, ...ts2']) =>
      if (rank(t1) < rank(t2)) {
        [t1, ...merge_trees(ts1', ts2)];
      } else if (rank(t2) < rank(t1)) {
        [t2, ...merge_trees(ts1, ts2')];
      } else {
        ins_tree(link(t1, t2), merge_trees(ts1', ts2'));
      }
    };

  let normalize =
    fun
    | [] => []
    | [t, ...ts] => ins_tree(t, ts);

  let insert = x =>
    fun
    | [t1, t2, ...rest] as ts =>
      if (rank(t1) == rank(t2)) {
        [skew_link(x, t1, t2), ...rest];
      } else {
        [ Node(0, x, [], []), ...ts];
      }
    | ts => [ Node(0, x, [], []), ...ts];

  let merge = (ts1, ts2) => merge_trees(normalize(ts1), normalize(ts2));

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
    let ( Node(_, _, xs, ts1), ts2) = remove_min_tree(ts);
    let rec insert_all = ts =>
      fun
      | [] => ts
      | [x, ...xs'] => insert_all(insert(x, ts), xs');
    insert_all(merge(List.rev(ts1), ts2), xs);
  };
};
