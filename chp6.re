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
/*                              Chapter 6                              */
/***********************************************************************/

exception Empty;
exception Impossible_pattern(string);

let impossible_pat = x => raise(Impossible_pattern(x));

module type QUEUE = {
  type queue('a);

  let empty: queue('a);
  let is_empty: queue('a) => bool;

  let snoc: (queue('a), 'a) => queue('a);
  let head: queue('a) => 'a; /* raises Empty if queue is empty */
  let tail: queue('a) => queue('a); /* raises Empty if queue is empty */
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

/* ---------- Streams as found in chapter 4 ---------- */

let (!$) = Lazy.force;

module type STREAM = {
  type stream_cell('a) =
    | Nil
    | Cons('a, stream('a))
  and stream('a) = Lazy.t(stream_cell('a));

  let (++): (stream('a), stream('a)) => stream('a); /* stream append */
  let take: (int, stream('a)) => stream('a);
  let drop: (int, stream('a)) => stream('a);
  let reverse: stream('a) => stream('a);
};

module Stream: STREAM = {
  type stream_cell('a) =
    | Nil
    | Cons('a, stream('a))
  and stream('a) = Lazy.t(stream_cell('a));

  let rec (++) = (s1, s2) =>
    lazy(
      switch (s1) {
      | lazy Nil => Lazy.force(s2)
      | lazy ( Cons(hd, tl)) =>
         Cons(hd, tl ++ s2)
      }
    );

  let rec take = (n, s) =>
    lazy(
      if (n == 0) {
        Nil;
      } else {
        switch (s) {
        | lazy Nil => Nil
        | lazy ( Cons(hd, tl)) =>
           Cons(hd, take(n - 1, tl))
        };
      }
    );

  let rec drop = (n, s) =>
    lazy(
      switch (n, s) {
      | (0, _) => !$s
      | (_, lazy Nil) => Nil
      | (_, lazy ( Cons(_, tl))) => !$drop(n - 1, tl)
      }
    );

  let reverse = s => {
    let rec reverse' = (acc, s) =>
      lazy(
        switch (s) {
        | lazy Nil => !$acc
        | lazy ( Cons(hd, tl)) =>
          !$reverse'(lazy( Cons(hd, acc)), tl)
        }
      );

    reverse'(lazy(Nil), s);
  };
};

open Stream;

module BankersQueue: QUEUE = {
  type queue('a) = (int, stream('a), int, stream('a));

  let empty = (0, lazy(Nil), 0, lazy(Nil));
  let is_empty = ((lenf, _, _, _)) => lenf == 0;

  let check = ((lenf, f, lenr, r) as q) =>
    if (lenr <= lenf) {
      q;
    } else {
      (lenf + lenr, f ++ reverse(r), 0, lazy(Nil));
    };

  let snoc = ((lenf, f, lenr, r), x) =>
    check((lenf, f, lenr + 1, lazy( Cons(x, r))));

  let head =
    fun
    | (_, lazy Nil, _, _) => raise(Empty)
    | (_, lazy ( Cons(x, _)), _, _) => x;

  let tail =
    fun
    | (_, lazy Nil, _, _) => raise(Empty)
    | (lenf, lazy ( Cons(_, f')), lenr, r) =>
      check((lenf - 1, f', lenr, r));
};

module LazyBinomialHeap =
       (Element: ORDERED)
       : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type tree =
    | Node(int, Elem.t, list(tree));
  type heap = Lazy.t(list(tree));

  let empty = lazy([]);
  let is_empty = ts => !$ts == [];

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

  let rec ins_tree = (t, ts) =>
    switch (t, ts) {
    | (_, []) => [t]
    | (t, [t', ...ts']) =>
      if (rank(t) < rank(t')) {
        [t, ...ts];
      } else {
        ins_tree(link(t, t'), ts');
      }
    };

  let rec mrg = (ts1, ts2) =>
    switch (ts1, ts2) {
    | (_, []) => ts1
    | ([], _) => ts2
    | ([t1, ...ts1'], [t2, ...ts2']) =>
      if (rank(t1) < rank(t2)) {
        [t1, ...mrg(ts1', ts2)];
      } else if (rank(t2) < rank(t1)) {
        [t2, ...mrg(ts1, ts2')];
      } else {
        ins_tree(link(t1, t2), mrg(ts1', ts2'));
      }
    };

  /* fun lazy */
  let insert = (x, ts) =>
    lazy(ins_tree( Node(0, x, []), !$ts));

  /* fun lazy */
  let merge = (ts1, ts2) => lazy(mrg(!$ts1, !$ts2));

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

  let find_min = ts => {
    let (t, _) = remove_min_tree(!$ts);
    root(t);
  };

  /* fun lazy */
  let delete_min = ts => {
    let ( Node(_, _, ts1), ts2) = remove_min_tree(!$ts);
    lazy(mrg(List.rev(ts1), ts2));
  };
};

module PhysicistsQueue: QUEUE = {
  type queue('a) = (list('a), int, Lazy.t(list('a)), int, list('a));

  let empty = ([], 0, lazy([]), 0, []);
  let is_empty = ((_, lenf, _, _, _)) => lenf == 0;

  let checkw =
    fun
    | ([], lenf, f, lenr, r) => (!$f, lenf, f, lenr, r)
    | q => q;

  let check = ((_, lenf, f, lenr, r) as q) =>
    if (lenr <= lenf) {
      checkw(q);
    } else {
      let f' = !$f;
      checkw((f', lenf + lenr, lazy(f' @ List.rev(r)), 0, []));
    };

  let snoc = ((w, lenf, f, lenr, r), x) =>
    check((w, lenf, f, lenr + 1, [x, ...r]));

  let head =
    fun
    | ([], _, _, _, _) => raise(Empty)
    | ([x, ..._], _, _, _, _) => x;

  let tail =
    fun
    | ([], _, _, _, _) => raise(Empty)
    | ([_, ...w], lenf, f, lenr, r) =>
      check((w, lenf - 1, lazy(List.tl(!$f)), lenr, r));
};

module type SORTABLE = {
  module Elem: ORDERED;

  type sortable;

  let empty: sortable;
  let add: (Elem.t, sortable) => sortable;
  let sort: sortable => list(Elem.t);
};

module BottomUpMergeSort =
       (Element: ORDERED)
       : (SORTABLE with module Elem = Element) => {
  module Elem = Element;

  type sortable = (int, Lazy.t(list(list(Elem.t))));

  let rec mrg = (xs, ys) =>
    switch (xs, ys) {
    | ([], _) => ys
    | (_, []) => xs
    | ([x, ...xs'], [y, ...ys']) =>
      if (Elem.leq(x, y)) {
        [x, ...mrg(xs', ys)];
      } else {
        [y, ...mrg(xs, ys')];
      }
    };

  let empty = (0, lazy([]));

  let add = (x, (size, segs)) => {
    let rec add_seg = (seg, size, segs) =>
      if (size mod 2 == 0) {
        [seg, ...segs];
      } else {
        add_seg(mrg(seg, List.hd(segs)), size / 2, List.tl(segs));
      };
    (size + 1, lazy(add_seg([x], size, !$segs)));
  };

  let sort = ((_, segs)) => {
    let rec mrg_all = xs =>
      fun
      | [] => xs
      | [seg, ...segs] => mrg_all(mrg(xs, seg), segs);
    mrg_all([], !$segs);
  };
};

module LazyPairingHeap =
       (Element: ORDERED)
       : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type heap =
    | E
    | T(Elem.t, heap, Lazy.t(heap));

  let empty = E;
  let is_empty = h => h == E;

  let rec merge = (a, b) =>
    switch (a, b) {
    | (_, E) => a
    | (E, _) => b
    | ( T(x, _, _),  T(y, _, _)) =>
      if (Elem.leq(x, y)) {
        link(a, b);
      } else {
        link(b, a);
      }
    }

  and link = (h, a) =>
    switch (h) {
    |  T(x, E, m) =>  T(x, a, m)
    |  T(x, b, m) =>
       T(x, E, lazy(merge(merge(a, b), !$m)))
    | _ => impossible_pat("link")
    };

  let insert = (x, a) => merge( T(x, E, lazy(E)), a);

  let find_min =
    fun
    | E => raise(Empty)
    |  T(x, _, _) => x;
  let delete_min =
    fun
    | E => raise(Empty)
    |  T(_, a, b) => merge(a, !$b);
};
