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
/*                              Chapter 7                              */
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

module type SORTABLE = {
  module Elem: ORDERED;

  type sortable;

  let empty: sortable;
  let add: (Elem.t, sortable) => sortable;
  let sort: sortable => list(Elem.t);
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

module RealTimeQueue: QUEUE = {
  type queue('a) = (stream('a), list('a), stream('a));

  let empty = (lazy(Nil), [], lazy(Nil));

  let is_empty =
    fun
    | (lazy Nil, _, _) => true
    | _ => false;

  let rec rotate =
    fun
    | (lazy Nil, [y, ..._], a) => lazy( Cons(y, a))
    | (lazy ( Cons(x, xs)), [y, ...ys], a) =>
      lazy(

        Cons(x, rotate((xs, ys, lazy( Cons(y, a)))))
      )
    | (_, [], _) => impossible_pat("rotate");

  let exec =
    fun
    | (f, r, lazy ( Cons(_, s))) => (f, r, s)
    | (f, r, lazy Nil) => {
        let f' = rotate((f, r, lazy(Nil)));
        (f', [], f');
      };

  let snoc = ((f, r, s), x) => exec((f, [x, ...r], s));

  let head = ((f, _, _)) =>
    switch (f) {
    | lazy Nil => raise(Empty)
    | lazy ( Cons(x, _)) => x
    };

  let tail =
    fun
    | (lazy Nil, _, _) => raise(Empty)
    | (lazy ( Cons(_, f)), r, s) => exec((f, r, s));
};

let rec list_to_stream =
  fun
  | [] => lazy(Nil)
  | [x, ...xs] => lazy( Cons(x, list_to_stream(xs)));

module ScheduledBinomialHeap =
       (Element: ORDERED)
       : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type tree =
    | Node(Elem.t, list(tree));
  type digit =
    | Zero
    | One(tree);
  type schedule = list(stream(digit));
  type heap = (stream(digit), schedule);

  let empty = (lazy(Nil), []);
  let is_empty = ((ds, _)) => ds == (lazy(Nil));

  let link =
      (
         Node(x1, c1) as t1,
         Node(x2, c2) as t2,
      ) =>
    if (Elem.leq(x1, x2)) {
       Node(x1, [t2, ...c1]);
    } else {
       Node(x2, [t1, ...c2]);
    };

  let rec ins_tree = t =>
    fun
    | lazy Nil => lazy( Cons(One(t), lazy(Nil)))
    | lazy ( Cons(Zero, ds)) =>
      lazy( Cons(One(t), ds))
    | lazy ( Cons(One(t'), ds)) =>
      lazy( Cons(Zero, ins_tree(link(t, t'), ds)));

  let rec mrg = (a, b) =>
    switch (a, b) {
    | (ds1, lazy Nil) => ds1
    | (lazy Nil, ds2) => ds2
    | (
        lazy ( Cons(Zero, ds1)),
        lazy ( Cons(d, ds2)),
      ) =>
      lazy( Cons(d, mrg(ds1, ds2)))
    | (
        lazy ( Cons(d, ds1)),
        lazy ( Cons(Zero, ds2)),
      ) =>
      lazy( Cons(d, mrg(ds1, ds2)))
    | (
        lazy ( Cons(One(t1), ds1)),
        lazy ( Cons(One(t2), ds2)),
      ) =>
      lazy(
         Cons(Zero, ins_tree(link(t1, t2), mrg(ds1, ds2)))
      )
    };

  let rec normalize = ds =>
    switch (ds) {
    | lazy Nil => ds
    | lazy ( Cons(_, ds')) =>
      ignore(normalize(ds'));
      ds;
    };

  let exec =
    fun
    | [] => []
    | [lazy ( Cons(Zero, job)), ...sched] => [
        job,
        ...sched,
      ]
    | [_, ...sched] => sched;

  let insert = (x, (ds, sched)) => {
    let ds' = ins_tree( Node(x, []), ds);
    (ds', exec(exec([ds', ...sched])));
  };

  let merge = ((ds1, _), (ds2, _)) => (normalize(mrg(ds1, ds2)), []);

  let rec remove_min_tree =
    fun
    | lazy Nil => raise(Empty)
    | lazy ( Cons(hd, tl)) =>
      switch (hd, tl) {
      | (One(t), lazy Nil) => (t, lazy(Nil))
      | (Zero, ds) =>
        let (t', ds') = remove_min_tree(ds);
        (t', lazy( Cons(Zero, ds')));
      | (One( Node(x, _) as t), ds) =>
        let ( Node(x', _) as t', ds') =
          remove_min_tree(ds);
        if (Elem.leq(x, x')) {
          (t, lazy( Cons(Zero, tl)));
        } else {
          (t', lazy( Cons(One(t), ds')));
        };
      };

  let find_min = ((ds, _)) => {
    let ( Node(x, _), _) = remove_min_tree(ds);
    x;
  };

  let delete_min = ((ds, _)) => {
    let ( Node(_, c), ds') = remove_min_tree(ds);
    let ds'' =
      mrg(list_to_stream(List.map(e => One(e), List.rev(c))), ds');
    (normalize(ds''), []);
  };
};

let rec stream_to_list =
  fun
  | lazy Nil => []
  | lazy ( Cons(x, xs)) => [x, ...stream_to_list(xs)];

module ScheduledBottomUpMergeSort =
       (Element: ORDERED)
       : (SORTABLE with module Elem = Element) => {
  module Elem = Element;

  type schedule = list(stream(Elem.t));
  type sortable = (int, list((stream(Elem.t), schedule)));

  /* fun lazy */
  let rec mrg = (xs, ys) =>
    switch (xs, ys) {
    | (lazy Nil, _) => ys
    | (_, lazy Nil) => xs
    | (
        lazy ( Cons(x, xs')),
        lazy ( Cons(y, ys')),
      ) =>
      if (Elem.leq(x, y)) {
        lazy( Cons(x, mrg(xs', ys)));
      } else {
        lazy( Cons(y, mrg(xs, ys')));
      }
    };

  let rec exec1 =
    fun
    | [] => []
    | [lazy Nil, ...sched] => exec1(sched)
    | [lazy ( Cons(_, xs)), ...sched] => [xs, ...sched];

  let exec2 = ((xs, sched)) => (xs, exec1(exec1(sched)));

  let empty = (0, []);

  let add = (x, (size, segs)) => {
    let rec add_seg = (xs, segs, size, rsched) =>
      if (size mod 2 == 0) {
        [(xs, List.rev(rsched)), ...segs];
      } else {
        switch (segs) {
        | [(xs', []), ...segs'] =>
          let xs'' = mrg(xs, xs');
          add_seg(xs'', segs', size / 2, [xs'', ...rsched]);
        | _ => impossible_pat("add")
        };
      };
    let segs' =
      add_seg(lazy( Cons(x, lazy(Nil))), segs, size, []);
    (size + 1, List.map(exec2, segs'));
  };

  let sort = ((_, segs)) => {
    let rec mrg_all =
      fun
      | (xs, []) => xs
      | (xs, [(xs', _), ...segs]) => mrg_all((mrg(xs, xs'), segs));
    stream_to_list(mrg_all((lazy(Nil), segs)));
  };
};
