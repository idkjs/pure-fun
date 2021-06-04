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
/*                              Chapter 5                              */
/***********************************************************************/

exception Empty;

module type QUEUE = {
  type queue('a);

  let empty: queue('a);
  let is_empty: queue('a) => bool;

  let snoc: (queue('a), 'a) => queue('a);
  let head: queue('a) => 'a; /* raises Empty if queue is empty */
  let tail: queue('a) => queue('a); /* raises Empty if queue is empty */
};

module BatchedQueue: QUEUE = {
  type queue('a) = (list('a), list('a));

  let empty = ([], []);
  let is_empty = ((f, _)) => f == [];

  let checkf = ((f, r) as q) =>
    if (f == []) {
      (List.rev(r), f);
    } else {
      q;
    };

  let snoc = ((f, r), x) => checkf((f, [x, ...r]));
  let head =
    fun
    | ([], _) => raise(Empty)
    | ([x, ..._], _) => x;
  let tail =
    fun
    | ([], _) => raise(Empty)
    | ([_, ...f], r) => checkf((f, r));
};

module type DEQUE = {
  type queue('a);

  let empty: queue('a);
  let is_empty: queue('a) => bool;

  /* insert, inspect, and remove the front element */
  let cons: ('a, queue('a)) => queue('a);
  let head: queue('a) => 'a; /* raises Empty if queue is empty */
  let tail: queue('a) => queue('a); /* raises Empty if queue is empty */

  /* insert, inspect, and remove the rear element */
  let snoc: (queue('a), 'a) => queue('a);
  let last: queue('a) => 'a; /* raises Empty if queue is empty */
  let init: queue('a) => queue('a); /* raises Empty if queue is empty */
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

module SplayHeap = (Element: ORDERED) : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type heap =
    | E
    | T(heap, Elem.t, heap);

  let empty = E;
  let is_empty = h => h == E;

  let rec partition = pivot =>
    fun
    | E => (E, E)
    |  T(a, x, b) as t =>
      if (Elem.leq(x, pivot)) {
        switch (b) {
        | E => (t, E)
        |  T(b1, y, b2) =>
          if (Elem.leq(y, pivot)) {
            let (small, big) = partition(pivot, b2);
            (
               T( T(a, x, b1), y, small),
              big,
            );
          } else {
            let (small, big) = partition(pivot, b1);
            (
               T(a, x, small),
               T(big, y, b2),
            );
          }
        };
      } else {
        switch (a) {
        | E => (E, t)
        |  T(a1, y, a2) =>
          if (Elem.leq(y, pivot)) {
            let (small, big) = partition(pivot, a2);
            (
               T(a1, y, small),
               T(big, x, b),
            );
          } else {
            let (small, big) = partition(pivot, a1);
            (
              small,
               T(big, y,  T(a2, x, b)),
            );
          }
        };
      };

  let insert = (x, t) => {
    let (a, b) = partition(x, t);
     T(a, x, b);
  };

  let rec merge = (s, t) =>
    switch (s, t) {
    | (E, _) => t
    | ( T(a, x, b), _) =>
      let (ta, tb) = partition(x, t);
       T(merge(ta, a), x, merge(tb, b));
    };

  let rec find_min =
    fun
    | E => raise(Empty)
    |  T(E, x, _) => x
    |  T(a, _, _) => find_min(a);

  let rec delete_min =
    fun
    | E => raise(Empty)
    |  T(E, _, b) => b
    |  T( T(E, _, b), y, c) =>
       T(b, y, c)
    |  T( T(a, x, b), y, c) =>
       T(delete_min(a), x,  T(b, y, c));
};

module PairingHeap = (Element: ORDERED) : (HEAP with module Elem = Element) => {
  module Elem = Element;

  type heap =
    | E
    | T(Elem.t, list(heap));

  let empty = E;
  let is_empty = h => h == E;

  let merge = (h1, h2) =>
    switch (h1, h2) {
    | (_, E) => h1
    | (E, _) => h2
    | ( T(x, hs1),  T(y, hs2)) =>
      if (Elem.leq(x, y)) {
         T(x, [h2, ...hs1]);
      } else {
         T(y, [h1, ...hs2]);
      }
    };

  let insert = (x, h) => merge( T(x, []), h);

  let rec merge_pairs =
    fun
    | [] => E
    | [h] => h
    | [h1, h2, ...hs] => merge(merge(h1, h2), merge_pairs(hs));

  let find_min =
    fun
    | E => raise(Empty)
    |  T(x, _) => x;

  let delete_min =
    fun
    | E => raise(Empty)
    |  T(_, hs) => merge_pairs(hs);
};
