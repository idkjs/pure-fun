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
/*                              Chapter 8                              */
/***********************************************************************/

exception Empty;
exception Not_implemented;
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

module HoodMelvilleQueue: QUEUE = {
  type rotation_state('a) =
    | Idle
    | Reversing(int, list('a), list('a), list('a), list('a))
    | Appending(int, list('a), list('a))
    | Done(list('a));

  type queue('a) = (int, list('a), rotation_state('a), int, list('a));

  let exec =
    fun
    |  Reversing(ok, [x, ...f], f', [y, ...r], r') =>
       Reversing(ok + 1, f, [x, ...f'], r, [y, ...r'])
    |  Reversing(ok, [], f', [y], r') =>
       Appending(ok, f', [y, ...r'])
    |  Appending(0, _, r') => Done(r')
    |  Appending(ok, [x, ...f'], r') =>
       Appending(ok - 1, f', [x, ...r'])
    | state => state;

  let invalidate =
    fun
    |  Reversing(ok, f, f', r, r') =>
       Reversing(ok - 1, f, f', r, r')
    |  Appending(0, _, [_, ...r']) => Done(r')
    |  Appending(ok, f', r') =>
       Appending(ok - 1, f', r')
    | state => state;

  let exec2 = ((lenf, f, state, lenr, r)) =>
    switch (exec(exec(state))) {
    | Done(newf) => (lenf, newf, Idle, lenr, r)
    | newstate => (lenf, f, newstate, lenr, r)
    };

  let check = ((lenf, f, _, lenr, r) as q) =>
    if (lenr <= lenf) {
      exec2(q);
    } else {
      let newstate =  Reversing(0, f, [], r, []);
      exec2((lenf + lenr, f, newstate, 0, []));
    };

  let empty = (0, [], Idle, 0, []);
  let is_empty = ((lenf, _, _, _, _)) => lenf == 0;

  let snoc = ((lenf, f, state, lenr, r), x) =>
    check((lenf, f, state, lenr + 1, [x, ...r]));

  let head =
    fun
    | (_, [], _, _, _) => raise(Empty)
    | (_, [x, ..._], _, _, _) => x;

  let tail =
    fun
    | (_, [], _, _, _) => raise(Empty)
    | (lenf, [_, ...f], state, lenr, r) =>
      check((lenf - 1, f, invalidate(state), lenr, r));
};

module BankersDeque = (C: {let c: int;}) : DEQUE => {
  /* c > 1 */

  let c = C.c;

  type queue('a) = (int, stream('a), int, stream('a));

  let empty = (0, lazy(Nil), 0, lazy(Nil));
  let is_empty = ((lenf, _, lenr, _)) => lenf + lenr == 0;

  let check = ((lenf, f, lenr, r) as q) =>
    if (lenf > c * lenr + 1) {
      let i = (lenf + lenr) / 2;
      (i, take(i, f), lenf + lenr - i, r ++ reverse(drop(i, f)));
    } else if (lenr > c * lenf + 1) {
      let j = (lenf + lenr) / 2;
      (lenf + lenr - j, f ++ reverse(drop(j, r)), j, take(j, r));
    } else {
      q;
    };

  let cons = (x, (lenf, f, lenr, r)) =>
    check((lenf + 1, lazy( Cons(x, f)), lenr, r));

  let head =
    fun
    | (_, lazy Nil, _, lazy Nil) => raise(Empty)
    | (_, lazy Nil, _, lazy ( Cons(x, _))) => x
    | (_, lazy ( Cons(x, _)), _, _) => x;

  let tail =
    fun
    | (_, lazy Nil, _, lazy Nil) => raise(Empty)
    | (_, lazy Nil, _, lazy ( Cons(_, _))) => empty
    | (lenf, lazy ( Cons(_, f')), lenr, r) =>
      check((lenf - 1, f', lenr, r));

  let snoc = ((lenf, f, lenr, r), x) =>
    check((lenf, f, lenr + 1, lazy( Cons(x, r))));

  let last =
    fun
    | (_, lazy Nil, _, lazy Nil) => raise(Empty)
    | (_, lazy ( Cons(x, _)), _, lazy Nil) => x
    | (_, _, _, lazy ( Cons(x, _))) => x;

  let init =
    fun
    | (_, lazy Nil, _, lazy Nil) => raise(Empty)
    | (_, lazy ( Cons(_, _)), _, lazy Nil) => empty
    | (lenf, f, lenr, lazy ( Cons(_, r'))) =>
      check((lenf, f, lenr - 1, r'));
};

module RealTimeDeque = (C: {let c: int;}) : DEQUE => {
  /* c = 2 or c = 3 */

  let c = C.c;

  type queue('a) = (
    int,
    stream('a),
    stream('a),
    int,
    stream('a),
    stream('a),
  );

  let empty = (0, lazy(Nil), lazy(Nil), 0, lazy(Nil), lazy(Nil));
  let is_empty = ((lenf, _, _, lenr, _, _)) => lenf + lenr == 0;

  let exec1 =
    fun
    | lazy ( Cons(_, s)) => s
    | s => s;
  let exec2 = s => exec1(exec1(s));

  let rec rotate_rev = (s, r, a) =>
    switch (s, r, a) {
    | (lazy Nil, _, _) => reverse(r) ++ a
    | (lazy ( Cons(x, f)), _, _) =>
      lazy(

        Cons(x, rotate_rev(f, drop(c, r), reverse(take(c, r)) ++ a))
      )
    };

  let rec rotate_drop = (f, j, r) =>
    if (j < c) {
      rotate_rev(f, drop(j, r), lazy(Nil));
    } else {
      switch (f) {
      | lazy ( Cons(x, f')) =>
        lazy( Cons(x, rotate_drop(f', j - c, drop(c, r))))
      | _ => impossible_pat("rotate_drop")
      };
    };

  let check = ((lenf, f, _, lenr, r, _) as q) =>
    if (lenf > c * lenr + 1) {
      let i = (lenf + lenr) / 2;
      let f' = take(i, f)
      and r' = rotate_drop(r, i, f);
      (i, f', f', lenf + lenr - i, r', r');
    } else if (lenr > c * lenf + 1) {
      let j = (lenf + lenr) / 2;
      let r' = take(j, r)
      and f' = rotate_drop(f, j, r);
      (lenf + lenr - j, f', f', j, r', r');
    } else {
      q;
    };

  let cons = (x, (lenf, f, sf, lenr, r, sr)) =>
    check((
      lenf + 1,
      lazy( Cons(x, f)),
      exec1(sf),
      lenr,
      r,
      exec1(sr),
    ));

  let head =
    fun
    | (_, lazy Nil, _, _, lazy Nil, _) => raise(Empty)
    | (_, lazy Nil, _, _, lazy ( Cons(x, _)), _) => x
    | (_, lazy ( Cons(x, _)), _, _, _, _) => x;

  let tail =
    fun
    | (_, lazy Nil, _, _, lazy Nil, _) => raise(Empty)
    | (_, lazy Nil, _, _, lazy (Cons(_)), _) => empty
    | (lenf, lazy ( Cons(_, f')), sf, lenr, r, sr) =>
      check((lenf - 1, f', exec2(sf), lenr, r, exec2(sr)));

  let snoc = ((lenf, f, sf, lenr, r, sr), x) =>
    check((
      lenf,
      f,
      exec1(sf),
      lenr + 1,
      lazy( Cons(x, r)),
      exec1(sr),
    ));

  let last =
    fun
    | (_, lazy Nil, _, _, lazy Nil, _) => raise(Empty)
    | (_, lazy ( Cons(x, _)), _, _, lazy Nil, _) => x
    | (_, _, _, _, lazy ( Cons(x, _)), _) => x;

  let init =
    fun
    | (_, lazy Nil, _, _, lazy Nil, _) => raise(Empty)
    | (_, lazy (Cons(_)), _, _, lazy Nil, _) => empty
    | (lenf, f, sf, lenr, lazy ( Cons(_, r')), sr) =>
      check((lenf, f, exec2(sf), lenr - 1, r', exec2(sr)));
};
