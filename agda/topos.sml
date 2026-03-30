fun the (a : 'a option) : 'a
    = case a of
          NONE => raise Fail "THE failed"
        | SOME m => m;

(*
 * tree predicate calculator
 *)
type 'a obj = int -> 'a;
type psub = int;
type 'a pred = ('a -> psub) obj;

val top : int obj = fn i => i;
val bot : int obj = fn i => 0;
fun land ca cb = fn i => Int.min (ca i, cb i);
fun lor ca cb = fn i => Int.max (ca i, cb i);
fun later c = fn i => Int.min (i, c i + 1);
fun limp ca cb = fn i => if ca i <= cb i then i else cb i;

fun lift (s : psub option obj) : psub obj
    = fn i => case s i of
                NONE => 1
              | SOME k => k + 1;

fun unfold (seed : 'a) (f : 'a -> 'b * 'a) =
    let fun unfold' i seed
            = if i = 0 then []
              else case f seed of (n,newSeed) => n :: unfold' (i - 1) newSeed
    in fn i => unfold' i seed end;

fun take n (a : 'a obj) : 'a list
    = if n = 0 then [] else take (n - 1) a @ [a n];

fun next (a : 'a obj) : ('a option) obj
    = fn i => if i = 1 then NONE else SOME (a (i - 1));

fun lapp (f : ('a -> 'b) option obj) (a : 'a option obj) : 'b option obj
    = fn i => case f i of
                NONE => NONE
              | SOME realF => SOME (realF (the (a i)));

(* morphisms from int->a to int->b are int->(a->b) *)
fun toObj (f : 'a obj -> 'b obj) : ('a -> 'b) obj
    = fn i => fn a => f (fn i => a) i;

fun toFn (objF : ('a -> 'b) obj) : 'a obj -> 'b obj
    = fn objA => fn i => objF i (objA i);

(* calculate a guarded fixed-point *)
fun fix (later : ('a -> 'b) option obj -> ('a -> 'b) obj) : ('a -> 'b) obj
    = let fun fixpoint' i =
              if (i = 1)
              then later (fn _ => NONE) 1
              else later (fn i => SOME (fixpoint' (i - 1))) i
      in fixpoint' end;

(*
 * streams
 *)
type pstr = int list;

fun lhd (s : pstr obj) : int obj = fn i => hd (s i);

fun ltl (s : pstr obj) : pstr option obj
    = fn i => if i = 1
            then NONE
            else SOME (tl (s i));

fun lhdSat (s : pstr obj) (P : int -> bool) : psub obj
    = if P (hd (s 1)) then top else bot;

fun eq (s : ''a obj) t : psub obj
    = fn i =>
         let fun test j = if s j <> t j then j-1
                          else if j = i then i
                          else test (j+1)
         in test 1 end;

(* tree drawing *)
fun pad depth = if depth = 0 then "" else "  " ^ pad (depth-1);
fun printTree alphabet P maxDepth =
    let
        fun subtree pstr depth =
            if depth >= maxDepth then ()
            else (map (fn c =>
                          (print ((if c = hd alphabet
                                   then "-"
                                   else "\n"^pad depth^"\\-")
                                  ^ Int.toString c);
                           if P (depth + 1) (pstr @ [c]) = depth+1
                           then subtree (pstr @ [c]) (depth + 1)
                           else print "-x"))
                      alphabet ; ())
    in print "\\" ; subtree [] 0 ; print "\n"
    end;

(*
 * examples
 *)

val alternating = unfold 0 (fn i => (i mod 2, i+1));
fun const n = unfold 0 (fn s => (n, s));
fun ascending from by = unfold from (fn i => (i, i+by));

(* strict positive test *)
val onlyEvens = fix (fn recf => toObj (fn str => land (lhdSat str (fn n => n mod 2 = 0))
                                                  (lift (lapp recf (ltl str)))));
val s1 = ascending 0 2;
val d1 = take 5 s1;
val p1 = take 5 (toFn onlyEvens s1);

val onlyZerod = fix (fn recf => toObj (fn str => land (eq (lhd str) bot)
                                                  (lift (lapp recf (ltl str)))));
val s2 = unfold 0 (fn n => if n >= 3 then (1,0) else (0,n+1));
val d2 = take 5 s1;
val p2 = take 5 (toFn onlyZerod s2);

(* |> r(tl s) => hd s = 0
 *   starts with zero
 *)
val startsWithZero : (pstr -> psub) obj =
    fix (fn recf => toObj (fn str =>
        limp (lift (lapp recf (ltl str)))
             (eq (lhd str) bot)));

(* |> (r (tl s)) ⇒ (later hd s ≥ hd (tl s))
 * ??
 *)
val test : (pstr -> psub) obj =
    fix (fn recf => toObj (fn str =>
                            limp (lift (lapp recf (ltl str)))
                                 (fn i => if i = 1 then 1
                                        else if hd (str i) >= hd (tl (str i))
                                        then i else 0)));

val _ = printTree [0,1,2] test 4;
