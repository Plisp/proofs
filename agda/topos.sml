fun inter s f [] = ""
  | inter s f [v] = f v
  | inter s f (v::vs) = f v ^ s ^ inter s f vs
fun csv f = inter "," f;

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

(* pstr -> psub *)
val zeroed = fix (fn recf => toObj (fn str => land (lhdSat str (fn n => n = 0))
                                               (lift (lapp recf (ltl str)))))

val zerod = fix (fn recf => toObj (fn str => land (eq (lhd str) bot)
                                              (lift (lapp recf (ltl str)))))
