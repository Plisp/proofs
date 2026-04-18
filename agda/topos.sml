(*
 * tree predicate grapher
 *)
type 'a obj = int -> 'a;
type psub = int;
type 'a pred = ('a -> psub) obj;

fun take n (a : 'a obj) : 'a list =
    let fun take' i acc = if i = 0 then acc else take' (i-1) (a i :: acc)
    in take' n [] end;

(*
 * subobject classifier
 *)
val (psubRestr : psub * int -> psub) = Int.min;

val top : int obj = fn i => i;
val bot : int obj = fn i => 0;
fun land ca cb = fn i => Int.min (ca i, cb i);
fun lor ca cb = fn i => Int.max (ca i, cb i);
fun later c = fn i => Int.min (i, c i + 1);
fun limp ca cb = fn i => if ca i <= cb i then i else cb i;

fun eq (s : ''a obj) t : psub obj =
    fn i =>
       let fun test j = if s j <> t j then j-1
                        else if j = i then i
                        else test (j+1)
       in test 1 end;

fun lift (s : psub option obj) : psub obj =
    fn i => case s i of
              NONE => 1
            | SOME k => k + 1;

(*
 * later functor
 *)
fun next (a : 'a obj) : ('a option) obj =
    fn i => if i = 1 then NONE else SOME (a (i - 1));

fun optRestr restr =
    fn (po,i) => case po of
                   NONE => NONE
                 | SOME p => if i = 1 then NONE else SOME (restr (p, i-1));

val psubOptRestr = optRestr psubRestr;

fun lapp (f : ('a -> 'b) option obj) (a : 'a option obj) : 'b option obj =
    fn i => if i = 1
          then case f i of
                   SOME _ => raise Fail "f wasn't none at stage 1"
                 | NONE => case a i of
                              NONE => NONE
                            | SOME _ => raise Fail "a wasn't none at stage 1"
          else case f i of
                   NONE => raise Fail ("lapp fun was NONE at " ^ Int.toString i)
                 | SOME realF =>
                   case a i of
                       NONE => raise Fail ("lapp arg was NONE at " ^ Int.toString i)
                     | SOME pa => SOME (realF pa);

(* morphisms
 * from int->a to int->b are int->(a->b)
 * we need a restriction map to correctly simulate earlier stages of an object
 * e.g. for equality
 *)
fun toObj (restr : ('a * int) -> 'a) (f : 'a obj -> 'b obj) : ('a -> 'b) obj =
    fn i => fn a => f (fn j => if j <= i then restr (a,j)
                         else raise Fail "non causal")
                  i;

fun toFn (objF : ('a -> 'b) obj) : 'a obj -> 'b obj =
    fn objA => fn i => objF i (objA i);

(* calculate a guarded fixed-point *)
fun fix (func : 'a option obj -> 'a obj) : 'a obj =
    let fun fixpoint' i =
            func (fn j => if j = 1 then NONE
                        else if j <= i then SOME (fixpoint' (j - 1))
                        else raise Fail "non causal")
                 i
    in fixpoint' end;

(*
 * streams
 *)
type pstr = int list;

fun unfold (seed : 'a) (f : 'a -> 'b * 'a) =
    let fun unfold' i seed
            = if i = 0 then []
              else case f seed of (n,newSeed) => n :: unfold' (i - 1) newSeed
    in fn i => unfold' i seed end;

fun lhd (s : pstr obj) : int obj = fn i => hd (s i);

fun ltl (s : pstr obj) : pstr option obj =
    fn i => if i = 1 then NONE else SOME (tl (s i));

fun lhdSat (s : pstr obj) (P : int -> bool) : psub obj =
    if P (hd (s 1)) then top else bot;

fun lsuc (s : pstr obj) : pstr obj = fn i => map (fn n => 1 + n) (s i)

fun toStrObj (obj : pstr obj -> 'a obj) : (pstr -> 'a) obj = toObj List.take obj;

fun ltl2 (s : pstr obj) : pstr option option obj =
    lapp (next (toStrObj ltl)) (ltl s);
val pstrOptRestr = optRestr (List.take : pstr * int -> pstr);

(* tree drawing *)
val horLine = "\226\149\180";
val teeRight = "\226\148\156";
val vertLine = "\226\148\130";
val downRight = "\226\149\176";
val upLeft = "\226\148\140";

(* allTrue and allFalse are inclusive *)
datatype node = Node of {last: int, children : node list,
                         allTrue : bool, allFalse : bool};

(* barely improves performance over stateless computation,
 * but it'll be needed later anyways *)
fun buildTree alphabet P maxDepth =
    let fun build pstr depth = (* depth > 0 *)
            let val truth = P depth pstr = depth
                val last = List.last pstr
            in
                if depth = maxDepth
                then Node {last = last, children = [],
                           allTrue = truth, allFalse = not truth}
                else if truth
                then let val children = map (fn c => build (pstr @ [c]) (depth+1))
                                            alphabet
                     in (* release some memory if children not needed *)
                         if List.all (fn (Node ch) => #allTrue ch) children
                         then Node {last = last, allTrue = true,
                                    children = [], allFalse = false}
                         else Node {last = last, allFalse = false,
                                    children = children, allTrue = false}
                     end
                else Node {last = last, children = [],
                           allTrue = false, allFalse = true}
            end
    in if maxDepth = 0 then []
       else map (fn c => build [c] 1) alphabet end;

fun printTree alphabet P maxDepth =
    let val firstSym = hd alphabet
        val lastSym = List.last alphabet
        fun drawSub (Node node) backward depth =
            let fun pad [] = ""
                  | pad (i :: is) =
                    pad is ^ (if i <> lastSym then vertLine ^ " " else "  ");
            in
                print (Int.toString (#last node))
              ; if #allTrue node then print "?"
                else if #allFalse node then print "F"
                else app (fn (Node ch) =>
                             (print (if #last ch = firstSym then horLine
                                     else "\n" ^ pad backward ^
                                          (if #last ch <> lastSym then teeRight
                                           else downRight) ^
                                          horLine)
                             ; drawSub (Node ch) (#last ch :: backward) (depth+1)))
                         (#children node)
            end
    in app (fn node => (drawSub node [] 0 ; print "\n"))
           (buildTree alphabet P maxDepth)
     ; print "\n"
    end;

(*
 * examples
 *)

val alternating = unfold 0 (fn i => (i mod 2, i+1));
fun const n = unfold 0 (fn s => (n, s));
fun ascending from by = unfold from (fn i => (i, i+by));
fun constUntil n = unfold 0 (fn k => if k >= n then (0,k) else (1,k+1));

(* strict positive test *)
val onlyEvens = fix (fn recf =>
                        toStrObj (fn str => land (lhdSat str (fn n => n mod 2 = 0))
                                               (lift (lapp recf (ltl str)))));
val s1 = ascending 0 2;
val _ = take 5 s1;
val p1 = take 5 (toFn onlyEvens s1);
val _ = printTree [0,1,2] onlyEvens 3;

val onlyOnes = fix (fn recf =>
                       toStrObj (fn str => land (eq (lhd str) (later bot))
                                              (lift (lapp recf (ltl str)))));
val _ = printTree [0,1] onlyOnes 3;

(* >(r s) => s = [0...]
 * trivial by fixpoint theorem
 *)
val eqZeroes : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (next str)))
                                    (eq str (const 0))));
val _ = printTree [0,1] eqZeroes 3;

(* >(r s') => hd s = 0
 * trivial since 'classical'
 *)
val startsWithZero : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (eq (lhd str) bot)));
val _ = printTree [0,1] startsWithZero 2;

(* >(r s') => >(hd s >= hd s')
 * also trivial, since the consequent predicate is 'classical'
 *)
val firstGeqSecond : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (fn i => if i = 1 then 1
                                           else if hd (str i) >= hd (tl (str i))
                                           then i else 0)));
val _ = printTree [0,1,2] firstGeqSecond 3;

(* >(r s') => hd s = 0 \/ hd s' = 0
 * disjunctions are 'classical', as the bottom value is constant
 *)
val firstOrSecondZero : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (lor (eq (lhd str) bot)
                                         (eq (lapp (next (toStrObj lhd)) (ltl str))
                                             (next bot)))));
val _ = printTree [0,1] firstOrSecondZero 5;

(* >(r s') => hd s = 0 /\ hd s' = 0
 * note: only considers the head
 *)
val firstSecondZero : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (land (eq (lhd str) bot)
                                          (eq (lapp (next (toStrObj lhd)) (ltl str))
                                              (next bot)))));
val _ = printTree [0,1] firstSecondZero 5;

(* >(r s') => hd s = 0 /\ hd s' = 1
 * note: 02 allowed
 *)
val firstZeroSecondOne : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (land (eq (lhd str) bot)
                                          (eq (lapp (next (toStrObj lhd)) (ltl str))
                                              (next (later bot))))));
val _ = printTree [0,1,2] firstZeroSecondOne 5;

(* >(r s') => s = 0*
 * an alternation sequence
 *)
val oddZeroPrefix : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (eq str (const 0))));
val _ = printTree [0,1] oddZeroPrefix 7;

(* s = 00.rec \/ s = 01...
 * strict positive version of above
 *)
fun lift2 (oo : psub option option obj) : psub obj =
    lift (lapp (next (toObj psubOptRestr lift)) oo)

val oddZeroPrefix' : (pstr -> psub) obj =
    fix (fn recf =>
            toStrObj
                (fn str =>
                    lor (land (land (eq (lhd str) bot)
                                    (eq (lapp (next (toStrObj lhd)) (ltl str))
                                        (next bot)))
                              (lift2 (lapp (next (toObj pstrOptRestr (lapp recf)))
                                           (ltl2 str))))
                        (land (eq (lhd str) bot)
                              (eq (lapp (next (toStrObj lhd)) (ltl str))
                                  (next (later bot))))));
val _ = printTree [0,1] oddZeroPrefix' 7;

(* >>(r s'') => s = 0*
 * period 2 variation
 *)
val mod2Prefix : (pstr -> psub) obj =
    fix (fn recf => toStrObj
                      (fn str =>
                          limp (lift2 (lapp (next (toObj pstrOptRestr (lapp recf)))
                                            (ltl2 str)))
                               (eq str (const 0))))
val _ = printTree [0,1] mod2Prefix 9;

(* >(r s') => 111...10
 * TODO generalize above more
 *)
fun constUntilTree n : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (eq str (constUntil n))));
val _ = printTree [0,1] (constUntilTree 1) 5;
val _ = printTree [0,1] (constUntilTree 2) 5;
val _ = printTree [0,1] (constUntilTree 3) 5;
val _ = printTree [0,1] (constUntilTree 4) 7;

(* note: *any* with head 1 is allowed *)
val zeroOrAny : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (next (lsuc str)))) (* 0+1 *)
                                    (lor (eq str (const 0))
                                         (eq str (const 1))))); (* >= 1 true *)
val _ = printTree [0,1,2] zeroOrAny 3;

(* multiple recursive conjuncts rs /\ rs => x
 * by making the antecedent smaller with and, we get more structure
 *)
val conjuncts : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (land (lift (lapp recf (next (lsuc str))))
                                          (lift (lapp recf (ltl str))))
                                    (lor (eq str (const 0))
                                         (eq str (const 1)))));
val _ = printTree [0,1,2] conjuncts 4;
