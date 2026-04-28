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
fun lland [] = (fn i => i)
  | lland (a :: rest) = land a (lland rest);
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

(* morphisms, defined using the global elements functor
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

fun lnthSat (str : pstr obj) n (P : pstr -> bool) : psub obj =
    fn i => if i <= n then i
          else if P (str i)
          then i else n

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
fun const0Until n = unfold 0 (fn k => if k >= n then (1,k) else (0,k+1));

(* strict positive test *)
val onlyEvens = fix (fn recf =>
                        toStrObj (fn str =>
                                     land (lnthSat str 0 (fn l => (hd l) mod 2 = 0))
                                          (lift (lapp recf (ltl str)))));
val s1 = ascending 0 2;
val _ = take 5 s1;
val p1 = take 5 (toFn onlyEvens s1);
val _ = printTree [0,1,2] onlyEvens 3;

val onlyOnes = fix (fn recf =>
                       toStrObj (fn str => land (eq (lhd str) (later bot))
                                              (lift (lapp recf (ltl str)))));
val _ = printTree [0,1] onlyOnes 3;

(* >(r s) => s = 0*
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
val startsWith0 : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (eq (lhd str) bot)));
val _ = printTree [0,1] startsWith0 2;

(* >(r s') => >(hd s >= hd s')
 * also trivial, since the consequent predicate is 'classical'
 *)
val firstGeqSecond : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (lnthSat str 1 (fn l => hd l >= hd (tl l)))));
val _ = printTree [0,1,2] firstGeqSecond 3;

(* >(r s') => hd s = 0 \/ hd s' = 0
 * 'classical' props are closed under OR, as the bottom value is constant
 *)
val firstOrSecond0 : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (lor (eq (lhd str) bot)
                                         (eq (lapp (next (toStrObj lhd)) (ltl str))
                                             (next bot)))));
val _ = printTree [0,1] firstOrSecond0 5;

(* >(r s') => hd s = 0 /\ hd s'..' = 0
 * note: 01* allowed in addition to usual
 * new note: depth limited by P as imp only adds truth - no higher false values
 * ==> any propositional combination is depth limited and so non-recursive
 *)
fun firstNth0 n : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (land (eq (lhd str) bot)
                                          (lnthSat str n
                                                   (fn l => List.nth (l,n) = 0)))));
val _ = printTree [0,1] (firstNth0 1) 5;
val _ = printTree [0,1] (firstNth0 2) 5;
val _ = printTree [0,1] (firstNth0 3) 5;

(* >(r s') => hd s = 0 /\ hd s'..' = 1
 * note: both 01* and 02* allowed
 *)
fun first0Nth1 n : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (land (eq (lhd str) bot)
                                          (lnthSat str n
                                                   (fn l => List.nth (l,n) = 1)))));
val _ = printTree [0,1,2] (first0Nth1 1) 5;
val _ = printTree [0,1,2] (first0Nth1 2) 5;
val _ = printTree [0,1,2] (first0Nth1 3) 5;

(* >(r s') => s = 0*
 * an alternation sequence, can be unfolded as the limit of a big conjunction
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

(* >(r s') => s = 00..01*
 * odd and even periods differ in structure
 *)
fun constUntilTree n : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (eq str (const0Until n))));
val _ = printTree [0,1] (constUntilTree 1) 5; (* same as alternating *)
val _ = printTree [0,1] (constUntilTree 2) 5;
val _ = printTree [0,1] (constUntilTree 3) 5;
val _ = printTree [0,1] (constUntilTree 4) 7;

(* >(r s') => s = 00..01* \/ s = 1*
 * alternating structure in both branches
 *)
fun disjTree n : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (lor (eq str (const0Until n))
                                         (eq str (const 1)))));
val _ = printTree [0,1] (disjTree 1) 6;
val _ = printTree [0,1] (disjTree 2) 6;
val _ = printTree [0,1] (disjTree 3) 6;
val _ = printTree [0,1] (disjTree 4) 7;

(* >(r s') => s = 00..01* /\ >bot
 * note: >bot can be encoded using hd s' = 0 /\ hd s' = 1
 * note: obviously depth-limited, due to implication
 *)
fun conjTree n : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (ltl str)))
                                    (land (* (eq str (const0Until n)) *) top
                                          (later bot))));
val _ = printTree [0,1] (conjTree 1) 5;

(* >>(r s'') => s = 0*
 * period 4 variation, 0000.rec \/ s = 001.. \/ s = 0001...
 * note: further evidence for even period of implication
 *)
val mod2Prefix : (pstr -> psub) obj =
    fix (fn recf => toStrObj
                      (fn str =>
                          limp (lift2 (lapp (next (toObj pstrOptRestr (lapp recf)))
                                            (ltl2 str)))
                               (eq str (const 0))))
val _ = printTree [0,1] mod2Prefix 9;

(* note: *any* with head 1 is allowed *)
val zeroOrAny : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf (next (lsuc str)))) (* 0+1 *)
                                    (lor (eq str (const 0))
                                         (eq str (const 1))))); (* >= 1 true *)
val _ = printTree [0,1] zeroOrAny 3;

(* note: 000 allowed, iterates 100 -> 000 form alternating sequence *)
val flip : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (lift (lapp recf
                                                (next (fn i =>
                                                          let val l = str i in
                                                              (if hd l = 0
                                                               then 1
                                                               else 0) :: tl l
                                                          end))))
                                    (lor (eq str (const0Until 2))
                                         (eq str (const 1)))));
val _ = printTree [0,1] flip 3;

(* TODO multiple recursive conjuncts rs /\ rs => x
 * by making the antecedent smaller we get more structure
 *)
val conjuncts : (pstr -> psub) obj =
    fix (fn recf => toStrObj (fn str =>
                               limp (land (lift (lapp recf (next (lsuc str))))
                                          (lift (lapp recf (ltl str))))
                                    (lor (eq str (const 0))
                                         (eq str (const 1)))));
val _ = printTree [0,1,2] conjuncts 4;
