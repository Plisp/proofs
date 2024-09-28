open preamble HolKernel boolLib bossLib BasicProvers; (* recommended by Magnus *)
open stringLib; (* parsing, text examples etc. *)
open itreeTauTheory;

open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panSemTheory; (* eval_def, byte stuff *)
open panLangTheory; (* size_of_shape_def *)
open arithmeticTheory;
open listTheory;

local
  val f =
    List.mapPartial
       (fn s => case helperLib.remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
  end

fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> fromMLstring
  in
    EVAL “(parse_funs_to_ast ^code)”
end

val ast = parse_pancake ‘
fun net_enqueue_free(1 queue_handle, 2 buffer) {
    var test = < 1 , 2 >;
    return test.0;
}
’;
