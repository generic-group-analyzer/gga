(*i*)
open NonParamInput
open Util
(*i*)

type recipe =
  | Param of int
  | Iso   of iso * recipe
  | Emap  of emap * recipe list

(* \ic{%
   Given a group setting and a list of group elements ([inputs]),
   return the elements of the completion residing in the target group
   and the corresponding recipes. The list of recipes only depends on
   the shape of the [inputs] list.} *)
val completion_for_group :
  closed_group_setting ->
  group_id ->
  group_elem list list ->
  (rpoly list list * recipe list)

val pp_recipe : F.formatter -> recipe -> unit