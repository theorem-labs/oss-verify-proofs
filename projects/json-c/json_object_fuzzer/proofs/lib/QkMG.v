(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition ST_eatws := 0.  Definition ST_start := 1.  Definition ST_finish := 2.  Definition ST_null := 3.
Definition ST_comment_start := 4.  Definition ST_comment := 5.  Definition ST_comment_eol := 6.  Definition ST_comment_end := 7.
Definition ST_string := 8.  Definition ST_string_escape := 9.  Definition ST_escape_unicode := 10.
Definition ST_esc_need_escape := 11.  Definition ST_esc_need_u := 12.  Definition ST_boolean := 13.  Definition ST_number := 14.
Definition ST_array := 15.  Definition ST_array_add := 16.  Definition ST_array_sep := 17.
Definition ST_ofs := 18.  Definition ST_ofield := 19.  Definition ST_ofend := 20.  Definition ST_ovalue := 21.
Definition ST_ovadd := 22.  Definition ST_osep := 23.  Definition ST_array_after_sep := 24.  Definition ST_ofs_after_sep := 25.
Definition ST_inf := 26.

Inductive ccls := CNone | CAny | CArr | CObj.

Definition cls_ok (c : ccls) (cs : option jshape) : Prop :=
match c, cs with
| CNone, None => True
| CAny, _ => True
| CArr, Some (Sarr _) => True
| CObj, Some (Sobj _) => True
| _, _ => False
end.

Definition zin (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.

Definition ws_states : list Z := [ST_eatws; ST_comment_start; ST_comment; ST_comment_eol; ST_comment_end].

Definition val_states : list Z := [ST_start; ST_null; ST_boolean; ST_number; ST_inf; ST_string].
Definition esc_states : list Z := [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u].

Definition lvl_mode (st ss : Z) : option (ccls * bool) :=
if zin ss [ST_start] && zin st (ws_states ++ val_states) then Some (CNone, false)
else if zin ss [ST_string] && zin st (ST_string :: esc_states) then Some (CNone, false)
else if zin ss [ST_finish] && zin st (ST_finish :: ws_states) then Some (CAny, false)
else if zin ss [ST_array; ST_array_sep; ST_array_after_sep] && (zin st ws_states || Z.eqb st ss) then Some (CArr, false)
else if zin st [ST_array_add] then Some (CArr, false)
else if zin ss [ST_ofs; ST_ofs_after_sep; ST_osep] && (zin st ws_states || Z.eqb st ss) then Some (CObj, false)
else if zin ss [ST_ofs; ST_ofs_after_sep; ST_ofield] && zin st (ST_ofield :: esc_states) then Some (CObj, false)
else if zin ss [ST_ofend; ST_ovalue] && (zin st ws_states || Z.eqb st ss) then Some (CObj, true)
else if zin st [ST_ovadd] then Some (CObj, true)
else None.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Definition name_ok (m : word -> option byte) (hn : bool) (l : tlevel) : Prop :=
match hn with
| false => tl_name l = 0 /\ tl_nbs l = []
| true => tl_name l <> 0 /\ exists nn ks, tl_nbs l = [(tl_name l, nn)] /\ 0 <= nn <= 2^31 /\ cstr segs m (tl_name l) nn ks
end.

Definition lvl_cur (m : word -> option byte) (depth : nat) (i : nat) (l : tlevel) : Prop :=
0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26 /\
jopt segs fn (tl_cs l) m (tl_cbs l) (tl_cur l) /\
if (i <? depth)%nat then
(tl_st l = ST_array_add /\ cls_ok CArr (tl_cs l) /\ name_ok m false l) \/
(tl_st l = ST_ovadd /\ cls_ok CObj (tl_cs l) /\ name_ok m true l)
else if (i =? depth)%nat then
exists c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) /\ cls_ok c (tl_cs l) /\ name_ok m hn l
else lvl_clean l.

#[using="Type"] Lemma name_ok_agree : forall BS m m' hn l,
name_ok m hn l -> agree_on segs BS m m' -> incl (tl_nbs l) BS -> name_ok m' hn l.
Proof.
intros BS m m' [|] l N AG Hi; cbn in *; [| exact N].
destruct N as (Hn & nn & ks & E & Hnn & C). split; [exact Hn|]. exists nn, ks. split; [exact E|]. split; [exact Hnn|].
eapply cstr_agree; [exact C | exact AG | apply Hi; rewrite E; left; reflexivity | lia].
Qed.

#[using="Type"] Lemma lvl_cur_agree : forall BS m m' depth i l,
lvl_cur m depth i l -> agree_on segs BS m m' -> incl (lvl_blocks l) BS -> lvl_cur m' depth i l.
Proof.
intros BS m m' depth i l (R1 & R2 & J & M) AG Hi.
assert (Hc : incl (tl_cbs l) BS) by (intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; left; exact Hb).
assert (Hn : incl (tl_nbs l) BS) by (intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; right; exact Hb).
split; [exact R1|]. split; [exact R2|]. split; [eapply jopt_agree; eauto|].
destruct (i <? depth)%nat.
- destruct M as [(A1 & A2 & A3) | (A1 & A2 & A3)]; [left | right]; (split; [exact A1|]); (split; [exact A2|]); eapply name_ok_agree; eauto.
- destruct (i =? depth)%nat; [| exact M].
destruct M as (c & hn & A1 & A2 & A3). exists c, hn. split; [exact A1|]. split; [exact A2|]. eapply name_ok_agree; eauto.
Qed.

Record tstate := TST {
t_depth : nat;
t_levels : list tlevel;
t_co : Z;
t_pb : Z; t_pbs : list blk;
t_x : tscal;
t_obj : Z; t_objs : option jshape; t_objbs : list blk
}.

Definition tstate_blocks (ts : tstate) : list blk := t_pbs ts ++ t_objbs ts ++ concat (map lvl_blocks (t_levels ts)).

Definition cur_st (ts : tstate) : Z :=
match nth_error (t_levels ts) (t_depth ts) with Some l => tl_st l | None => 0 end.

Definition TINV (m : word -> option byte) (tk q : Z) (len : Z) (ts : tstate) : Prop :=
length (t_levels ts) = 32%nat /\ (t_depth ts < 32)%nat /\
0 <= t_co ts <= len /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells segs m tk (tok_cells (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf segs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack segs m q (t_levels ts) /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur m (t_depth ts) i l) /\

(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt segs fn (t_objs ts) m (t_objbs ts) (t_obj ts)
else t_objbs ts = []).

Definition base_rank (s : Z) : nat :=
if zin s [ST_array_add; ST_ovadd] then 2
else if zin s [ST_finish] then 4
else if zin s [ST_inf; ST_null; ST_boolean] then 6
else if zin s [ST_number] then 7
else if zin s [ST_start] then 8
else if zin s [ST_array; ST_array_after_sep; ST_ovalue] then 11
else if zin s [ST_esc_need_escape; ST_esc_need_u] then 1
else 0.

Definition rank (st ss : Z) : nat :=
S (if st =? ST_eatws then S (base_rank ss) else base_rank st).
Definition RANK_LOOP : nat := 15.

End WithSegs.

End RC__1.
