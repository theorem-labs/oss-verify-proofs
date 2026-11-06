(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 QlKV QsKa QJZd Q3Gm QGm2 QhtD QbKA QjDJ Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq8.
Import Q3Gm.Mq0.
Import QGm2.Mq0 QhtD.Mq0 QbKA.Mq2 QjDJ.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac has_var e := match e with context [?v] => is_var v end.
Ltac closed_term e := tryif has_var e then fail 0 "open term" e else idtac.

Ltac fold_closed_bv2 :=
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac | Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac | Z.opp _ => idtac
end;
closed_term e;
let v0 := eval vm_compute in e in
lazymatch v0 with
| Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
end;
let v := eval vm_compute in (Z.modulo v0 (2^64)) in
first [ change (Z_to_bv 64 e) with (Z_to_bv 64 v)
| replace (Z_to_bv 64 e : bv 64) with (Z_to_bv 64 v : bv 64) by (apply bv_eq; vm_compute; reflexivity) ]
end
end.

Ltac amo_fix :=
repeat match goal with
| |- context [amo_aligned ?wd (Z_to_bv 64 ?a)] =>
closed_term a;
let v := eval vm_compute in (amo_aligned wd (Z_to_bv 64 a)) in change (amo_aligned wd (Z_to_bv 64 a)) with v; cbn [negb]; exec_cbv
| |- context [if Z.eqb ?x ?y then EStore ?n ?a ?v ?k else ?e] =>
closed_term x; closed_term y;
let b := eval vm_compute in (Z.eqb x y) in
change (if Z.eqb x y then EStore n a v k else e) with (if b then EStore n a v k else e); exec_cbv
end.
Ltac solve_load ::= amo_fix; first [ solve_load_base | solve_load_image | idtac ]. Ltac mkr__solve_load_1 := amo_fix; first [ solve_load_base | solve_load_image | idtac ].

Definition META_SH : Z := 0x8001552c.
Definition MUTEX_A : Z := 0xed3b0.

Definition got9 (g0 g1 g5 g6 g7 : word) : list cell :=
[C8 g0; C8 g1; C8 (Z_to_bv 64 0x181628); C8 (Z_to_bv 64 0xed2f8); C8 (Z_to_bv 64 0xefaf8); C8 g5; C8 g6; C8 g7; C8 (Z_to_bv 64 0xe7db0)].

Definition W_UNREG (usp : Z) : list (Z * Z) := [(usp - 240, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0a00)]%Z.

Definition g_ok2b (r : list Z) : bool :=
(0x10000 <=? g_beg r) && (g_beg r mod 8 =? 0) && (g_szrz r mod 8 =? 0) && (8 <=? g_szrz r) && (g_szrz r <=? 4096)
&& (g_beg r + g_szrz r <=? 0x645000) && ((g_odr r =? 0) || (g_odr r =? 2^64 - 1) || (g_odr r =? ODR_A)).
Lemma g_ok2b_ok : forall r, g_ok2b r = true -> g_ok2 r.
Proof.
intros r H. unfold g_ok2b in H. unfold g_ok2.
repeat (apply andb_prop in H as [H ?X]).
repeat match goal with G : (_ && _) = true |- _ => apply andb_prop in G as [G ?Y] end.
rewrite ?Z.leb_le, ?Z.eqb_eq in *.
repeat split; try assumption.
repeat match goal with G : (_ || _) = true |- _ => apply orb_prop in G as [G | G] end; rewrite ?Z.eqb_eq in *; tauto.
Qed.
Fixpoint chainedb (l : list (list Z)) : bool :=
match l with
| [] => true
| r :: l' => forallb (fun r' => g_beg r + g_szrz r <=? g_beg r') l' && chainedb l'
end.
Lemma chainedb_ok : forall l, chainedb l = true -> chained l.
Proof.
induction l as [|r l IH]; intros H; cbn [chainedb chained] in *; [exact I|].
apply andb_prop in H as [H1 H2]. split; [|apply IH; exact H2].
apply Forall_forall. intros r' Hin. apply Z.leb_le. exact (proj1 (forallb_forall _ _) H1 r' Hin).
Qed.
Lemma tok_ok2 : Forall g_ok2 tokA_globals8.
Proof. apply Forall_forall. intros r Hin. apply g_ok2b_ok. revert r Hin. apply forallb_forall. vm_compute. reflexivity. Qed.
Lemma tok_chained : chained tokA_globals8.
Proof. apply chainedb_ok. vm_compute. reflexivity. Qed.
Lemma tok_len : Z.of_nat (length tokA_globals8) = 107.
Proof. reflexivity. Qed.

Lemma outside_map_sh : forall l x, Forall g_ok2 l -> ~ (0x7fffa000 <= x < 0x800c0a00) -> outside (map g_sh l) x.
Proof.
induction l as [|r l IH]; intros x OK Hx; cbn [map outside]; [exact I|].
apply Forall_cons_iff in OK as [OKr OK]. unfold g_ok2 in OKr. unfold g_sh. split; [lia | apply IH; assumption].
Qed.
Lemma disjoint_from_map_sh2 : forall l A n, (A + n <= 0x7fffa000 \/ 0x800c0a00 <= A) -> Forall g_ok2 l -> disjoint_from (map g_sh l) A n.
Proof.
induction l as [|r l IH]; intros A n HA OK; cbn [map disjoint_from]; [exact I|].
apply Forall_cons_iff in OK as [OKr OK]. unfold g_ok2 in OKr. unfold g_sh. cbn [fst snd]. split; [lia | apply IH; assumption].
Qed.
Definition disjoint_fromb (W : list (Z * Z)) (a n : Z) : bool :=
forallb (fun lh : Z * Z => (a + n <=? fst lh) || (snd lh <=? a)) W.
Lemma disjoint_fromb_ok : forall W a n, disjoint_fromb W a n = true -> disjoint_from W a n.
Proof.
induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
cbn [disjoint_fromb forallb fst snd] in H. apply andb_prop in H as [H1 H2].
split; [| apply IH; exact H2]. apply orb_prop in H1 as [H1|H1]; [left|right]; apply Z.leb_le; exact H1.
Qed.
Lemma shadows_rw_transport_gen : forall l W m m',
shadows_rw m l -> munch W m m' -> wmono asegs m m' ->
(forall A n, 0x7fffa000 <= A -> A + n <= 0x800c0a00 -> disjoint_from W A n) -> Forall g_ok2 l ->
shadows_rw m' l.
Proof.
intros l W m m' H MU WM HW OK. unfold shadows_rw in *.
apply Forall_forall. intros r' Hin.
pose proof (proj1 (Forall_forall _ _) H r' Hin) as (junk & RW).
pose proof (proj1 (Forall_forall _ _) OK r' Hin) as OK'. unfold g_ok2 in OK'.
exists junk. eapply rw_cells_transport; [exact RW | exact MU | exact WM |].
unfold g_sh. cbn [fst cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply HW; lia.
Qed.

Section P1.
Context {RC__ : Q6q3.RunConsts}.
Definition poison_meta_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (META_SH, META_SH + 856)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma poison_meta_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
a0 = Z_to_bv 64 0xea960 -> a1 = Z_to_bv 64 6848 -> a2 = Z_to_bv 64 0 ->
ro_cells asegs m 0xe5d98 (got9 g0 g1 g5 g6 g7) ->
ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
rw_cells asegs m META_SH [CB 856 junkM] ->
evt asegs (poison_meta_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x64824) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO A0 A1 A2 GOT SB THR RM MSH. subst a0 a1 a2. unfold META_SH in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x8001552c, 0x8001552c + 856)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
step. step. step. step. step. step. step. step.
step. if_truex.
step. step. if_falsex.
step. step. step.
step. step. step. step.
fold_closed_bv.
step. if_truex.
step. step. if_falsex.
step. step. fold_closed_bv. step. if_truex.
step. step. step. step. if_falsex.
step. step. step. step. step. fold_closed_bv.
step. if_falsex.
step. step. step.
step. if_truex.
step. step.
step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
step.
try replace (ret_pc (Z_to_bv 64 898896)) with (Z_to_bv 64 898896 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
eapply evt_cut; [eapply Q3Gm.Mq0.memset_spec; [rewrite !unsigned_lit by lia; exact MSH | exact MI] | ].
intros ms' PO. unfold memset_post in PO.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & E & MUc & WMc & MI1 & SH1). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in SH1 by lia. change (0 mod 256) with 0 in SH1. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in SH1.
transport_after_call rsegs m0 m1 MUc WMc.
change (Z.to_nat 856) with 856%nat in SH1.
apply evt_done. unfold poison_meta_post.
exists u0, u1, u2, (Z_to_bv 64 2147570988), ua1, ua2, ua3, ua4, ua5, ua6, ua7, u3, u4, u5, u6, m1.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST | exact SH1].
Qed.
End P1.

Section P2.
Context {RC__ : Q6q3.RunConsts}.
Definition unreg_globals_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_UNREG (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' MUTEX_A [C8 (Z_to_bv 64 0)]
/\ (exists ob', rw_cells asegs m' ODR_A [C1 ob']) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma unreg_globals_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 240 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 AGLOB_START -> a1 = Z_to_bv 64 107 ->
ro_cells asegs m 0xe5d98 (got9 g0 g1 g5 g6 g7) ->
ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xed310 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xefaf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xef35c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x1816a0 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xe7db0 [C8 (Z_to_bv 64 0xdb750)] ->
rw_cells asegs m MUTEX_A [C8 (Z_to_bv 64 0)] ->
recs_ro m AGLOB_START tokA_globals8 -> shadows_rw m tokA_globals8 -> rw_cells asegs m ODR_A [C1 ob] ->
rw_cells asegs m META_SH [CB 856 junkM] ->
evt asegs (unreg_globals_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4d2c0) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL A0 A1 GOT INITED RG SB CP THR RM MUT RR SW ODRB MSH. subst a0 a1.
unfold AGLOB_START, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (0xed3b0, 0xed3b0 + 8)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 176%nat ST.
do 14 step.
step. step. step. step.
stepz.
step.
match goal with |- context [sx32 (Z_to_bv 64 1)] => replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
if_falsex.
do 9 (stepz; fold_closed_bv2).
step.
do 4 (stepz; fold_closed_bv2).
do 4 (stepz; fold_closed_bv2).
step. fold_closed_bv2. step. if_falsex.
step. fold_closed_bv2. step. fold_closed_bv2.
step.
step. if_falsex.
stepz.
step. if_falsex.
step. if_truex.
stepz. stepz.
step. if_falsex.
do 7 step.
step.
step. stepz. step. stepz. step. stepz.
step. step. step. stepz.
step. step. step. fold_closed_bv2.
step. step. step.

eapply (unreg_loop2 tokA_globals8) with (ob := ob);
[ exact tok_len | lia | lia | lia | reflexivity | exact MI | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; cbn [disjoint_from length]; rewrite tok_len in Hq2 || idtac; lia]
| exact tok_ok2 | exact tok_chained
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | ].
intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m2 ob' MU2 WM2 MI2 ODRB2.
assert (DJL : forall A n, (A + n <= 0x6221a0 \/ (0x6221a1 <= A /\ A + n <= 0x7fffa000) \/ 0x800c0a00 <= A) -> disjoint_from (W_ODR :: map g_sh tokA_globals8) A n).
{ intros A n HA. cbn [disjoint_from W_ODR]. unfold ODR_A. split; [lia|]. apply disjoint_from_map_sh2; [lia | exact tok_ok2]. }
eapply (rw_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in FR; [| exact MU2 | exact WM2 | apply DJL; cbn; lia].
eapply (rw_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in MUT; [| exact MU2 | exact WM2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in GOT; [| exact MU2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in SB; [| exact MU2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in THR; [| exact MU2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in RM; [| exact MU2 | apply DJL; cbn; lia].
eapply (rw_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in MSH; [| exact MU2 | exact WM2 | apply disjoint_fromb_ok; vm_compute; reflexivity].
eapply (stk_transport_disjoint rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in ST; [| exact MU2 | exact WM2 | apply DJL; lia].
assert (MUA : munch (W_UNREG (bv_unsigned sp)) m m2).
{ eapply munch_join; [exact MU | exact MU2 | |].
- intros x Hx. unfold W_UNREG, W_ODR, MUTEX_A, ODR_A in Hx. cbn [outside] in Hx |- *. lia.
- intros x Hx. unfold W_UNREG, W_ODR, MUTEX_A, ODR_A in Hx. cbn [outside] in Hx. cbn [outside W_ODR]. unfold ODR_A.
split; [lia|]. apply outside_map_sh; [exact tok_ok2 | lia]. }
pose proof (wmono_trans _ _ _ _ WM WM2) as WMA.
clear MU MU2 WM WM2 DJL MI INITED RG CP ODRB RR SW. rename MI2 into MI. rename MUA into MU. rename WMA into WM.
unfold ODR_A in ODRB2.

step. step. fold_closed_bv2. step. step. fold_closed_bv2. step. step.
step.
eapply evt_cut; [eapply (poison_meta_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lo g0 g1 g5 g6 g7 junkM);
[exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | reflexivity | exact GOT | exact SB | exact THR | exact RM | exact MSH] | ].
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold META_SH in MUc, MSH3. unfold W_UNREG, MUTEX_A, W_ODR, ODR_A in MU.
clear MSH ST.
transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc.
replace (ret_pc (Z_to_bv 64 317084)) with (Z_to_bv 64 317084 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
clear MI; rename MI3 into MI.
step. step.
do 7 (step; fold_closed_bv2).
step.
do 4 (step; fold_closed_bv2).
step.
step. fold_closed_bv2. step. fold_closed_bv2.
step. if_falsex.
step. fold_closed_bv2. step. if_truex.
do 7 (step; fold_closed_bv2).
step. if_truex.
step.
step. if_falsex.
stepz.
step. if_falsex.
step. if_truex.
step. if_falsex.
do 13 step.
step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_done. unfold unreg_globals_post.
do 16 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
unfold MUTEX_A, META_SH. split; [exact MUT|]. split; [| exact MSH3].
exists ob'. exact ODRB2.
Qed.
End P2.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3Gm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3Gm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDJ.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac has_var e := match e with context [?v] => is_var v end.
Ltac closed_term e := tryif has_var e then fail 0 "open term" e else idtac.

Ltac fold_closed_bv2 :=
repeat match goal with
| |- evt _ _ (MS ?R _ _ _ _ _ _) =>
match R with context [Z_to_bv 64 ?e] =>
lazymatch e with
| Z.land _ _ => idtac | Z.lor _ _ => idtac | Z.add _ _ => idtac | bv_unsigned _ => idtac | Z.shiftr _ _ => idtac | Z.shiftl _ _ => idtac | Z.sub _ _ => idtac | Z.mul _ _ => idtac | Z.modulo _ _ => idtac | Z.opp _ => idtac
end;
closed_term e;
let v0 := eval vm_compute in e in
lazymatch v0 with
| Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
end;
let v := eval vm_compute in (Z.modulo v0 (2^64)) in
first [ change (Z_to_bv 64 e) with (Z_to_bv 64 v)
| replace (Z_to_bv 64 e : bv 64) with (Z_to_bv 64 v : bv 64) by (apply bv_eq; vm_compute; reflexivity) ]
end
end.

Ltac amo_fix :=
repeat match goal with
| |- context [amo_aligned ?wd (Z_to_bv 64 ?a)] =>
closed_term a;
let v := eval vm_compute in (amo_aligned wd (Z_to_bv 64 a)) in change (amo_aligned wd (Z_to_bv 64 a)) with v; cbn [negb]; exec_cbv
| |- context [if Z.eqb ?x ?y then EStore ?n ?a ?v ?k else ?e] =>
closed_term x; closed_term y;
let b := eval vm_compute in (Z.eqb x y) in
change (if Z.eqb x y then EStore n a v k else e) with (if b then EStore n a v k else e); exec_cbv
end.
Ltac solve_load ::= amo_fix; first [ solve_load_base | solve_load_image | idtac ]. Ltac mkr__solve_load_1 := amo_fix; first [ solve_load_base | solve_load_image | idtac ].

Definition META_SH : Z := 0x80015a08.
Definition MUTEX_A : Z := 0xefa70.

Definition got9 (g0 g1 g5 g6 g7 : word) : list cell :=
[C8 g0; C8 g1; C8 (Z_to_bv 64 0x183ce8); C8 (Z_to_bv 64 0xef9b8); C8 (Z_to_bv 64 0xf21b8); C8 g5; C8 g6; C8 g7; C8 (Z_to_bv 64 0xea1d0)].

Definition W_UNREG (usp : Z) : list (Z * Z) := [(usp - 240, usp); (MUTEX_A, MUTEX_A + 8); W_ODR; (0x7fffa000, 0x800c0e00)]%Z.

Definition g_ok2b (r : list Z) : bool :=
(0x10000 <=? g_beg r) && (g_beg r mod 8 =? 0) && (g_szrz r mod 8 =? 0) && (8 <=? g_szrz r) && (g_szrz r <=? 4096)
&& (g_beg r + g_szrz r <=? 0x647000) && ((g_odr r =? 0) || (g_odr r =? 2^64 - 1) || (g_odr r =? ODR_A)).
Lemma g_ok2b_ok : forall r, g_ok2b r = true -> g_ok2 r.
Proof.
intros r H. unfold g_ok2b in H. unfold g_ok2.
repeat (apply andb_prop in H as [H ?X]).
repeat match goal with G : (_ && _) = true |- _ => apply andb_prop in G as [G ?Y] end.
rewrite ?Z.leb_le, ?Z.eqb_eq in *.
repeat split; try assumption.
repeat match goal with G : (_ || _) = true |- _ => apply orb_prop in G as [G | G] end; rewrite ?Z.eqb_eq in *; tauto.
Qed.
Fixpoint chainedb (l : list (list Z)) : bool :=
match l with
| [] => true
| r :: l' => forallb (fun r' => g_beg r + g_szrz r <=? g_beg r') l' && chainedb l'
end.
Lemma chainedb_ok : forall l, chainedb l = true -> chained l.
Proof.
induction l as [|r l IH]; intros H; cbn [chainedb chained] in *; [exact I|].
apply andb_prop in H as [H1 H2]. split; [|apply IH; exact H2].
apply Forall_forall. intros r' Hin. apply Z.leb_le. exact (proj1 (forallb_forall _ _) H1 r' Hin).
Qed.
Lemma tok_ok2 : Forall g_ok2 tokA_globals8.
Proof. apply Forall_forall. intros r Hin. apply g_ok2b_ok. revert r Hin. apply forallb_forall. vm_compute. reflexivity. Qed.
Lemma tok_chained : chained tokA_globals8.
Proof. apply chainedb_ok. vm_compute. reflexivity. Qed.
Lemma tok_len : Z.of_nat (length tokA_globals8) = 107.
Proof. reflexivity. Qed.

Lemma outside_map_sh : forall l x, Forall g_ok2 l -> ~ (0x7fffa000 <= x < 0x800c0e00) -> outside (map g_sh l) x.
Proof.
induction l as [|r l IH]; intros x OK Hx; cbn [map outside]; [exact I|].
apply Forall_cons_iff in OK as [OKr OK]. unfold g_ok2 in OKr. unfold g_sh. split; [lia | apply IH; assumption].
Qed.
Lemma disjoint_from_map_sh2 : forall l A n, (A + n <= 0x7fffa000 \/ 0x800c0e00 <= A) -> Forall g_ok2 l -> disjoint_from (map g_sh l) A n.
Proof.
induction l as [|r l IH]; intros A n HA OK; cbn [map disjoint_from]; [exact I|].
apply Forall_cons_iff in OK as [OKr OK]. unfold g_ok2 in OKr. unfold g_sh. cbn [fst snd]. split; [lia | apply IH; assumption].
Qed.
Definition disjoint_fromb (W : list (Z * Z)) (a n : Z) : bool :=
forallb (fun lh : Z * Z => (a + n <=? fst lh) || (snd lh <=? a)) W.
Lemma disjoint_fromb_ok : forall W a n, disjoint_fromb W a n = true -> disjoint_from W a n.
Proof.
induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
cbn [disjoint_fromb forallb fst snd] in H. apply andb_prop in H as [H1 H2].
split; [| apply IH; exact H2]. apply orb_prop in H1 as [H1|H1]; [left|right]; apply Z.leb_le; exact H1.
Qed.
Lemma shadows_rw_transport_gen : forall l W m m',
shadows_rw m l -> munch W m m' -> wmono asegs m m' ->
(forall A n, 0x7fffa000 <= A -> A + n <= 0x800c0e00 -> disjoint_from W A n) -> Forall g_ok2 l ->
shadows_rw m' l.
Proof.
intros l W m m' H MU WM HW OK. unfold shadows_rw in *.
apply Forall_forall. intros r' Hin.
pose proof (proj1 (Forall_forall _ _) H r' Hin) as (junk & RW).
pose proof (proj1 (Forall_forall _ _) OK r' Hin) as OK'. unfold g_ok2 in OK'.
exists junk. eapply rw_cells_transport; [exact RW | exact MU | exact WM |].
unfold g_sh. cbn [fst cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply HW; lia.
Qed.

Section P1.
Context {RC__ : Q6q3.RunConsts}.
Definition poison_meta_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (META_SH, META_SH + 856)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma poison_meta_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
a0 = Z_to_bv 64 0xed040 -> a1 = Z_to_bv 64 6848 -> a2 = Z_to_bv 64 0 ->
ro_cells asegs m 0xe8198 (got9 g0 g1 g5 g6 g7) ->
ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
rw_cells asegs m META_SH [CB 856 junkM] ->
evt asegs (poison_meta_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x64bfc) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO A0 A1 A2 GOT SB THR RM MSH. subst a0 a1 a2. unfold META_SH in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x80015a08, 0x80015a08 + 856)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
step. step. step. step. step. step. step. step.
step. if_truex.
step. step. if_falsex.
step. step. step.
step. step. step. step.
fold_closed_bv.
step. if_truex.
step. step. if_falsex.
step. step. fold_closed_bv. step. if_truex.
step. step. step. step. if_falsex.
step. step. step. step. step. fold_closed_bv.
step. if_falsex.
step. step. step.
step. if_truex.
step. step.
step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
step.
try replace (ret_pc (Z_to_bv 64 908820)) with (Z_to_bv 64 908820 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
eapply evt_cut; [eapply Q3Gm.memset_spec; [rewrite !unsigned_lit by lia; exact MSH | exact MI] | ].
intros ms' PO. unfold memset_post in PO.
destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & E & MUc & WMc & MI1 & SH1). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in SH1 by lia. change (0 mod 256) with 0 in SH1. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in SH1.
transport_after_call rsegs m0 m1 MUc WMc.
change (Z.to_nat 856) with 856%nat in SH1.
apply evt_done. unfold poison_meta_post.
exists u0, u1, u2, (Z_to_bv 64 2147572232), ua1, ua2, ua3, ua4, ua5, ua6, ua7, u3, u4, u5, u6, m1.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST | exact SH1].
Qed.
End P1.

Section P2.
Context {RC__ : Q6q3.RunConsts}.
Definition unreg_globals_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (W_UNREG (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' MUTEX_A [C8 (Z_to_bv 64 0)]
/\ (exists ob', rw_cells asegs m' ODR_A [C1 ob']) /\ rw_cells asegs m' META_SH [CB 856 (repeat (Z_to_bv 8 0) 856)].

Lemma unreg_globals_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (g0 g1 g5 g6 g7 : word) (ob : byte) (junkM : list byte),
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 240 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 AGLOB_START -> a1 = Z_to_bv 64 107 ->
ro_cells asegs m 0xe8198 (got9 g0 g1 g5 g6 g7) ->
ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0xef9d0 [C4 (Z_to_bv 64 1)] ->
ro_cells asegs m 0xf21b8 [C8 (Z_to_bv 64 0x7fff8000)] ->
ro_cells asegs m 0xf1a1c [C1 (Z_to_bv 8 1)] ->
ro_cells asegs m 0x183d60 [C8 (Z_to_bv 64 0xffffffffffffffff)] ->
ro_cells asegs m 0xea1d0 [C8 (Z_to_bv 64 0xdde14)] ->
rw_cells asegs m MUTEX_A [C8 (Z_to_bv 64 0)] ->
recs_ro m AGLOB_START tokA_globals8 -> shadows_rw m tokA_globals8 -> rw_cells asegs m ODR_A [C1 ob] ->
rw_cells asegs m META_SH [CB 856 junkM] ->
evt asegs (unreg_globals_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x4d698) fc None m (seg_rom asegs)).
Proof.
intros until junkM. intros MI ST CEIL LO AL A0 A1 GOT INITED RG SB CP THR RM MUT RR SW ODRB MSH. subst a0 a1.
unfold AGLOB_START, MUTEX_A, META_SH, ODR_A in *. unfold got9 in GOT.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (0xefa70, 0xefa70 + 8)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 176%nat ST.
do 14 step.
step. step. step. step.
stepz.
step.
match goal with |- context [sx32 (Z_to_bv 64 1)] => replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
if_falsex.
do 9 (stepz; fold_closed_bv2).
step.
do 4 (stepz; fold_closed_bv2).
do 4 (stepz; fold_closed_bv2).
step. fold_closed_bv2. step. if_falsex.
step. fold_closed_bv2. step. fold_closed_bv2.
step.
step. if_falsex.
stepz.
step. if_falsex.
step. if_truex.
stepz. stepz.
step. if_falsex.
do 7 step.
step.
step. stepz. step. stepz. step. stepz.
step. step. step. stepz.
step. step. step. fold_closed_bv2.
step. step. step.

eapply (unreg_loop2 tokA_globals8) with (ob := ob);
[ exact tok_len | lia | lia | lia | reflexivity | exact MI | exact INITED | exact RG | exact SB | exact CP | exact THR | exact RM
| eapply recs_ro_transport; [exact RR | exact MU | intros q Hq1 Hq2; cbn [disjoint_from length]; rewrite tok_len in Hq2 || idtac; lia]
| exact tok_ok2 | exact tok_chained
| eapply shadows_rw_transport_gen; [exact SW | exact MU | exact WM | intros A n HA1 HA2; cbn [disjoint_from]; lia | exact tok_ok2]
| exact ODRB | ].
intros ra' a0' a1' a2' a3' a4' a5' a6' a7' s0' t0' t1' t2' t3' t4' t5' t6' m2 ob' MU2 WM2 MI2 ODRB2.
assert (DJL : forall A n, (A + n <= 0x624860 \/ (0x624861 <= A /\ A + n <= 0x7fffa000) \/ 0x800c0e00 <= A) -> disjoint_from (W_ODR :: map g_sh tokA_globals8) A n).
{ intros A n HA. cbn [disjoint_from W_ODR]. unfold ODR_A. split; [lia|]. apply disjoint_from_map_sh2; [lia | exact tok_ok2]. }
eapply (rw_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in FR; [| exact MU2 | exact WM2 | apply DJL; cbn; lia].
eapply (rw_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in MUT; [| exact MU2 | exact WM2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in GOT; [| exact MU2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in SB; [| exact MU2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in THR; [| exact MU2 | apply DJL; cbn; lia].
eapply (ro_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in RM; [| exact MU2 | apply DJL; cbn; lia].
eapply (rw_cells_transport rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in MSH; [| exact MU2 | exact WM2 | apply disjoint_fromb_ok; vm_compute; reflexivity].
eapply (stk_transport_disjoint rsegs (W_ODR :: map g_sh tokA_globals8) m1 m2) in ST; [| exact MU2 | exact WM2 | apply DJL; lia].
assert (MUA : munch (W_UNREG (bv_unsigned sp)) m m2).
{ eapply munch_join; [exact MU | exact MU2 | |].
- intros x Hx. unfold W_UNREG, W_ODR, MUTEX_A, ODR_A in Hx. cbn [outside] in Hx |- *. lia.
- intros x Hx. unfold W_UNREG, W_ODR, MUTEX_A, ODR_A in Hx. cbn [outside] in Hx. cbn [outside W_ODR]. unfold ODR_A.
split; [lia|]. apply outside_map_sh; [exact tok_ok2 | lia]. }
pose proof (wmono_trans _ _ _ _ WM WM2) as WMA.
clear MU MU2 WM WM2 DJL MI INITED RG CP ODRB RR SW. rename MI2 into MI. rename MUA into MU. rename WMA into WM.
unfold ODR_A in ODRB2.

step. step. fold_closed_bv2. step. step. fold_closed_bv2. step. step.
step.
eapply evt_cut; [eapply (poison_meta_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 lo g0 g1 g5 g6 g7 junkM);
[exact MI | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; lia | reflexivity | reflexivity | reflexivity | exact GOT | exact SB | exact THR | exact RM | exact MSH] | ].
intros ms' PO. destruct PO as (v0 & v1 & v2 & va0 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m3 & E & MUc & WMc & MI3 & ST3 & MSH3). subst ms'.
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST3 by lia. unfold META_SH in MUc, MSH3. unfold W_UNREG, MUTEX_A, W_ODR, ODR_A in MU.
clear MSH ST.
transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc.
replace (ret_pc (Z_to_bv 64 318068)) with (Z_to_bv 64 318068 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
clear MI; rename MI3 into MI.
step. step.
do 7 (step; fold_closed_bv2).
step.
do 4 (step; fold_closed_bv2).
step.
step. fold_closed_bv2. step. fold_closed_bv2.
step. if_falsex.
step. fold_closed_bv2. step. if_truex.
do 7 (step; fold_closed_bv2).
step. if_truex.
step.
step. if_falsex.
stepz.
step. if_falsex.
step. if_truex.
step. if_falsex.
do 13 step.
step.
release_frame FR ST3 (bv_unsigned sp).
step.
apply evt_done. unfold unreg_globals_post.
do 16 eexists.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
unfold MUTEX_A, META_SH. split; [exact MUT|]. split; [| exact MSH3].
exists ob'. exact ODRB2.
Qed.
End P2.
