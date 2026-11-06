(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGcC.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QS67.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QS67. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0TL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGm2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGm2.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbKA.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrJ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrJ1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlna.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlna.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qirj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qirj.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMjx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMjx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition TAIL_A : Z := 0x917ec.

Fixpoint recs_ro_b (p : Z) (l : list (list Z)) : bool :=
match l with
| [] => true
| r :: l' => rw_bytes_b asegs p (cells_bytes (g_cells r)) && recs_ro_b (p + 64) l'
end.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma recs_ro_of_pristine : forall l m p, pristine m p (p + 64 * Z.of_nat (length l)) -> 0 <= p -> p + 64 * Z.of_nat (length l) <= 2^64 ->
recs_ro_b p l = true -> recs_ro m p l.
Proof.
induction l as [|r l IH]; intros m p P Hp Hhi Hb; cbn [recs_ro]; [exact I|].
cbn [recs_ro_b] in Hb. apply andb_true_iff in Hb as [H1 H2]. cbn [length] in P, Hhi.
assert (L : length (cells_bytes (g_cells r)) = 64%nat) by (cbn [cells_bytes g_cells cbytes]; rewrite ?length_app, !length_le8; reflexivity).
split.
- apply ro_of_rw. eapply rw_cells_pristine_recast; [| exact H1 | lia | rewrite L; lia | cbn [cells_wf cell_wf g_cells csize cbytes]; rewrite length_le8; repeat split; reflexivity | reflexivity | rewrite L; reflexivity].
rewrite L. eapply pristine_sub; [exact P | lia | lia].
- apply IH; [eapply pristine_sub; [exact P | lia | lia] | lia | lia | exact H2].
Qed.

Lemma tok_recs_ro : forall m, pris_A m -> recs_ro m AGLOB_START tokA_globals8.
Proof.
intros m P. pris_get P 0xea960 0xec420. pose proof tok_len as TL.
apply recs_ro_of_pristine; [rewrite TL; unfold AGLOB_START; eapply pristine_sub; [exact PR | lia | lia] | unfold AGLOB_START; lia | rewrite TL; unfold AGLOB_START; lia |].
vm_compute. reflexivity.
Qed.

Lemma img_shadow_rw : forall (HIx : heap_iface_A A4L) A LB LM FR B m md a n,
HEAPA A4L HIx A LB LM FR B m md -> 0x2000 <= a - A_SB -> a - A_SB + Z.of_nat n <= 0xc8a00 ->
exists junk, rw_cells asegs m a [CB n junk].
Proof.
intros HIx A LB LM FR B m md a n HP H1 H2.
assert (G : forall i, (i < n)%nat -> bytes_at asegs m (a + Z.of_nat i) [Z_to_bv 8 (img_shadow_val tokA_reg_globals (a - A_SB + Z.of_nat i))]).
{ intros i Hi. pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (a - A_SB + Z.of_nat i) HP ltac:(cbn; lia) ltac:(cbn; lia)) as SH.
cbn [hl_sb hl_reg_globals A4L] in SH. replace (a - A_SB + Z.of_nat i + A_SB) with (a + Z.of_nat i) in SH by lia. exact SH. }
exists (map (fun i => Z_to_bv 8 (img_shadow_val tokA_reg_globals (a - A_SB + Z.of_nat i))) (seq 0 n)).
apply rw_of_ro_high; [| unfold A_SB in *; lia].
split; [cbn; rewrite length_map, length_seq; split; [reflexivity | exact I]|].
cbn [cells_bytes cbytes]. rewrite app_nil_r.
split; [unfold A_SB in *; lia|]. split; [rewrite length_map, length_seq; unfold A_SB in *; lia|].
intros i Hi. rewrite length_map, length_seq in Hi.
destruct (G i Hi) as (_ & _ & Gi). specialize (Gi 0%nat ltac:(cbn; lia)). cbn [nth_error] in Gi. rewrite Z.add_0_r in Gi.
rewrite Gi. rewrite nth_error_map, nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add]. reflexivity.
Qed.

Lemma tok_shadows_rw : forall (HIx : heap_iface_A A4L) A LB LM FR B m md,
HEAPA A4L HIx A LB LM FR B m md -> shadows_rw m tokA_globals8.
Proof.
intros HIx A LB LM FR B m md HP. unfold shadows_rw. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) tok_ok2 r Hr) as OK. unfold g_ok2, g_ok in OK. cbn [g_sh fst].
apply (img_shadow_rw HIx _ _ _ _ _ _ _ _ _ HP); unfold A_SB; [Z.div_mod_to_equations; lia | rewrite Z2Nat.id by lia; Z.div_mod_to_equations; lia].
Qed.

Lemma rdn_pristine : forall m a bs,
pristine m a (a + Z.of_nat (length bs)) -> rw_bytes_b asegs a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
rdn asegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros m a bs P Hb H0 Hhi.
pose proof (rw_cells_pristine m a bs P Hb H0 Hhi) as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
pose proof (bytes_at_rdn asegs m a bs 0 (length bs) BA ltac:(lia)) as X. cbn [Z.of_nat skipn] in X. rewrite Z.add_0_r, firstn_all in X.
exact X.
Qed.

Lemma rdn_bytes_at : forall m a bs, bytes_at asegs m a bs -> rdn asegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros m a bs BA. pose proof (bytes_at_rdn asegs m a bs 0 (length bs) BA ltac:(lia)) as X. cbn [Z.of_nat skipn] in X. rewrite Z.add_0_r, firstn_all in X. exact X.
Qed.

Section Tail.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.

Lemma exit_facts : forall argv USP A LB LM FR B m md,
drvA_mem argv USP m -> HEAPAx A LB LM FR B m md ->
(ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]) ->
(exists tid g0 g1 g5 g6 g7 dso ob junkM mid, exit_cells_A m tid g0 g1 g5 g6 g7 dso ob junkM mid)
/\ stdio_globalsA m
/\ (forall a, 0x7fffa000 <= a < 0x800c0a00 -> wview asegs m (wa a) <> None)
/\ file_clean m 0xea840 (Z_to_bv 64 0) (Z_to_bv 64 0).
Proof.
intros argv USP A LB LM FR B m md DM HP AEF0.
destruct DM as [MI ARGC _ _ PRS (tid & TID & TIDR) LOC (mid & AT & MIDL)].
pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as RT. cbn [hl_rt_consts A4L] in RT. unfold a4_rt_consts in RT.
pose proof (heapA_need_locks A4L HIx _ _ _ _ _ _ _ HP) as NL. cbn [hl_libc hla_base A4L A4H] in NL.

Ltac rtc' RT a bs H := pose proof (proj1 (Forall_forall _ _) RT (a, bs) ltac:(cbn [In]; repeat (try (left; reflexivity); right))) as H; cbn [fst snd] in H.
rtc' RT 0xf07d8 [Z_to_bv 8 1] XIN. rtc' RT 0xed310 (le4 (Z_to_bv 64 1)) XRG. rtc' RT 0xef35c [Z_to_bv 8 1] XCP.
rtc' RT 0x1816a0 (le8 (Z_to_bv 64 0xffffffffffffffff)) XTH. rtc' RT 0xe7db0 (le8 (Z_to_bv 64 0xdb750)) XRM.
rtc' RT 0xed3b0 (le8 (Z_to_bv 64 0)) XMU. rtc' RT 0xec440 (le8 (Z_to_bv 64 1)) XFL.

pose proof (rtc_R_of_HEAPA HIx _ _ _ _ _ _ _ HP) as PRR.
pose proof I as PR. pose proof I as PR0. pris_get PRS 0xec450 0xec498. pris_get PRS 0x1819a0 0x1819a8.
pris_get PRS 0x642fe0 0x6430e0. pris_get PRS 0xea748 0xea750. pris_get PRS 0x643588 0x6435e0. pose proof I as PR6.
pris_get PRS 0xea838 0xea940. pris_get PRS 0xea948 0xea960.
destruct (img_shadow_rw HIx _ _ _ _ _ _ _ META_SH 856 HP ltac:(unfold META_SH, A_SB; lia) ltac:(unfold META_SH, A_SB; cbn; lia)) as (junkM & MSH).
destruct (img_rw_any ODR_A 1 m ltac:(vm_compute; reflexivity) ltac:(unfold ODR_A; lia) ltac:(unfold ODR_A; cbn; lia)) as (obl & ODR).
assert (OB : exists ob, rw_cells asegs m ODR_A [C1 ob]).
{ destruct ODR as [[WF BA] WR]. cbn in WF. destruct obl as [|ob [|]]; cbn in WF; try lia. exists ob.
split; [split; [cbn; split; exact I | exact BA] | exact WR]. }
destruct OB as (ob & OB).

Ltac pcell m PRx a bs :=
eapply (rw_cells_pristine_recast m a bs);
[ eapply pristine_sub; [exact PRx | lia | rewrite ?length_app, ?length_app, ?length_le8, ?length_le4; cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia]
| vm_compute; reflexivity | lia
| rewrite ?length_app, ?length_app, ?length_le8, ?length_le4; cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; lia
| cbn [cells_wf cell_wf csize cbytes]; rewrite ?length_le8, ?length_le4; repeat split; reflexivity
| vm_compute; reflexivity
| cbn [cells_size csize Nat.add]; rewrite ?length_app, ?length_app, ?length_le8, ?length_le4; reflexivity ].
split; [| split; [| split]].
- exists tid, (Z_to_bv 64 0x17f5a0), (Z_to_bv 64 0xe7de8), (Z_to_bv 64 0xf07e8), (Z_to_bv 64 0xf07f0), (Z_to_bv 64 0xf07e0), (Z_to_bv 64 0xe7c00), ob, junkM, mid.
constructor.
+ exact TID.
+ exact TIDR.
+ unfold EXITLOCK_A. pcell m PR3 0x6430d0 (le4 (Z_to_bv 64 0)).
+ unfold NEEDLOCKS_A. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact NL].
+ unfold COVFLAG_A. apply ro_of_rw. pcell m PR2 0x1819a0 [Z_to_bv 8 0].
+ exact AT.
+ exact MIDL.
+ exact AEF0.
+ unfold FINI_A. rtcR_cell PRR 0xe6bb0 (le8 (Z_to_bv 64 0xe2400) ++ le8 (Z_to_bv 64 0xe23f0)).
+ unfold FINI_A. rtcR_cell PRR 0xe23f0 (le8 (Z_to_bv 64 0x99f88) ++ le8 (Z_to_bv 64 0x3dee0)).
+ unfold COMPLETED_A. pcell m PR1 0xec490 [Z_to_bv 8 0].
+ rtcR_cell PRR 0xe5d88 (le8 (Z_to_bv 64 0xcc594) ++ le8 (Z_to_bv 64 0x0)).
+ rtcR_cell PRR 0xe7c00 (le8 (Z_to_bv 64 0xe7c00)).
+ unfold got9.
rtcR_cell PRR 0xe5d98 (le8 (Z_to_bv 64 0x17f5a0) ++ le8 (Z_to_bv 64 0xe7de8) ++ le8 (Z_to_bv 64 0x181628) ++ le8 (Z_to_bv 64 0xed2f8) ++ le8 (Z_to_bv 64 0xefaf8)
++ le8 (Z_to_bv 64 0xf07e8) ++ le8 (Z_to_bv 64 0xf07f0) ++ le8 (Z_to_bv 64 0xf07e0) ++ le8 (Z_to_bv 64 0xe7db0)).
+ unfold AGLOB_START, AGLOB_STOP. rtcR_cell PRR 0xe6ab0 (le8 (Z_to_bv 64 0xea960) ++ le8 (Z_to_bv 64 0xec420)).
+ split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact XIN].
+ split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact XRG].
+ apply ro_C8_of_bytes_at. exact (proj1 (proj2 (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP))).
+ split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact XCP].
+ apply ro_C8_of_bytes_at. exact XTH.
+ apply ro_C8_of_bytes_at. exact XRM.
+ apply rw_of_ro_img; [apply ro_C8_of_bytes_at; exact XMU | vm_compute; reflexivity].
+ apply rw_of_ro_img; [apply ro_C8_of_bytes_at; exact XFL | vm_compute; reflexivity].
+ apply tok_recs_ro. exact PRS.
+ eapply tok_shadows_rw. exact HP.
+ exact OB.
+ exact MSH.
-
split; [| split; [| split; [| split]]].
+ exact (rdn_bytes_at m 0x6430f3 [Z_to_bv 8 0] NL).
+ apply (rdn_pristine m 0x6435d0 (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact PR5 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+
apply (rdn_pristine m 0xea928 (word_to_le_bytes 8 (Z_to_bv 64 0xea840))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+ apply (rdn_pristine m 0xea838 (word_to_le_bytes 8 (Z_to_bv 64 0xea750))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+ apply (rdn_pristine m 0xea748 (word_to_le_bytes 8 (Z_to_bv 64 0xea660))); [eapply pristine_sub; [exact PR4 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
- intros a Ha. destruct (img_shadow_rw HIx _ _ _ _ _ _ _ a 1 HP ltac:(unfold A_SB; lia) ltac:(unfold A_SB; cbn; lia)) as (j & [_ (_ & _ & W)]).
replace a with (a + 0) by lia. apply W. cbn. lia.
-
split; [| split; [| split; [| split]]].
+ apply (rdn_pristine m (0xea840 + 140) (word_to_le_bytes 4 (Z_to_bv 64 4294967295))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+ apply (rdn_pristine m (0xea840 + 40) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+ apply (rdn_pristine m (0xea840 + 56) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+ apply (rdn_pristine m (0xea840 + 8) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
+ apply (rdn_pristine m (0xea840 + 16) (word_to_le_bytes 8 (Z_to_bv 64 0))); [eapply pristine_sub; [exact PR7 | lia | cbn; lia] | vm_compute; reflexivity | lia | cbn; lia].
Qed.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.
Variables (argv : list (list byte)) (USP LO : Z) (fs : Fs.Fs) (LM0 : list blk).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.

Record TINV (status buf cap : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (pending : list byte) : Prop := MKT {
t_mem   : drvA_mem argv USP m;
t_heap  : HEAPAx A ((buf, cap) :: LK) LM0 [] B m md;
t_bud   : 512 <= bB B;
t_errno : exists errv, rw_cells asegs m (A_TP - 164) [C4 errv];
t_stk   : stk asegs m LO SP;
t_frame : exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN));
t_out   : (pending = [] /\ exists wp1 rp1, file_clean m 0xea750 wp1 rp1)
\/ (pending <> [] /\ fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
/\ exists wb wp bufp bufsz rp1 can, stdout_pending m wb wp bufp bufsz rp1 can pending /\ STDOUT_BUF <= wb /\ wp <= STDOUT_BUF + 1024);
t_err   : exists wp2 rp2, file_clean m 0xea660 wp2 rp2;
t_fs    : m_fs (cfg_model md) = fs;
t_st    : 0 <= status < 256;
t_aef   : ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]
}.

Definition EPI_A : Z := 0x917f4.
Record EINV (status : Z) (LB : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (pending : list byte) : Prop := MKE {
e_mem   : drvA_mem argv USP m;
e_heap  : HEAPAx A LB LM0 [] B m md;
e_stk   : stk asegs m LO SP;
e_frame : exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN));
e_out   : (pending = [] /\ exists wp1 rp1, file_clean m 0xea750 wp1 rp1)
\/ (pending <> [] /\ fd_lookup (m_fds (cfg_model md)) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
/\ exists wb wp bufp bufsz rp1 can, stdout_pending m wb wp bufp bufsz rp1 can pending /\ STDOUT_BUF <= wb /\ wp <= STDOUT_BUF + 1024);
e_err   : exists wp2 rp2, file_clean m 0xea660 wp2 rp2;
e_fs    : m_fs (cfg_model md) = fs;
e_st    : 0 <= status < 256;
e_aef   : ax_phase m = 2 -> ro_cells asegs m AEF_FLAG_A [C1 (Z_to_bv 8 0)]
}.
Definition epi_stmt : Prop :=
forall (status : Z) (LB : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (pending : list byte)
(ra gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
EINV status LB m md A B pending ->
RZAx A md (t_emit (W 1 pending) (t_exit (exit_code status) fs))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 status) s1 a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 EPI_A) fc None m (seg_rom asegs)).

Theorem epi_ok : epi_stmt.
Proof.
unfold epi_stmt. intros until fc. intros EI.
destruct EI as [DM' HP' ST' (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR') OUT (wp2 & rp2 & FC2') Hfs Hst AEFT'].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.    pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
d5_enter.
unfold EPI_A. unfold main_frame in FR'.
step.
do 9 step.
step. step.
replace (ret_pc (Z_to_bv 64 RA_MAIN)) with (Z_to_bv 64 RA_MAIN : word) by (symmetry; apply ret_pc_even; [unfold RA_MAIN; lia| reflexivity]).
unfold RA_MAIN. step.
apply evt_done.
destruct (exit_facts argv USP A LB LM0 [] _ m md DM' HP' AEFT') as ((tid & g0 & g1 & g5 & g6 & g7 & dso & ob & junkM & mid & XC) & SG & SHW & FC0).
release_frame FR' ST' (SP + 80).
rewrite <- (exit_code_and_255 status) by lia.
rewrite <- Hfs.
destruct OUT as [(-> & wp1 & rp1 & FC1) | (NE & FD1 & wb & wp & bufp & bufsz & rp1 & can & SP1)].
-
eapply (aj_conseq Jx); [| apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
eapply (exit_clean_A Jx SYS) with (lo := LO);
[ exact HCK' | exact MI'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | exact XC | exact SG | exact FC0 | exact FC1 | exact FC2' ].
-
destruct SP1 as ([P1 P2 P3 P4 P5 P6 P7 P8 P9 RANGE LEN PMAX BYTES _] & WB1 & WP1). unfold STDOUT_BUF in WB1, WP1.
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP') as (can' & CG & CC & _). cbn [hl_got_guard hl_guard hla_base A4L A4H] in CG, CC.
assert (SP1' : stdout_pending m wb wp bufp bufsz rp1 can' pending).
{ constructor; try assumption. split; [exact (rdn_bytes_at m _ _ CG) | exact (rdn_bytes_at m _ _ CC)]. }
eapply (exit_flush_A Jx SYS) with (lo := LO);
[ exact HCK' | exact MI'
| rewrite unsigned_lit by lia; exact ST' | unfold alloc_ceiling; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | exact XC | exact SG | exact FC0 | exact FC2' | exact SP1' ].
Qed.

Definition tail_stmt : Prop :=
forall (status buf cap : Z) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (pending : list byte)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
TINV status buf cap LK m md A B pending ->
RZAx A md (t_emit (W 1 pending) (t_exit (exit_code status) fs))
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 status) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TAIL_A) fc None m (seg_rom asegs)).

Theorem tail_ok : tail_stmt.
Proof.
unfold tail_stmt. intros until fc. intros TI.
destruct TI as [DM HP HB (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) OUT (wp2 & rp2 & FC2) Hfs Hst AEFT].
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [BB0 BD0].
d5_enter.
unfold TAIL_A. step. step.
evt_done5.
eapply (OBL_FREE_NN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md _ A ((buf, cap) :: LK) LM0 [] B buf LO errv UWptr HP);
[ right; exists cap; left; reflexivity
| rewrite unsigned_lit by lia; exact ST | unfold alloc_ceiling; lia | cbn [hl_stack_A A4L]; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | reflexivity
| split; [cbn [uw_pre]; rewrite !unsigned_lit by lia; left; lia
| cbn [uw_ok uw_key]; rewrite unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]
| lia | destruct (buf =? 0); cbn [uw_cost]; lia | ].
intros ms' m' md' A' r RS VM ST' PRES ERR' HP' REQ'.
destruct RS as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & ->).
rewrite unsigned_lit in ST', PRES by lia. cbn [hl_tp A4H app] in ERR', PRES.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'.
assert (DM' : drvA_mem argv USP m') by (eapply (drvA_mem_pres OBL_CS_WIDE argv USP LO [] USPF LOF); [exact DM | exact PRES | exact MI']).
assert (FR' : rw_cells asegs m' SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact FR |]. left. lia. }

assert (AGR : forall x, (0xea618 <= x < 0xea960 \/ 0x643588 <= x < 0x6439f0) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
{ intros x Hx. apply (proj1 (PRES x ltac:(lia) ltac:(right; left; apply OBL_CS_WIDE; unfold cs_wide; lia))). }
assert (XF : forall a n bs, (0xea618 <= a /\ a + Z.of_nat n <= 0xea960) \/ (0x643588 <= a /\ a + Z.of_nat n <= 0x6439f0) ->
rdn asegs m (Z_to_bv 64 a) n = Some bs -> rdn asegs m' (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Ha Hr. rewrite (rdn_ext asegs n m' m (Z_to_bv 64 a)); [exact Hr | rewrite unsigned_lit by lia; lia |].
intros x Hx. rewrite unsigned_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned x). apply AGR. lia. }
replace (ret_pc (Z_to_bv 64 595956)) with (Z_to_bv 64 EPI_A : word) by (symmetry; apply ret_pc_even; [unfold EPI_A; lia| reflexivity]).
replace (lb_remove buf ((buf, cap) :: LK)) with LK in HP' by (cbn [lb_remove blk_addr fst]; rewrite Z.eqb_refl; reflexivity).
change (seg_rom (hl_segs A4H)) with (seg_rom asegs).
apply (epi_ok status LK m' md' A' (charge B 512 (if buf =? 0 then 0 else uw_cost UWptr)) pending). constructor.
- exact DM'.
- exact HP'.
- exact ST'.
- exists j8, x7, x6, x5, x4, x3, x2, x1, x0. exact FR'.
- replace (m_fds (cfg_model md')) with (m_fds (cfg_model md)) by (destruct VM as (F0 & _); unfold m_fds; rewrite F0; reflexivity).
destruct OUT as [(-> & wp1 & rp1 & FC1) | (NE & FD1 & wb & wp & bufp & bufsz & rp1 & can & SP1 & WB1 & WP1)].
+ left. split; [reflexivity|]. exists wp1, rp1. destruct FC1 as (K1 & K2 & K3 & K4 & K5). repeat split; (eapply XF; [| eassumption]); cbn; lia.
+ right. split; [exact NE|]. split; [exact FD1|].
destruct (heapA_canary A4L HIx _ _ _ _ _ _ _ HP') as (can' & CG & CC & _). cbn [hl_got_guard hl_guard hla_base A4L A4H] in CG, CC.
exists wb, wp, bufp, bufsz, rp1, can'. split; [| split; [exact WB1 | exact WP1]].
unfold STDOUT_BUF in WB1, WP1.
destruct SP1 as [P1 P2 P3 P4 P5 P6 P7 P8 P9 RANGE LEN PMAX BYTES _].
constructor; try assumption; try (eapply XF; [| eassumption]; cbn; lia);
try (split; [exact (rdn_bytes_at m' _ _ CG) | exact (rdn_bytes_at m' _ _ CC)]).
all: rewrite (rdn_ext asegs _ m' m (Z_to_bv 64 wb)); [exact BYTES | rewrite unsigned_lit by lia; lia |];
intros x Hx; rewrite unsigned_lit in Hx by lia; rewrite <- (Z_to_bv_bv_unsigned x); apply AGR; lia.
- exists wp2, rp2. destruct FC2 as (K1 & K2 & K3 & K4 & K5). repeat split; (eapply XF; [| eassumption]); cbn; lia.
- replace (m_fs (cfg_model md')) with (m_fs (cfg_model md)) by (destruct VM as (_ & _ & F0 & _); unfold m_fs; rewrite F0; reflexivity). exact Hfs.
- exact Hst.
-
assert (AGF : forall x, ADFLAG_A <= x < ADFLAG_A + 8 -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
{ intros x Hx. apply (proj1 (PRES x ltac:(unfold ADFLAG_A in Hx; lia) ltac:(right; left; apply OBL_CS_WIDE; unfold cs_wide; unfold ADFLAG_A in Hx; lia))). }
intros E. rewrite (ax_phase_agree m m' (AGF ADFLAG_A ltac:(lia))) in E. destruct (AEFT E) as [WF BA]. split; [exact WF|].
eapply (QscU.Mq1.bytes_at_agree USP []); [exact BA|]. intros x Hx. cbn in Hx. apply AGF. unfold AEF_FLAG_A, ADFLAG_A in *. lia.
Qed.
End Tail.
End RC__1.
