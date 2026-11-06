(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import MState Mem Cells ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanHandoffBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AsanPlan MainExport MainFactsBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase AMalloc_iface ARepInit_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations. Import AP.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma resv_named : forall V k n kd lo hi,
In (LMap (ZMul (ZLit 4096) (ZV k)) n kd) both_ledger ->
0 <= V k <= 34359738368 -> 0 <= n < 2^62 ->
4096 * V k <= lo -> hi <= 4096 * V k + n ->
pcov (resv_of V) lo hi.
Proof.
intros V k n kd lo hi HIN HV HN LO HI x Hx.
exists (4096 * V k, 4096 * V k + n). split; [| cbn [fst snd]; lia].
unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
apply in_map_iff. exists (wa (zv V (ZMul (ZLit 4096) (ZV k))), wa n). split.
- unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
- apply in_flat_map. exists (LMap (ZMul (ZLit 4096) (ZV k)) n kd). split; [exact HIN| left; reflexivity].
Qed.
#[using="Type"] Lemma resv_lit : forall V b n kd lo hi,
In (LMap (ZLit b) n kd) both_ledger ->
0 <= b < 2^62 -> 0 <= n < 2^62 ->
b <= lo -> hi <= b + n ->
pcov (resv_of V) lo hi.
Proof.
intros V b n kd lo hi HIN HB HN LO HI x Hx.
exists (b, b + n). split; [| cbn [fst snd]; lia].
unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. left.
apply in_map_iff. exists (wa (zv V (ZLit b)), wa n). split.
- unfold iv_of, wa. cbn [fst snd zv]. rewrite !unsigned_lit by lia. reflexivity.
- apply in_flat_map. exists (LMap (ZLit b) n kd). split; [exact HIN| left; reflexivity].
Qed.
#[using="Type"] Lemma resv_img : forall V, pcov (resv_of V) 0x10000 AIMG_HI.
Proof.
intros V x Hx. unfold AIMG_HI in Hx.
assert (SEG : forall b n, In (b, n) (map uns2 (segments_reserved bsegs)) -> In (b, b + n) (resv_of V)).
{ intros b n Hin. apply in_map_iff in Hin. destruct Hin as ([a m] & E & Hin). unfold uns2 in E. cbn [fst snd] in E. injection E as <- <-.
unfold resv_of, resv_entries. rewrite map_app. apply in_app_iff. right. apply in_map_iff. exists (a, m). split; [reflexivity| exact Hin]. }
rewrite reserved_eval in SEG.
destruct (Z_lt_le_dec x 200704); [| destruct (Z_lt_le_dec x 626688); [| destruct (Z_lt_le_dec x 634880)]].
- exists (65536, 65536 + 135168). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
- exists (200704, 200704 + 425984). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
- exists (626688, 626688 + 8192). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
- exists (634880, 634880 + 5619712). split; [apply SEG; cbn; tauto| cbn [fst snd]; lia].
Qed.
End CANSEC1.
Local Ltac inled := cbn; repeat (first [left; reflexivity | right]).
Local Ltac pv PF k lo hi :=
let H := fresh in pose proof (pfact_find _ (PVar k lo hi) PF ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok] in H.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Theorem aresv_ok_handoff : forall V (w : bool) (U : list (list Z)),
Forall (pfact_ok V) both_pure_facts ->
aresv_ok (mkALayout (LV V) w U) (resv_of V).
Proof.
intros V w U PF.
pv PF 78%nat 1527 34359736304. pv PF 207%nat 1527 34359735410. pv PF 208%nat 4295491576 34326181871.
pv PF 226%nat 1527 34359734272. pv PF 227%nat 1 34359736319. pv PF 228%nat 1527 34359736304.
pv PF 245%nat 1 34359736319. pv PF 310%nat 1 34359736319. pv PF 377%nat 1527 34359733495.
pv PF 453%nat 1527 34359736064. pv PF 454%nat 1527 34359734272. pv PF 471%nat 1 34359736319.
unfold aresv_ok, al_space_beg, al_ptr_array, al_t, al_ctx, al_nodes, al_store, al_fake. cbv [al_V LV Nat.eqb].
split; [apply resv_img|].
split.
{
intros x Hx.
destruct (Z_lt_le_dec x 0x8fff7000); [| destruct (Z_lt_le_dec x 0x2008fff7000)].
- eapply (resv_lit V 2147446784 268435456 KRWLAZY); [inled| lia| lia| | | exact (conj (proj1 Hx) l)]; cbn; lia.
- eapply (resv_lit V 2415882240 2199023255552 KNONELAZY); [inled| lia| lia| | | exact (conj l l0)]; cbn; lia.
- eapply (resv_lit V 2201439137792 15392894357504 KRWLAZY); [inled| lia| lia| | | exact (conj l0 (proj2 Hx))]; cbn; lia. }
split; [eapply (resv_named V 208 137439023104 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 226 8388608 KNONELAZY); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 227 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 228 65536 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 453 1048576 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 454 8388608 KRWLAZY); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 377 11571200 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 310 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 78 65536 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 207 3727360 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 245 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
split; [eapply (resv_named V 471 4096 KRW); [inled| lia| lia| lia| cbn; lia]|].
eapply (resv_named V 471 4096 KRW); [inled| lia| lia| lia| cbn; lia].
Qed.
End CANSEC2.
