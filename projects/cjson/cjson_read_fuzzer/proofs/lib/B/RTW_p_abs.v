(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_lib3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac artcells_destruct H := unfold ARTCELLS in H; decompose [and ex] H; clear H.

(* [comment removed for export] *)
Lemma artcells_icpt : forall m, ARTCELLS m -> icpt_cells m.
Proof.
  intros m H. artcells_destruct H. unfold icpt_cells, shbase_cells, ro_cells. unfold A_MUSL_MEMCPY, A_MUSL_MEMSET, A_MUSL_STRLEN in *.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma artcells_poison : forall m, ARTCELLS m -> poison_cells m.
Proof.
  intros m H. artcells_destruct H. unfold poison_cells, ro_cells.
  repeat match goal with |- _ /\ _ => split end; try assumption. eexists. eassumption.
Qed.

(* [comment removed for export] *)
Lemma aflags_word : forall m k v, cells_at bsegs m A_AFLAGS [CB 120 (map zb aflags_bytes)] -> (k + 4 <= 120)%nat -> 0 <= v < 2^32 ->
  (forall i, (i < 4)%nat -> nth (k + i) aflags_bytes 0 = (v / 2 ^ (8 * Z.of_nat i)) mod 256) ->
  cells_at bsegs m (A_AFLAGS + Z.of_nat k) [C4 (wz v)].
Proof.
  intros m k v HC Hk Hv HB. apply cells_at_C4_of_bytes; [lia|]. intros i Hi.
  exists (nth (k + i) (map zb aflags_bytes) (zb 0)). split.
  - replace (A_AFLAGS + Z.of_nat k + Z.of_nat i) with (A_AFLAGS + Z.of_nat (k + i)) by lia. apply aflags_byte; [exact HC| lia].
  - change (zb 0) with ((fun z => zb z) 0). rewrite map_nth. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite (HB i Hi). apply Z.mod_mod. lia.
Qed.

Lemma rtrep_fill_cells : forall st m, RTREP st m -> ARTCELLS m -> fill_cells m.
Proof.
  intros st m HR HA. pose proof (rr_consts st m HR) as HC. destruct HC as (_ & _ & HAF & _).
  artcells_destruct HA. unfold fill_cells, ro_cells. unfold A_MUSL_MEMSET in *.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split.
  - change 1371748 with (A_AFLAGS + Z.of_nat 44). change (Z_to_bv 64 4096) with (wz 4096). apply (aflags_word m 44 4096 HAF); [lia| lia|].
    intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
  - unfold MALLOC_FILL_BYTE. change 1371756 with (A_AFLAGS + Z.of_nat 52). change (Z_to_bv 64 190) with (wz 190). apply (aflags_word m 52 190 HAF); [lia| lia|].
    intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma rtrep_memtoshadow_cells : forall st m, RTREP st m -> ARTCELLS m -> memtoshadow_cells m.
Proof.
  intros st m HR HA. pose proof (rr_consts st m HR) as HC. destruct HC as (_ & _ & HAF & _).
  artcells_destruct HA. unfold memtoshadow_cells, ro_cells.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  change 1371789 with (A_AFLAGS + Z.of_nat 85). pose proof (aflags_byte m 85 HAF ltac:(lia)) as HB85. exact HB85.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vis_carve : forall m lo hi a (n : nat), stk bsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells bsegs m a [CB n junk].
Proof.
  intros m lo hi a n ST H1 H2.
  destruct (stk_split bsegs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve bsegs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ [junk FR]].
  exists junk. replace a with (a + Z.of_nat n - Z.of_nat n) by lia. exact FR.
Qed.

Lemma vis_c8 : forall m lo hi a, stk bsegs m lo hi -> lo <= a -> a + 8 <= hi -> exists v : word, rw_cells bsegs m a [C8 v].
Proof.
  intros m lo hi a ST H1 H2. destruct ST as (S0 & S1 & SV). apply c8_of_bytes; [lia| lia|]. intros i Hi. apply SV. lia.
Qed.

Lemma vis_c8x3 : forall m lo hi a, stk bsegs m lo hi -> lo <= a -> a + 24 <= hi ->
  exists v0 v1 v2 : word, rw_cells bsegs m a [C8 v0; C8 v1; C8 v2].
Proof.
  intros m lo hi a ST H1 H2.
  destruct (vis_c8 m lo hi a ST ltac:(lia) ltac:(lia)) as [v0 R0].
  destruct (vis_c8 m lo hi (a + 8) ST ltac:(lia) ltac:(lia)) as [v1 R1].
  destruct (vis_c8 m lo hi (a + 16) ST ltac:(lia) ltac:(lia)) as [v2 R2].
  exists v0, v1, v2. apply (proj2 (rw_cells_app m a [C8 v0] [C8 v1; C8 v2])). split; [exact R0|].
  apply (proj2 (rw_cells_app m (a + Z.of_nat (cells_size [C8 v0])) [C8 v1] [C8 v2])). cbn [cells_size Cells.csize Nat.add].
  change (Z.of_nat 8) with 8. replace (a + 8 + 8) with (a + 16) by lia. split; [exact R1| exact R2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_bytes_zcells : forall vs, cells_bytes (zcells vs) = map zb vs.
Proof. intros vs. unfold zcells. induction vs as [|v vs IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.
Lemma cells_wf_zcells : forall vs, cells_wf (zcells vs).
Proof. intros vs. unfold zcells. induction vs as [|v vs IH]; [exact I|]. cbn [map cells_wf cell_wf]. split; [exact I| exact IH]. Qed.
Lemma map_zb_zrep : forall v k, map zb (zrep v k) = repeat (zb v) (Z.to_nat k).
Proof. intros. unfold zrep. apply map_repeat. Qed.

Lemma zcells_zrep_to_CB : forall m A v k, 0 <= k ->
  rw_cells bsegs m A (zcells (zrep v k)) -> rw_cells bsegs m A [CB (Z.to_nat k) (repeat (zb v) (Z.to_nat k))].
Proof.
  intros m A v k Hk [[Hwf HB] HW]. split; [split|].
  - cbn. split; [apply repeat_length| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite cells_bytes_zcells, map_zb_zrep in HB. exact HB.
  - cbn [cells_size Cells.csize Nat.add]. rewrite Nat.add_0_r. rewrite zcells_size in HW. unfold zlen in HW. rewrite zrep_length in HW by lia.
    rewrite Z2Nat.id by lia. exact HW.
Qed.
Lemma CB_to_zcells_zrep : forall m A v k, 0 <= k ->
  rw_cells bsegs m A [CB (Z.to_nat k) (repeat (zb v) (Z.to_nat k))] -> rw_cells bsegs m A (zcells (zrep v k)).
Proof.
  intros m A v k Hk [[Hwf HB] HW]. split; [split|].
  - apply cells_wf_zcells.
  - cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite cells_bytes_zcells, map_zb_zrep. exact HB.
  - cbn [cells_size Cells.csize Nat.add] in HW. rewrite Nat.add_0_r in HW. rewrite zcells_size. unfold zlen. rewrite zrep_length by lia.
    rewrite Z2Nat.id in HW by lia. exact HW.
Qed.

Lemma zrep_split : forall v a b, 0 <= a -> 0 <= b -> zrep v (a + b) = zrep v a ++ zrep v b.
Proof. intros. unfold zrep. rewrite Z2Nat.inj_add by lia. apply repeat_app. Qed.
Lemma zrep_one : forall v, zrep v 1 = [v]. Proof. reflexivity. Qed.
Lemma zcells_app' : forall a b, zcells (a ++ b) = zcells a ++ zcells b.
Proof. intros. unfold zcells. apply map_app. Qed.
Lemma zcells_size_Z : forall vs, Z.of_nat (cells_size (zcells vs)) = zlen vs.
Proof. intros. apply zcells_size. Qed.

(* [comment removed for export] *)
Lemma avail_shadow_split : forall m A c rz q,
  rw_cells bsegs m A (zcells (sh_avail c)) -> 0 <= rz -> 0 <= q -> rz + q <= csize c / 8 ->
  rw_cells bsegs m A (zcells (zrep SV_HEAP_LEFT_RZ rz))
  /\ rw_cells bsegs m (A + rz) [CB (Z.to_nat q) (repeat (zb SV_HEAP_LEFT_RZ) (Z.to_nat q))]
  /\ rw_cells bsegs m (A + rz + q) (zcells (zrep SV_HEAP_LEFT_RZ (csize c / 8 - rz - q))).
Proof.
  intros m A c rz q H Hrz Hq Hle. unfold sh_avail in H.
  replace (csize c / 8) with (rz + (q + (csize c / 8 - rz - q))) in H by lia.
  rewrite (zrep_split _ rz) in H by lia. rewrite (zrep_split _ q) in H by lia. rewrite !zcells_app' in H.
  pose proof (proj1 (rw_cells_app m A _ _) H) as [H1 H23]. rewrite zcells_size_Z in H23. unfold zlen in H23. rewrite zrep_length in H23 by lia.
  pose proof (proj1 (rw_cells_app m (A + rz) _ _) H23) as [H2 H3]. rewrite zcells_size_Z in H3. unfold zlen in H3. rewrite zrep_length in H3 by lia.
  split; [exact H1|]. split; [apply zcells_zrep_to_CB; [lia| exact H2]| exact H3].
Qed.

(* [comment removed for export] *)
Lemma avail_shadow_head : forall m A c, 1 <= c <= 31 ->
  rw_cells bsegs m A (zcells (sh_avail c)) -> rw_cells bsegs m A [C1 (zb SV_HEAP_LEFT_RZ)].
Proof.
  intros m A c Hc H. pose proof (csize_pos c Hc). unfold sh_avail in H.
  replace (csize c / 8) with (1 + (csize c / 8 - 1)) in H by lia. rewrite zrep_split, zrep_one, zcells_app' in H by (Z.div_mod_to_equations; lia).
  exact (rw_cells_take m A _ _ H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_rt_frame : forall FP lo SP m m' A cs vlo vhi,
  rt_frame FP lo SP m m' -> rw_cells bsegs m A cs -> stk bsegs m' vlo vhi ->
  vlo <= A -> A + Z.of_nat (cells_size cs) <= vhi -> vhi <= 2^64 ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ (lo <= a < SP) /\ ~ in_ivs FP a) ->
  rw_cells bsegs m' A cs.
Proof.
  intros FP lo SP m m' A cs vlo vhi RF [[Hwf (B0 & B1 & HB)] HW] ST V1 V2 V3 OUT.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi. unfold mrd in *. rewrite <- (HB i Hi).
    destruct (OUT (A + Z.of_nat i) ltac:(rewrite L in Hi; lia)) as [O1 O2].
    rewrite (RF (A + Z.of_nat i) ltac:(destruct ST as (S0 & S1 & _); rewrite L in Hi; lia) O1 O2). reflexivity.
  - eapply stk_wr_at; [exact ST| lia| lia].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac artcells_destruct H := unfold ARTCELLS in H; decompose [and ex] H; clear H.
End RTW_m_lib3.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_m_i1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AMALLOC_ICPT : Z := 0x54698.
Definition I1_DEPTH : Z := 2128 + 32.

(* [comment removed for export] *)
Lemma c8_zero_c44 : forall m a, rw_cells bsegs m a [C8 (wz 0)] -> rw_cells bsegs m a [C4 (wz 0); C4 (wz 0)].
Proof.
  intros m a [[Hwf HB] HW]. split; [split; [cbn; tauto|]| exact HW].
  cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact HB.
Qed.

Lemma wr_at_wmono : forall m m' a n, wr_at bsegs m a n -> wmono bsegs m m' -> wr_at bsegs m' a n.
Proof. intros m m' a n (H0 & H1 & HW) WM. split; [exact H0|]. split; [exact H1|]. intros i Hi. apply WM, HW, Hi. Qed.

Definition i1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (g8 : list byte),
    ms' = MS (mkR (wz 0x547bc) (wz (bv_unsigned sp + -2128)) gp tp t0' t1' t2'
                  sp (wz n) (wz (bv_unsigned sp + -2128)) (wz PC0_MALLOC) sp (wz 0) (wz 1)
                  (wz TRACE_MAX_LEN) a6' a7'
                  (wz PC0_MALLOC) (wz 1) (wz (bv_unsigned sp + -2128)) (wz (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (wz AUNWIND_IMPL) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C4 (wz 0); C4 (wz 0)]
    /\ stk bsegs m' (bv_unsigned sp + -2112) (bv_unsigned sp + -72)
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 g8]
    /\ rw_cells bsegs m' (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section I1.
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.

Lemma malloc_i1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (n lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m -> a0 = wz n -> 0 <= n < 2^32 ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + I1_DEPTH <= bv_unsigned sp ->
  evt bsegs (i1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz AMALLOC) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HR WF MI -> Hn ST HCL LO. unfold i1_post.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof HR as HR0.
  (* [comment removed for export] *)
  pose proof (rr_consts st m HR) as HC0. (nelim HC0 5%nat; intros _ _ _ HCF _).
  pose proof (cflags_byte m 34 HCF ltac:(lia)) as CF34. change (nth 34 (map zb cflags_bytes) (zb 0)) with (zb 1) in CF34.
  change (cells_at bsegs m (A_CFLAGS + Z.of_nat 34) [C1 (zb 1)]) with (ro_cells bsegs m 0x13b50a [C1 (zb 1)]) in CF34. clear HCF.
  pose proof (rtrep_artcells st m HR) as HA. unfold ARTCELLS in HA.
  (nelim HA 12%nat; intros _ _ _ _ _ _ _ _ _ _ GOTCF _).
  change (cells_at bsegs m 0xa16f0 [C8 (Z_to_bv 64 0x13b4e8)]) with (ro_cells bsegs m 0xa16f0 [C8 (Z_to_bv 64 0x13b4e8)]) in GOTCF.
  unfold AMALLOC, I1_DEPTH, PC0_MALLOC, AUNWIND_IMPL, TRACE_MAX_LEN in *. leaf_prep.
  (* [comment removed for export] *)
  carve_frame 56%nat ST.
  destruct (stk_split bsegs m lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [STlo SThi].
  destruct (stk_split bsegs m _ (bv_unsigned sp + -2112) _ SThi ltac:(lia)) as [STobj SThi2].
  (nelim (stk_carve bsegs m _ _ 16 STobj ltac:(lia)) 3%nat; intros _ jo OBJ).
  replace (bv_unsigned sp + -2112 - Z.of_nat 16) with (bv_unsigned sp + -2128) in OBJ by lia.
  destruct (stk_split bsegs m _ (bv_unsigned sp + -72) _ SThi2 ltac:(lia)) as [STbuf STbp].
  (nelim (stk_carve bsegs m _ _ 16 STbp ltac:(lia)) 3%nat; intros _ jb BP).
  replace (bv_unsigned sp + -56 - Z.of_nat 16) with (bv_unsigned sp + -72) in BP by lia.
  clear SThi STobj SThi2 STbp ST. rename STlo into ST.
  lstep. (* [comment removed for export] *)
  do 8 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  call try_asan_init_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz 1 |- _ => cbv beta delta [wz] in H; subst x end.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  call get_malloc_ctx_size_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz _ |- _ => cbv beta delta [wz] in H; unfold TRACE_MAX_LEN in H; subst x end.
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  call get_current_pc_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = Z_to_bv 64 _ |- _ => subst x end.
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  call get_malloc_ctx_size_proof; [exact HR1 | eassumption | intros; discriminate | rewrite ?unsigned_lit by lia; exact ST | idtac; lia | rewrite ?unsigned_lit by lia; lia | ].
  clear HR1. restk. rewrite ?unsigned_lit in ST by lia.
  match goal with H : ?x = wz _ |- _ => cbv beta delta [wz] in H; unfold TRACE_MAX_LEN in H; subst x end.
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  change (bv_unsigned (zb 1)) with 1.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -72) _ |- _ =>
    change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64) in H;
    rewrite Z.land_comm, Z.land_ones, Z.mod_small, Z_to_bv_bv_unsigned in H by lia; rename H into BP' end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) [C8 _; C8 _] |- _ =>
    pose proof (proj1 (rw_cells_app _ _ [C8 _] [C8 _]) H) as [OB1 OB2]; clear H;
    cbn [cells_size Cells.csize Nat.add] in OB2; apply c8_zero_c44 in OB2;
    pose proof (proj2 (rw_cells_app _ _ [C8 _] [C4 _; C4 _]) (conj OB1 OB2)) as OBJ' end.
  apply evt_done. nexists 9%nat. eexists. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption; try eassumption.
Qed.
End I1.


End CeilWrap.
End RTW_m_i1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_m_at1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a6 RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma icpt_cells_high : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> icpt_cells m -> icpt_cells m'.
Proof.
  intros W m m' MU HW IC. eapply icpt_cells_munch; [exact IC| exact MU|].
  unfold icpt_cell_ivs. repeat constructor; cbn [fst snd]; apply (disjoint_high_img W _ _ HW); unfold AIMG_HI; lia.
Qed.
Lemma poison_cells_high : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> poison_cells m -> poison_cells m'.
Proof.
  intros W m m' MU HW PC. eapply poison_cells_munch; [exact PC| exact MU|].
  unfold poison_cell_ivs. repeat constructor; cbn [fst snd]; apply (disjoint_high_img W _ _ HW); unfold AIMG_HI; lia.
Qed.
Lemma memtoshadow_cells_high : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W ->
  memtoshadow_cells m -> memtoshadow_cells m'.
Proof.
  intros W m m' MU HW nelH_; (nelim nelH_ 10%nat; intros K1 K2 K3 K4 K5 K6 K7 K8 K9 K10). unfold memtoshadow_cells.
  repeat match goal with |- _ /\ _ => split end;
  (eapply ro_cells_transport; [(cut_on [K1 K2 K3 K4 K5 K6 K7 K8 K9 K10] eassumption)| exact MU| apply disjoint_high_img; [exact HW| unfold AIMG_HI; cbn; lia]]).
Qed.
Lemma leafc_out : forall st W m m', munch W m m' -> wmono bsegs m m' ->   (* [comment removed for export] *)
  Forall (fun iv : Z * Z => (snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= st_ctx st + 152 \/ st_ctx st + 160 <= fst iv)) W ->
  leafc st m -> leafc st m'.
Proof.
  intros st W m m' MU WM HW LC. eapply leafc_munch; [exact MU| exact WM| | exact LC].
  intros lo hi a b Hin Hab. pose proof (proj1 (Forall_forall _ _) HW _ Hin) as [X Y]. cbn [fst snd] in X, Y.
  unfold leafc_ivs in Hab. cbn in Hab. unfold AIMG_LO, AIMG_HI in X.
  destruct Hab as [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; injection E as E1 E2; subst a b; lia.
Qed.
Lemma leafc_high : forall st W m m', munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => AIMG_HI <= fst iv /\ (snd iv <= st_ctx st + 152 \/ st_ctx st + 160 <= fst iv)) W ->
  leafc st m -> leafc st m'.
Proof.
  intros st W m m' MU WM HW. apply (leafc_out st W m m' MU WM). eapply Forall_impl; [| exact HW]. intros iv [X Y]. split; [right; exact X| exact Y].
Qed.

(* [comment removed for export] *)
Lemma sh_live_pieces : forall n q rem, bprim n = true -> usz n = 8 * q + rem -> 0 <= rem < 8 -> 0 <= q ->
  zcells (sh_live n) =
    zcells (zrep SV_HEAP_LEFT_RZ (rz_size n / 8))
    ++ (zcells (zrep 0 q) ++ (if rem =? 0 then [] else [C1 (zb rem)]))
    ++ zcells (zrep SV_HEAP_LEFT_RZ (csize (pclass n) / 8 - rz_size n / 8 - (usz n + 7) / 8)).
Proof.
  intros n q rem HP HU HR HQ. unfold sh_live, sh_chunk, sh_left, sh_tot. rewrite HP.
  (nelimp (prim_facts n HP) 5%nat; intros _ _ _ _ ->). unfold pslot.
  rewrite !zcells_app'. f_equal. f_equal.
  - unfold shadow_enc. rewrite HU. replace ((8 * q + rem) / 8) with q by (Z.div_mod_to_equations; lia).
    replace ((8 * q + rem) mod 8) with rem by (Z.div_mod_to_equations; lia).
    rewrite zcells_app'. unfold zrep. f_equal. destruct (Z.eqb_spec rem 0); reflexivity.
  - f_equal. f_equal. unfold zlen. rewrite rt_shadow_enc_length by lia. reflexivity.
Qed.

Section AT1.
Hypothesis poison_shadow_proof : poison_shadow_spec.

(* [comment removed for export] *)
Lemma alloc_t1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n r id b1 lo q rem : Z) (j1 j8 : list byte),
  mem_inv bsegs m -> icpt_cells m -> poison_cells m -> memtoshadow_cells m -> leafc st m ->
  a0 = wz id -> s0 = wz 1 -> s1 = wz (usz n) -> s2 = wz r -> s4 = wz (r + rz_size n) -> s5 = wz (r + rz_size n + -16) -> s8 = wz 0 ->
  0 <= n < 2^32 -> bprim n = true -> 0 <= id < 2^32 -> usz n = 8 * q + rem -> 0 <= rem < 8 ->
  KHIGHMEM_BEG <= r -> r + csize (pclass n) + 4096 <= alloc_ceiling -> r mod 32 = 0 ->
  (st_ctx st + 160 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_ctx st) -> st_ctx st + 160 <= alloc_ceiling -> (r + csize (pclass n) <= st_ctx st \/ st_ctx st + 160 <= r) ->   (* [comment removed for export] *)
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells bsegs m (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); CB 8 j8] ->
  rw_cells bsegs m (SH r) (zcells (sh_avail (pclass n))) ->
  evt bsegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz 0x3246c) fc None m' (seg_rom bsegs)
      /\ munch [(SH r + rz_size n / 8, SH r + rz_size n / 8 + (usz n + 7) / 8); (r + rz_size n + -8, r + rz_size n);
                (bv_unsigned sp - 1024, bv_unsigned sp)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]
      /\ rw_cells bsegs m' (SH r) (zcells (sh_live n)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x322cc) fc None m (seg_rom bsegs)).
Proof.
  intros until j8. intros MI IC PC MC LC -> -> -> -> -> -> -> Hn HP Hid HU HR R1 R2 R3 X1 X2 X3 ST HCL LO SPH HDR SHA.
  (nelimp (prim_facts n HP) 5%nat; intros PCL URZ P32 PM32 ASZ). unfold pslot in *.
  set (c := pclass n) in *.
  pose proof (rz_size_range n) as [RZ RZ16]. pose proof (csize_pos c ltac:(lia)) as CSP.
  assert (U1 : 1 <= usz n) by (unfold usz; lia).
  (nelimp (usz_le_rounded8 n) 3%nat; intros V1 V2 V3).
  assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in HP; apply Z.leb_le in HP; exact HP).
  assert (UMAX : usz n <= 65536) by (unfold needed0 in NP; lia).
  assert (NDp : needed n = needed0 n) by (unfold needed; unfold bprim in HP; rewrite HP; reflexivity).
  assert (NCS : needed n <= csize c).
  { rewrite NDp. pose proof (needed0_range n Hn) as NR. destruct (class_ok (needed0 n) ltac:(lia)) as [C1 _]. subst c. unfold pclass. exact C1. }
  set (rz8 := rz_size n / 8) in *. set (cs8 := csize c / 8) in *. set (shn := (usz n + 7) / 8) in *.
  assert (RZ8 : rz_size n = 8 * rz8) by (subst rz8; Z.div_mod_to_equations; lia).
  assert (CS8 : csize c = 8 * cs8) by (subst cs8; Z.div_mod_to_equations; lia).
  assert (SHN : shn = q + (if rem =? 0 then 0 else 1)) by (subst shn; rewrite HU; destruct (Z.eqb_spec rem 0); Z.div_mod_to_equations; lia).
  assert (Q0 : 0 <= q) by lia.
  assert (QE : usz n / 8 = q) by (rewrite HU; Z.div_mod_to_equations; lia).
  assert (RE : usz n mod 8 = rem) by (rewrite HU; Z.div_mod_to_equations; lia).
  assert (FIT : rz8 + shn <= cs8) by (destruct (Z.eqb_spec rem 0); lia).
  assert (UB8 : (r + rz_size n) mod 8 = 0) by (rewrite RZ8; Z.div_mod_to_equations; lia).
  assert (SHUB : SH (r + rz_size n) = SH r + rz8) by (rewrite RZ8, rt_SH_aligned_add by (Z.div_mod_to_equations; lia); f_equal; Z.div_mod_to_equations; lia).
  assert (SHUQ : SH ((r + rz_size n) + usz n / 8 * 8) = SH (r + rz_size n) + q) by (rewrite QE, rt_SH_aligned_add by exact UB8; f_equal; Z.div_mod_to_equations; lia).
  pose proof (rt_SH_mono KHIGHMEM_BEG r ltac:(lia)) as SB1. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in SB1.
  pose proof (rt_SH_mono (r + csize c) (@CEIL ACEIL) ltac:(idtac; unfold CEIL; lia)) as SB2. rewrite SH_CEIL in SB2.
  rewrite (rt_SH_aligned_add r (csize c)) in SB2 by (Z.div_mod_to_equations; lia).
  change (csize c / 8) with cs8 in SB2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold KHIGHMEM_BEG, AIMG_HI in *. idtac.
  pose proof (munch_refl [(SH r + rz8, SH r + rz8 + shn); ((r + rz_size n) + -8, (r + rz_size n)); (bv_unsigned sp - 1024, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (HWH : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(SH r + rz8, SH r + rz8 + shn); ((r + rz_size n) + -8, (r + rz_size n)); (bv_unsigned sp - 1024, bv_unsigned sp)]).
  { repeat constructor; cbn [fst]; unfold AIMG_HI; lia. }
  assert (HWL : Forall (fun iv : Z * Z => AIMG_HI <= fst iv /\ (snd iv <= st_ctx st + 152 \/ st_ctx st + 160 <= fst iv))
                       [(SH r + rz8, SH r + rz8 + shn); ((r + rz_size n) + -8, (r + rz_size n)); (bv_unsigned sp - 1024, bv_unsigned sp)]).
  { unfold AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (cut_on [R1 R3 X1 X3 URZ P32 RZ CSP U1 V2 RZ8 CS8 FIT SB1 SB2 X2 HCL LO] blia). }
  (* [comment removed for export] *)
  pose proof (avail_shadow_head m (SH r) c ltac:(lia) SHA) as SH1.
  (nelim (avail_shadow_split m (SH r) c rz8 shn SHA ltac:(lia) ltac:(lia) ltac:(lia)) 3%nat; intros SHL SHM SHT).
  change (csize c / 8) with cs8 in SHT. clear SHA.
  apply zcells_zrep_to_CB in SHL; [| lia]. apply zcells_zrep_to_CB in SHT; [| lia]. rewrite <- SHUB in SHM, SHT.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_a4p_spec with (n := n) (r := r) (id := id);
    [ exact MI| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn| exact Hid| unfold KHIGHMEM_BEG, AIMG_HI; lia
    | idtac; lia
    | Z.div_mod_to_equations; lia| exact HDR
    | destruct IC as ((I1 & I2) & _); exact I1| destruct IC as ((I1 & I2) & _); exact I2| exact SH1 ]) ltac:(clear HDR).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : rw_cells _ _ ((r + rz_size n) + -16) _ |- _ => rename H into HDR1 end.
  match goal with H : rw_cells _ _ (SH (r + rz_size n)) [CB (Z.to_nat shn) _] |- _ => rename H into SHM1 end.
  match goal with H : rw_cells _ _ (SH r) [CB (Z.to_nat rz8) _] |- _ => rename H into SHL1 end.
  match goal with H : rw_cells _ _ (SH (r + rz_size n) + shn) [CB _ _] |- _ => rename H into SHT1 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST5 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  (* [comment removed for export] *)
  apply CB_to_zcells_zrep in SHM1; [| lia]. rewrite SHN, zrep_split, zcells_app' in SHM1 by (destruct (Z.eqb_spec rem 0); lia).
  apply (proj1 (rw_cells_app m5 _ _ _)) in SHM1 as [SHMq SHMp]. rewrite zcells_size_Z in SHMp. unfold zlen in SHMp. rewrite zrep_length in SHMp by lia.
  apply zcells_zrep_to_CB in SHMq; [| lia].
  (* [comment removed for export] *)
  assert (FIN : forall mf, rem <> 0 ->
     rw_cells bsegs mf (SH r) [CB (Z.to_nat rz8) (repeat (zb SV_HEAP_LEFT_RZ) (Z.to_nat rz8))] ->
     rw_cells bsegs mf (SH (r + rz_size n)) [CB (Z.to_nat q) (repeat (Z_to_bv 8 0) (Z.to_nat q))] ->
     rw_cells bsegs mf (SH (r + rz_size n) + q) [C1 (zb rem)] ->
     rw_cells bsegs mf (SH (r + rz_size n) + shn) [CB (Z.to_nat (cs8 - rz8 - shn)) (repeat (zb SV_HEAP_LEFT_RZ) (Z.to_nat (cs8 - rz8 - shn)))] ->
     rw_cells bsegs mf (SH r) (zcells (sh_live n))).
  { intros mf Hrem KL KZ KP KT.
    rewrite (sh_live_pieces n q rem HP HU HR Q0). change (rz_size n / 8) with rz8. change (csize (pclass n) / 8) with cs8. change ((usz n + 7) / 8) with shn.
    replace (rem =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply (proj2 (rw_cells_app _ _ _ _)). split; [apply CB_to_zcells_zrep; [lia| exact KL]|]. rewrite zcells_size_Z. unfold zlen. rewrite zrep_length by lia. rewrite <- SHUB.
    apply (proj2 (rw_cells_app _ _ _ _)). split.
    - apply (proj2 (rw_cells_app _ _ _ _)). split; [apply CB_to_zcells_zrep; [lia| exact KZ]|].
      rewrite zcells_size_Z. unfold zlen. rewrite zrep_length by lia. exact KP.
    - rewrite cells_size_app, Nat2Z.inj_add, zcells_size_Z. unfold zlen. rewrite zrep_length by lia. cbn [cells_size Cells.csize Nat.add]. change (Z.of_nat 1) with 1.
      replace (SH (r + rz_size n) + (q + 1)) with (SH (r + rz_size n) + shn) by (rewrite SHN; replace (rem =? 0) with false by (symmetry; apply Z.eqb_neq; lia); lia).
      apply CB_to_zcells_zrep; [lia| exact KT]. }
  assert (FIN0 : forall mf, rem = 0 ->
     rw_cells bsegs mf (SH r) [CB (Z.to_nat rz8) (repeat (zb SV_HEAP_LEFT_RZ) (Z.to_nat rz8))] ->
     rw_cells bsegs mf (SH (r + rz_size n)) [CB (Z.to_nat q) (repeat (Z_to_bv 8 0) (Z.to_nat q))] ->
     rw_cells bsegs mf (SH (r + rz_size n) + shn) [CB (Z.to_nat (cs8 - rz8 - shn)) (repeat (zb SV_HEAP_LEFT_RZ) (Z.to_nat (cs8 - rz8 - shn)))] ->
     rw_cells bsegs mf (SH r) (zcells (sh_live n))).
  { intros mf Hrem KL KZ KT.
    rewrite (sh_live_pieces n q rem HP HU HR Q0). change (rz_size n / 8) with rz8. change (csize (pclass n) / 8) with cs8. change ((usz n + 7) / 8) with shn.
    replace (rem =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite app_nil_r.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [apply CB_to_zcells_zrep; [lia| exact KL]|]. rewrite zcells_size_Z. unfold zlen. rewrite zrep_length by lia. rewrite <- SHUB.
    apply (proj2 (rw_cells_app _ _ _ _)). split; [apply CB_to_zcells_zrep; [lia| exact KZ]|].
    rewrite zcells_size_Z. unfold zlen. rewrite zrep_length by lia.
    replace (SH (r + rz_size n) + q) with (SH (r + rz_size n) + shn) by (rewrite SHN; replace (rem =? 0) with true by (symmetry; apply Z.eqb_eq; lia); lia).
    apply CB_to_zcells_zrep; [lia| exact KT]. }
  (* [comment removed for export] *)
  destruct (Z.eq_dec q 0) as [Qz|Qnz].
  - lstep; if_lia. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lstep; if_lia.
    assert (LC5 : leafc st m5) by (eapply leafc_high; [exact MU| exact WM| exact HWL| exact LC]).
    assert (MC5 : memtoshadow_cells m5) by (eapply memtoshadow_cells_high; [exact MU| exact HWH| exact MC]).
    assert (SHP : rw_cells bsegs m5 (SH ((r + rz_size n) + usz n / 8 * 8)) [C1 (zb SV_HEAP_LEFT_RZ)]).
    { rewrite SHUQ. replace (if rem =? 0 then 0 else 1) with 1 in SHMp by (destruct (Z.eqb_spec rem 0); lia). rewrite zrep_one in SHMp. exact SHMp. }
    clear SHMp.
    sepM. callxp ltac:(eapply alloc_a5_spec with (st := st) (n := n) (ub := r + rz_size n) (lo := lo);
      [ exact LC5| exact MI1| exact MC5| reflexivity| reflexivity| reflexivity| exact Hn| lia| apply ablk_high; [unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia]| idtac; lia| exact UB8
      | exact ST5| idtac; lia| lia| exact SHP ]) ltac:(clear SHP ST5).
    cbv beta delta [wz] in *.
    match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    match goal with H : rw_cells _ _ (SH ((r + rz_size n) + usz n / 8 * 8)) _ |- _ => rename H into SHP2 end.
    rewrite SHUQ, RE in SHP2.
    apply evt_done. nexists 18%nat. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [assumption|]. split; [assumption|].
    eapply FIN; [lia| assumption| | exact SHP2| assumption].
    replace (repeat (Z_to_bv 8 0) (Z.to_nat q)) with (repeat (zb SV_HEAP_LEFT_RZ) (Z.to_nat q)) by (rewrite Qz; reflexivity). assumption.
  - lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    assert (IC5 : icpt_cells m5) by (eapply icpt_cells_high; [exact MU| exact HWH| exact IC]).
    assert (PC5 : poison_cells m5) by (eapply poison_cells_high; [exact MU| exact HWH| exact PC]).
    apply zcells_zrep_to_CB in SHMp; [| destruct (Z.eqb_spec rem 0); lia].
    sepM. callxp ltac:(eapply poison_shadow_proof with (a := (r + rz_size n)) (sz := usz n / 8 * 8) (v := 0) (lo := lo);
      [ exact IC5| exact PC5| exact MI1| exact ST5| idtac; lia| unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity
      | exact UB8| rewrite QE; apply Z_mod_mult| lia
      | right; unfold highmem_range, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; lia| lia
      | intros _; rewrite QE, Z.div_mul by lia; lia
      | rewrite QE, Z.div_mul by lia; exact SHMq ])
      ltac:(unfold poison_shadow_post, APOISON_STACK; clear SHMq ST5).
    cbv beta delta [wz] in *.
    match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    match goal with H : rw_cells _ _ (SH (r + rz_size n)) [CB _ (repeat (Z_to_bv 8 0) _)] |- _ => rename H into SHZ end.
    rewrite QE, Z.div_mul in SHZ by lia.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST6 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : rw_cells _ m6 (SH (r + rz_size n) + q) [CB _ _] |- _ => rename H into SHMp6 end.
    (* [comment removed for export] *)
    destruct (Z.eq_dec rem 0) as [Rz|Rnz].
    + lstep; if_lia. (* [comment removed for export] *)
      apply evt_done. nexists 18%nat. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [assumption|]. split; [assumption|].
      eapply FIN0; [lia| assumption| exact SHZ| assumption].
    + lstep; if_lia. (* [comment removed for export] *)
      assert (LC6 : leafc st m6) by (eapply leafc_high; [exact MU| exact WM| exact HWL| exact LC]).
      assert (MC6 : memtoshadow_cells m6) by (eapply memtoshadow_cells_high; [exact MU| exact HWH| exact MC]).
      assert (SHP : rw_cells bsegs m6 (SH ((r + rz_size n) + usz n / 8 * 8)) [C1 (zb SV_HEAP_LEFT_RZ)]).
      { rewrite SHUQ. replace (if rem =? 0 then 0 else 1) with 1 in SHMp6 by (destruct (Z.eqb_spec rem 0); lia).
        apply CB_to_zcells_zrep in SHMp6; [| lia]. rewrite zrep_one in SHMp6. exact SHMp6. }
      clear SHMp6.
      sepM. callxp ltac:(eapply alloc_a5_spec with (st := st) (n := n) (ub := r + rz_size n) (lo := lo);
        [ exact LC6| exact MI2| exact MC6| reflexivity| reflexivity| reflexivity| exact Hn| lia| apply ablk_high; [unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia]| idtac; lia| exact UB8
        | exact ST6| idtac; lia| lia| exact SHP ]) ltac:(clear SHP ST6).
      cbv beta delta [wz] in *.
      match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
      match goal with H : rw_cells _ _ (SH ((r + rz_size n) + usz n / 8 * 8)) _ |- _ => rename H into SHP2 end.
      rewrite SHUQ, RE in SHP2.
      apply evt_done. nexists 18%nat. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [assumption|]. split; [assumption|].
      eapply FIN; [lia| assumption| assumption| exact SHP2| assumption].
Qed.
End AT1.


End CeilWrap.
End RTW_m_at1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_pop.
Import RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz RTW_p_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition wf_pd (st : rtstate) : Prop := forall c, 1 <= c < KNUMCLASSES ->
  (r_mapped (rg st c) < r_allocated (rg st c) + csize c
   \/ (r_allocated (rg st c) + 2^18 <= r_mapped (rg st c) /\ r_mapped (rg st c) < r_allocated (rg st c) + 2^18 + csize c))
  /\ (r_exhausted (rg st c) = true -> r_mapped (rg st c) = KFREEARRAY_OFF /\ r_mapped (rg st c) < r_allocated (rg st c) + csize c).

(* [comment removed for export] *)
Definition newc (c nc Nv : Z) : list Z := map (fun t => chunk_cptr c (nc + Nv - 1 - Z.of_nat t)) (seq 0 (Z.to_nat Nv)).
Lemma newc_length : forall c nc Nv, 0 <= Nv -> zlen (newc c nc Nv) = Nv.
Proof. intros. unfold newc, zlen. rewrite length_map, length_seq. lia. Qed.

Lemma nthz_app_l : forall (a b : list Z) i d, 0 <= i < zlen a -> nthz (a ++ b) i d = nthz a i d.
Proof. intros a b i d Hi. unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. apply app_nth1. lia. Qed.
Lemma nthz_app_r : forall (a b : list Z) i d, zlen a <= i -> nthz (a ++ b) i d = nthz b (i - zlen a) d.
Proof.
  intros a b i d Hi. pose proof (zlen_nonneg a). unfold nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. destruct (Z.ltb_spec0 (i - Z.of_nat (length a)) 0); [lia|].
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma nthz_firstn : forall (l : list Z) k i d, 0 <= i < Z.of_nat k -> nthz (firstn k l) i d = nthz l i d.
Proof.
  intros l k i d Hi. unfold nthz. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [LT|GE].
  - rewrite nth_firstn || (rewrite <- (firstn_skipn k l) at 2; rewrite app_nth1 by (rewrite length_firstn; lia)); first [reflexivity| destruct (Nat.ltb_spec0 (Z.to_nat i) k); [reflexivity| lia]].
  - rewrite !nth_overflow; [reflexivity| lia| rewrite length_firstn; lia].
Qed.
Lemma nthz_skipn : forall (l : list Z) k i d, 0 <= i -> nthz (skipn k l) i d = nthz l (Z.of_nat k + i) d.
Proof.
  intros l k i d Hi. unfold nthz. destruct (Z.ltb_spec0 i 0); [lia|]. destruct (Z.ltb_spec0 (Z.of_nat k + i) 0); [lia|].
  rewrite nth_skipn. f_equal. lia.
Qed.
Lemma map_seq_nth : forall (f : nat -> Z) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof. intros f n i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia). rewrite map_nth, seq_nth by lia. reflexivity. Qed.
Lemma nthz_newc : forall c nc Nv t, 0 <= t < Nv -> nthz (newc c nc Nv) t 0 = chunk_cptr c (nc + Nv - 1 - t).
Proof.
  intros c nc Nv t Ht. unfold nthz, newc. destruct (Z.ltb_spec0 t 0); [lia|].
  rewrite map_seq_nth by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Section PT.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Variables (cls n Nv nm : Z) (um fm pop : bool).
Let r := rg st cls.
Let S := csize cls.
Let nf := num_freed st cls.
Let L := r_fa r ++ newc cls (ncarved st cls) Nv.
Let base := nf + Nv - n.
Definition r_new : region_st :=
  mkRegion (r_allocated r + Nv * S) (r_mapped r + (if um then 262144 else 0)) (if fm then nm else r_mapped_fa r)
           (if pop then false else r_exhausted r) (firstn (Z.to_nat base) L).
Let cache' := skipn (Z.to_nat base) L.
Let st' := mkRT a1 a2 a3 (updz a4 cls r_new) true (updz a6 cls cache') a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.

Hypothesis WF : RTWF st.
Hypothesis WX : wf_pd st.
Hypothesis Hc : 1 <= cls <= 30.
Hypothesis HC0 : cch st cls = [].
Hypothesis Hn : n = nrefill cls.
Hypothesis HNv : 0 <= Nv /\ n <= nf + Nv.
(* [comment removed for export] *)
Hypothesis HPOP : pop = true ->
  nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
  /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
  /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144.
Hypothesis HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false.

Lemma Hcls : 0 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma Hc1 : 1 <= cls < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.
Lemma WC : wf_class st cls. Proof. exact (wf_class_ok st WF cls Hcls). Qed.
Lemma ES : S = csize cls. Proof. reflexivity. Qed.
Lemma Er : r = rg st cls. Proof. reflexivity. Qed.
Lemma Enf : nf = zlen (r_fa r). Proof. reflexivity. Qed.
Lemma EL : L = r_fa r ++ newc cls (ncarved st cls) Nv. Proof. reflexivity. Qed.
Lemma Ebase : base = nf + Nv - n. Proof. reflexivity. Qed.
Lemma csize_le64k : forall c, 1 <= c <= 30 -> csize c <= 65536.
Proof.
  intros c Hc'.
  assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct H as [->|H]; [vm_compute; discriminate|]). subst. vm_compute. discriminate.
Qed.
Lemma Spos : 32 <= S <= 65536.
Proof. rewrite ES. split; [apply csize_pos; lia| apply csize_le64k; lia]. Qed.
#[using="HNv Hn Hc base nf r um Nv st b5 b4 b3 b2 b1 a23 a22 a21 a20 a19 a18 a17 a16 a15 a14 a13 a12 a11 a10 a9 a8 a7 a6 a5 a4 a3 a2 a1"] Lemma nrange : 1 <= n <= 8 /\ n * S <= 65536.
Proof.
  rewrite Hn, ES. unfold nrefill, cmaxcount, clampz. pose proof (csize_pos cls ltac:(lia)) as SP. pose proof (csize_le64k cls Hc) as SL.
  pose proof (Z.le_max_l 1 (Z.min 8 (1024 / csize cls))) as M1. pose proof (Z.le_min_l 8 (1024 / csize cls)) as M2.
  pose proof (Z.le_min_r 8 (1024 / csize cls)) as M3.
  rewrite (Z.mul_comm 2), Z.div_mul by lia.
  assert (D : csize cls * (1024 / csize cls) <= 1024) by (apply Z.mul_div_le; lia).
  assert (D0 : 0 <= 1024 / csize cls) by (apply Z.div_pos; lia).
  destruct (Z_le_gt_dec (Z.min 8 (1024 / csize cls)) 1).
  - rewrite Z.max_l by lia. lia.
  - rewrite Z.max_r by lia. split; [lia|]. (cut_on [HNv SP SL M1 M3 D D0 g] nia).
Qed.

Lemma len_regions : length a4 = 32%nat. Proof. exact (wb_len_regions st (wf_base_ok st WF)). Qed.
Lemma len_cache : length a6 = 32%nat. Proof. exact (wb_len_cache st (wf_base_ok st WF)). Qed.

(* [comment removed for export] *)
Lemma rg_same : rg st' cls = r_new.
Proof. unfold rg. cbn [st_regions st']. apply nthz_updz_same. unfold zlen. rewrite len_regions. unfold KNUMCLASSES in *. lia. Qed.
Lemma rg_other : forall c, c <> cls -> rg st' c = rg st c.
Proof. intros c H. unfold rg. cbn [st_regions st st']. apply nthz_updz_other. lia. Qed.
Lemma cch_same : cch st' cls = cache'.
Proof. unfold cch. cbn [st_cache st']. apply nthz_updz_same. unfold zlen. rewrite len_cache. unfold KNUMCLASSES in *. lia. Qed.
Lemma cch_other : forall c, c <> cls -> cch st' c = cch st c.
Proof. intros c H. unfold cch. cbn [st_cache st st']. apply nthz_updz_other. lia. Qed.
Lemma rbeg_same : forall c, rbeg st' c = rbeg st c. Proof. reflexivity. Qed.
Lemma fabeg_same : forall c, fabeg st' c = fabeg st c. Proof. reflexivity. Qed.
Lemma rinfo_same : forall c, rinfo st' c = rinfo st c. Proof. reflexivity. Qed.
Lemma cptr_addr_same : forall c k, cptr_addr st' c k = cptr_addr st c k. Proof. reflexivity. Qed.
Lemma pcaddr_same : forall c, pcaddr st' c = pcaddr st c. Proof. reflexivity. Qed.
Lemma all_blocks_same : all_blocks st' = all_blocks st. Proof. reflexivity. Qed.
Lemma qall_same : qall st' = qall st. Proof. reflexivity. Qed.
Lemma live_same : forall c, live_cptrs st' c = live_cptrs st c. Proof. reflexivity. Qed.
Lemma quar_same : forall c, quar_cptrs st' c = quar_cptrs st c. Proof. reflexivity. Qed.
Lemma qpend_same : forall c, qpend_cptrs st' c = qpend_cptrs st c. Proof. reflexivity. Qed.
Lemma batch_same : forall c, batch_cptrs st' c = batch_cptrs st c. Proof. reflexivity. Qed.
Lemma apend_same : forall c, apend_cptrs st' c = apend_cptrs st c. Proof. reflexivity. Qed.
Lemma rt_ranges_same : rt_ranges st' = rt_ranges st. Proof. reflexivity. Qed.
Lemma rt_loose_same : rt_loose st' = rt_loose st. Proof. reflexivity. Qed.

Lemma ncarved_eq : ncarved st cls * S = r_allocated r.
Proof. rewrite ES, Er. symmetry. exact (wc_alloc_carved st cls WC). Qed.
Lemma ncarved_nonneg : 0 <= ncarved st cls.
Proof. pose proof (wc_alloc_nonneg st cls WC). pose proof ncarved_eq. pose proof Spos. rewrite <- Er in *. nia. Qed.
Lemma ncarved_same' : ncarved st' cls = ncarved st cls + Nv.
Proof.
  unfold ncarved. rewrite rg_same. cbn [r_allocated r_new]. pose proof ncarved_eq as E. pose proof (csize_pos cls ltac:(lia)).
  rewrite <- E. change (csize cls) with S. replace (ncarved st cls * S + Nv * S) with ((ncarved st cls + Nv) * S) by lia.
  rewrite Z.div_mul by (rewrite ES; lia). reflexivity.
Qed.
Lemma ncarved_other : forall c, c <> cls -> ncarved st' c = ncarved st c.
Proof. intros c H. unfold ncarved. rewrite rg_other by exact H. reflexivity. Qed.
Lemma carved_mono : forall c k, carved_cptr st c k -> carved_cptr st' c k.
Proof.
  intros c k nelH_; (nelim nelH_ 3%nat; intros j Hj E). exists j. split; [| exact E]. destruct (Z.eq_dec c cls) as [->|NE]; [rewrite ncarved_same'; lia| rewrite ncarved_other by exact NE; exact Hj].
Qed.
Lemma num_freed_same' : num_freed st' cls = base.
Proof.
  unfold num_freed. rewrite rg_same. cbn [r_fa r_new]. unfold zlen. rewrite length_firstn.
  assert (LL : zlen L = nf + Nv) by (rewrite EL, zlen_app, newc_length, Enf by lia; reflexivity).
  unfold zlen in LL. rewrite Ebase. pose proof nrange. lia.
Qed.
Lemma avail_same' : avail_cptrs st' cls = L.
Proof. unfold avail_cptrs. rewrite rg_same, cch_same. cbn [r_fa r_new]. apply firstn_skipn. Qed.
Lemma avail_other : forall c, c <> cls -> avail_cptrs st' c = avail_cptrs st c.
Proof. intros c H. unfold avail_cptrs. rewrite rg_other, cch_other by exact H. reflexivity. Qed.
Lemma used_same' : used_cptrs st' cls = L ++ (live_cptrs st cls ++ quar_cptrs st cls ++ qpend_cptrs st cls ++ batch_cptrs st cls ++ apend_cptrs st cls).
Proof. unfold used_cptrs. rewrite avail_same'. reflexivity. Qed.
Lemma used_old : used_cptrs st cls = r_fa r ++ (live_cptrs st cls ++ quar_cptrs st cls ++ qpend_cptrs st cls ++ batch_cptrs st cls ++ apend_cptrs st cls).
Proof. unfold used_cptrs, avail_cptrs. rewrite Er. rewrite HC0, app_nil_r. reflexivity. Qed.
Lemma used_other : forall c, c <> cls -> used_cptrs st' c = used_cptrs st c.
Proof. intros c H. unfold used_cptrs. rewrite avail_other by exact H. reflexivity. Qed.
Lemma navail_same' : navail st' cls = nf + Nv.
Proof. unfold navail. rewrite avail_same', EL, zlen_app, newc_length, Enf by lia. reflexivity. Qed.
Lemma navail_old : navail st cls = nf.
Proof. unfold navail, avail_cptrs. rewrite Enf, Er, HC0, app_nil_r. reflexivity. Qed.
Lemma navail_other : forall c, c <> cls -> navail st' c = navail st c.
Proof. intros c H. unfold navail. rewrite avail_other by exact H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma chunk_cptr_inj : forall j j', chunk_cptr cls j = chunk_cptr cls j' -> j = j'.
Proof.
  intros j j' E. pose proof (chunk_cptr_eq cls j ltac:(lia)) as E1. pose proof (chunk_cptr_eq cls j' ltac:(lia)) as E2.
  pose proof (csize_pos cls ltac:(lia)). rewrite E in E1. rewrite E1 in E2. nia.
Qed.
Lemma newc_In : forall k, In k (newc cls (ncarved st cls) Nv) <-> exists j, ncarved st cls <= j < ncarved st cls + Nv /\ k = chunk_cptr cls j.
Proof.
  intros k. unfold newc. rewrite in_map_iff. split.
  - intros nelH_; (nelim nelH_ 3%nat; intros t <- Ht). apply in_seq in Ht. exists (ncarved st cls + Nv - 1 - Z.of_nat t). split; [lia| reflexivity].
  - intros nelH_; (nelim nelH_ 3%nat; intros j Hj ->). exists (Z.to_nat (ncarved st cls + Nv - 1 - j)). split; [f_equal; lia| apply in_seq; lia].
Qed.
Lemma newc_nodup : List.NoDup (newc cls (ncarved st cls) Nv).
Proof.
  unfold newc. apply Finite.Injective_map_NoDup; [| apply seq_NoDup].
  intros x y E. apply chunk_cptr_inj in E. lia.
Qed.

Lemma nodup_app_intro : forall (l1 l2 : list Z), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 N1 N2 D; [exact N2|]. cbn. inversion N1; subst. constructor.
  - rewrite in_app_iff. intros [H|H]; [exact (H1 H)| exact (D a ltac:(left; reflexivity) H)].
  - apply IH; [assumption| assumption|]. intros x Hx Hy. exact (D x ltac:(right; exact Hx) Hy).
Qed.

(* [comment removed for export] *)
Lemma Nv_le : Nv <= 8193 /\ Nv * S <= r_mapped r + (if um then 262144 else 0) - r_allocated r
  /\ (pop = true -> r_mapped r + (if um then 262144 else 0) - r_allocated r - Nv * S < S).
Proof.
  pose proof Spos as SP. pose proof nrange as [NR1 NR2]. destruct (WX cls Hc1) as [DEL EXH]. rewrite <- Er in DEL, EXH.
  pose proof (wc_alloc_mapped st cls WC) as AM. rewrite <- Er in AM. pose proof (zlen_nonneg (r_fa r)) as NF0. rewrite <- Enf in NF0.
  destruct pop.
  - (nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 P6).
    assert (DIV : Nv * S <= r_mapped r + (if um then 262144 else 0) - r_allocated r /\ r_mapped r + (if um then 262144 else 0) - r_allocated r - Nv * S < S).
    { rewrite P2. set (x := r_mapped r + (if um then 262144 else 0) - r_allocated r). clearbody x. clear -SP.
      pose proof (Z.div_mod x S ltac:(lia)). pose proof (Z.mod_pos_bound x S ltac:(lia)). nia. }
    split; [| split; [exact (proj1 DIV)| intros _; exact (proj2 DIV)]].
    assert (QS1 : 1 * S <= (n - nf) * S) by (apply Z.mul_le_mono_nonneg_r; lia). assert (QS2 : (n - nf) * S <= n * S) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (UB : r_mapped r + (if um then 262144 else 0) - r_allocated r < 262144 + S).
    { destruct um.
      - symmetry in P3. apply Z.ltb_lt in P3. lia.
      - symmetry in P3. apply Z.ltb_ge in P3. lia. }
    assert (NS : Nv * S < 262144 + S) by lia. assert (Nv * 32 <= Nv * S) by (apply Z.mul_le_mono_nonneg_l; lia). clear -NS H SP. nia.
  - (nelim (HHAVE eq_refl) 3%nat; intros ENv Eum _). rewrite ENv, Eum. split; [lia|]. split; [lia| intros E; discriminate].
Qed.

(* [comment removed for export] *)
Lemma exh_same : r_exhausted r_new = r_exhausted r.
Proof.
  cbn [r_exhausted r_new]. destruct pop; [| reflexivity].
  (nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 P6). destruct (WX cls Hc1) as [DEL EXH]. rewrite <- Er in DEL, EXH.
  pose proof Spos. pose proof nrange.
  destruct (r_exhausted r) eqn:E; [| reflexivity]. exfalso. destruct (EXH eq_refl) as [M1 M2].
  destruct um.
  - specialize (P4 eq_refl). unfold KFREEARRAY_OFF in *. lia.
  - symmetry in P3. apply Z.ltb_ge in P3. nia.
Qed.
Lemma nexh_same : nexh st' = nexh st.
Proof.
  unfold nexh. cbn [st_regions st st']. rewrite count_exh_updz by (unfold zlen; rewrite len_regions; unfold KNUMCLASSES in *; lia).
  rewrite exh_same. replace (nthz a4 cls region0) with r by reflexivity. lia.
Qed.

Lemma used_perm : Permutation (used_cptrs st' cls) (newc cls (ncarved st cls) Nv ++ used_cptrs st cls).
Proof.
  rewrite used_same', used_old, EL.
  apply (Permutation_trans (Permutation_app_tail _ (Permutation_app_comm (r_fa r) (newc cls (ncarved st cls) Nv)))).
  rewrite <- app_assoc. apply Permutation_refl.
Qed.

Lemma wf_pd_new : wf_pd st'.
Proof.
  intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE]; [| rewrite rg_other by exact NE; exact (WX c Hc')].
  rewrite rg_same, exh_same. unfold r_new. cbn [r_allocated r_mapped r_exhausted].
  (nelimp Nv_le 3%nat; intros NB ND1 ND2). pose proof Spos. pose proof nrange. destruct (WX cls Hc1) as [DEL EXH]. rewrite <- Er in DEL, EXH. change (csize cls) with S in DEL, EXH |- .
  destruct pop.
  - specialize (ND2 eq_refl). split; [left; lia|]. intros E. destruct (EXH E) as [M1 M2]. (nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 P6).
    exfalso. destruct um; [specialize (P4 eq_refl); unfold KFREEARRAY_OFF in *; lia| symmetry in P3; apply Z.ltb_ge in P3; (cut_on [HNv HPOP NB ND1 ND2 H H0 DEL M2 P1 P2 P3] nia)].
  - (nelim (HHAVE eq_refl) 3%nat; intros ENv Eum _). rewrite ENv, Eum in *. rewrite ?Z.add_0_r, ?Z.mul_0_l, ?Z.add_0_r. exact (conj DEL EXH).
Qed.

Lemma RTWF_new : RTWF st'.
Proof.
  pose proof (wf_base_ok st WF) as WB. pose proof Spos as SP. pose proof nrange as [NR1 NR2]. (nelimp Nv_le 3%nat; intros NB ND1 ND2).
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_alloc_nonneg st cls WC) as A0. pose proof (wc_num_freed st cls WC) as NF.
  pose proof (wc_fa_nonneg st cls WC) as F0. pose proof (wc_fa_align st cls WC) as FA. pose proof (wc_fa_max st cls WC) as FM.
  pose proof (wc_mapped_align st cls WC) as MA. pose proof (wc_mapped_max st cls WC) as MM. rewrite <- Er in *.
  unfold num_freed in NF. rewrite <- Er, <- Enf in NF.
  pose proof (zlen_nonneg (r_fa r)) as NF0. rewrite <- Enf in NF0.
  assert (LL : zlen L = nf + Nv) by (rewrite EL, zlen_app, newc_length, Enf by lia; reflexivity).
  constructor.
  - destruct WB; constructor; try assumption.
    + cbn [st_regions st']. rewrite updz_length. assumption.
    + cbn [st_cache st']. rewrite updz_length. assumption.
    + split; [rewrite rg_other by (lia_on Hc HNv wb_sp0 wb_nres SP NR1 ND1 LL); apply (proj1 wb_class0)| rewrite cch_other by (lia_on Hc HNv wb_sp0 wb_nres SP NR1 ND1 LL); apply (proj2 wb_class0)].
    + intros Hu. exfalso. cbn in Hu. discriminate.
    + change (emb_sz st') with (emb_sz st). rewrite nexh_same. exact wb_emb_sz.
  - intros c Hc'. destruct (Z.eq_dec c cls) as [->|NE].
    + constructor; rewrite ?rg_same, ?ncarved_same', ?cch_same, ?num_freed_same'; cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_new].
      * nia.
      * pose proof ncarved_eq. change (csize cls) with S. lia.
      * lia.
      * destruct um; [rewrite Z.add_mod, MA by lia; reflexivity| rewrite Z.add_0_r; exact MA].
      * destruct pop.
        -- (nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 P6). destruct um; [pose proof (P4 eq_refl); lia| rewrite Z.add_0_r; exact MM].
        -- (nelim (HHAVE eq_refl) 3%nat; intros _ Eum _). rewrite Eum, Z.add_0_r. exact MM.
      * destruct fm; [destruct pop; [(nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 ->); apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia| (nelim (HHAVE eq_refl) 3%nat; intros _ _ E); discriminate]| exact F0].
      * destruct fm; [destruct pop; [(nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 ->); change (2^18) with 262144; apply Z_mod_mult| (nelim (HHAVE eq_refl) 3%nat; intros _ _ E); discriminate]| exact FA].
      * destruct fm; [destruct pop; [(nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 ->)| (nelim (HHAVE eq_refl) 3%nat; intros _ _ E); discriminate]| exact FM].
        unfold KFREEARRAY_SIZE. clear -NB NR1 HNv NF0 P1. Z.div_mod_to_equations. nia.
      * (* [comment removed for export] *) rewrite Ebase.
        destruct fm; [destruct pop; [(nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 ->)| (nelim (HHAVE eq_refl) 3%nat; intros _ _ E); discriminate]|].
        -- clear -NR1 HNv NF0. Z.div_mod_to_equations. nia.
        -- destruct pop; [(nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 P6); symmetry in P5; apply Z.ltb_ge in P5; lia| (nelim (HHAVE eq_refl) 3%nat; intros ENv _ _); rewrite ENv; lia].
      * (* [comment removed for export] *)
        assert (LC : zlen cache' = n) by (unfold zlen; unfold cache'; rewrite length_skipn; unfold zlen in LL; rewrite Ebase; lia). rewrite LC.
        rewrite Hn. unfold nrefill. pose proof (cmaxcount_le16 cls).
        assert (0 <= cmaxcount cls) by (unfold cmaxcount, clampz; lia). Z.div_mod_to_equations. lia.
      * intros k Hk. eapply Permutation_in in Hk; [| exact used_perm]. apply in_app_iff in Hk as [Hk|Hk].
        -- apply newc_In in Hk as (j & Hj & ->). exists j. rewrite ncarved_same'. split; [pose proof ncarved_nonneg; lia| reflexivity].
        -- apply carved_mono. exact (wc_used_carved st cls WC k Hk).
      * eapply Permutation_NoDup; [apply Permutation_sym; exact used_perm|]. apply nodup_app_intro; [exact newc_nodup| exact (wc_used_nodup st cls WC)|].
        intros x Hx Hy. apply newc_In in Hx as (j & Hj & ->). (nelim (wc_used_carved st cls WC _ Hy) 3%nat; intros j' Hj' E).
        apply chunk_cptr_inj in E. lia.
      * unfold zlen in *. rewrite (Permutation_length used_perm), length_app. pose proof (wc_used_all st cls WC) as UA. unfold zlen in UA.
        pose proof (newc_length cls (ncarved st cls) Nv ltac:(lia)) as NL. unfold zlen in NL. lia.
      * change (csize cls) with S. pose proof (wc_residue st cls WC) as RS. rewrite <- Er in RS. change (csize cls) with S in RS.
        destruct pop; [specialize (ND2 eq_refl); lia| (nelim (HHAVE eq_refl) 3%nat; intros ENv Eum _); rewrite ENv, Eum; lia].
      * (* [comment removed for export] *) intros _. pose proof (proj1 (wf_pd_new cls Hc1)) as D.
        rewrite ?rg_same in D. cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_new] in D. exact D.
      * (* [comment removed for export] *) pose proof (proj2 (wf_pd_new cls Hc1)) as D.
        rewrite ?rg_same in D. cbn [r_allocated r_mapped r_mapped_fa r_exhausted r_fa r_new] in D. exact D.
    + assert (NFo : num_freed st' c = num_freed st c) by (unfold num_freed; rewrite rg_other by exact NE; reflexivity).
      destruct (wf_class_ok st WF c Hc'); constructor; rewrite ?rg_other, ?ncarved_other, ?cch_other, ?used_other, ?NFo by exact NE; try assumption.
      intros k Hk. apply carved_mono. apply wc_used_carved. exact Hk.
  - destruct (wf_blocks_ok st WF); constructor; assumption.
  - destruct (wf_sec_ok st WF); constructor; assumption.
  - destruct (wf_quar_ok st WF); constructor; try assumption.
    intros b Hb. destruct (wq_batch b Hb) as [C (k & CK & E)]. split; [exact C| exists k; split; [apply carved_mono; exact CK| exact E]].
  - destruct (wf_depot_ok st WF); constructor; assumption.
  - destruct (wf_fs_ok st WF); constructor; assumption.
Qed.


(* [comment removed for export] *)
Lemma provU_other : forall c, c <> cls -> provU st' c = provU st c.
Proof. intros c H. unfold provU, delta. rewrite rg_other, navail_other by exact H. reflexivity. Qed.
Lemma provF_other : forall c, c <> cls -> provF st' c = provF st c.
Proof. intros c H. unfold provF, fa_cap. rewrite rg_other, ncarved_other by exact H. reflexivity. Qed.

Lemma slack_ok : forall c, 1 <= c <= 30 -> 64 + 2 * (nrefill c * csize c) - 2 * csize c <= 2048 /\ nrefill c <= 8 /\ 1 <= nrefill c.
Proof.
  intros c Hc'.
  assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct H as [->|H]; [vm_compute; repeat split; discriminate|]). subst. vm_compute. repeat split; discriminate.
Qed.

Lemma prov_step : provU st' cls + provF st' cls + (if um then LUMPU else 0) + (if fm then LUMPF else 0) <= provU st cls + provF st cls.
Proof.
  (nelimp Nv_le 3%nat; intros NB ND1 ND2). pose proof Spos as SP. pose proof nrange as [NR1 NR2]. destruct (WX cls Hc1) as [DEL EXH]. rewrite <- Er in DEL.
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_num_freed st cls WC) as NF. pose proof (wc_fa_nonneg st cls WC) as F0. pose proof (wc_fa_align st cls WC) as FA.
  rewrite <- Er in *. unfold num_freed in NF. rewrite <- Er, <- Enf in NF. pose proof (zlen_nonneg (r_fa r)) as NF0. rewrite <- Enf in NF0.
  pose proof ncarved_nonneg as NC0. pose proof ncarved_eq as NCE. (nelimp (slack_ok cls Hc) 3%nat; intros SL1 SL2 SL3). rewrite <- Hn in SL1, SL2, SL3. change (csize cls) with S in SL1.
  unfold provU, provF, delta, fa_cap. rewrite rg_same, navail_same', navail_old, ncarved_same'. cbn [r_allocated r_mapped r_mapped_fa r_new].
  rewrite <- Hn. change (csize cls) with S. unfold Nmax. change (csize cls) with S. unfold LUMPU, LUMPF, LUMPU, FAPROV.
  set (Q := 2^18 / S) in *.
  assert (NX : S * Q <= 2^18 /\ 2^18 - S < S * Q) by (subst Q; clear -SP; split; [apply Z.mul_div_le; lia| Z.div_mod_to_equations; nia]).
  assert (SNF : S * nf <= S * n - S \/ pop = false).
  { destruct pop; [left| right; reflexivity]. destruct (HPOP eq_refl) as (P1 & _). assert (S * nf <= S * (n - 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  destruct pop.
  - (nelim (HPOP eq_refl) 6%nat; intros P1 P2 P3 P4 P5 P6). destruct SNF as [SNF|SNF]; [| discriminate]. specialize (ND2 eq_refl).
    assert (FMF : fm = true -> r_mapped_fa r = 0 /\ nm = 262144).
    { intros Efm. rewrite Efm in P5. symmetry in P5. apply Z.ltb_lt in P5. change (2^18) with 262144 in FA.
      assert (r_mapped_fa r = 0) by (clear -P5 F0 FA NB NR1 NF0 P1 HNv; Z.div_mod_to_equations; nia). split; [assumption|].
      rewrite P6. clear -NB NR1 NF0 P1 HNv. Z.div_mod_to_equations. nia. }
    (* [comment removed for export] *)
    assert (BIGQ : 262144 - S < Nv * S /\ Nv <= n - nf + Q + 1).
    { destruct um.
      - symmetry in P3. apply Z.ltb_lt in P3. split; [clear -P3 ND1 ND2 SP AM; lia|].
        assert (LT : S * Nv < S * (n - nf + Q + 1 + 1)) by (clear -P3 ND1 NX SP; nia). apply Z.mul_lt_mono_pos_l in LT; lia.
      - symmetry in P3. apply Z.ltb_ge in P3. rewrite Z.add_0_r in *.
        assert (S <= (n - nf) * S) by (clear -SP P1 NR1; nia).
        destruct DEL as [D|[D1 D2]]; [exfalso; clear -D P3 H; lia|]. split; [clear -D1 ND2 SP AM; lia|].
        assert (LT : S * Nv < S * (Q + 1 + 1)) by (clear -D2 ND1 NX SP; nia). apply Z.mul_lt_mono_pos_l in LT; lia. }
    destruct BIGQ as [BIG NvQ].
    (* [comment removed for export] *)
    set (sNv := Nv * S) in *. set (sNf := S * nf) in *. set (sN := S * n) in *.
    replace (2 * S * (nf + Nv)) with (2 * sNf + 2 * sNv) by (subst sNv sNf; lia). replace (2 * S * nf) with (2 * sNf) by (subst sNf; lia).
    replace ((n - nf) * S) with (sN - sNf) in P3 by (subst sN sNf; lia). replace (n * S) with sN in * by (subst sN; lia). replace (nrefill cls * S) with sN by (rewrite <- Hn; subst sN; lia).
    assert (Q8 : 8 * Q <= 65536) by (subst Q; clear -SP; Z.div_mod_to_equations; nia).
    assert (SN1 : S <= sN) by (subst sN; clear -SP NR1; nia). assert (SNF0 : 0 <= sNf) by (subst sNf; clear -SP NF0; nia).
    assert (SNF2 : sNf <= sN - S - 4 * (n - 1 - nf)) by (subst sNf sN; clear -SP NF0 P1; nia).
    clearbody sNv sNf sN Q. rewrite <- !Er.
    replace (r_mapped r + (if um then 262144 else 0) - (r_allocated r + sNv) <? sN) with true by (symmetry; apply Z.ltb_lt; clear -ND2 SN1; lia).
    destruct um.
    + symmetry in P3. apply Z.ltb_lt in P3. replace (r_mapped r - r_allocated r <? sN) with true by (symmetry; apply Z.ltb_lt; clear -P3 SNF0; lia).
      destruct fm; [destruct (FMF eq_refl) as [EF EN]; rewrite ?EF, ?EN in *|];
        clear - SP NR1 NR2 SL1 SL2 SL3 NX BIG NvQ P1 P3 NF0 NC0 NB ND1 ND2 F0 Q8 SNF SNF0 SNF2 SN1 HNv AM; lia.
    + symmetry in P3. apply Z.ltb_ge in P3. rewrite ?Z.add_0_r in *.
      replace (r_mapped r - r_allocated r <? sN) with false by (symmetry; apply Z.ltb_ge; destruct DEL as [D|[D1 D2]]; [clear -D P3 SN1 SNF SNF0| clear -D1 NR2]; lia).
      destruct fm; [destruct (FMF eq_refl) as [EF EN]; rewrite ?EF, ?EN in *|];
        clear - SP NR1 NR2 SL1 SL2 SL3 NX BIG NvQ P1 P3 NF0 NC0 NB ND1 ND2 F0 Q8 SNF SNF0 SNF2 SN1 HNv AM; lia.
  - (nelim (HHAVE eq_refl) 3%nat; intros ENv Eum Efm). rewrite ENv, Eum, Efm in *. rewrite ?Z.add_0_r, ?Z.mul_0_l, ?Z.sub_0_r, ?Z.add_0_r. rewrite <- !Er. lia.
Qed.

Lemma zsum_map_le' : forall (f g : Z -> Z) l d x, (forall y, In y l -> y <> x -> f y = g y) -> f x + d <= g x ->
  List.NoDup l -> In x l -> zsum (map f l) + d <= zsum (map g l).
Proof.
  intros f g l d x Hfg Hx ND IN. induction l as [|y l IH]; [destruct IN|].
  inversion ND as [|y' l' Hni ND']; subst. cbn [map]. rewrite !zsum_cons.
  destruct (Z.eq_dec y x) as [->|NE].
  - rewrite (zsum_map_ext f g l); [lia|]. intros z Hz. apply Hfg; [right; exact Hz|]. intros ->. exact (Hni Hz).
  - rewrite (Hfg y ltac:(left; reflexivity) NE). destruct IN as [E|IN]; [exfalso; exact (NE E)|].
    specialize (IH ltac:(intros w Hw Hne; apply Hfg; [right; exact Hw| exact Hne]) ND' IN). lia.
Qed.

Lemma prov_classes_new : prov_classes st' + (if um then LUMPU else 0) + (if fm then LUMPF else 0) <= prov_classes st.
Proof.
  unfold prov_classes. rewrite <- Z.add_assoc.
  apply (zsum_map_le' (fun c => provU st' c + provF st' c) (fun c => provU st c + provF st c) classes _ cls).
  - intros y Hy Hne. rewrite provU_other, provF_other by exact Hne. reflexivity.
  - pose proof prov_step. lia.
  - apply classes_nodup.
  - unfold classes. apply in_map_iff. exists (Z.to_nat cls). split; [lia| apply in_seq; lia].
Qed.

Lemma rt_prov_new : rt_prov st' + (if um then LUMPU else 0) + (if fm then LUMPF else 0) <= rt_prov st.
Proof.
  assert (E2 : prov_nb st' = prov_nb st) by reflexivity.
  assert (E3 : prov_q st' = prov_q st) by reflexivity.
  assert (E4 : prov_ptr st' = prov_ptr st) by reflexivity.
  assert (E5 : prov_live st' = prov_live st) by reflexivity.
  assert (E6 : prov_quar st' = prov_quar st) by reflexivity.
  assert (E7 : prov_depot st' = prov_depot st) by reflexivity.
  assert (E8 : prov_slots st' = prov_slots st) by reflexivity.
  assert (E9 : prov_l24 st' = prov_l24 st) by reflexivity.
  assert (E10 : prov_emb st' = prov_emb st) by reflexivity.
  unfold rt_prov. rewrite E2, E3, E4, E5, E6, E7, E8, E9, E10. pose proof prov_classes_new. lia.
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_new : forall mo, RTMODEL st mo -> RTMODEL st' mo.
Proof. intros mo H. exact H. Qed.
Lemma GWIN_new : forall m mo g, GWIN st m mo g -> GWIN st' m mo g.
Proof. intros m mo g H. exact H. Qed.
Lemma SWIN_new : forall g, SWIN st g -> SWIN st' g.
Proof. intros g H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variables (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis HR : RTREP st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis HW : Forall (pz_ok st cls) W.
Let rb := rbeg st cls.
Let fb := fabeg st cls.
Let alloc := r_allocated r.
Let mapped := r_mapped r.
Let mapped' := r_mapped r + (if um then 262144 else 0).
Let fam' := if fm then nm else r_mapped_fa r.
(* [comment removed for export] *)
Hypothesis RINFO : exists jr je js, rw_cells bsegs m' (rinfo st cls) (rinfo_cells st' cls jr je js).
(* [comment removed for export] *)
Hypothesis VU : um = true -> vis m' (rb + mapped) (rb + mapped + 262144) /\ rw_cells bsegs m' (SH (rb + mapped)) (zcells (zrep SV_HEAP_LEFT_RZ 32768)).
Hypothesis VF : vis m' fb (fb + fam') /\ vis m' (SH fb) (SH fb + fam' / 8).
(* [comment removed for export] *)
Hypothesis FILL : forall t, 0 <= t < Nv -> rw_cells bsegs m' (fb + 4 * (nf + t)) [W4 (chunk_cptr cls (ncarved st cls + Nv - 1 - t))].
(* [comment removed for export] *)
Hypothesis PCH : forall c, 0 <= c < KNUMCLASSES -> rw_cells bsegs m' (pcaddr st c) [W4 (zlen (cch st' c)); W4 (if c =? 0 then 0 else cmaxcount c); W8 (if c =? 0 then 0 else csize c)].
Hypothesis PCE : forall i, 0 <= i < n -> rw_cells bsegs m' (pcaddr st cls + 16 + 4 * i) [W4 (nthz L (base + i) 0)].
Hypothesis PCO : forall c i, 0 <= c < KNUMCLASSES -> c <> cls -> 0 <= i < zlen (cch st c) -> rw_cells bsegs m' (pcaddr st c + 16 + 4 * i) [W4 (nthz (cch st c) i 0)].

Lemma RF : KHIGHMEM_BEG <= rb /\ rb mod 8 = 0 /\ alloc mod 8 = 0 /\ mapped mod 8 = 0 /\ 0 <= alloc <= mapped /\ mapped <= KFREEARRAY_OFF /\ rb + KREGIONSIZE <= CEIL.
Proof.
  pose proof (region_facts st WF cls Hcls) as X. cbn zeta in X. (nelim X 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  unfold rb, alloc, mapped, r. unfold CEIL. repeat split; try lia; assumption.
Qed.

(* [comment removed for export] *)
Lemma tail_shadow : rw_cells bsegs m' (SH (rb + alloc)) (zcells (zrep SV_HEAP_LEFT_RZ ((mapped' - alloc) / 8))).
Proof.
  (nelimp RF 7%nat; intros X1 X2 X3 X4 X5 X6 X7).
  (nelim (pz_others st WF cls Hc W HW m m' MU WM HR) 5%nat; intros _ _ _ RG _).
  (nelim (RG cls Hcls) 6%nat; intros _ _ _ _ _ TL). fold r in TL. change (rbeg st cls) with rb in TL. change (r_allocated r) with alloc in TL. change (r_mapped r) with mapped in TL.
  unfold mapped'. change (r_mapped r) with mapped. destruct um.
  - destruct (VU eq_refl) as [_ SHU].
    replace ((mapped + 262144 - alloc) / 8) with ((mapped - alloc) / 8 + 32768) by (clear -X3 X4 X5; Z.div_mod_to_equations; lia).
    rewrite zrep_split, zcells_app' by (clear -X3 X4 X5; Z.div_mod_to_equations; lia).
    apply rw_cells_app. split; [exact TL|]. rewrite zcells_zrep_size by (clear -X3 X4 X5; Z.div_mod_to_equations; lia).
    replace (SH (rb + alloc) + (mapped - alloc) / 8) with (SH (rb + mapped)); [exact SHU|].
    rewrite !rt_SH_aligned_add by exact X2. clear -X3 X4 X5. Z.div_mod_to_equations. lia.
  - rewrite Z.add_0_r. exact TL.
Qed.

(* [comment removed for export] *)
Lemma zrep_sub : forall mm A v N i k, rw_cells bsegs mm A (zcells (zrep v N)) -> 0 <= i -> 0 <= k -> i + k <= N ->
  rw_cells bsegs mm (A + i) (zcells (zrep v k)).
Proof.
  intros mm A v N i k H Hi Hk Hle.
  replace N with (i + (k + (N - i - k))) in H by lia. rewrite !zrep_split, !zcells_app' in H by lia.
  apply rw_cells_mid in H. rewrite zcells_zrep_size in H by lia. exact H.
Qed.

Lemma RTREP_new : RTREP st' m'.
Proof.
  (nelimp RF 7%nat; intros X1 X2 X3 X4 X5 X6 X7). pose proof Spos as SP. (nelimp Nv_le 3%nat; intros NB ND1 ND2). pose proof nrange as [NR1 NR2].
  pose proof ncarved_eq as NCE. pose proof ncarved_nonneg as NC0. fold alloc in NCE.
  (nelim (pz_others st WF cls Hc W HW m m' MU WM HR) 14%nat; intros Y1 Y2 Y3 Y5 Y6 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16).
  pose proof tail_shadow as TS.
  assert (LL : zlen L = nf + Nv) by (rewrite EL, zlen_app, newc_length, Enf by lia; reflexivity).
  pose proof (zlen_nonneg (r_fa r)) as NF0. rewrite <- Enf in NF0.
  constructor.
  - exact Y1.
  - exact Y2.
  - exact Y3.
  - (* [comment removed for export] *) split.
    { pose proof (proj1 (rr_rinfo st m HR)) as VR. (nelimp (ris_range st WF) 4%nat; intros Z1 Z2 Z3 Z4). change (ris st') with (ris st).
      (nelimp RINFO 4%nat; intros jr0 je0 js0 RC0). pose proof (rw_cells_bound bsegs m' _ _ RC0) as RB0.
      assert (E128 : Z.of_nat (cells_size (rinfo_cells st' cls jr0 je0 js0)) = 128).
      { destruct RC0 as [[Wf _] _]. cbn in Wf. unfold rinfo_cells. cbn [cells_size Cells.csize].
        (nelim Wf 13%nat; intros _ _ _ _ _ _ _ _ L1 _ L2 L3 _). lia. }
      assert (RL : rinfo st cls = ris st + 128 * cls) by reflexivity.
      destruct (stk_split bsegs m (ris st) (rinfo st cls) (ris st + 4096) VR ltac:(rewrite RL; lia)) as [VA VB].
      destruct (stk_split bsegs m (rinfo st cls) (rinfo st cls + 128) (ris st + 4096) VB ltac:(rewrite RL; lia)) as [_ VC].
      apply (stk_merge bsegs m' _ (rinfo st cls)); [| | rewrite RL; lia].
      - eapply stk_transport_disjoint; [exact VA| exact MU| exact WM|].
        (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
        apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE in *; lia.
      - apply (stk_merge bsegs m' _ (rinfo st cls + 128)); [| | rewrite RL; lia].
        + pose proof (stk_of_rw_cells bsegs m' _ _ RC0) as SR. rewrite E128 in SR. exact SR.
        + eapply stk_transport_disjoint; [exact VC| exact MU| exact WM|].
          (nelimp (cls_facts st WF cls Hc) 14%nat; intros C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).
          apply (pz_prim st WF cls Hc W HW); rewrite ?C13; unfold KFREEARRAY_OFF, KFREEARRAY_SIZE, KREGIONSIZE, KNUMCLASSES in *; (lia_on Hc X5 SP C2 C3 C14 Z4 HNv NR1 LL). }
    intros c Hc'. change (rinfo st' c) with (rinfo st c). destruct (Z.eq_dec c cls) as [->|NE]; [exact RINFO|].
    (nelim (proj2 (rr_rinfo st m HR) c Hc') 4%nat; intros jr je js RC). exists jr, je, js.
    replace (rinfo_cells st' c jr je js) with (rinfo_cells st c jr je js) by (unfold rinfo_cells; rewrite rg_other by exact NE; unfold num_freed; rewrite rg_other by exact NE; reflexivity).
    exact (pz_rinfo_other st WF cls Hc W HW m m' c jr je js MU WM Hc' NE RC).
  - (* [comment removed for export] *) intros c Hc'. change (rbeg st' c) with (rbeg st c). change (fabeg st' c) with (fabeg st c).
    destruct (Z.eq_dec c cls) as [->|NE].
    2:{ unfold num_freed. rewrite rg_other by exact NE. exact (Y5 c Hc'). }
    rewrite rg_same. unfold num_freed. rewrite rg_same. cbn [r_allocated r_mapped r_mapped_fa r_fa r_new]. fold rb fb. change (r_mapped r + (if um then 262144 else 0)) with mapped'. fold alloc.
    (nelim (Y5 cls Hcls) 6%nat; intros V1 V2 V3 V4 EN TL). fold r rb fb in V1, V2, V3, V4, EN, TL |- *.
    change (r_mapped r) with mapped in V1, V2. change (num_freed st cls) with nf in EN.
    split; [| split; [| split; [exact (proj1 VF)| split; [exact (proj2 VF)| split]]]].
    + unfold mapped'. change (r_mapped r) with mapped. destruct um; [| rewrite Z.add_0_r; exact V1]. destruct (VU eq_refl) as [VU1 _]. replace (rb + (mapped + 262144)) with (rb + mapped + 262144) by lia. eapply stk_merge; [exact V1| exact VU1| lia].
    + unfold mapped'. change (r_mapped r) with mapped. destruct um; [| rewrite Z.add_0_r; exact V2]. destruct (VU eq_refl) as [_ SHU].
      apply zcells_zrep_to_CB in SHU; [| lia]. apply (stk_of_rw_cellsZ _ _ _ 32768) in SHU; [| cbn; lia].
      replace (SH rb + (mapped + 262144) / 8) with (SH (rb + mapped) + 32768) by (rewrite rt_SH_aligned_add by exact X2; clear -X4 X5; Z.div_mod_to_equations; lia).
      replace (SH rb + mapped / 8) with (SH (rb + mapped)) in V2 by (rewrite rt_SH_aligned_add by exact X2; reflexivity).
      eapply stk_merge; [exact V2| exact SHU| pose proof (rt_SH_mono rb (rb + mapped) ltac:(lia)); lia].
    + (* [comment removed for export] *) intros i Hi. unfold zlen in Hi. rewrite length_firstn in Hi. unfold zlen in LL.
      assert (Hi' : 0 <= i < nf + Nv) by lia.
      rewrite nthz_firstn by lia.
      destruct (Z_lt_le_dec i nf) as [LT|GE].
      * rewrite EL, nthz_app_l by (rewrite <- Enf; lia). apply EN. lia.
      * rewrite EL, nthz_app_r, <- Enf, nthz_newc by (rewrite <- ?Enf; lia).
        replace i with (nf + (i - nf)) at 1 by lia. apply FILL. lia.
    + (* [comment removed for export] *) pose proof (csize_mod32 cls ltac:(lia)) as M32. change (csize cls) with S in M32.
      pose proof (mod0_trans S 8 32 ltac:(lia) ltac:(lia) eq_refl M32) as S8.
      assert (NS8 : (Nv * S) mod 8 = 0) by (rewrite Z.mul_mod, S8, Z.mul_0_r by lia; reflexivity).
      replace (SH (rb + (alloc + Nv * S))) with (SH (rb + alloc) + Nv * S / 8).
      2:{ rewrite !rt_SH_aligned_add by exact X2. clear -X3 NS8. Z.div_mod_to_equations. lia. }
      replace ((mapped' - (alloc + Nv * S)) / 8) with ((mapped' - alloc) / 8 - Nv * S / 8) by (clear -NS8 X3; Z.div_mod_to_equations; lia).
      eapply zrep_sub; [exact TS| apply Z.div_pos; [apply Z.mul_nonneg_nonneg; lia| lia]| clear -ND1 NS8 X3; unfold mapped', alloc; Z.div_mod_to_equations; lia| lia].
  - (* [comment removed for export] *) intros c k Hc' Hk. change (cptr_addr st' c k) with (cptr_addr st c k).
    destruct (Z.eq_dec c cls) as [->|NE].
    2:{ rewrite avail_other, apend_same in Hk by exact NE. exact (Y6 c k Hc' Hk). }
    rewrite avail_same', apend_same, EL in Hk. rewrite <- app_assoc, in_app_iff, in_app_iff in Hk.
    destruct Hk as [Hk|[Hk|Hk]].
    + apply (Y6 cls k Hcls). unfold avail_cptrs. fold r. rewrite HC0, app_nil_r. apply in_app_iff. left. exact Hk.
    + apply newc_In in Hk as (j & Hj & ->).
      pose proof (csize_mod32 cls ltac:(lia)) as M32. change (csize cls) with S in M32.
      pose proof (chunk_cptr_eq cls j ltac:(lia)) as CE. change (csize cls) with S in CE.
      pose proof (mod0_trans S 8 32 ltac:(lia) ltac:(lia) eq_refl M32) as S8.
      assert (AJ : ((j - ncarved st cls) * S) mod 8 = 0) by (rewrite Z.mul_mod, S8, Z.mul_0_r by lia; reflexivity).
      unfold sh_avail. change (csize cls) with S.
      replace (SH (cptr_addr st cls (chunk_cptr cls j))) with (SH (rb + alloc) + (j - ncarved st cls) * S / 8).
      2:{ unfold cptr_addr. change (rbeg st cls) with rb. replace (rb + 16 * chunk_cptr cls j) with (rb + alloc + (j - ncarved st cls) * S) by lia.
          rewrite (rt_SH_aligned_add (rb + alloc) ((j - ncarved st cls) * S)); [reflexivity| rewrite Z.add_mod, X2, X3 by lia; reflexivity]. }
      eapply zrep_sub; [exact TS| apply Z.div_pos; [apply Z.mul_nonneg_nonneg; lia| lia]| apply Z.div_pos; lia|].
      assert ((j - ncarved st cls) * S + S <= Nv * S) by (replace ((j - ncarved st cls) * S + S) with ((j - ncarved st cls + 1) * S) by lia; apply Z.mul_le_mono_nonneg_r; lia).
      clear -H AJ S8 ND1 X3 X4 SP. unfold mapped', alloc, mapped. Z.div_mod_to_equations. lia.
    + apply (Y6 cls k Hcls). apply in_app_iff. right. exact Hk.
  - (* [comment removed for export] *) intros c Hc'. change (pcaddr st' c) with (pcaddr st c).
    assert (PM : pc_max_count st' c = (if c =? 0 then 0 else cmaxcount c)) by (unfold pc_max_count; cbn [st_cache_inited st']; destruct (c =? 0); reflexivity).
    assert (PS' : pc_class_size st' c = (if c =? 0 then 0 else csize c)) by (unfold pc_class_size; cbn [st_cache_inited st']; destruct (c =? 0); reflexivity).
    rewrite PM, PS'. split; [exact (PCH c Hc')|].
    destruct (Z.eq_dec c cls) as [->|NE].
    + rewrite cch_same. intros i Hi.
      assert (LC : zlen cache' = n) by (unfold zlen; unfold cache'; rewrite length_skipn; unfold zlen in LL; rewrite Ebase; (lia_on HNv X5 SP ND1 NR1 NCE NC0 LL)). rewrite LC in Hi.
      unfold cache'. rewrite nthz_skipn by lia. replace (Z.of_nat (Z.to_nat base) + i) with (base + i) by (rewrite Ebase; lia). exact (PCE i Hi).
    + rewrite cch_other by exact NE. intros i Hi. exact (PCO c i Hc' NE Hi).
  - exact Y8.
  - exact Y9.
  - exact Y10.
  - exact Y11.
  - exact Y12.
  - exact Y13.
  - exact Y14.
  - exact Y15.
  - exact Y16.
Qed.
End PT.


End CeilWrap.
