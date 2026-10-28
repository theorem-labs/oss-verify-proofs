(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdTbl ZdDctxRep SepHide DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_tbl
     AZ_blk_iface AZ_blk_iface2 AZ_blk_iface3 AZ_bst_stk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition APLL_BASE : Z := 0x21780.  Definition APLL_BITS : Z := 0x21840.
Definition APOF_BASE : Z := 0x21b40.  Definition APOF_BITS : Z := 0x21be0.
Definition APML_BASE : Z := 0x21d80.  Definition APML_BITS : Z := 0x21e80.

Lemma apll_base_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APLL_BASE (u32s (map (Z_to_bv 64) (kind_base K_LL))).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma apll_bits_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APLL_BITS (map (Z_to_bv 8) (kind_bits K_LL)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma apof_base_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APOF_BASE (u32s (map (Z_to_bv 64) (kind_base K_OF))).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma apof_bits_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APOF_BITS (map (Z_to_bv 8) (kind_bits K_OF)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma apml_base_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APML_BASE (u32s (map (Z_to_bv 64) (kind_base K_ML))).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.
Lemma apml_bits_at : forall m, mem_inv bsegs m -> bytes_at bsegs m APML_BITS (map (Z_to_bv 8) (kind_bits K_ML)).
Proof. intros m MI. apply img_bytes_at; [exact MI | vm_compute; reflexivity | vm_compute; discriminate | vm_compute; discriminate]. Qed.

(* [comment removed for export] *)
Lemma aro_tables : forall RNG m, aro_client RNG m ->
  aro RNG m APLL_BASE 144 /\ aro RNG m APLL_BITS 36 /\ aro RNG m APZD_LL_DEFAULT 520 /\
  aro RNG m APOF_BASE 128 /\ aro RNG m APOF_BITS 32 /\ aro RNG m APZD_OF_DEFAULT 264 /\
  aro RNG m APML_BASE 212 /\ aro RNG m APML_BITS 53 /\ aro RNG m APZD_ML_DEFAULT 520.
Proof.
  intros RNG m H. unfold APLL_BASE, APLL_BITS, APZD_LL_DEFAULT, APOF_BASE, APOF_BITS, APZD_OF_DEFAULT, APML_BASE, APML_BITS, APZD_ML_DEFAULT.
  assert (G : forall A n, In (A, n) ACLIENT_RO -> aro RNG m A n) by (intros A n HI; exact (aro_client_at RNG m A n H HI)).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]; (apply G; cbn; tauto).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FC.
Variable AI : AMallocIface.
Hypothesis FHL : fake_heap_law AI.

Lemma sh_disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[x y] W IH]; intros a n a' n' D H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; [exact D2| lia| lia]].
Qed.

Lemma shc_bytes_pres : forall L RNG st LB m0 (m m' : amem) W X bs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (zlen bs) -> disjoint_from W X (zlen bs) ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> bytes_at bsegs m X bs -> bytes_at bsegs m' X bs.
Proof.
  intros L RNG st LB m0 m m' W X bs AH (b & Hb & H1 & H2) DJ MU FP B.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply bytes_at_transport; [exact B| exact MU|]. apply disjoint_from_app2; [exact DJ| eapply sh_disjoint_from_sub; [exact DF| lia| lia]].
  - eapply bytes_at_magree; [exact FP| exact B|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.

Lemma shc_cells_pres : forall L RNG st LB m0 (m m' : amem) W X cs,
  AHEAP AI L RNG st LB m0 -> ainblk LB X (Z.of_nat (cells_size cs)) -> disjoint_from W X (Z.of_nat (cells_size cs)) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> rw_cells bsegs m X cs -> rw_cells bsegs m' X cs.
Proof.
  intros L RNG st LB m0 m m' W X cs AH IB DJ MU WM FP [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - eapply shc_bytes_pres; [exact AH| rewrite cells_bytes_length by assumption; exact IB| rewrite cells_bytes_length by assumption; exact DJ| exact MU| exact FP| exact HB].
  - eapply wr_at_transport; [exact HW| exact WM].
Qed.

Lemma shc_stk_pres : forall L RNG st LB m0 (m m' : amem) W lo hi,
  AHEAP AI L RNG st LB m0 -> ainblk LB lo (hi - lo) -> disjoint_from W lo (hi - lo) ->
  munch (W ++ fake_area L) m m' -> wmono bsegs m m' -> ffr_pres W LB m m' -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros L RNG st LB m0 m m' W lo hi AH (b & Hb & H1 & H2) DJ MU WM FP ST.
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [DF _].
    eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. apply disjoint_from_app2; [exact DJ| eapply sh_disjoint_from_sub; [exact DF| lia| lia]].
  - eapply stk_magree; [exact FP| exact ST|]. intros a Ha. left. split.
    + exists c, A, n. split; [exact Hb| lia].
    + eapply disjoint_outside; [exact DJ| lia].
Qed.

Lemma shc_unp_pres : forall L RNG st LB m0 (m m' : amem) W X k,
  AHEAP AI L RNG st LB m0 -> ainblk LB X k -> 0 < k -> X + k <= KEND -> aappW W ->
  munch (W ++ fake_area L) m m' -> ffr_pres W LB m m' -> unpoisoned m X (X + k) -> unpoisoned m' X (X + k).
Proof.
  intros L RNG st LB m0 m m' W X k AH (b & Hb & H1 & H2) Hk XH HW MU FP U.
  pose proof U as (U0 & U1 & _).
  destruct b as [[p|c] A n]; cbn [ab_addr ab_size] in H1, H2.
  - destruct (fake_area_block AI _ _ _ _ _ p A n FHL AH Hb) as [_ DSF].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (N & (BR & _) & _). pose proof (ablk_lin _ _ BR) as (L1 & L2 & L3 & L4).
    eapply unpoisoned_munch; [exact U| exact MU|]. apply disjoint_from_app2.
    + apply aappW_shadow_disjoint; [exact HW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
    + eapply sh_disjoint_from_sub; [exact DSF| |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - eapply unpoisoned_agree; [exact U|]. intros s Hs.
    set (a' := Z.max X (8 * (s - ASHOFF))).
    assert (Ra : X <= a' < X + k).
    { subst a'. rewrite !shad_div in Hs. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    assert (Ea : shad a' = s).
    { subst a'. rewrite !shad_div in Hs. rewrite shad_div. unfold ASHOFF in *. destruct (Z.max_spec X (8 * (s - 2147450880))) as [[Hm ->]|[Hm ->]]; Z.div_mod_to_equations; lia. }
    destruct (FP s ltac:(rewrite !shad_div in Hs; unfold ASHOFF in Hs; unfold KEND in XH; Z.div_mod_to_equations; lia)
                 ltac:(right; exists a'; split; [exists c, A, n; split; [exact Hb| lia]| symmetry; exact Ea])) as [E _].
    exact E.
Qed.
End FC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation TSZ k := (8 + 8 * 2^(kind_maxLog k)) (only parsing).

Definition tab_infoA (DCTX : Z) (k : seq_kind) (own dflt : Z) (d : seq_table) (pv : word) (T : Z) (bs : list byte) : Prop :=
  exists t, pv = Z_to_bv 64 T /\ bs = map (Z_to_bv 8) (seq_table_bytes t) /\ seq_table_ok k t /\ tbl_ptr DCTX own dflt d T t.

Lemma tab_infoA_tab : forall m DCTX k own dflt d pv T bs,
  tab_infoA DCTX k own dflt d pv T bs -> bytes_at bsegs m T bs -> seqhdr_tab m DCTX k own dflt d pv.
Proof. intros m DCTX k own dflt d pv T bs (t & -> & -> & OK & TP) BA. exists T, t. split; [reflexivity|]. split; [exact TP|]. split; assumption. Qed.

Lemma tab_infoA_len : forall DCTX k own dflt d pv T bs, tab_infoA DCTX k own dflt d pv T bs -> Z.of_nat (length bs) <= TSZ k.
Proof. intros DCTX k own dflt d pv T bs (t & _ & -> & OK & _). pose proof (seq_tbl_len_le k t OK). lia. Qed.

Lemma tab_after_callA : forall (m m' : amem) W DCTX k own dflt d (oldp pv frw : word) (ty : Z) T0 bs0,
  bytes_at bsegs m T0 bs0 -> Z.of_nat (length bs0) <= TSZ k ->
  (frw <> Z_to_bv 64 0 -> tab_infoA DCTX k own dflt d oldp T0 bs0) ->
  (T0 = DCTX + own \/ disjoint_from W T0 (Z.of_nat (length bs0))) ->
  (forall A bs, bytes_at bsegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> bytes_at bsegs m' A bs) ->
  seq_tbl_at bsegs m' k dflt d ->
  ((ty = 0 /\ pv = Z_to_bv 64 dflt)
   \/ (ty = 3 /\ frw <> Z_to_bv 64 0 /\ pv = oldp /\
       forall bs, bytes_at bsegs m (DCTX + own) bs -> Z.of_nat (length bs) <= TSZ k -> bytes_at bsegs m' (DCTX + own) bs)
   \/ ((ty = 1 \/ ty = 2) /\ pv = Z_to_bv 64 (DCTX + own) /\
       exists t, seq_table_ok k t /\ bytes_at bsegs m' (DCTX + own) (map (Z_to_bv 8) (seq_table_bytes t)))) ->
  exists T bs, tab_infoA DCTX k own dflt d pv T bs /\ bytes_at bsegs m' T bs.
Proof.
  intros m m' W DCTX k own dflt d oldp pv frw ty T0 bs0 OB OL OV LOC FRAME (DB & DOK) [(_ & ->) | [(_ & FRN & -> & SAME) | (_ & -> & t & TOK & TB)]].
  - exists dflt, (map (Z_to_bv 8) (seq_table_bytes d)). split; [|exact DB].
    exists d. split; [reflexivity|]. split; [reflexivity|]. split; [exact DOK|]. right. auto.
  - exists T0, bs0. split; [exact (OV FRN)|]. destruct LOC as [-> | DJ]; [apply SAME; assumption | apply FRAME; assumption].
  - exists (DCTX + own), (map (Z_to_bv 8) (seq_table_bytes t)). split; [|exact TB].
    exists t. split; [reflexivity|]. split; [reflexivity|]. split; [exact TOK|]. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tab_infoA_geo : forall DCTX k own dflt d pv T bs lo SPV,
  tab_infoA DCTX k own dflt d pv T bs ->
  0x10000 <= dflt -> dflt + TSZ k <= 0x30000 -> 32 <= own -> own + TSZ k <= 10296 ->
  0x625000 <= DCTX -> 0x625000 <= lo -> (DCTX + 95992 <= lo \/ SPV <= DCTX) ->
  (T = DCTX + own \/ (T + TSZ k <= DCTX \/ DCTX + 30372 <= T)) /\ (T + TSZ k <= lo \/ SPV <= T) /\ (T = DCTX + own \/ T + TSZ k <= 0x30000).
Proof.
  intros DCTX k own dflt d pv T bs lo SPV (t & _ & _ & _ & [-> | [-> _]]) D0 D1 O0 O1 DC LOC OFFD; repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma ah5_cold_cell : forall m DCTX ws, dctx_h5 bsegs m DCTX ws -> rw_cells bsegs m (DCTX + 30204) [C4 (wnth ws H5_ddictIsCold)].
Proof.
  intros m DCTX ws (C & L). h5_open ws L.
  lazymatch type of C with rw_cells _ _ _ ?cs =>
    change cs with (firstn 17 cs ++ [nth 17 cs (C1 (Z_to_bv 8 0))] ++ skipn 18 cs) in C end.
  cbn [firstn skipn nth] in C.
  apply rw_cells_app in C. destruct C as [_ C]. apply rw_cells_app in C. destruct C as [C _].
  cbn [cells_size csize Nat.add] in C. replace (DCTX + 30096 + Z.of_nat 108) with (DCTX + 30204) in C by lia. exact C.
Qed.

(* [comment removed for export] *)
Lemma ah3_fse_cell : forall m DCTX pcs dsz bt stg le fe, dctx_h3 bsegs m DCTX pcs dsz bt stg le fe -> rw_cells bsegs m (DCTX + 30004) [C4 fe].
Proof.
  intros m DCTX pcs dsz bt stg le fe C. unfold dctx_h3 in C.
  change [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] with ([C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le] ++ [C4 fe]) in C.
  apply rw_cells_app in C. destruct C as [_ C]. cbn [cells_size csize Nat.add] in C.
  replace (DCTX + 29976 + Z.of_nat 28) with (DCTX + 30004) in C by lia. exact C.
Qed.

Lemma abytes_at_skipn : forall (m1 : amem) SRC src i, bytes_at bsegs m1 SRC (map (Z_to_bv 8) src) -> 0 <= i <= Z.of_nat (length src) ->
  bytes_at bsegs m1 (SRC + i) (map (Z_to_bv 8) (skipn (Z.to_nat i) src)).
Proof.
  intros m1 SRC src i (B0 & B1 & B) Hi. rewrite length_map in *. split; [lia|]. split; [rewrite length_map, skipn_length; lia|].
  intros j Hj. rewrite length_map, skipn_length in Hj.
  replace (SRC + i + Z.of_nat j) with (SRC + Z.of_nat (Z.to_nat i + j)) by lia. rewrite B by lia.
  rewrite <- skipn_map. rewrite nth_error_skipn. reflexivity.
Qed.

End CANSEC1.
