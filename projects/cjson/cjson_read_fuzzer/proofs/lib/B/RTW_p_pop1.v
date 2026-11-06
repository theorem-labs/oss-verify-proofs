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
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_p_lib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
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
Section COMMIT.
Variables (mo : Model) (A n : Z).
Hypothesis HO : LOK bsegs mo.
Hypothesis HA : KHIGHMEM_BEG <= A /\ A + n <= CEIL /\ 0 < n.

Lemma lzf_commit_out : forall x : word, in_range A n x = false -> lzf (mm_commit (wz A) (wz n) mo) x = lzf mo x.
Proof.
  intros x Hx. destruct HA as (G1 & G2 & G3). unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  assert (HuA : bv_unsigned (wz A) = A) by (unfold wz; apply unsigned_lit; lia).
  assert (Hun : bv_unsigned (wz n) = n) by (unfold wz; apply unsigned_lit; lia).
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  unfold lzf. rewrite mm_commit_lazy, mm_commit_na, !inzr_maps_subtract by (try assumption; rewrite ?HuA, ?Hun; lia).
  rewrite HuA, Hun. unfold in_range in Hx. rewrite Hx. cbn [negb]. rewrite !andb_true_r. reflexivity.
Qed.
Lemma lzf_commit_imp : forall x : word, lzf (mm_commit (wz A) (wz n) mo) x = true -> lzf mo x = true.
Proof.
  intros x H. destruct (in_range A n x) eqn:E; [| rewrite (lzf_commit_out x E) in H; exact H].
  exfalso. destruct HA as (G1 & G2 & G3). unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  assert (HuA : bv_unsigned (wz A) = A) by (unfold wz; apply unsigned_lit; lia).
  assert (Hun : bv_unsigned (wz n) = n) by (unfold wz; apply unsigned_lit; lia).
  pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  unfold lzf in H. rewrite mm_commit_lazy, inzr_maps_subtract in H by (try assumption; rewrite ?HuA, ?Hun; lia).
  rewrite HuA, Hun in H. unfold in_range in E. rewrite E in H. cbn [negb] in H. rewrite andb_false_r in H. discriminate.
Qed.

Lemma RTMODEL_commit : forall st0, RTMODEL st0 mo -> RTMODEL st0 (mm_commit (wz A) (wz n) mo).
Proof.
  intros st0 (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). destruct HA as (G1 & G2 & G3).
  unfold RTMODEL. rewrite mm_commit_maps. change (vm_limit (m_vmmaps (mm_commit (wz A) (wz n) mo))) with (vm_limit (m_vmmaps mo)).
  repeat (split; [assumption|]). split; [| split; [exact M8|]].
  - intros x Hx. rewrite lzf_commit_out; [exact (M7 x Hx)|].
    unfold in_range. unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    apply andb_false_iff. left. apply Z.leb_gt. lia.
  - intros e He x Hx. destruct (M9 e He x Hx) as [P1 P2]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    assert (HuA : bv_unsigned (wz A) = A) by (unfold wz; apply unsigned_lit; lia).
    assert (Hun : bv_unsigned (wz n) = n) by (unfold wz; apply unsigned_lit; lia).
    pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
    rewrite mm_commit_lazy, mm_commit_na, !inzr_maps_subtract by (try assumption; rewrite ?HuA, ?Hun; lia).
    rewrite P1, P2. split; reflexivity.
Qed.
Lemma GWIN_commit : forall st0 m g, GWIN st0 m mo g -> GWIN st0 m (mm_commit (wz A) (wz n) mo) g.
Proof. intros st0 m g H x Hw Hz Hr. apply (H x Hw); [| exact Hr]. apply lzf_commit_imp. exact Hz. Qed.

(* [comment removed for export] *)
Lemma prim_fixed_site : forall st0, RTMODEL st0 mo -> st_pbase st0 <= A -> A + n <= st_pbase st0 + PRIM_RES_SIZE -> A mod 4096 = 0 ->
  st_pbase st0 + PRIM_RES_SIZE <= CEIL -> mmap_fixed_site mo A n.
Proof.
  intros st0 HM HP1 HP2 HAL HP3. pose proof HM as (M1 & _). destruct HA as (G1 & G2 & G3).
  unfold mmap_fixed_site. unfold PRIM_RES_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  split; [exact HAL|]. split; [lia|]. split; [rewrite CEIL_eq; unfold CEIL; lia|]. split.
  - apply region_free_intro. intros b s Hin. pose proof (reserved_below mo b s HO Hin) as R. unfold AIMG_HI in R.
    unfold iv_overlap. rewrite !unsigned_lit by lia. apply andb_false_iff.
    first [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia].
  - unfold map_contains. apply existsb_exists. exists (wz (st_pbase st0), wz PRIM_RES_SIZE). split; [exact M1|]. cbn [fst snd].
    unfold wz, PRIM_RES_SIZE. rewrite !unsigned_lit by lia. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
End COMMIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_high_img' : forall W a n, Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha; [exact I|]. cbn. pose proof (Forall_inv HW) as H1. cbn [fst] in H1.
  split; [lia| apply IH; [exact (Forall_inv_tail HW)| exact Ha]].
Qed.
Lemma icpt_cells_high' : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> icpt_cells m -> icpt_cells m'.
Proof.
  intros W m m' MU HW IC. eapply icpt_cells_munch; [exact IC| exact MU|].
  unfold icpt_cell_ivs. repeat constructor; cbn [fst snd]; apply (disjoint_high_img' W _ _ HW); unfold AIMG_HI; lia.
Qed.
Lemma poison_cells_high' : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> poison_cells m -> poison_cells m'.
Proof.
  intros W m m' MU HW PC. eapply poison_cells_munch; [exact PC| exact MU|].
  unfold poison_cell_ivs. repeat constructor; cbn [fst snd]; apply (disjoint_high_img' W _ _ HW); unfold AIMG_HI; lia.
Qed.
Lemma mmap_consts_high : forall W m m', munch W m m' -> Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> mmap_consts m -> mmap_consts m'.
Proof.
  intros W m m' MU HW HC. eapply mmap_consts_munch; [exact HC| exact MU| ..]; apply (disjoint_high_img' W _ _ HW); unfold AIMG_HI; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma p_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (p_bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma p_le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le4, le_bytes_to_word.
  pose proof (p_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply p_Z_to_le_bytes_to_Z.
Qed.

Lemma p_u32arr_of_u8arr : forall segs m A bs k,
  u8arr segs m A bs -> length bs = (4 * k)%nat ->
  exists ws, length ws = k /\ u32arr segs m A ws.
Proof.
  intros segs m A bs k [Hb Hw] HL.
  assert (G : forall k bs, length bs = (4 * k)%nat -> exists ws, length ws = k /\ u32s ws = bs).
  { clear. induction k as [|k IH]; intros bs HL.
    - exists []. destruct bs; [split; reflexivity| cbn in HL; lia].
    - destruct (IH (skipn 4 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hlen & Hu).
      exists (le_bytes_to_word (firstn 4 bs) :: ws). split; [cbn; lia|].
      cbn [u32s]. rewrite Hu, p_le4_of_bytes by (rewrite length_firstn; lia). apply firstn_skipn. }
  destruct (G k bs HL) as (ws & Hlen & Hu). exists ws. split; [exact Hlen|]. split.
  - rewrite Hu. exact Hb.
  - rewrite Hlen. replace (4 * Z.of_nat k)%Z with (Z.of_nat (length bs)) by lia. exact Hw.
Qed.

Lemma p_u8arr_of_u32arr : forall segs m A ws, u32arr segs m A ws -> u8arr segs m A (u32s ws).
Proof. intros segs m A ws [Hb Hw]. split; [exact Hb|]. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32arr_app : forall m A ws1 ws2,
  u32arr bsegs m A ws1 -> u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr bsegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [B1 W1] [B2 W2]. split.
  - rewrite u32s_app. apply bytes_at_app. split; [exact B1|]. rewrite u32s_length. replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) by lia. exact B2.
  - rewrite length_app. replace (4 * Z.of_nat (length ws1 + length ws2)) with (4 * Z.of_nat (length ws1) + 4 * Z.of_nat (length ws2)) by lia.
    apply wr_at_app; [lia| lia|]. split; [exact W1| exact W2].
Qed.
Lemma u32arr_split : forall m A ws1 ws2,
  u32arr bsegs m A (ws1 ++ ws2) -> u32arr bsegs m A ws1 /\ u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 [B W]. rewrite u32s_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite u32s_length in B2.
  rewrite length_app in W. replace (4 * Z.of_nat (length ws1 + length ws2)) with (4 * Z.of_nat (length ws1) + 4 * Z.of_nat (length ws2)) in W by lia.
  apply wr_at_app in W; [| lia| lia]. destruct W as [W1 W2].
  replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) in B2 by lia.
  split; split; assumption.
Qed.
Lemma u32arr_of_C4 : forall m A (w : word), rw_cells bsegs m A [C4 w] -> u32arr bsegs m A [w].
Proof.
  intros m A w [[WF B] W]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn [cells_size Cells.csize] in W.
  split; [exact B| exact W].
Qed.
Lemma C4_of_u32arr : forall m A (w : word), u32arr bsegs m A [w] -> rw_cells bsegs m A [C4 w].
Proof.
  intros m A w [B W]. split; [split; [cbn; split; [reflexivity| exact I]|]|].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size Cells.csize]. exact W.
Qed.
(* [comment removed for export] *)
Lemma u32arr_of_cells : forall (k : nat) m A lo (f : Z -> Z),
  0 <= A -> A + 4 * (lo + Z.of_nat k) <= 2^64 -> 0 <= lo ->
  (forall i, lo <= i < lo + Z.of_nat k -> rw_cells bsegs m (A + 4 * i) [W4 (f i)]) ->
  u32arr bsegs m (A + 4 * lo) (map (fun j => wz (f (lo + Z.of_nat j))) (seq 0 k)).
Proof.
  induction k as [|k IH]; intros m A lo f HA HB Hlo CELLS.
  - cbn [map seq]. split; [apply bytes_at_nil; lia|]. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - rewrite seq_S, map_app. cbn [map]. apply u32arr_app.
    + apply IH; [lia| lia| lia|]. intros i Hi. apply CELLS. lia.
    + rewrite length_map, length_seq. replace (A + 4 * lo + 4 * Z.of_nat k) with (A + 4 * (lo + Z.of_nat k)) by lia.
      replace (lo + Z.of_nat (0 + k)) with (lo + Z.of_nat k) by lia. apply u32arr_of_C4. apply (CELLS (lo + Z.of_nat k)). lia.
Qed.
(* [comment removed for export] *)
Lemma cells_of_u32arr : forall m A ws i w, u32arr bsegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  rw_cells bsegs m (A + 4 * i) [C4 w].
Proof.
  intros m A ws i w ARR NTH Hi.
  destruct (nth_error_split ws (Z.to_nat i) w NTH) as (l1 & l2 & -> & L1).
  apply u32arr_split in ARR. destruct ARR as [_ ARR]. rewrite L1 in ARR. replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) in ARR by lia.
  change (w :: l2) with ([w] ++ l2) in ARR. apply u32arr_split in ARR. destruct ARR as [ARR _]. apply C4_of_u32arr. exact ARR.
Qed.


End CeilWrap.
End RTW_p_lib.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_mmapN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_p_efa.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_depot_n2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_mmapN.RTW_sec_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_map RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land_align18 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709289472 = x / 262144 * 262144.
Proof.
  intros x Hx.
  replace 18446744073709289472 with (Z.lxor (Z.ones 64) (Z.ones 18)) by reflexivity.
  replace (x / 262144 * 262144) with (Z.shiftl (Z.shiftr x 18) 18).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 18) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 18)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 18 + 18) with i by lia. rewrite (Z.ones_spec_high 18 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Definition A_EFA : Z := 0x34ddc.
Definition EFA_STACK : Z := 1200.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma efa_fast : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc RB n fam lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  AIMG_HI <= Rc -> Rc + 128 <= alloc_ceiling -> rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
  0 <= n < 2^40 -> 0 <= fam < 2^40 -> 4 * n <= fam ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 48, bv_unsigned sp)] lo m (fun a0' _ m' => a0' = wz 1 /\ rw_cells bsegs m' (Rc + 24) [C8 (Z_to_bv 64 fam)]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz Rc) (wz RB) (wz n) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_EFA) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO HR1 HR2 RI24 Hn Hfam LE.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_EFA, A_ALLOC, AIMG_HI in *. leaf_prep. idtac.
  carve_frame 48%nat ST.
  do 6 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (4 * n)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. do 5 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

(* [comment removed for export] *)
Definition efa_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition efa_pre_post (ra sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Rc U nm fam lo : Z) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) (j : list byte),
    ms1 = MS (mkR (wz 0x34e7c) (wz (bv_unsigned sp + -48)) gp tp x5 x6 x7 (wz nm) (wz U) (wz A_ALLOC) (wz U) (wz (nm - fam)) (wz 0x1890d) x14 x15 x16 x17
                  (wz (nm - fam)) (wz Rc) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (wz A_RAR_MAP) fc None m1 (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -48)
    /\ rw_cells bsegs m1 (bv_unsigned sp + -48) (efa_frame j s3 s2 s1 s0 ra).

Lemma efa_pre_map : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc RB n fam nm lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  AIMG_HI <= Rc -> Rc + 128 <= alloc_ceiling -> rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
  ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)] ->
  0 <= n -> 4 * n <= 2^29 -> 0 <= fam -> fam < 4 * n -> nm = (4 * n + 262143) / 262144 * 262144 ->
  AIMG_HI <= RB -> RB + 2^32 <= alloc_ceiling ->
  evt bsegs (efa_pre_post ra sp gp tp s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 F fc m Rc (RB + KFREEARRAY_OFF + fam) nm fam lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz Rc) (wz RB) (wz n) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_EFA) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO HR1 HR2 RI24 A56 Hn Hn2 Hfam LT Hnm HB1 HB2.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_EFA, A_ALLOC, AIMG_HI, KFREEARRAY_OFF in *. leaf_prep. idtac.
  assert (Hnm2 : 4 * n <= nm <= 2^29 /\ fam < nm) by (subst nm; Z.div_mod_to_equations; lia).
  carve_frame 48%nat ST.
  do 6 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (4 * n)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 nm) ltac:(f_equal; rewrite land_align18 by lia; subst nm; reflexivity).
  lstep. lstep. lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 (RB + 3758096384 + fam)) ltac:(f_equal; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold efa_pre_post, efa_frame, A_RAR_MAP. cbv delta [wz].
  nexists 13%nat. split. { cbv delta [mkR]. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma efa_ref_tail : forall (ra sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc U sz nm lo : Z) (j : list byte),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -48) (efa_frame j s3 s2 s1 s0 ra) ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp)] lo m (fun a0' _ _ => a0' = wz 0))
    (MS (mkR (wz 0x34e7c) (wz (bv_unsigned sp + -48)) gp tp x5 x6 x7 (wz nm) (wz U) (wz 0) x11 x12 x13 x14 x15 x16 x17 (wz sz) (wz Rc) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x34e7c) fc None m (seg_rom bsegs)).
Proof.
  intros until j. intros MI ST CEIL LO FR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof aceil as CEILlo.
  unfold efa_frame in FR. cbv beta delta [wz] in *.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. do 5 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. reflexivity.
Qed.

Section EFAG.
  Hypothesis PS : poison_shadow_spec.

  (* [comment removed for export] *)
  Lemma efa_grant_tail : forall (ra sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (Rc U sz nm fam lo : Z) (j shj : list byte) (tj1 tj2 : word),
    icpt_cells m -> poison_cells m -> leafc st m -> RTWF st -> tp = wz ATP -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo + EFA_STACK <= bv_unsigned sp ->
    rw_cells bsegs m (bv_unsigned sp + -48) (efa_frame j s3 s2 s1 s0 ra) ->
    rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)] -> KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
    (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) -> (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st) ->
    rw_cells bsegs m (st_t st + 2872) [C8 tj1; C8 tj2] ->
    U mod 8 = 0 -> sz mod 8 = 0 -> 8 <= sz -> app_range U sz -> KHIGHMEM_BEG <= U -> 0 <= nm < 2^64 ->
    rw_cells bsegs m (SH U) [CB (Z.to_nat (sz / 8)) shj] ->
    evt bsegs (fun ms2 => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m2 : word -> option byte) (tj1' tj2' : word),
                 ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz 1) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                          F (ret_pc ra) fc None m2 (seg_rom bsegs)
                 /\ munch [(lo, bv_unsigned sp); (SH U, SH U + sz / 8); (st_t st + 2872, st_t st + 2888); (Rc + 24, Rc + 32)] m m2
                 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
                 /\ rw_cells bsegs m2 (Rc + 24) [C8 (Z_to_bv 64 nm)]
                 /\ rw_cells bsegs m2 (SH U) [CB (Z.to_nat (sz / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (sz / 8)))]
                 /\ rw_cells bsegs m2 (st_t st + 2872) [C8 tj1'; C8 tj2'])
      (MS (mkR (wz 0x34e7c) (wz (bv_unsigned sp + -48)) gp tp x5 x6 x7 (wz nm) (wz U) (wz U) x11 x12 x13 x14 x15 x16 x17 (wz sz) (wz Rc) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x34e7c) fc None m (seg_rom bsegs)).
  Proof.
    intros until tj2. intros IC PC LC WF TP MI ST CEIL LO FR RI24 HR1 HR2 DJC DJT TST U8 SZ8 SZ1 AR HU Hnm SHJ. unfold KHIGHMEM_BEG, AIMG_HI in HU. olin_all.
    pose proof (munch_refl [(lo, bv_unsigned sp); (SH U, SH U + sz / 8); (st_t st + 2872, st_t st + 2888); (Rc + 24, Rc + 32)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    pose proof (t_range st WF) as TR. olin TR. pose proof (ctx_range st WF) as CR. olin CR. unfold KHIGHMEM_BEG, AIMG_HI in TR, CR, HR1. olin_all. unfold EFA_STACK in LO.
    pose proof (app_range_lt47 U sz AR) as UR. pose proof (rt_SH_bounds U ltac:(lia)) as SHR.
    unfold efa_frame in FR. cbv beta delta [wz] in *. subst tp.
    assert (SHE : SH U + sz / 8 <= 17594333495296) by (unfold SH, SHADOW_OFFSET; unfold SH, SHADOW_OFFSET in SHR; clear -UR SHR SZ1; Z.div_mod_to_equations; lia).
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    unfold poison_shadow_spec, APOISON_STACK, APOISON_SHADOW in PS.
    sepM. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply PS; [exact IC| exact PC| exact MI| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia
                                  | reflexivity| reflexivity| reflexivity| exact U8| exact SZ8| exact SZ1| exact AR| lia| lia| exact SHJ]
                      | cbv beta; unfold poison_shadow_post, APOISON_STACK; post_call bsegs mm ] end.
    rewrite ?unsigned_lit in * by lia.
    restk. fixMI.
    lstep. (* [comment removed for export] *)
    pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LC1 : leafc st mm) by
       (eapply (leafc_munch st _ _ _ MU WM); [| exact LC]; intros lo' hi' a b Hin Hab; cbn in Hin, Hab;
        destruct Hin as [E|[E|[E|[E|[]]]]]; injection E; intros; subst;
        destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; (lia_on CEIL SZ1 HU CR SHR OLx0 SHE OLx CT HR1 DJC)) end.
    sepM. call get_thread_stats_c; [exact LC1| exact WF| exact MI| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
    after_call. rewrite ?unsigned_lit in * by lia. unfold T_STATS.
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. do 5 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. nexists 17%nat. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact RI24|]. split; [exact PC0| exact TST].
  Qed.
End EFAG.


Lemma stk_of_some : forall (m : word -> option byte) lo hi, 0 <= lo -> hi <= 2^64 ->
  (forall x : word, lo <= bv_unsigned x < hi -> m x <> None) -> stk bsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  specialize (H (wa a) ltac:(rewrite wa_unsigned by lia; lia)).
  destruct (m (wa a)) as [b|] eqn:E; [| congruence].
  unfold wview, mrd. rewrite E. split; [discriminate| exists b; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section EFAW.
  Hypothesis PS : poison_shadow_spec.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate) (Rc RB n fam lo : Z) (tj1 tj2 : word).
  Let nm := (4 * n + 262143) / 262144 * 262144.
  Let U := RB + KFREEARRAY_OFF + fam.
  Let sz := nm - fam.
  Hypothesis HC : mmap_consts m.
  Hypothesis IC : icpt_cells m.
  Hypothesis PC : poison_cells m.
  Hypothesis LC : leafc st m.
  Hypothesis WF : RTWF st.
  Hypothesis TP : tp = wz ATP.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo + EFA_STACK <= bv_unsigned sp.
  Hypothesis RI24 : rw_cells bsegs m (Rc + 24) [C8 (Z_to_bv 64 fam)].
  Hypothesis A56 : ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)].
  Hypothesis TST : rw_cells bsegs m (st_t st + 2872) [C8 tj1; C8 tj2].
  Hypothesis HRc : KHIGHMEM_BEG <= Rc /\ Rc + 128 <= alloc_ceiling /\ (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) /\ (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st)
                   /\ RB + 2^32 <= Rc.
  Hypothesis HRB : KHIGHMEM_BEG <= RB /\ RB + 2^32 <= alloc_ceiling /\ RB mod 32768 = 0
                   /\ (st_ctx st + 160 <= RB \/ RB + 2^32 <= st_ctx st) /\ (st_t st + 4096 <= RB \/ RB + 2^32 <= st_t st).
  Hypothesis Hn : 0 <= n /\ 4 * n <= 2^29.
  Hypothesis Hfam : 0 <= fam /\ fam mod 262144 = 0 /\ 4 * n <= fam + 262144 /\ fam <= 2^29.
  Hypothesis HO : LOK bsegs mo.
  Hypothesis SITE : fam < 4 * n -> mmap_fixed_site mo U sz.
  Hypothesis LZS : forall x : word, SH U <= bv_unsigned x < SH U + sz / 8 -> lzf mo x = true.
  Hypothesis HVIS : forall x : word, SH U <= bv_unsigned x < SH U + sz / 8 -> lzf mo x = true -> in_winb G x = true -> m x <> None.
  Hypothesis HR : fam < 4 * n -> sz + sz / 8 <= R.

  Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz Rc) (wz RB) (wz n) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_EFA) fc None m (seg_rom bsegs).
  Let RET (r : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) :=
    MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom bsegs).

  Lemma sz_val : fam < 4 * n -> sz = 262144.
  Proof. intros LT. subst sz nm. (nelimp Hfam 4%nat; intros F1 F2 F3 _). Z.div_mod_to_equations. lia. Qed.
  Lemma fam_hi : fam < 4 * n -> fam + 262144 <= 2^29.
  Proof. intros LT. pose proof (sz_val LT) as SV. subst sz nm. (nelimp Hfam 4%nat; intros F1 F2 F3 _). destruct Hn as [Hn1 Hn2]. Z.div_mod_to_equations. lia. Qed.

  Lemma efa_spec : forall (spin : bool) (P : machine_state -> Model -> lghost -> Prop),
    (* [comment removed for export] *)
    (4 * n <= fam -> forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte),
       mem_inv bsegs m' -> munch [(lo, bv_unsigned sp)] m m' -> wmono bsegs m m' -> stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' (Rc + 24) [C8 (Z_to_bv 64 fam)] ->
       LSCPS bsegs P (RET 1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') mo (mkG G R)) ->
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    True ->
    (* [comment removed for export] *)
    (fam < 4 * n -> forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (m' : word -> option byte) (tj1' tj2' : word),
       mem_inv bsegs m' ->
       munch [(lo, bv_unsigned sp); (U, U + sz); (SH U, SH U + sz / 8); (st_t st + 2872, st_t st + 2888); (Rc + 24, Rc + 32)] m m' ->
       wmono bsegs m m' -> stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' (Rc + 24) [C8 (Z_to_bv 64 nm)] -> stk bsegs m' U (U + sz) ->
       rw_cells bsegs m' (SH U) [CB (Z.to_nat (sz / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (sz / 8)))] ->
       rw_cells bsegs m' (st_t st + 2872) [C8 tj1'; C8 tj2'] ->
       LSCPS bsegs P (RET 1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m') (mm_commit (wz U) (wz sz) mo)
             (mkG ((SH U, SH U + sz / 8) :: G) (R - sz - sz / 8))) ->
    LSCPS bsegs P ENTRY mo (mkG G R).
  Proof.
    intros spin P K1 _ KG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct LO as [CEIL LO2]. pose proof CEIL as CEILn. idtac. unfold EFA_STACK in LO2.
    (nelimp HRc 5%nat; intros RC1 RC2 RC3 RC4 RC5). (nelimp HRB 5%nat; intros RB1 RB2 RB3 RB4 RB5). pose proof fam_hi as F4. destruct Hn as [Hn1 Hn2]. (nelimp Hfam 4%nat; intros F1 F2 F3 F5).
    pose proof RC2 as RC2n. idtac. pose proof RB2 as RB2n. idtac.
    destruct (Z_lt_le_dec fam (4 * n)) as [LT|GE].
    2:{ (* [comment removed for export] *)
      eapply lscps_evt_then.
      { eapply efa_fast; [exact MI| exact ST| exact CEIL| lia| unfold AIMG_HI, KHIGHMEM_BEG in *; lia| exact RC2| exact RI24| (lia_on Hn Hn2 F5 GE)| lia| exact GE]. }
      cbv beta. intros ms' nelH_; (nelim nelH_ 23%nat; intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m' -> MU WM MI' ST' -> RI').
      apply (K1 GE); [exact MI'| eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn; intros; (lia_on HRc HRB LO2 RC3 RC4 RC5 RB4 RB5 Hn1 H)| exact WM| exact ST'| exact RI']. }
    (* [comment removed for export] *)
    pose proof (sz_val LT) as SZV. assert (EU : U = RB + KFREEARRAY_OFF + fam) by reflexivity. assert (ESZ : sz = nm - fam) by reflexivity. clearbody sz U.
    pose proof EU as EUn. unfold KFREEARRAY_OFF in EUn.
    eapply lscps_evt_then.
    { eapply (efa_pre_map ra sp) with (nm := nm); [exact MI| exact ST| exact CEIL| lia| unfold AIMG_HI, KHIGHMEM_BEG in *; lia| exact RC2| exact RI24| exact A56| lia| lia| lia| exact LT| reflexivity| unfold AIMG_HI, KHIGHMEM_BEG in *; lia| exact RB2]. }
    cbv beta. intros ms1 nelH_; (nelim nelH_ 19%nat; intros x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m1 j -> MU1 WM1 MI1 ST1 FR1).
    rewrite <- EU, <- ESZ.
    assert (E48 : bv_unsigned (wz (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (unfold wz; apply unsigned_lit; lia).
    assert (HC1 : mmap_consts m1).
    { eapply mmap_consts_munch; [exact HC| exact MU1| ..]; cbn; (lia_on CEILn LT). }
    assert (HU : KHIGHMEM_BEG <= U /\ U + sz <= RB + 2^32 /\ U mod 32768 = 0).
    { subst U. unfold KFREEARRAY_OFF, KHIGHMEM_BEG, AIMG_HI in *. split; [lia|]. split; [lia|].
      clear - RB3 F2. Z.div_mod_to_equations. lia. }
    (nelim HU 3%nat; intros U1 U2 U3). unfold KHIGHMEM_BEG, AIMG_HI in U1, RC1, RB1. olin_all.
    replace (wz A_RAR_MAP) with (wz RTW_p_map.A_RAR_MAP) by reflexivity.
    eapply (map_tol_spec (wz 216700) (wz (bv_unsigned sp + -48))) with (lo := lo) (spin := spin);
      [exact HC1| exact MI1| rewrite E48; exact ST1| rewrite E48; split; [exact CEIL| unfold MAPTOL_STACK; lia]
      | (lia_on RC5 RB1 F1 F2 LT SZV ESZ U1)| clear -U3; Z.div_mod_to_equations; lia| unfold AIMG_HI; lia| lia| exact (SITE LT)| lia| |].
    - (* [comment removed for export] *) exact I.
    - (* [comment removed for export] *)
      intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 MI2 MU2 WM2 ST2 ZN. rewrite E48 in MU2, ST2.
      cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 216700)) with (Z_to_bv 64 216700 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof FR1 as FR2. eapply (rw_cells_transport bsegs _ m1 m2) in FR2; [| exact MU2| exact WM2| cbn; lia]. unfold efa_frame in FR2.
      pose proof (t_range st WF) as TR. olin TR. pose proof (ctx_range st WF) as CR. olin CR. unfold KHIGHMEM_BEG, AIMG_HI in TR, CR. olin_all.
      assert (SHU : SH U mod 4096 = 0 /\ 2147450880 <= SH U /\ SH U + sz / 8 <= 17594333495296 /\ SH (U + sz) = SH U + sz / 8).
      { unfold SH, SHADOW_OFFSET. clear - U1 U2 U3 RB2n SZV. Z.div_mod_to_equations. lia. }
      (nelim SHU 4%nat; intros SH1 SH2 SH3 SH4).
      eapply (lscps_open bsegs _ _ _ G (R - sz) (SH U) (SH U + sz / 8)).
      { unfold win_ok. cbn [fst snd]. rewrite SZV in *. clear - SH1 SH2 SH3. Z.div_mod_to_equations. lia. }
      { replace (4096 * ((SH U + sz / 8 - SH U) / 4096)) with (sz / 8) by (rewrite SZV; clear; Z.div_mod_to_equations; lia). pose proof (HR LT). lia. }
      intros mv' Emv ZFN FRZ. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS msw] in Emv |- *.
      replace (4096 * ((SH U + sz / 8 - SH U) / 4096)) with (sz / 8) by (rewrite SZV; clear; Z.div_mod_to_equations; lia).
      (* [comment removed for export] *)
      assert (VNN : forall x : word, SH U <= bv_unsigned x < SH U + sz / 8 -> mv' x <> None).
      { intros x Hx. pose proof (LZS x Hx) as Hz. destruct (in_winb G x) eqn:EW.
        - assert (V0 : m x <> None) by (apply (HVIS x Hx Hz EW)).
          assert (V1 : m1 x <> None) by (rewrite (MU1 x); [exact V0|]; cbn; lia).
          assert (V2 : m2 x <> None) by (rewrite (MU2 x); [exact V1|]; cbn; (lia_on HRc HRB CEILn RC5 RB1 F1 LT EUn U1 SH2 SH3 Hx)).
          rewrite Emv, (open_mem_mono _ _ _ _ _ V2). exact V2.
        - rewrite (FRZ x Hx); [discriminate| | exact EW]. unfold wz. rewrite (lzf_commit_out mo U sz HO); [exact Hz| unfold RT_artF.CEIL, KHIGHMEM_BEG, AIMG_HI; (lia_on HRc HRB RC5 RB1 RC2n LT SZV ESZ EUn U1 U2 TR CR SH2)|].
          unfold in_range. apply andb_false_iff. left. apply Z.leb_gt. lia. }
      assert (STSH : stk bsegs mv' (SH U) (SH U + sz / 8)) by (apply stk_of_some; [lia| lia| exact VNN]).
      (nelim (stk_carve bsegs mv' (SH U) (SH U + sz / 8) (Z.to_nat (sz / 8)) STSH ltac:((lia_on HRc HRB RC5 RB1 F1 LT SZV ESZ U1 SH2))) 3%nat; intros _ shj SHJ).
      replace (SH U + sz / 8 - Z.of_nat (Z.to_nat (sz / 8))) with (SH U) in SHJ by (lia_on HRc HRB RC5 RB1 F1 LT SZV ESZ U1 SH2).
      (* [comment removed for export] *)
      pose proof (rw_cells_open bsegs _ (SH U) (SH U + sz / 8) m2 _ _ ZFN FR2) as FRv. rewrite <- Emv in FRv.
      pose proof (rw_cells_open bsegs _ (SH U) (SH U + sz / 8) m2 _ _ ZFN ZN) as ZNv. rewrite <- Emv in ZNv.
      pose proof (stk_open bsegs _ (SH U) (SH U + sz / 8) m2 _ _ ZFN ST2) as STv. rewrite <- Emv in STv.
      pose proof (mem_inv_open bsegs _ (SH U) (SH U + sz / 8) m2 ZFN MI2) as MIv. rewrite <- Emv in MIv.
      assert (MUv : munch [(lo, bv_unsigned sp); (U, U + sz); (SH U, SH U + sz / 8)] m mv').
      { rewrite Emv. apply munch_open_r; [| cbn; intros; lia].
        eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn; intros; (lia_on HRc HRB RC3 RC4 RB4 RB5 LT H). }
      assert (WMv : wmono bsegs m mv').
      { rewrite Emv. apply wmono_open. eapply wmono_trans; [exact WM1| exact WM2]. }
      assert (HWv : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(lo, bv_unsigned sp); (U, U + sz); (SH U, SH U + sz / 8)]).
      { repeat constructor; cbn [fst]; unfold AIMG_HI; (lia_on CEILn RB1 LT U1 SH2). }
      pose proof (icpt_cells_high' _ _ _ MUv HWv IC) as ICv. pose proof (poison_cells_high' _ _ _ MUv HWv PC) as PCv.
      pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
      assert (LCv : leafc st mv').
      { eapply (leafc_munch st _ _ _ MUv WMv); [| exact LC]. intros lo' hi' a b Hin Hab. cbn in Hin, Hab.
        destruct Hin as [E|[E|[E|[]]]]; injection E; intros; subst;
        destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; (lia_on CEIL RB1 SH2 HRB F1 CR EUn U2 OLx0 SH3). }
      pose proof RI24 as RIv. eapply (rw_cells_transport bsegs _ m mv') in RIv; [| exact MUv| exact WMv| cbn; (lia_on HRc HRB CEILn RC5 RB1 F1 RC2n LT SZV ESZ EUn U1 U2 TR CR SH2 SH3)].
      pose proof TST as TSv. eapply (rw_cells_transport bsegs _ m mv') in TSv; [| exact MUv| exact WMv| cbn; (lia_on HRB CEILn F4 F1 LT SZV EUn TR OLx SH2 SH3)].
      clear FR2 ZN ST2 MI2 VNN STSH.
      lazymatch goal with |- LSCPS _ _ (msw (MS ?RR ?FF ?p ?c ?v ?mm ?ro) ?mv) _ _ => change (msw (MS RR FF p c v mm ro) mv) with (MS RR FF p c v mv ro) end.
      eapply lscps_evt_then.
      { eapply (efa_grant_tail PS ra sp); [exact ICv| exact PCv| exact LCv| exact WF| exact TP| exact MIv| exact STv| exact CEIL| unfold EFA_STACK; lia| exact FRv| exact RIv
          | unfold KHIGHMEM_BEG, AIMG_HI; lia| exact RC2| exact RC3| exact RC4| exact TSv| clear -U3; Z.div_mod_to_equations; lia| rewrite SZV; reflexivity| lia
          | right; unfold highmem_range, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; (lia_on HRc SZV U1 U2)| unfold KHIGHMEM_BEG, AIMG_HI; lia| subst nm; Z.div_mod_to_equations; lia| exact SHJ]. }
      cbv beta. intros ms3 nelH_; (nelim nelH_ 25%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 tj1' tj2' -> MU3 WM3 MI3 ST3 RI3 SH3' TS3).
      cbv beta delta [wz] in KG. apply (KG LT) with (tj1' := tj1') (tj2' := tj2'); [exact MI3| | eapply wmono_trans; [exact WMv| exact WM3]| exact ST3| exact RI3| | exact SH3'| exact TS3].
      + eapply munch_trans; [eapply munch_weaken; [| exact MUv]| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn; intros; (lia_on HRc HRB RC3 RC4 RB4 RB5 LT H).
      + apply (stk_of_rw_cells bsegs) in ZNv. cbn [cells_size Cells.csize] in ZNv. replace (U + Z.of_nat (Z.to_nat sz + 0)) with (U + sz) in ZNv by (lia_on HRc HRB RC5 RB1 F1 LT SZV ESZ U1 SH2).
        eapply (stk_transport_disjoint bsegs _ mv' m3); [exact ZNv| exact MU3| exact WM3| cbn; (lia_on HRc HRB CEILn RC5 RB1 F1 RC2n LT SZV ESZ EUn U1 U2 TR CR SH2 SH3)].
  Qed.
End EFAW.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
End RTW_p_efa.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_loops.
Module RTW_p_gfa.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].

Definition A_GFA : Z := 0x36e10.
Definition MTX_LOCKED : Z := 1152921504606846976.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition gfa_frame (j : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma p_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (p_bytes_le_to_Z_range bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in B.
  rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). rewrite <- L. apply p_Z_to_le_bytes_to_Z.
Qed.
Lemma rw_cells_recast_p : forall m A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
(* [comment removed for export] *)
Lemma rinfo_split72 : forall m Rc (alloc z1 mapped z2 : word) jr exh je js,
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; CB 56 js] ->
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 (le_bytes_to_word (firstn 8 js)); CB 48 (skipn 8 js)].
Proof.
  intros m Rc alloc z1 mapped z2 jr exh je js H.
  pose proof H as [[W _] _]. cbn in W.
  assert (LJ : length js = 56%nat) by tauto.
  eapply rw_cells_recast_p; [exact H| cbn; rewrite ?length_firstn, ?length_skipn; intuition lia|].
  cbn [cells_bytes cbytes]. rewrite p_le8_of_bytes by (rewrite length_firstn; lia).
  rewrite <- (firstn_skipn 8 js) at 3. rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma rinfo_join72 : forall m Rc (alloc z1 mapped z2 w : word) jr exh je js2,
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 w; CB 48 js2] ->
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; CB 56 (le8 w ++ js2)].
Proof.
  intros m Rc alloc z1 mapped z2 w jr exh je js2 H.
  pose proof H as [[W _] _]. cbn in W.
  eapply rw_cells_recast_p; [exact H| cbn; rewrite ?length_app, ?length_le8; intuition lia|].
  cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfa_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Rc FA stt c CH n lo : Z) (sem nfw : word) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x10 x15 x16 x17 x21 x22 x24 x25 x28 x29 x30 x31 : word) (j : list byte) (m1 : word -> option byte),
    ms1 = MS (mkR ra (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz A_ALLOC) x10 (wz stt) (wz c) (wz CH) (wz n) x15 x16 x17
                  s2 (wz 2305843009213693952) (wz FA) x21 x22 (wz MTX_LOCKED) x24 x25 s10 s11 x28 x29 x30 x31)
             F (wz 0x36f60) fc None m1 (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m1 (bv_unsigned sp + -128) (gfa_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m1 Rc [C8 (wz MTX_LOCKED); C8 sem; C8 nfw].

Lemma gfa_A : forall (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S RIS Rc stt c CH n lo : Z) (sem nfw : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 128 <= bv_unsigned sp ->
  ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)] -> ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 RIS)] ->
  rw_cells bsegs m Rc [C8 (wz 0); C8 sem; C8 nfw] ->
  Rc = RIS + 128 * c -> KHIGHMEM_BEG <= RIS -> RIS + 4096 <= alloc_ceiling -> RIS mod 4096 = 0 -> 1 <= c <= 30 ->
  KHIGHMEM_BEG <= S -> S + 2^37 + 4096 <= alloc_ceiling ->
  evt bsegs (gfa_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Rc (S + c * 2^32 + KFREEARRAY_OFF) stt c CH n lo sem nfw)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz stt) (wz c) (wz CH) (wz n) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_GFA) fc None m (seg_rom bsegs)).
Proof.
  intros until nfw. intros MI ST CEIL LO AC32 AC48 MTX ERc HR1 HR2 HRA Hc HS1 HS2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc, Rc + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_GFA, A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, MTX_LOCKED in *. leaf_prep. idtac.
  assert (RcR : 17594333495296 <= Rc /\ Rc + 128 <= alloc_ceiling /\ Rc mod 8 = 0) by (subst Rc; split; [lia|]; split; [lia|]; clear -HRA; Z.div_mod_to_equations; lia).
  (nelim RcR 3%nat; intros R1 R2 R8).
  destruct (ex_intro (fun r => r = Rc) _ eq_refl) as [r Hr]. rewrite <- Hr in MTX, MU |- *.
  carve_frame 128%nat ST.
  do 14 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  do 8 lstep. fl. (* [comment removed for export] *)
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 r) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; subst r Rc; lia).
  lstep. (* [comment removed for export] *)
  setreg 20 (Z_to_bv 64 (S + c * 2^32 + 3758096384)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia).
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. fl. lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. unfold gfa_A_post, gfa_frame. subst r.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact MTX].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_unlock : forall (x1 sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc r lo : Z) (j : list byte) (sem nfw : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo + 128 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -128) (gfa_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 nfw] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> Rc mod 8 = 0 -> 0 <= r <= 1 ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz r) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 Rc [C8 (wz 0); C8 sem; C8 nfw])
    (MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz r) x10 x11 x12 x13 x14 x15 x16 x17 x18 (wz 2305843009213693952) x20 x21 x22 (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x36fa8) fc None m (seg_rom bsegs)).
Proof.
  intros until nfw. intros MI ST CEIL LO FR MTX HR1 HR2 R8 Hr.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc, Rc + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, MTX_LOCKED, gfa_frame in *. cbv beta delta [wz] in *.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX, MU |- *.
  assert (QR : 17594333495296 <= q < alloc_ceiling /\ q mod 8 = 0) by (subst q; lia). clear Hq.
  lstep. (* [comment removed for export] *)
  do 6 lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RO98 : ro_cells bsegs mm 0x103e0 [CB 8 [Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0x0f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0xaf]])
      by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]) end.
  lstep. fl. clear RO98. (* [comment removed for export] *)
  do 6 lstep. fl. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. fl. lstep. if_lit. (* [comment removed for export] *)
  do 7 lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 13 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. nexists 15%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact MTX].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_tail : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (Rc FA CH n base lo : Z) (j : list byte) (sem : word) (fa : list Z) (dpre : list word)
    (alloc z1 mapped z2 : word) (exh : byte) (jr je js2 : list byte) (sna : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo + 128 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -128) (gfa_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 base)] ->
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 sna; CB 48 js2] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> Rc mod 8 = 0 ->
  KHIGHMEM_BEG <= FA -> FA + 2^29 <= Rc -> (4096 <= CH /\ (CH + 4 * n <= AIMG_LO \/ AIMG_HI <= CH)) -> CH + 4 * n <= alloc_ceiling -> (CH + 4 * n <= Rc \/ Rc + 128 <= CH) -> (CH + 4 * n <= FA \/ FA + 2^29 <= CH) ->
  1 <= n <= 8 -> 0 <= base -> 4 * (base + n) <= 2^29 ->
  length fa = Z.to_nat n -> Forall (fun z => 0 <= z < 2^31) fa -> length dpre = Z.to_nat n ->
  u32arr bsegs m (FA + 4 * base) (wl fa) -> u32arr bsegs m CH dpre ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2 (sna' : word),
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz 1) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8); (Rc + 72, Rc + 80); (CH, CH + 4 * n)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 Rc [C8 (wz 0); C8 sem; C8 (Z_to_bv 64 base)]
      /\ rw_cells bsegs m2 (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 sna'; CB 48 js2]
      /\ u32arr bsegs m2 (FA + 4 * base) (wl fa) /\ u32arr bsegs m2 CH (wl fa))
    (MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) x9 x10 x11 x12 (wz CH) (wz n) (wz base) x16 x17 x18 (wz 2305843009213693952) (wz FA) x21 x22 (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x36f74) fc None m (seg_rom bsegs)).
Proof.
  intros until sna. intros MI ST CEIL LO FR MTX RIb HR1 HR2 R8 HF1 HF2 HC1 HC2 DISJ DISJ2 Hn Hb Hbn LF SMALL LD SRC DST.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, MTX_LOCKED in *. cbv beta delta [wz] in *.
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 20 (Z_to_bv 64 (FA + 4 * base + 4 * 0)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  setreg 11 (Z_to_bv 64 (CH + 4 * n)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  setreg 13 (Z_to_bv 64 (CH + 4 * 0)) ltac:(f_equal; lia).
  eapply (copy_loop_gfa (Z.to_nat n) 0 n (FA + 4 * base) CH fa dpre);
    [lia| lia| lia| unfold AIMG_LO, AIMG_HI; lia| unfold AIMG_LO, AIMG_HI; blia| lia| exact LF| exact SMALL| exact LD| exact SRC| cbn [Z.to_nat firstn app]; exact DST| exact MI|].
  intros m1 x12' SRC1 DST1 MU1 WM1 MI1.
  assert (MU : munch [(lo, bv_unsigned sp); (Rc, Rc + 8); (Rc + 72, Rc + 80); (CH, CH + 4 * n)] m m1) by (eapply munch_weaken; [| exact MU1]; subfp).
  pose proof WM1 as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc, Rc + 8); (Rc + 72, Rc + 80)] m1) as MU'. pose proof (wmono_refl bsegs m1) as WM'.
  hide SRC1. hide DST1.
  pose proof FR as FR1. eapply (rw_cells_transport bsegs _ m m1) in FR1; [| exact MU1| exact WM1| cbn; lia].
  pose proof MTX as MTX1. eapply (rw_cells_transport bsegs _ m m1) in MTX1; [| exact MU1| exact WM1| cbn; lia].
  pose proof RIb as RIb1. eapply (rw_cells_transport bsegs _ m m1) in RIb1; [| exact MU1| exact WM1| cbn; lia].
  pose proof ST as ST1. eapply (stk_transport_disjoint bsegs _ m m1) in ST1; [| exact MU1| exact WM1| cbn; lia].
  clear FR MTX RIb ST SRC DST MU1 WM1.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX1, RIb1, MU, MU' |- *.
  assert (QR : 17594333495296 <= q < alloc_ceiling /\ q mod 8 = 0) by (subst q; lia).
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  eapply evt_mono.
  { eapply (gfa_unlock _ sp gp tp) with (lo := lo) (r := 1); [exact MI1| exact ST1| exact CEIL| lia| exact FR1| exact MTX1| unfold KHIGHMEM_BEG, AIMG_HI; subst q; lia| idtac; lia| lia| lia]. }
  cbv beta. intros ms2 nelH_; (nelim nelH_ 21%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 -> MU2 WM2 MI2 ST2 MTX2).
  subst q. nexists 16%nat. split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; subfp. }
  split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact MTX2|].
  split. { eapply (rw_cells_transport bsegs _ _ m2); [exact RIb1| exact MU2| exact WM2| cbn; lia]. }
  unhide SRC1. unhide DST1.
  split. { eapply (u32arr_transport bsegs _ _ m2); [| exact MU2| exact WM2| cbn; rewrite wl_length, LF; lia]. eapply (u32arr_transport bsegs _ m1); [exact SRC1| exact MU'| exact WM'| cbn; rewrite wl_length, LF; lia]. }
  eapply (u32arr_transport bsegs _ _ m2); [| exact MU2| exact WM2| cbn; rewrite wl_length, LF; lia]. eapply (u32arr_transport bsegs _ m1); [exact DST1| exact MU'| exact WM'| cbn; rewrite wl_length, LF; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gfa_have : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc FA CH n nf : Z) (sem : word),
  mem_inv bsegs m ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 nf)] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= n <= 8 -> n <= nf < 2^40 ->
  evt bsegs (fun ms1 => exists m1,
      ms1 = MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) x9 x10 x11 x12 (wz CH) (wz n) (wz (nf - n)) x16 x17 x18 (wz 2305843009213693952) (wz FA) x21 x22 (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
               F (wz 0x36f74) fc None m1 (seg_rom bsegs)
      /\ munch [(Rc + 16, Rc + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 (nf - n))])
    (MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) x9 x10 x11 x12 (wz CH) (wz n) x15 x16 x17 x18 (wz 2305843009213693952) (wz FA) x21 x22 (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x36f60) fc None m (seg_rom bsegs)).
Proof.
  intros until sem. intros MI MTX HR1 HR2 Hn Hnf.
  pose proof (munch_refl [(Rc + 16, Rc + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold KHIGHMEM_BEG, AIMG_HI, MTX_LOCKED in *. cbv beta delta [wz] in *. idtac.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX, MU |- *.
  assert (QR : 17594333495296 <= q < alloc_ceiling) by (subst q; lia).
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. subst q. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact MTX].
Qed.

(* [comment removed for export] *)
Lemma gfa_need : forall (x1 sp gp tp x5 x6 x7 x10 x15 x16 x17 x18 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc FA stt c CH n nf : Z) (sem : word),
  mem_inv bsegs m ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 nf)] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= n <= 8 -> 0 <= nf < n ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz A_ALLOC) (wz A_ALLOC) (wz stt) (wz c) (wz Rc) (wz (n - nf)) (wz nf) x16 x17
                    x10 (wz 2305843009213693952) (wz FA) (wz CH) (wz n) (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
               F (wz 0x37118) fc None m (seg_rom bsegs))
    (MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz A_ALLOC) x10 (wz stt) (wz c) (wz CH) (wz n) x15 x16 x17 x18 (wz 2305843009213693952) (wz FA) x21 x22 (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x36f60) fc None m (seg_rom bsegs)).
Proof.
  intros until sem. intros MI MTX HR1 HR2 Hn Hnf.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold KHIGHMEM_BEG, AIMG_HI, MTX_LOCKED, A_ALLOC in *. cbv beta delta [wz] in *. idtac.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX |- *.
  assert (QR : 17594333495296 <= q < alloc_ceiling) by (subst q; lia).
  lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. subst q. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gfa_ok : forall (sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc FA CH n nf' : Z) (sem : word),
  mem_inv bsegs m ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 nf')] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= n <= 8 -> n <= nf' < 2^40 ->
  evt bsegs (fun ms1 => exists m1,
      ms1 = MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz A_ALLOC) x18 x11 x12 (wz CH) (wz n) (wz (nf' - n)) x16 x17
                    x18 (wz 2305843009213693952) (wz FA) (wz CH) (wz n) (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
               F (wz 0x36f74) fc None m1 (seg_rom bsegs)
      /\ munch [(Rc + 16, Rc + 24)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 (nf' - n))])
    (MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz A_ALLOC) (wz 1) x11 x12 x13 x14 x15 x16 x17
             x18 (wz 2305843009213693952) (wz FA) (wz CH) (wz n) (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x370cc) fc None m (seg_rom bsegs)).
Proof.
  intros until sem. intros MI MTX HR1 HR2 Hn Hnf.
  pose proof (munch_refl [(Rc + 16, Rc + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold KHIGHMEM_BEG, AIMG_HI, MTX_LOCKED, A_ALLOC in *. cbv beta delta [wz] in *. idtac.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX, MU |- *.
  assert (QR : 17594333495296 <= q < alloc_ceiling) by (subst q; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. subst q. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact MTX].
Qed.

(* [comment removed for export] *)
Lemma gfa_fail : forall (sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc lo : Z) (j : list byte) (sem nfw : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo + 128 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -128) (gfa_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 nfw] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> Rc mod 8 = 0 ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz 0) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 Rc [C8 (wz 0); C8 sem; C8 nfw])
    (MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz A_ALLOC) (wz 0) x11 x12 x13 x14 x15 x16 x17
             x18 (wz 2305843009213693952) x20 x21 x22 (wz MTX_LOCKED) x24 x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x370cc) fc None m (seg_rom bsegs)).
Proof.
  intros until nfw. intros MI ST CEIL LO FR MTX HR1 HR2 R8.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold A_ALLOC in *. cbv beta delta [wz] in *.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  eapply (gfa_unlock _ sp gp tp) with (lo := lo) (r := 0); [exact MI| exact ST| exact CEIL| exact LO| exact FR| exact MTX| exact HR1| exact HR2| exact R8| lia].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].
End RTW_p_gfa.

(* [comment removed for export] *)
Module RTW_cd_leaves.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops RTW_p_gfa.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_UNMAPORDIE : Z := 0x678ac.
Definition A_SSR : Z := 0x34f24.        (* [comment removed for export] *)
Definition A_MRTO : Z := 0x34f5c.       (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma unmap00 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(bv_unsigned sp - 48, bv_unsigned sp)] lo m (fun _ _ _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_UNMAPORDIE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_UNMAPORDIE in *. leaf_prep.
  carve_frame 48%nat ST.
  do 5 lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  do 4 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finish. exact I.
Qed.

(* [comment removed for export] *)
Lemma rta_spin : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  cells_at bsegs m GOT_SEALED [W8 1; W8 A_DYING] -> cells_at bsegs m A_DYING [W4 0] ->
  evt bsegs (jself bsegs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x34da0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO GS DY.
  change (cells_at bsegs m GOT_SEALED [W8 1; W8 A_DYING]) with (ro_cells bsegs m GOT_SEALED [W8 1; W8 A_DYING]) in GS.
  change (cells_at bsegs m A_DYING [W4 0]) with (ro_cells bsegs m A_DYING [W4 0]) in DY.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold GOT_SEALED, A_DYING in *. leaf_prep.
  lstep. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  apply evt_done. apply jself_MS. vm_compute. reflexivity.
Qed.



(* [comment removed for export] *)
Lemma rta_refused : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  ro_cells bsegs m GOT_SEALED [C8 (Z_to_bv 64 1)] -> ro_cells bsegs m GOT_DYING [C8 (Z_to_bv 64 A_DYING)] -> ro_cells bsegs m A_DYING [C4 (Z_to_bv 64 0)] ->
  evt bsegs (jself bsegs)
    (MS (mkR (wz 0x34c18) sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x34c18) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO GS GD DY.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold GOT_SEALED, GOT_DYING, A_DYING in *. leaf_prep.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  carve_frame 16%nat ST.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  apply evt_done. apply jself_MS. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma leaf_post_back : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W : list (Z * Z)) (lo : Z) (m m1 : word -> option byte) ms,
  munch W m m1 -> wmono bsegs m m1 ->
  leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W lo m1 (fun _ _ _ => True) ms ->
  leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W lo m (fun _ _ _ => True) ms.
Proof.
  intros until ms. intros MU WM nelH_; (nelim nelH_ 22%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' -> MU' WM' MI' ST' _).
  unfold leaf_post. nexists 16%nat. split; [reflexivity|]. split; [eapply munch_trans; [exact MU| exact MU']|].
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'| exact I].
Qed.

(* [comment removed for export] *)
Definition mrto_frame (j : list byte) (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma mrto_tail : forall (ra sp gp tp t0 t1 t2 x1 x8 a0 a2 a3 a4 a5 a6 a7 x18 x20 x23 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0 s1 s2 s3 s4 s5 s6 s7 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RIS Rc c lo : Z) (j : list byte) (nfw s80 s88 : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -80) -> alloc_ceiling <= lo -> lo + 80 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -80) (mrto_frame j s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  mmap_consts m -> ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)] ->
  rw_cells bsegs m (Rc + 16) [C8 nfw] -> rw_cells bsegs m (Rc + 80) [C8 s80; C8 s88] ->
  Rc = RIS + 128 * c -> KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp)] lo m (fun _ _ _ => True))
    (MS (mkR x1 (wz (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 (wz c) a0 (wz (128 * c)) a2 a3 a4 a5 a6 a7 x18 (wz A_ALLOC) x20 (wz 0) (wz RIS) x23 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x34fd8) fc None m (seg_rom bsegs)).
Proof.
  intros until s88. intros MI ST CEIL LO FR HC AC40 RI16 RI80 ERc HR1 HR2 Hc.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  (nelim HC 3%nat; intros G10 PSZ _).
  unfold KHIGHMEM_BEG, AIMG_HI, A_ALLOC, mrto_frame in *. cbv beta delta [wz] in *.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in RI16, RI80.
  assert (QR : 17594333495296 <= q /\ q + 128 <= alloc_ceiling) by (subst q; lia).
  lstep. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 q) ltac:(f_equal; subst q Rc; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  assert (EPI : forall (y10 y11 y12 : word) y20 mm, mm = m ->
    evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp)] lo m (fun _ _ _ => True))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 (Z_to_bv 64 c) y10 y11 y12 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 680792) y20 (Z_to_bv 64 0) (Z_to_bv 64 q) x23 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x35104) fc None mm (seg_rom bsegs))).
  { intros y10 y11 y12 y20 mm ->. do 9 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp). finish. exact I. }
  lstep. (* [comment removed for export] *)
  let K := fresh "K" in (if_cases K; clear K).
  2:{ lstep. (* [comment removed for export] *) apply EPI. reflexivity. }
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  let K := fresh "K" in (if_cases K; clear K).
  { apply EPI. reflexivity. }
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  apply EPI. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mrto : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (RIS Rc c mm lo : Z) (nfw s80 s88 : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 80 <= bv_unsigned sp ->
  mmap_consts m -> ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)] -> ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 RIS)] ->
  rw_cells bsegs m (Rc + 16) [C8 nfw] -> rw_cells bsegs m (Rc + 80) [C8 s80; C8 s88] ->
  Rc = RIS + 128 * c -> KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 ->
  evt bsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc [(lo, bv_unsigned sp)] lo m (fun _ _ _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz mm) (wz c) (wz 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A_MRTO) fc None m (seg_rom bsegs)).
Proof.
  intros until s88. intros MI ST CEIL LO HC AC40 AC48 RI16 RI80 ERc HR1 HR2 Hc.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_MRTO, A_ALLOC in *. cbv beta delta [wz] in *.
  carve_frame 80%nat ST.
  do 10 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (128 * c)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  let K := fresh "K" in (if_cases K; clear K).
  - (* [comment removed for export] *) do 9 lstep. (* [comment removed for export] *)
    eapply evt_mono; [eapply (mrto_tail ra sp gp tp) with (lo := lo) (Rc := Rc); [exact MI| exact ST| exact CEIL| lia| unfold mrto_frame; exact FR| | | | | exact ERc| exact HR1| exact HR2| exact Hc]|];
      [eapply (mmap_consts_high _ m); [exact MU| apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia| apply Forall_nil]| exact HC]
      | first [exact AC40| eapply (ro_cells_transport bsegs _ m); [| exact MU| cbn; lia]; exact AC40]
      | first [exact RI16| eapply (rw_cells_transport bsegs _ m); [| exact MU| exact WM| cbn; lia]; exact RI16]
      | first [exact RI80| eapply (rw_cells_transport bsegs _ m); [| exact MU| exact WM| cbn; lia]; exact RI80]
      | cbv beta; intros ms' HP; exact (leaf_post_back _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU WM HP) ].
  - (* [comment removed for export] *) lstep. lstep. (* [comment removed for export] *)
    eapply evt_mono; [eapply (mrto_tail ra sp gp tp) with (lo := lo) (Rc := Rc); [exact MI| exact ST| exact CEIL| lia| unfold mrto_frame; exact FR| | | | | exact ERc| exact HR1| exact HR2| exact Hc]|];
      [eapply (mmap_consts_high _ m); [exact MU| apply Forall_cons; [cbn [fst]; unfold AIMG_HI; lia| apply Forall_nil]| exact HC]
      | first [exact AC40| eapply (ro_cells_transport bsegs _ m); [| exact MU| cbn; lia]; exact AC40]
      | first [exact RI16| eapply (rw_cells_transport bsegs _ m); [| exact MU| exact WM| cbn; lia]; exact RI16]
      | first [exact RI80| eapply (rw_cells_transport bsegs _ m); [| exact MU| exact WM| cbn; lia]; exact RI80]
      | cbv beta; intros ms' HP; exact (leaf_post_back _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MU WM HP) ].
Qed.


End CeilWrap.
End RTW_cd_leaves.

(* [comment removed for export] *)
Module RTW_cd_rta.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops RTW_p_gfa RTW_p_efa.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].

Definition A_RTA : Z := 0x34ab4.
Definition MTX_BIT61 : Z := 2305843009213693952.   (* [comment removed for export] *)
Definition LOCK_MASK : Z := 1152921504607895551.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rta_frame (j : list byte) (q s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 16 j; C8 q; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Rc RB mm c CH n nf lo : Z) (sem : word) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x28 x29 x30 x31 : word) (j : list byte) (m1 : word -> option byte),
    ms1 = MS (mkR (wz 0x34c18) (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) (wz nf) (wz A_ALLOC) (wz Rc) (wz RB) (wz (nf + n))
                  (wz 0) (wz MTX_LOCKED) (wz 0) (wz 1500)
                  (wz c) (wz mm) (wz A_ALLOC) (wz n) (wz CH) (wz (nf + n)) (wz MTX_BIT61) (wz (RB + KFREEARRAY_OFF)) (wz LOCK_MASK) (wz MTX_LOCKED) x28 x29 x30 x31)
             F (wz A_EFA) fc None m1 (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m1 (bv_unsigned sp + -128) (rta_frame j (wz (Rc + 8)) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m1 Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 nf)].

Lemma rta_A : forall (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S RIS Rc RB mm stt c CH n nf lo : Z) (sem : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 128 <= bv_unsigned sp ->
  ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)] -> ro_cells bsegs m 0xa6388 [C8 (Z_to_bv 64 RIS)] ->
  rw_cells bsegs m Rc [C8 (wz 0); C8 sem; C8 (Z_to_bv 64 nf)] ->
  Rc = RIS + 128 * c -> RB = S + c * 2^32 -> KHIGHMEM_BEG <= RIS -> RIS + 4096 <= alloc_ceiling -> RIS mod 4096 = 0 -> 1 <= c <= 30 ->
  KHIGHMEM_BEG <= S -> S + 2^37 + 4096 <= alloc_ceiling -> 0 <= nf < 2^40 -> 1 <= n <= 8 -> 0 <= mm < 2^64 -> 0 <= stt < 2^64 -> 0 <= CH < 2^64 ->
  evt bsegs (rta_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m Rc RB mm c CH n nf lo sem)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz mm) (wz stt) (wz c) (wz CH) (wz n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_RTA) fc None m (seg_rom bsegs)).
Proof.
  intros until sem. intros MI ST CEIL LO AC32 AC48 MTX ERc ERB HR1 HR2 HRA Hc HS1 HS2 Hnf Hn Hmm Hstt HCH.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc, Rc + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_RTA, A_ALLOC, A_EFA, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, MTX_LOCKED, MTX_BIT61, LOCK_MASK in *. leaf_prep. idtac.
  assert (RcR : 17594333495296 <= Rc /\ Rc + 128 <= alloc_ceiling /\ Rc mod 8 = 0) by (subst Rc; split; [lia|]; split; [lia|]; clear -HRA Hc; Z.div_mod_to_equations; lia).
  (nelim RcR 3%nat; intros R1 R2 R8).
  destruct (ex_intro (fun r => r = Rc) _ eq_refl) as [r Hr]. rewrite <- Hr in MTX, MU |- *.
  carve_frame 128%nat ST.
  do 14 lstep. (* [comment removed for export] *)
  do 5 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. fl. lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 r) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; subst r Rc; lia).
  lstep. (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 RB) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; subst RB; lia).
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (RB + 3758096384)) ltac:(f_equal; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold rta_A_post, rta_frame. subst r.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact MTX].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_B_post (sp gp tp s8 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Rc mm c CH D0 n nf : Z) (sem alloc z1 mapped z2 s72 s88 : word) (exh : byte) (jr je js3 : list byte) (zs : list Z) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x14 x15 x16 x17 : word) (m1 : word -> option byte) (s80' : word),
    ms1 = MS (mkR (wz 0x34c68) sp gp tp x5 x6 x7 (wz Rc) (wz (4 * nf)) (wz A_ALLOC) (wz mm) (wz c) (wz 0) x14 x15 x16 x17
                  (wz c) (wz mm) (wz A_ALLOC) (wz n) (wz (CH + 4 * n)) (wz (nf + n)) s8 (wz (D0 + 4 * n)) s10 s11 x28 x29 x30 x31)
             F (wz 0x34f5c) fc None m1 (seg_rom bsegs)
    /\ munch [(Rc + 16, Rc + 24); (Rc + 80, Rc + 88); (D0, D0 + 4 * n)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
    /\ rw_cells bsegs m1 Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 (nf + n))]
    /\ rw_cells bsegs m1 (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 s72; C8 s80'; C8 s88; CB 32 js3]
    /\ u32arr bsegs m1 CH (wl zs) /\ u32arr bsegs m1 D0 (wl zs).

Lemma rta_B : forall (sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (s8 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc mm c CH FA n nf : Z)
    (sem alloc z1 mapped z2 s72 s80 s88 : word) (exh : byte) (jr je js3 : list byte) (zs : list Z) (dpre : list word),
  mem_inv bsegs m ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 (Z_to_bv 64 nf)] ->
  rw_cells bsegs m (Rc + 32) [C8 alloc; C8 z1; C8 mapped; C8 z2; CB 4 jr; C1 exh; CB 3 je; C8 s72; C8 s80; C8 s88; CB 32 js3] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
  AIMG_HI <= FA -> FA + 2^29 <= Rc -> (4096 <= CH /\ (CH + 4 * n <= AIMG_LO \/ AIMG_HI <= CH)) -> CH + 4 * n <= alloc_ceiling ->   (* [comment removed for export] *)
  (CH + 4 * n <= Rc \/ Rc + 128 <= CH) -> (CH + 4 * n <= FA \/ FA + 2^29 <= CH) ->
  1 <= n <= 8 -> 0 <= nf -> 4 * (nf + n) <= 2^29 -> 0 <= mm < 2^64 ->
  length zs = Z.to_nat n -> Forall (fun z => 0 <= z < 2^31) zs -> length dpre = Z.to_nat n ->
  u32arr bsegs m CH (wl zs) -> u32arr bsegs m (FA + 4 * nf) dpre ->
  evt bsegs (rta_B_post sp gp tp s8 s10 s11 x28 x29 x30 x31 F fc m Rc mm c CH (FA + 4 * nf) n nf sem alloc z1 mapped z2 s72 s88 exh jr je js3 zs)
    (MS (mkR (wz 0x34c18) sp gp tp x5 x6 x7 (wz Rc) (wz nf) (wz 1) x11 x12 x13 x14 x15 x16 x17
             (wz c) (wz mm) (wz A_ALLOC) (wz n) (wz CH) (wz (nf + n)) s8 (wz FA) s10 s11 x28 x29 x30 x31)
        F (wz 0x34c18) fc None m (seg_rom bsegs)).
Proof.
  intros until dpre. intros MI MTX RIb HR1 HR2 HF1 HF2 HC1 HC2 DISJ DISJ2 Hn Hnf Hnn Hmm LF SMALL LD SRC DST.
  pose proof HR2 as HR2n. idtac. pose proof HC2 as HC2n. idtac.
  unfold KHIGHMEM_BEG, MTX_LOCKED, A_ALLOC, AIMG_LO, AIMG_HI in *. cbv beta delta [wz] in *.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 (4 * nf)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  setreg 25 (Z_to_bv 64 (FA + 4 * nf + 4 * 0)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  setreg 10 (Z_to_bv 64 (CH + 4 * n)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
  setreg 22 (Z_to_bv 64 (CH + 4 * 0)) ltac:(f_equal; lia).
  eapply (copy_loop_rta (Z.to_nat n) 0 n CH (FA + 4 * nf) zs dpre);
    [lia| lia| lia| unfold AIMG_LO, AIMG_HI; lia| unfold AIMG_LO, AIMG_HI; lia| lia| exact LF| exact SMALL| exact LD| exact SRC| cbn [Z.to_nat firstn app]; exact DST| exact MI|].
  intros m1 x11' SRC1 DST1 MU1 WM1 MI1.
  assert (MU : munch [(Rc + 16, Rc + 24); (Rc + 80, Rc + 88); (FA + 4 * nf, FA + 4 * nf + 4 * n)] m m1) by (eapply munch_weaken; [| exact MU1]; subfp).
  pose proof WM1 as WM.
  pose proof (munch_refl [(Rc + 16, Rc + 24); (Rc + 80, Rc + 88)] m1) as MU'. pose proof (wmono_refl bsegs m1) as WM'.
  hide SRC1. hide DST1.
  pose proof MTX as MTX1. eapply (rw_cells_transport bsegs _ m m1) in MTX1; [| exact MU1| exact WM1| cbn; lia].
  pose proof RIb as RIb1. eapply (rw_cells_transport bsegs _ m m1) in RIb1; [| exact MU1| exact WM1| cbn; lia].
  clear MTX RIb SRC DST MU1 WM1.
  destruct (ex_intro (fun q => q = Rc) _ eq_refl) as [q Hq]. rewrite <- Hq in MTX1, RIb1, MU, MU' |- *.
  assert (QR : 17594333495296 <= q < alloc_ceiling) by (subst q; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold rta_B_post. subst q.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact MTX1|]. split; [exact RIb1|].
  unhide SRC1. unhide DST1.
  split. { eapply (u32arr_transport bsegs _ m1); [exact SRC1| exact MU'| exact WM'| cbn; rewrite wl_length, LF; lia]. }
  eapply (u32arr_transport bsegs _ m1); [exact DST1| exact MU'| exact WM'| cbn; rewrite wl_length, LF; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rta_unlock : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc lo : Z) (j : list byte) (q sem nfw : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo + 128 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -128) (rta_frame j q s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells bsegs m Rc [C8 (wz MTX_LOCKED); C8 sem; C8 nfw] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> Rc mod 8 = 0 ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 Rc [C8 (wz 0); C8 sem; C8 nfw])
    (MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz Rc) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (wz MTX_BIT61) x25 x26 x27 x28 x29 x30 x31)
        F (wz 0x34c68) fc None m (seg_rom bsegs)).
Proof.
  intros until nfw. intros MI ST CEIL LO FR MTX HR1 HR2 R8.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Rc, Rc + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, MTX_LOCKED, MTX_BIT61, rta_frame in *. cbv beta delta [wz] in *.
  destruct (ex_intro (fun q' => q' = Rc) _ eq_refl) as [r Hr]. rewrite <- Hr in MTX, MU |- *.
  assert (QR : 17594333495296 <= r < alloc_ceiling /\ r mod 8 = 0) by (subst r; lia). clear Hr.
  lstep. (* [comment removed for export] *)
  do 3 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 3 lstep. fl. (* [comment removed for export] *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RO98 : ro_cells bsegs mm 0x103e0 [CB 8 [Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0x0f; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0xff; Z_to_bv 8 0xff; Z_to_bv 8 0xaf]])
      by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]) end.
  lstep. fl. clear RO98. (* [comment removed for export] *)
  do 6 lstep. fl. (* [comment removed for export] *)
  lstep. fl. lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. fl. lstep. if_lit. (* [comment removed for export] *)
  do 7 lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  amo_zstep2. fix_lit_store. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  do 13 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. nexists 16%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact MTX].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].
End RTW_cd_rta.

(* [comment removed for export] *)
Module RTW_p_libo.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap RTW_p_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Definition outI (iv : Z * Z) : Prop := snd iv <= AIMG_LO \/ AIMG_HI <= fst iv.
Lemma outI_high : forall W, Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> Forall outI W.
Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv X. right. exact X. Qed.
Lemma disjoint_out_img' : forall W a n, Forall outI W -> AIMG_LO <= a -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha Hb; [exact I|]. cbn. pose proof (Forall_inv HW) as H1. unfold outI in H1. cbn [fst snd] in H1.
  split; [lia| apply IH; [exact (Forall_inv_tail HW)| exact Ha| exact Hb]].
Qed.
Lemma icpt_cells_out : forall W m m', munch W m m' -> Forall outI W -> icpt_cells m -> icpt_cells m'.
Proof.
  intros W m m' MU HW IC. eapply icpt_cells_munch; [exact IC| exact MU|].
  unfold icpt_cell_ivs. repeat constructor; cbn [fst snd]; apply (disjoint_out_img' W _ _ HW); unfold AIMG_LO, AIMG_HI; lia.
Qed.
Lemma poison_cells_out : forall W m m', munch W m m' -> Forall outI W -> poison_cells m -> poison_cells m'.
Proof.
  intros W m m' MU HW PC. eapply poison_cells_munch; [exact PC| exact MU|].
  unfold poison_cell_ivs. repeat constructor; cbn [fst snd]; apply (disjoint_out_img' W _ _ HW); unfold AIMG_LO, AIMG_HI; lia.
Qed.
Lemma mmap_consts_out : forall W m m', munch W m m' -> Forall outI W -> mmap_consts m -> mmap_consts m'.
Proof.
  intros W m m' MU HW HC. eapply mmap_consts_munch; [exact HC| exact MU| ..]; apply (disjoint_out_img' W _ _ HW); unfold AIMG_LO, AIMG_HI; lia.
Qed.

End CeilWrap.
End RTW_p_libo.

(* [comment removed for export] *)
Module RTW_p_refillw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Definition A_GFA' : Z := 0x36e10.
(* [comment removed for export] *)
Definition refill_frame (j : list byte) (s1 s0 ra : word) : list cell := [CB 8 j; C8 s1; C8 s0; C8 ra].

Lemma cmaxcount_range : forall c, 1 <= c <= 31 -> 2 <= cmaxcount c <= 16 /\ cmaxcount c = 2 * nrefill c.
Proof.
  intros c Hc. unfold nrefill, cmaxcount, clampz.
  pose proof (Z.le_max_l 1 (Z.min 8 (1024 / csize c))). pose proof (Z.le_min_l 8 (1024 / csize c)).
  split; [lia|]. rewrite (Z.mul_comm 2 (Z.max _ _)), Z.div_mul by lia. lia.
Qed.
Lemma nrefill_eq : forall c, 1 <= c <= 31 -> nrefill c = Z.shiftr (cmaxcount c) 1 /\ 1 <= nrefill c <= 8.
Proof.
  intros c Hc. pose proof (cmaxcount_range c Hc) as [R E]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite E. rewrite (Z.mul_comm 2), Z.div_mul by lia. lia.
Qed.

(* [comment removed for export] *)
Definition refill_call (sp gp tp x5 x6 x7 : word) (pc n : Z) (x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (stt cls : Z) (m1 : word -> option byte) : machine_state :=
  MS (mkR (wz 0x36d50) (wz (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz pc) (wz n) (wz A_ALLOC) (wz stt) (wz cls) (wz (pc + 16)) (wz n) x15 x16 x17
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
     F (wz A_GFA') fc None m1 (seg_rom bsegs).

(* [comment removed for export] *)
Lemma refill_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc cls lo mc : Z) (cnt w : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  rw_cells bsegs m pc [C4 cnt; C4 (Z_to_bv 64 mc); C8 w] ->
  (4096 <= pc /\ (pc + 80 <= AIMG_LO \/ AIMG_HI <= pc)) -> pc + 80 <= alloc_ceiling -> 0 <= mc < 2^31 ->
  evt bsegs (fun ms1 => exists (j : list byte) (m1 : word -> option byte),
      ms1 = MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz mc) (wz A_ALLOC) (wz cls) (wz cls) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if mc =? 0 then 0x36d6c else 0x36d30)) fc None m1 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -32)
      /\ rw_cells bsegs m1 (bv_unsigned sp + -32) (refill_frame j s1 s0 ra)
      /\ rw_cells bsegs m1 pc [C4 cnt; C4 (Z_to_bv 64 mc); C8 w])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz pc) (wz A_ALLOC) (wz cls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AREFILL) fc None m (seg_rom bsegs)).
Proof.
  intros until w. intros MI ST CEIL LO PCC HP1 HP2 Hmc.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold AREFILL, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. leaf_prep. idtac.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q; unfold AIMG_LO, AIMG_HI in *; lia).
  carve_frame 32%nat ST.
  do 4 lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 mc) ltac:(symmetry; apply sx32_small; lia).
  lstep. if_cases K0; zify_cond K0.
  all: apply evt_done; unfold refill_frame; subst q; do 2 eexists;
       split; [cbv delta [mkR]; first [rewrite (proj2 (Z.eqb_eq _ _)) by lia | rewrite (proj2 (Z.eqb_neq _ _)) by lia]; reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|]; split; [exact FR| exact PCC].
Qed.

(* [comment removed for export] *)
Lemma refill_B : forall (ra sp gp tp t0 t1 t2 s1 x13 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc cls : Z),
  mem_inv bsegs m -> pc = P + 80 * cls -> (4096 <= P /\ (P + 3888 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 3888 <= alloc_ceiling -> 1 <= cls <= 30 ->
  evt bsegs (fun ms1 => ms1 = refill_call sp gp tp t0 t1 t2 pc (nrefill cls) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (P + 2560) cls m)
    (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz (cmaxcount cls)) (wz A_ALLOC) x13 (wz cls) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36d30) fc None m (seg_rom bsegs)).
Proof.
  intros until cls. intros MI Epc HP1 HP2 Hc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, A_GFA', KHIGHMEM_BEG, AIMG_HI in *. cbv beta delta [wz] in *. idtac.
  pose proof (cmaxcount_range cls ltac:(lia)) as [CR CE]. pose proof (nrefill_eq cls ltac:(lia)) as [NE NR].
  lstep. (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 (nrefill cls)) ltac:(rewrite NE; f_equal; unfold bv_wrap; change (bv_modulus 32) with 4294967296; rewrite Z.mod_small by lia;
                                       symmetry; apply swrap32_small; rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (P + 2560)) ltac:(f_equal; lia).
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. unfold refill_call. cbv delta [mkR wz]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refill_init : forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc cls : Z) (cnt : Z -> word) (j2 j3 : Z -> list byte),
  mem_inv bsegs m -> pc = P + 80 * cls -> (4096 <= P /\ (P + 3888 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 3888 <= alloc_ceiling -> 1 <= cls <= 30 ->
  (forall c, 1 <= c <= 31 -> rw_cells bsegs m (P + 80 * c) [C4 (cnt c); CB 4 (j2 c); CB 8 (j3 c)]) ->
  evt bsegs (fun ms1 => exists (x13 x15 x28 x29 x30 : word) (m1 : word -> option byte),
      ms1 = MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp (wz 16) (wz 17) (wz 512) (wz pc) s1 (wz P) (wz (cmaxcount cls)) (wz A_ALLOC) x13 (wz cls) x15 (wz 15) (wz 1024)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
               F (wz 0x36d30) fc None m1 (seg_rom bsegs)
      /\ munch [(P + 80, P + 2560)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ (forall c, 1 <= c <= 31 -> rw_cells bsegs m1 (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]))
    (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz 0) (wz A_ALLOC) (wz cls) (wz cls) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36d6c) fc None m (seg_rom bsegs)).
Proof.
  intros until j3. intros MI Epc HP1 HP2 Hc CELLS.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. cbv beta delta [wz] in *. idtac.
  do 8 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (P + 80 * 1 + 8)) ltac:(f_equal; lia).
  replace (Z_to_bv 64 32 : word) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
  setreg 15 (Z_to_bv 64 (1 - 16)) ltac:(reflexivity).
  eapply (initc1_loop 31 1 P cnt j2 j3); [reflexivity| lia| unfold AIMG_LO, AIMG_HI; blia| lia| exact MI| intros c Hc'; apply CELLS; lia| intros c Hc'; lia|].
  intros m1 x11 x13 x15 x28 x29 x30 CELLS1 MU1 WM1 MI1.
  pose proof (CELLS1 cls ltac:(lia)) as PCC. rewrite <- Epc in PCC.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q pc; unfold AIMG_LO, AIMG_HI in *; lia).
  pose proof (cmaxcount_range cls ltac:(lia)) as [CR CE].
  lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (cmaxcount cls)) ltac:(symmetry; apply sx32_small; lia).
  lstep. (* [comment removed for export] *)
  apply evt_done. subst q. do 6 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1| exact CELLS1].
Qed.

(* [comment removed for export] *)
Lemma refill_ret : forall (sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (pc n r lo : Z) (j : list byte) (cnt mc : word) (csz : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -32) (refill_frame j s1 s0 ra) ->
  rw_cells bsegs m pc [C4 cnt; C4 mc; C8 (Z_to_bv 64 csz)] ->
  (4096 <= pc /\ (pc + 80 <= AIMG_LO \/ AIMG_HI <= pc)) -> pc + 80 <= alloc_ceiling -> 0 <= n <= 8 -> 0 <= r <= 1 ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz r) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (pc, pc + 4)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 pc [C4 (if r =? 1 then Z_to_bv 64 n else cnt); C4 mc; C8 (Z_to_bv 64 csz)])
    (MS (mkR (wz 0x36d50) (wz (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz pc) (wz n) (wz r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x36d50) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros MI ST CEIL LO FR PCC HP1 HP2 Hn Hr.
  pose proof (munch_refl [(lo, bv_unsigned sp); (pc, pc + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold KHIGHMEM_BEG, AIMG_HI, refill_frame in *. cbv beta delta [wz] in *.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC, MU |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q; unfold AIMG_LO, AIMG_HI in *; lia).
  assert (Hr' : r = 0 \/ r = 1) by lia. destruct Hr' as [-> | ->].
  - lstep. if_lia. (* [comment removed for export] *)
    do 3 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. subst q. do 15 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. cbn [Z.eqb]. exact PCC.
  - lstep. if_lia. (* [comment removed for export] *)
    lstep. fix_lit_store || idtac. (* [comment removed for export] *)
    do 3 lstep. lstep. lstep. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. subst q. do 15 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. cbn [Z.eqb Pos.eqb]. exact PCC.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
End RTW_p_refillw.

(* [comment removed for export] *)
Module RTW_cd_dd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap RTW_p_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_loops RTW_p_gfa RTW_p_refillw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface RTW_cd_leaves RTW_cd_rta OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Definition A_DRAIN : Z := 0x34910.

(* [comment removed for export] *)
Definition cd_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition drain_frame (j : list byte) (ra : word) : list cell :=
  [CB 8 j; C8 (wz A_ALLOC); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cd_pro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P c p lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  1 <= c <= 30 -> 0 <= P -> P + 4096 <= 2^64 -> 0 <= p < 2^64 ->
  evt bsegs (fun ms1 => exists m1,
      ms1 = MS (mkR ra (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz (P + 80 * c)) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) (wz 80) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x345b0) fc None m1 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m1 (bv_unsigned sp + -48) (cd_frame s4 s3 s2 s1 s0 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz A_ALLOC) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ACDEALLOC) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO Hc HP1 HP2 Hp.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold ACDEALLOC, A_ALLOC in *. leaf_prep.
  carve_frame 48%nat ST.
  do 7 lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (P + 80 * c)) ltac:(f_equal; lia).
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| unfold cd_frame; exact FR].
Qed.

(* [comment removed for export] *)
Lemma cd_chk_room : forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc c p cnt mc csz : Z),
  mem_inv bsegs m -> rw_cells bsegs m pc [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  (4096 <= pc /\ (pc + 80 <= AIMG_LO \/ AIMG_HI <= pc)) -> pc + 80 <= alloc_ceiling -> 0 <= cnt < 2^31 -> 1 <= mc < 2^31 -> cnt <> mc ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR ra sp gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) (wz cnt) (wz mc) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x345c0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x345b0) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros MI PCC HP1 HP2 Hcnt Hmc NE.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. cbv beta delta [wz] in *. idtac.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q; unfold AIMG_LO, AIMG_HI in *; lia).
  lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 mc) ltac:(symmetry; apply sx32_small; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 cnt) ltac:(symmetry; apply sx32_small; lia).
  lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. subst q. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cd_chk_full : forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc c p mc csz : Z),
  mem_inv bsegs m -> rw_cells bsegs m pc [C4 (Z_to_bv 64 mc); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  (4096 <= pc /\ (pc + 80 <= AIMG_LO \/ AIMG_HI <= pc)) -> pc + 80 <= alloc_ceiling -> 1 <= mc < 2^31 ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR ra sp gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) (wz mc) (wz mc) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x3470c) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x345b0) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros MI PCC HP1 HP2 Hmc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. cbv beta delta [wz] in *. idtac.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q; unfold AIMG_LO, AIMG_HI in *; lia).
  lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 mc) ltac:(symmetry; apply sx32_small; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 mc) ltac:(symmetry; apply sx32_small; lia).
  lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. subst q. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cd_init : forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc c p : Z),
  mem_inv bsegs m -> pc = P + 80 * c -> (4096 <= P /\ (P + 3888 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 3888 <= alloc_ceiling -> 1 <= c <= 30 ->
  (forall c', 1 <= c' <= 31 -> rw_cells bsegs m (P + 80 * c') [C4 (wz 0); C4 (wz 0); C8 (wz 0)]) ->
  evt bsegs (fun ms1 => exists (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte),
      ms1 = MS (mkR ra sp gp tp x5 x6 x7 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) (wz 0) (wz (cmaxcount c)) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x345c0) fc None m1 (seg_rom bsegs)
      /\ munch [(P + 80, P + 2560)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ (forall c', 1 <= c' <= 31 -> rw_cells bsegs m1 (P + 80 * c') [C4 (wz 0); C4 (Z_to_bv 64 (cmaxcount c')); C8 (Z_to_bv 64 (csize c'))]))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x345b0) fc None m (seg_rom bsegs)).
Proof.
  intros until p. intros MI Epc HP1 HP2 Hc CELLS.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. cbv beta delta [wz] in *. idtac.
  pose proof (CELLS c ltac:(lia)) as PCC. rewrite <- Epc in PCC.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q pc; unfold AIMG_LO, AIMG_HI in *; lia).
  lstep. fl. (* [comment removed for export] *)
  lstep. if_lit. (* [comment removed for export] *)
  clear PCC.
  (* [comment removed for export] *)
  assert (CELLS' : forall c', 1 <= c' <= 31 -> rw_cells bsegs m (P + 80 * c') [C4 (Z_to_bv 64 0); CB 4 (le4 (Z_to_bv 64 0)); CB 8 (le8 (Z_to_bv 64 0))]).
  { intros c' Hc'. eapply rw_cells_recast_p; [exact (CELLS c' Hc')| cbn; repeat split; reflexivity| reflexivity]. }
  do 8 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 (P + 80 * 1 + 8)) ltac:(f_equal; lia).
  replace (Z_to_bv 64 32 : word) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
  setreg 16 (Z_to_bv 64 (1 - 16)) ltac:(reflexivity).
  eapply (initc2_loop 31 1 P (fun _ => Z_to_bv 64 0) (fun _ => le4 (Z_to_bv 64 0)) (fun _ => le8 (Z_to_bv 64 0)));
    [reflexivity| lia| unfold AIMG_LO, AIMG_HI; blia| lia| exact MI| intros c' Hc'; apply CELLS'; lia| intros c' Hc'; lia|].
  intros m1 x14 x15 x16 x29 x30 x31 CELLS1 MU1 WM1 MI1. cbv beta in CELLS1.
  pose proof (CELLS1 c ltac:(lia)) as PCC. rewrite <- Epc, <- Hq in PCC.
  pose proof (cmaxcount_range c ltac:(lia)) as [CR CE].
  lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (cmaxcount c)) ltac:(symmetry; apply sx32_small; lia).
  lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  apply evt_done. subst q. nexists 10%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1| exact CELLS1].
Qed.

(* [comment removed for export] *)
Lemma cd_call_drain : forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc c p : Z),
  mem_inv bsegs m ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR (wz 0x3472c) sp gp tp t0 t1 t2 (wz pc) (wz P) (wz P) (wz pc) (wz A_ALLOC) (wz c) a4 a5 a6 a7 (wz A_ALLOC) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz A_DRAIN) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz pc) s1 (wz P) (wz A_ALLOC) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3470c) fc None m (seg_rom bsegs)).
Proof.
  intros until p. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, A_DRAIN in *. cbv beta delta [wz] in *.
  do 7 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cd_after_drain : forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc c p cnt : Z) (mcw : word) (csz : Z),
  mem_inv bsegs m -> rw_cells bsegs m pc [C4 (Z_to_bv 64 cnt); C4 mcw; C8 (Z_to_bv 64 csz)] ->
  (4096 <= pc /\ (pc + 80 <= AIMG_LO \/ AIMG_HI <= pc)) -> pc + 80 <= alloc_ceiling -> 0 <= cnt < 2^31 ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR ra sp gp tp t0 t1 t2 (wz pc) (wz P) (wz P) (wz A_ALLOC) (wz c) (wz p) (wz cnt) a5 a6 a7 (wz A_ALLOC) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x345c0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz pc) (wz P) a0 a1 a2 a3 a4 a5 a6 a7 (wz A_ALLOC) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x3472c) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros MI PCC HP1 HP2 Hcnt.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. cbv beta delta [wz] in *. idtac.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q; unfold AIMG_LO, AIMG_HI in *; lia).
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 cnt) ltac:(symmetry; apply sx32_small; lia).
  lstep. (* [comment removed for export] *)
  apply evt_done. subst q. cbv delta [mkR]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cd_push : forall (x1 sp gp tp t0 t1 t2 x9 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ra s0 s1 s2 s3 s4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S P pc c k cnt csz lo : Z) (mcw slot sa : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -48) (cd_frame s4 s3 s2 s1 s0 ra) ->
  ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)] ->
  rw_cells bsegs m pc [C4 (Z_to_bv 64 cnt); C4 mcw; C8 (Z_to_bv 64 csz)] ->
  rw_cells bsegs m (pc + 4 * cnt + 16) [C4 slot] ->
  rw_cells bsegs m (P + 2576) [C8 sa] ->
  pc = P + 80 * c -> (4096 <= P /\ (P + 3888 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 3888 <= alloc_ceiling -> P mod 8 = 0 -> 1 <= c <= 30 ->
  KHIGHMEM_BEG <= S -> S + 2^37 <= alloc_ceiling -> 0 <= k < 2^28 -> 0 <= cnt <= 15 -> 0 < csz < 2^40 ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2 (sa' : word),
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (pc, pc + 4); (pc + 4 * cnt + 16, pc + 4 * cnt + 20); (P + 2576, P + 2584)] m m2
      /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp)
      /\ rw_cells bsegs m2 pc [C4 (Z_to_bv 64 (cnt + 1)); C4 mcw; C8 (Z_to_bv 64 csz)]
      /\ rw_cells bsegs m2 (pc + 4 * cnt + 16) [C4 (Z_to_bv 64 k)]
      /\ rw_cells bsegs m2 (P + 2576) [C8 sa'])
    (MS (mkR x1 (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz pc) x9 (wz P) (wz A_ALLOC) (wz c) (wz (S + c * 2^32 + 16 * k)) (wz cnt) a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x345c0) fc None m (seg_rom bsegs)).
Proof.
  intros until sa. intros MI ST CEIL LO FR AC32 PCC SLOT SA Epc HP1 HP2 HP8 Hc HS1 HS2 Hk Hcnt Hcsz.
  pose proof (munch_refl [(lo, bv_unsigned sp); (pc, pc + 4); (pc + 4 * cnt + 16, pc + 4 * cnt + 20); (P + 2576, P + 2584)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI, cd_frame in *. cbv beta delta [wz] in *.
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC, SLOT, MU |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling /\ q mod 4 = 0) by (subst q pc; split; [unfold AIMG_LO, AIMG_HI in *; lia|]; split; [lia|]; clear -HP8 Hc; Z.div_mod_to_equations; lia).
  assert (AL8 : (P + 2576) mod 8 = 0) by (clear -HP8; Z.div_mod_to_equations; lia).
  assert (PR : 0 <= P + 2576 < 2^64) by lia.
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 (S + 16 * k)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia).
  lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 (16 * k)) ltac:(f_equal; lia).
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (4 * cnt)) ltac:(f_equal; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia).
  lstep. lstep. (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (P + 2576)) ltac:(f_equal; lia).
  lstep. (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 k) ltac:(f_equal; rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  amo_zstep. (* [comment removed for export] *)
  do 6 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. subst q. nexists 17%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact PCC|]. split; [exact SLOT| exact SA].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drain_pre : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P pc c cnt mc csz lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m pc [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)] ->
  pc = P + 80 * c -> (4096 <= P /\ (P + 3888 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 3888 <= alloc_ceiling -> 1 <= c <= 30 ->
  0 <= cnt < 2^31 -> 0 <= mc < 2^31 -> mc / 2 <= cnt ->
  evt bsegs (fun ms1 => exists (j : list byte) m1,
      ms1 = MS (mkR (wz 0x34974) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz (bv_unsigned sp + -64 + 8)) (wz (P + 2560)) (wz c)
                    (wz (pc + 16 + 4 * (cnt - mc / 2))) (wz (mc / 2)) (wz (P + 2560)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz A_RTA) fc None m1 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (pc, pc + 4)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells bsegs m1 (bv_unsigned sp + -64) (drain_frame j ra)
      /\ rw_cells bsegs m1 pc [C4 (Z_to_bv 64 (cnt - mc / 2)); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 csz)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz pc) (wz A_ALLOC) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_DRAIN) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO PCC Epc HP1 HP2 Hc Hcnt Hmc LE.
  pose proof (munch_refl [(lo, bv_unsigned sp); (pc, pc + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_DRAIN, A_RTA, A_ALLOC, KHIGHMEM_BEG, AIMG_HI in *. leaf_prep. idtac.
  assert (Hn : 0 <= mc / 2 <= cnt) by (split; [apply Z.div_pos; lia| exact LE]).
  destruct (ex_intro (fun q => q = pc) _ eq_refl) as [q Hq]. rewrite <- Hq in PCC, MU |- *.
  assert (QR : (4096 <= q /\ (q + 80 <= 65536 \/ 6287360 <= q)) /\ q + 80 <= alloc_ceiling) by (subst q pc; unfold AIMG_LO, AIMG_HI in *; lia).
  carve_frame 64%nat ST.
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 16 (Z_to_bv 64 cnt) ltac:(symmetry; apply sx32_small; lia).
  lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 mc) ltac:(symmetry; apply zx32_small; lia).
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (mc / 2)) ltac:(f_equal; rewrite ?Z.shiftr_div_pow2 by lia; rewrite ?unsigned_lit by lia; lia).
  lstep. lstep. (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 cnt) ltac:(f_equal; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia; rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia).
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 16 (Z_to_bv 64 (P + 2560)) ltac:(f_equal; lia).
  setreg 14 (Z_to_bv 64 (q + 16 + 4 * (cnt - mc / 2))) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia).
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. subst q. unfold drain_frame, A_ALLOC. cbv delta [wz]. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR| exact PCC].
Qed.

(* [comment removed for export] *)
Lemma drain_post : forall (sp gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (j : list byte),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 + 48 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (drain_frame j ra) ->
  evt bsegs (fun ms2 => exists (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) m2,
      ms2 = MS (mkR ra sp gp tp y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp))
    (MS (mkR (wz 0x34974) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x34974) fc None m (seg_rom bsegs)).
Proof.
  intros until j. intros MI ST CEIL LO FR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold drain_frame, A_ALLOC in *. cbv beta delta [wz] in *.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply (unmap00 (Z_to_bv 64 0x34984) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp) with (lo := lo);
                     [exact MI| rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia]
                   | cbv beta; unfold leaf_post; post_call bsegs mm ] end.
  rewrite ?unsigned_lit in * by lia. restk. fixMI.
  lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. nexists 16%nat. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; split_outside H | _ => idtac end.
Ltac subfp :=
  unfold sub_fp; cbn; intros xq Hxq; split_outside Hxq;
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I
        | intros Cq; match goal with H : ~ _ |- False => apply H; first [exact Cq| clear -Cq; lia] end ].
End RTW_cd_dd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_mmapN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_mmapN.RTW_sec_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit RTW_p_map.
Import RTW_p_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_loops.
Import RTW_p_efa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Definition A_POPULATE : Z := 0x37118.

(* [comment removed for export] *)
Definition pop_frame (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma csize_max : forall c, 1 <= c <= 30 -> csize c <= 65536.
Proof.
  intros c Hc.
  assert (H : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
    \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct H as [->|H]; [vm_compute; discriminate|]). subst. vm_compute. discriminate.
Qed.
Lemma csize_small : forall c, 1 <= c <= 16 -> csize c = 32 * c.
Proof. intros c Hc. unfold csize. replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; lia). replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Ltac cases_17_30 c :=
  let HH := fresh in
  assert (HH : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].

(* [comment removed for export] *)
Definition pop_A_post (ra sp gp tp s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S Rc stt c q alloc mapped lo exh : Z) (jr je js : list byte) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte),
    ms1 = MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) (wz stt) (wz A_ALLOC) (wz (Z.shiftl c 32)) (wz c) (wz alloc) (wz q) x15 x16 x17
                  (wz (S + c * 2^32)) (wz (alloc + csize c * q)) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (wz (if mapped <? alloc + csize c * q then 0x371b8 else 0x3728c)) fc None m1 (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -64)
    /\ rw_cells bsegs m1 (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m1 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js].

Lemma pop_A : forall (sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Rc stt c q alloc mapped lo : Z) (jr je js : list byte) (exh : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  ro_cells bsegs m 0xa6378 [C8 (Z_to_bv 64 S)] ->
  rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 -> 0 <= q <= 8 -> 0 <= alloc <= mapped -> mapped <= KFREEARRAY_OFF ->
  KHIGHMEM_BEG <= S -> S + 2^37 + 4096 <= alloc_ceiling ->
  evt bsegs (pop_A_post (wz 0x370cc) sp gp tp s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 F fc m S Rc stt c q alloc mapped lo exh jr je js)
    (MS (mkR (wz 0x370cc) sp gp tp t0 t1 t2 s0 s1 (wz A_ALLOC) (wz stt) (wz c) (wz Rc) (wz q) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A_POPULATE) fc None m (seg_rom bsegs)).
Proof.
  intros until exh. intros MI ST CEIL LO AC32 RIb HR1 HR2 Hc Hq Ham Hmx HS1 HS2.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_POPULATE, A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *. leaf_prep. idtac.
  pose proof (csize_pos c ltac:(lia)) as CP. pose proof (csize_max c ltac:(lia)) as CL.
  assert (QS : 0 <= csize c * q <= 8 * 65536) by nia.
  carve_frame 64%nat ST.
  sepM. do 9 lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  if_cases Kc; zify_cond Kc.
  - (* [comment removed for export] *)
    cases_17_30 c.
    all: do 9 (lstep; try fl).
    all: match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 225696) _ _ _ _) => idtac end.
    all: lstep; lstep; lstep; lstep; lstep. (* [comment removed for export] *)
    all: sepM. all: lstep; if_cases K0; zify_cond K0.
    all: try (lstep; match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => idtac p end).
    all: apply evt_done; unfold pop_A_post, pop_frame; eval_cls; cbv beta delta [wz].
    all: nexists 11%nat; split; [cbv delta [mkR]; first [rewrite (proj2 (Z.ltb_lt _ _)) by (cut_to K0; lia) | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity|].
    all: split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|]; split; [exact FR| exact RIb].
  - (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    setreg 21 (Z_to_bv 64 (csize c)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; rewrite csize_small by lia; lia).
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 18 (Z_to_bv 64 (S + c * 2^32)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    lstep. if_cases K0; zify_cond K0.
    all: try (lstep; match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => idtac p end).
    all: apply evt_done; unfold pop_A_post, pop_frame; cbv beta delta [wz].
    all: nexists 11%nat; split; [cbv delta [mkR]; first [rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity|].
    all: split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|]; split; [exact FR| exact RIb].
Qed.

(* [comment removed for export] *)
Lemma pop_B_map : forall (ra sp gp tp x5 x6 x7 x15 x16 x17 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S Rc stt c q alloc mapped RB : Z) (jr je js : list byte) (exh : Z) (a1v : word),
  mem_inv bsegs m ->
  ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)] -> ro_cells bsegs m 0xa6390 [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 -> 0 <= q -> csize c * q <= 262144 -> 0 <= alloc <= mapped ->
  mapped < alloc + csize c * q -> mapped + 262144 <= KFREEARRAY_OFF -> KHIGHMEM_BEG <= RB -> RB + 2^32 <= alloc_ceiling ->
  evt bsegs (fun ms1 => exists (y15 : word),
      ms1 = MS (mkR (wz 0x37238) sp gp tp x5 x6 x7 (wz Rc) (wz stt) (wz A_ALLOC) (wz (RB + mapped)) (wz 262144) (wz 0x17001) y15 x15 x16 x17
                    (wz RB) (wz 262144) (wz (RB + mapped)) (wz (csize c)) (wz A_ALLOC) s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz A_RAR_MAP) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp x5 x6 x7 (wz Rc) (wz stt) (wz A_ALLOC) a1v (wz c) (wz alloc) (wz q) x15 x16 x17
             (wz RB) (wz (alloc + csize c * q)) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x371b8) fc None m (seg_rom bsegs)).
Proof.
  intros until a1v. intros MI AC40 AC56 RIb HR1 HR2 Hc Hq QS Ham LT NEX HB1 HB2.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, A_RAR_MAP in *. cbv beta delta [wz] in *. idtac.
  pose proof (csize_pos c ltac:(lia)) as CP.
  assert (STEPB : forall mp a1w, mp = mapped ->
    evt bsegs (fun ms1 => exists (y15 : word),
      ms1 = MS (mkR (Z_to_bv 64 0x37238) sp gp tp x5 x6 x7 (Z_to_bv 64 Rc) (Z_to_bv 64 stt) (Z_to_bv 64 680792) (Z_to_bv 64 (RB + mapped)) (Z_to_bv 64 262144) (Z_to_bv 64 0x17001) y15 x15 x16 x17
                    (Z_to_bv 64 RB) (Z_to_bv 64 262144) (Z_to_bv 64 (RB + mapped)) (Z_to_bv 64 (csize c)) (Z_to_bv 64 680792) s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 458668) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp x5 x6 x7 (Z_to_bv 64 Rc) (Z_to_bv 64 stt) (Z_to_bv 64 680792) a1w (Z_to_bv 64 c) (Z_to_bv 64 alloc) (Z_to_bv 64 q) x15 x16 x17
             (Z_to_bv 64 RB) (Z_to_bv 64 (alloc + csize c * q)) (Z_to_bv 64 mp) (Z_to_bv 64 (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x371bc) fc None m (seg_rom bsegs))).
  { intros mp a1w ->.
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite zb_lxor_ones by lia; rewrite land_align18 by (apply Z.mod_pos_bound; lia); Z.div_mod_to_equations; lia).
    lstep. lstep. fl. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
    lstep. if_lia. (* [comment removed for export] *)
    lstep. fl. lstep. lstep. if_lia. (* [comment removed for export] *)
    setreg 20 (Z_to_bv 64 (RB + mapped)) ltac:(f_equal; lia).
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply evt_done. eexists. cbv delta [mkR]. reflexivity. }
  lstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    lstep. fl. lstep. if_lit. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    apply (STEPB 0). lia.
  - apply (STEPB mapped). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pop_ret0 : forall (x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (s6 s5 s4 s3 s2 s1 s0 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  evt bsegs (fun ms2 => exists (y11 : word) m2,
      ms2 = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) y11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x373a8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO FR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof aceil as CEILlo.
  unfold pop_frame in FR. cbv beta delta [wz] in *.
  lstep. lstep. (* [comment removed for export] *)
  lstep. do 8 lstep. lstep. lstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

(* [comment removed for export] *)
Lemma pop_mapref_tail : forall (sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (s6 s5 s4 s3 s2 s1 s0 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  evt bsegs (fun ms2 => exists (y11 : word) m2,
      ms2 = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) y11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp))
    (MS (mkR (wz 0x37238) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 (wz 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x37238) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  cbv beta delta [wz] in *.
  lstep. if_lia. (* [comment removed for export] *)
  eapply pop_ret0; [exact MI| exact ST| exact CEIL| exact LO| exact FR].
Qed.

(* [comment removed for export] *)
Lemma pop_efaref_tail : forall (sp gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (s6 s5 s4 s3 s2 s1 s0 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  evt bsegs (fun ms2 => exists (y11 : word) m2,
      ms2 = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) y11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp))
    (MS (mkR (wz 0x372ac) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 (wz 0) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x372ac) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  cbv beta delta [wz] in *.
  lstep. if_lia. (* [comment removed for export] *)
  eapply pop_ret0; [exact MI| exact ST| exact CEIL| exact LO| exact FR].
Qed.

(* [comment removed for export] *)
Lemma pop_exh1 : forall (sp gp tp x5 x6 x7 x15 x16 x17 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (s6 s5 s4 s3 s2 s1 s0 ra : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc stt c q alloc mapped RB lo : Z) (jr je js : list byte) (a1v : word),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  rw_cells bsegs m (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  ro_cells bsegs m 0xa6380 [C4 (Z_to_bv 64 4294967295)] ->
  rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 1); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 1 <= c <= 30 -> 0 <= q -> csize c * q <= 262144 -> 0 <= alloc <= mapped ->
  mapped < alloc + csize c * q -> mapped = KFREEARRAY_OFF -> KHIGHMEM_BEG <= RB -> RB + 2^32 <= alloc_ceiling ->
  evt bsegs (fun ms2 => exists (y11 y12 y13 : word) m2,
      ms2 = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) y11 y12 y13 (wz q) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m2 (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp))
    (MS (mkR (wz 0x370cc) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) (wz stt) (wz A_ALLOC) a1v (wz c) (wz alloc) (wz q) x15 x16 x17
             (wz RB) (wz (alloc + csize c * q)) (wz mapped) (wz (csize c)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x371b8) fc None m (seg_rom bsegs)).
Proof.
  intros until a1v. intros MI ST CEIL LO FR AC40 RIb HR1 HR2 Hc Hq QS Ham LT EXH HB1 HB2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEILn. idtac.
  unfold A_ALLOC, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF in *. cbv beta delta [wz] in *. idtac.
  pose proof (csize_pos c ltac:(lia)) as CP.
  lstep. if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite zb_lxor_ones by lia; rewrite land_align18 by (apply Z.mod_pos_bound; lia); Z.div_mod_to_equations; lia).
  lstep. lstep. fl. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. fl. (* [comment removed for export] *)
  lstep. if_lia. (* [comment removed for export] *)
  lstep. fl. lstep. if_lia. (* [comment removed for export] *)
  eapply evt_mono; [eapply pop_ret0; [exact MI| exact ST| exact CEIL| exact LO| exact FR]|].
  cbv beta. intros ms2 nelH_; (nelim nelH_ 7%nat; intros y11 m2 -> MU WM MI2 ST2). nexists 4%nat. split; [cbv delta [mkR wz]; reflexivity|]. repeat (split; [eassumption|]). exact ST2.
Qed.

(* [comment removed for export] *)
Lemma pop_C : forall (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x14 x15 x16 x17 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (mtx sem : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Rc RB S alloc mapped' nf : Z) (s3v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m Rc [C8 mtx; C8 sem; C8 (Z_to_bv 64 nf)] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> 0 < S < 2^40 -> 0 <= alloc <= mapped' -> mapped' <= 2^40 -> 0 <= nf < 2^40 ->
  evt bsegs (fun ms1 =>
      ms1 = MS (mkR (wz 0x372ac) sp gp tp x5 x6 x7 (wz Rc) (wz (nf + (mapped' - alloc) / S)) x10 (wz Rc) (wz RB) (wz (nf + (mapped' - alloc) / S)) x14 x15 x16 x17
                    (wz RB) (wz ((mapped' - alloc) / S)) (wz (mapped' - alloc)) (wz S) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz A_EFA) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp x5 x6 x7 (wz Rc) x9 x10 x11 x12 (wz alloc) x14 x15 x16 x17
             (wz RB) s3v (wz mapped') (wz S) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x3728c) fc None m (seg_rom bsegs)).
Proof.
  intros until s3v. intros MI RIa HR1 HR2 HS Ham Hm Hnf.
  unfold KHIGHMEM_BEG, AIMG_HI, A_EFA in *. cbv beta delta [wz] in *. idtac.
  assert (DV : 0 <= (mapped' - alloc) / S <= 2^40) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; nia]).
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite divu_lit by lia.
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Section POPD.
  Hypothesis PS : poison_shadow_spec.

  (* [comment removed for export] *)
  Lemma pop_D : forall (sp gp tp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (Rc stt RB S alloc mapped msz lo : Z) (jr je js shj : list byte) (exh : Z) (tj1 tj2 sa : word),
    icpt_cells m -> poison_cells m -> leafc st m -> RTWF st -> tp = wz ATP -> mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo + 1200 <= bv_unsigned sp ->
    rw_cells bsegs m (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mapped); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js] ->
    KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
    (st_ctx st + 160 <= Rc \/ Rc + 128 <= st_ctx st) -> (st_t st + 4096 <= Rc \/ Rc + 128 <= st_t st) -> RB + 2^32 <= Rc ->
    rw_cells bsegs m (st_t st + 2872) [C8 tj1; C8 tj2] -> rw_cells bsegs m (stt + 24) [C8 sa] -> stt = st_t st + 2768 ->
    KHIGHMEM_BEG <= RB -> RB + 2^32 <= alloc_ceiling -> RB mod 65536 = 0 ->
    (st_ctx st + 160 <= RB \/ RB + 2^32 <= st_ctx st) -> (st_t st + 4096 <= RB \/ RB + 2^32 <= st_t st) ->
    0 <= mapped -> mapped mod 8 = 0 -> msz = 262144 -> mapped + msz <= KFREEARRAY_OFF ->
    rw_cells bsegs m (SH (RB + mapped)) [CB (Z.to_nat (msz / 8)) shj] ->
    evt bsegs (fun ms2 => exists (y1 y5 y6 y7 y11 y12 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m2 : word -> option byte) (tj1' tj2' sa' : word),
        ms2 = MS (mkR y1 (wz (bv_unsigned sp + -64)) gp tp y5 y6 y7 (wz Rc) (wz (stt + 24)) (wz A_ALLOC) y11 y12 (wz alloc) y14 y15 y16 y17
                      (wz RB) (wz msz) (wz (mapped + msz)) (wz S) (wz A_ALLOC) s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 F (wz 0x3728c) fc None m2 (seg_rom bsegs)
        /\ munch [(lo, bv_unsigned sp + -64); (SH (RB + mapped), SH (RB + mapped) + msz / 8); (st_t st + 2872, st_t st + 2888); (stt + 24, stt + 32); (Rc + 48, Rc + 56)] m m2
        /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (bv_unsigned sp + -64)
        /\ rw_cells bsegs m2 (Rc + 32) [C8 (Z_to_bv 64 alloc); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (mapped + msz)); C8 (Z_to_bv 64 0); CB 4 jr; C1 (Z_to_bv 8 exh); CB 3 je; CB 56 js]
        /\ rw_cells bsegs m2 (SH (RB + mapped)) [CB (Z.to_nat (msz / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (msz / 8)))]
        /\ rw_cells bsegs m2 (st_t st + 2872) [C8 tj1'; C8 tj2'] /\ rw_cells bsegs m2 (stt + 24) [C8 sa'])
      (MS (mkR (wz 0x37238) (wz (bv_unsigned sp + -64)) gp tp x5 x6 x7 (wz Rc) (wz stt) (wz (RB + mapped)) x11 x12 x13 x14 x15 x16 x17
               (wz RB) (wz msz) (wz (RB + mapped)) (wz S) (wz A_ALLOC) s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x37238) fc None m (seg_rom bsegs)).
  Proof.
    intros until sa. intros IC PC LC WF TP MI ST CEIL LO RIb HR1 HR2 DJC DJT RBR TST SA Hstt HB1 HB2 HB3 DJC2 DJT2 Hm0 Hm8 Hmsz NEX SHJ.
    pose proof (munch_refl [(lo, bv_unsigned sp + -64); (SH (RB + mapped), SH (RB + mapped) + msz / 8); (st_t st + 2872, st_t st + 2888); (stt + 24, stt + 32); (Rc + 48, Rc + 56)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
    pose proof (t_range st WF) as TR. olin TR. pose proof (ctx_range st WF) as CR. olin CR. pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
    unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, A_ALLOC in *.
    assert (UR : 17594333495296 <= RB + mapped /\ RB + mapped + msz <= RB + 3758096384 /\ (RB + mapped) mod 8 = 0) by (split; [lia|]; split; [lia|]; clear -HB3 Hm8; Z.div_mod_to_equations; lia).
    (nelim UR 3%nat; intros U1 U2 U8).
    pose proof (rt_SH_bounds (RB + mapped) ltac:(lia)) as SHR.
    assert (SHE : SH (RB + mapped) + msz / 8 <= 17594333495296) by (unfold SH, SHADOW_OFFSET; unfold SH, SHADOW_OFFSET in SHR; clear -U1 U2 HB2 Hmsz; Z.div_mod_to_equations; lia).
    cbv beta delta [wz] in *. subst tp.
    lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    unfold poison_shadow_spec, APOISON_STACK, APOISON_SHADOW in PS.
    sepM. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply PS; [exact IC| exact PC| exact MI| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia
                                  | reflexivity| reflexivity| reflexivity| exact U8| rewrite Hmsz; reflexivity| lia
                                  | right; unfold highmem_range, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; lia| lia| lia| exact SHJ]
                      | cbv beta; unfold poison_shadow_post, APOISON_STACK; post_call bsegs mm ] end.
    rewrite ?unsigned_lit in * by lia.
    restk. fixMI.
    lstep. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (LC1 : leafc st mm) by
       (eapply (leafc_munch st _ _ _ MU WM); [| exact LC]; intros lo' hi' a b Hin Hab; cbn in Hin, Hab;
        destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E; intros; subst;
        destruct Hab as [E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[E'|[]]]]]]]]]]; injection E'; intros; subst; (lia_on CEIL CR SHR OLx0 SHE OLx CT HR1 DJC)) end.
    sepM. call get_thread_stats_c; [exact LC1| exact WF| exact MI| reflexivity| rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia|].
    after_call. rewrite ?unsigned_lit in * by lia. unfold T_STATS.
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    destruct (ex_intro (fun q => q = stt + 24) _ eq_refl) as [q Hq]. rewrite <- Hq in SA.
    assert (QAL : q mod 8 = 0) by (rewrite Hq, Hstt; pose proof (wb_t_align st (wf_base_ok st WF)); clear -H; Z.div_mod_to_equations; lia).
    assert (QR : 4096 <= q < alloc_ceiling /\ (q + 8 <= 65536 \/ 6287360 <= q)) by (rewrite Hq, Hstt; clear - OLx TR; unfold T_STATS in *; lia).
    setreg 9 (Z_to_bv 64 q) ltac:(rewrite Hq; reflexivity).
    amo_zstep. (* [comment removed for export] *)
    subst q.
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    apply evt_done. nexists 18%nat. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: try eassumption.
  Qed.
End POPD.



End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac cases_17_30 c :=
  let HH := fresh in
  assert (HH : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].
