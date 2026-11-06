(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.openssl.bndiv.lib.B Require Import Layout. From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OSSVerify.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface D_defs. From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import SegRw.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OSSVerify.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit.
From OSSVerify.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaEceInit HxaImage HxaInv HxaHooks HxaIface HxaHandoffImg HxaHandoff.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Lemma seg_rw_libdata : seg_rw_ok bsegs 6186592 2784 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_libbss : seg_rw_ok bsegs 12411008 2528 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_tsdmain : seg_rw_ok bsegs 12567040 64 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fact_lit (rho : valuation) (m : word -> option byte) (B off : Z) (n : nat) (v : Z) :
  0 <= v -> bytes_at bsegs m (B + off) (Z_to_le_bytes n v) -> fact_holds bsegs rho m B (off, kbs_Z n v).
Proof.
  intros Hv_nonneg Hlit_bytes. unfold fact_holds; cbn [fst snd].
  exists (Z_to_le_bytes n v). split; [apply kbs_Z_intro; exact Hv_nonneg | exact Hlit_bytes].
Qed.

Lemma fact_ptr (rho : valuation) (m : word -> option byte) (B off : Z) (tag : int) (A : Z) :
  rho tag = A -> 0 <= A < 2 ^ 64 -> bytes_at bsegs m (B + off) (le8 (Z_to_bv 64 A)) -> fact_holds bsegs rho m B (off, kbs_ptr tag).
Proof.
  intros Htag_val Hword_range Hptr_bytes.
  pose proof (kbs_ptr_intro rho tag A Htag_val Hword_range) as Hptr_kbs.
  exists (le8 (Z_to_bv 64 A)). exact (conj Hptr_kbs Hptr_bytes).
Qed.

(* [comment removed for export] *)
Lemma c8_bytes (m : word -> option byte) (a : Z) (w : word) : ro_cells bsegs m a [C8 w] -> bytes_at bsegs m a (le8 w).
Proof. intros [_ Hc8_raw]. cbn [cells_bytes cbytes] in Hc8_raw. rewrite app_nil_r in Hc8_raw. exact Hc8_raw. Qed.
Lemma c4_bytes (m : word -> option byte) (a : Z) (w : word) : ro_cells bsegs m a [C4 w] -> bytes_at bsegs m a (le4 w).
Proof. intros Hc4_cells. apply (bytes_at_ext bsegs m a (le4 w ++ [])); [exact (proj2 Hc4_cells) | apply app_nil_r]. Qed.
Lemma c1_bytes (m : word -> option byte) (a : Z) (b : byte) : ro_cells bsegs m a [C1 b] -> bytes_at bsegs m a [b].
Proof. intros Hc1_cells. exact (proj2 Hc1_cells). Qed.

(* [comment removed for export] *)
Lemma seg_rw_mapped (m : word -> option byte) (a n : Z) : seg_rw_ok bsegs a n = true ->
  forall i, 0 <= i < n -> (exists b, mrd bsegs m (wa (a + i)) = Some b) /\ wview bsegs m (wa (a + i)) <> None.
Proof.
  intros Hrw_ok i Hi_span.
  destruct (seg_rw_ok_sound bsegs a n Hrw_ok m) as [_ (_ & _ & Hstk_byte)].
  destruct (Hstk_byte (a + i) ltac:(lia)) as [Hview_some Hread_some].
  exact (conj Hread_some Hview_some).
Qed.

(* [comment removed for export] *)
Definition chunk_rng (lo A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ A + n <= lo /\ (A + n <= 65536 \/ 12570624 <= A) /\ (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A).
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

Lemma shad_chunk (A n : Z) : 0 < A -> 0 <= n -> A + 8 * n < 2 ^ 47 -> 0x7fff8000 <= shad A /\ shad A + n < 0x10007fff8000.
Proof.
  intros H0 Hn H1. pose proof (shad_range A ltac:(lia)) as X1. pose proof (shad_range (A + 8 * n) ltac:(lia)) as X2.
  rewrite shad_add8 in X2. unfold SH_LO, SH_HI in *. split; [|lia]. unfold shad, SHB. pose proof (Z.div_pos A 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Section Handoff.
Variables (rho : valuation) (m : word -> option byte) (ri : int).
Hypothesis H_ri : ri = 0%uint63 \/ ri = 16%uint63.
Hypothesis MI : mem_inv bsegs m.
Hypothesis V_relro : forall a, 5681152 <= a < 6172672 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).
Hypothesis C_shb : ro_cells bsegs m 6961656 [C8 (Z_to_bv 64 SHB)].
Hypothesis C_uar : ro_cells bsegs m 6961664 [C4 (Z_to_bv 64 1)].
Hypothesis C_tsd : rw_cells bsegs m 12430840 [C8 (Z_to_bv 64 0xbfc1f8)].
(* [comment removed for export] *)
Hypothesis C_memset : ro_cells bsegs m 0x5e6660 [C8 (Z_to_bv 64 0x1bcc34)].
Hypothesis C_malloc : ro_cells bsegs m 0x5e6680 [C8 (Z_to_bv 64 0x1f261c)].
Hypothesis C_free : ro_cells bsegs m 0x5e66c0 [C8 (Z_to_bv 64 0x1f2b40)].
(* [comment removed for export] *)
Hypothesis C_stopped : ro_cells bsegs m 0xbd6620 [C1 (Z_to_bv 8 0)].
Hypothesis C_optsdone : ro_cells bsegs m 0xbd66c0 [C8 (Z_to_bv 64 2)].
Hypothesis C_base_once : ro_cells bsegs m 0xbd66e0 [C4 (Z_to_bv 64 2)].
Hypothesis C_base_ret : ro_cells bsegs m 0xbd6700 [C4 (Z_to_bv 64 1)].
Hypothesis C_master_once : ro_cells bsegs m 0xbd61e0 [C4 (Z_to_bv 64 2)].
Hypothesis C_master_key : ro_cells bsegs m 0xbd6200 [C4 (Z_to_bv 64 3)].
Hypothesis H_imgsh : region_ok bsegs rho TE_IMGSH RG_IMGSH_E m.

Lemma eg4_ok : region_ok bsegs rho 4%uint63 eg_4 m.
Proof. exact (rg4_ok rho m MI). Qed.
Lemma eg5_ok : region_ok bsegs rho 5%uint63 eg_5 m.
Proof. exact (rg5_ok rho m V_relro). Qed.

Lemma Hri01 : to_Z ri = 0 \/ to_Z ri = 16.
Proof. destruct H_ri as [-> | ->]; [left | right]; reflexivity. Qed.
Lemma sz2 : to_Z (ESTK + ri)%uint63 = 81920 + to_Z ri.
Proof. destruct H_ri as [-> | ->]; reflexivity. Qed.
Lemma sz3 : to_Z ((ESTK + ri) >> 3)%uint63 = (81920 + to_Z ri) / 8.
Proof. destruct H_ri as [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac lit_learn base span seg_ok fs :=
  lazymatch goal with
  | |- region_ok bsegs ?val ?tg ?rg ?mm =>
      apply (region_ok_learn bsegs val tg rg mm fs);
      [ closed_side ..
      | intros off_i Hoff_i; change (to_Z (rg_size rg)) with span in Hoff_i; change (rbase val tg rg) with base;
        exact (proj1 (seg_rw_mapped mm base span seg_ok off_i Hoff_i))
      | intros Hwr_set; vm_compute in Hwr_set; discriminate Hwr_set
      | change (rbase val tg rg) with base;
        repeat (apply Forall_cons;
          [ first [ apply fact_lit; [closed_side | ] | eapply fact_ptr; [eassumption | assumption | ] ];
            first
              [ match goal with Hcell : ro_cells bsegs _ _ [C8 _] |- _ => exact (c8_bytes _ _ _ Hcell) end
              | match goal with Hcell : ro_cells bsegs _ _ [C4 _] |- _ => exact (c4_bytes _ _ _ Hcell) end
              | match goal with Hcell : ro_cells bsegs _ _ [C1 _] |- _ => exact (c1_bytes _ _ _ Hcell) end
              | match goal with Hcell : rw_cells bsegs _ _ [C8 _] |- _ => exact (c8_bytes _ _ _ (proj1 Hcell)) end ]
          | ]);
        apply Forall_nil
      | vm_compute; reflexivity ]
  end.

Lemma eg6_ok : region_ok bsegs rho 6%uint63 eg_6 m.
Proof. lit_learn 6186592 2784 seg_rw_libdata [(0, kbs_Z 8 1821748); (32, kbs_Z 8 2041372); (96, kbs_Z 8 2042688)]. Qed.

Lemma eg7_ok : region_ok bsegs rho 7%uint63 eg_7 m.
Proof.
  assert (Hshb_rw : seg_rw_ok bsegs 6961656 12 = true) by closed_side.
  lit_learn 6961656 12 Hshb_rw [(0, kbs_Z 8 SHB); (8, kbs_Z 4 1)].
Qed.

Lemma eg8_ok : region_ok bsegs rho 8%uint63 eg_8 m.
Proof.
  lit_learn 12411008 2528 seg_rw_libbss
    [(352, kbs_Z 4 2); (384, kbs_Z 4 3); (1440, kbs_Z 1 0); (1600, kbs_Z 8 2); (1632, kbs_Z 4 2); (1664, kbs_Z 4 1)].
Qed.

Lemma eg9_ok : region_ok bsegs rho 9%uint63 eg_9 m.
Proof.
  assert (Htsd_rw : seg_rw_ok bsegs 12430840 8 = true) by closed_side.
  lit_learn 12430840 8 Htsd_rw [(0, kbs_Z 8 12567032)].
Qed.

Lemma eg11_ok : region_ok bsegs rho 11%uint63 eg_11 m.
Proof. exact H_imgsh. Qed.

(* [comment removed for export] *)
Variables (lo sp0 : Z).
Hypothesis STKH : stk bsegs m lo sp0.
Hypothesis Hrho2 : rho 2%uint63 = sp0 - to_Z ri - 81920.
Hypothesis Hrho3 : rho 3%uint63 = shad (sp0 - to_Z ri - 81920).
Hypothesis Hlo : lo <= sp0 - to_Z ri - 81920.
Hypothesis Hlo0 : 0x7fff00000000 <= lo.
Hypothesis Hsp47 : sp0 + 16 <= USTACK_TOP.
Hypothesis Hsp32 : sp0 mod 32 = to_Z ri.
Hypothesis Z_stk : forall i, 0 <= i < (81920 + to_Z ri) / 8 -> mrd bsegs m (wa (shad (sp0 - to_Z ri - 81920) + i)) = Some z8.

Lemma lo_hi : lo < 2 ^ 47.
Proof. pose proof Hri01. unfold USTACK_TOP in Hsp47. lia. Qed.

Lemma B0_facts : 0x7fff00000000 <= sp0 - to_Z ri - 81920 /\ (sp0 - to_Z ri - 81920) mod 32 = 0
  /\ 0x80177a00 <= shad (sp0 - to_Z ri - 81920) /\ shad (sp0 - to_Z ri - 81920) + (81920 + to_Z ri) / 8 <= 0x7fff00000000.
Proof.
  pose proof Hri01 as Hr. unfold USTACK_TOP in Hsp47.
  split; [lia|]. split.
  { pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32 in D.
    replace (sp0 - to_Z ri - 81920) with (0 + (sp0 / 32 - 2560) * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold shad, SHB. split; Z.div_mod_to_equations; lia.
Qed.

Lemma eg3_ok : region_ok bsegs rho 3%uint63 (eg_3 ri) m.
Proof.
  pose proof sz3 as Hshadow_len.
  pose proof Hri01 as Hri_cases.
  destruct B0_facts as (_ & _ & Hshadow_lo & Hshadow_hi).
  assert (Hshadow_run : forall i, 0 <= i < to_Z ((ESTK + ri) >> 3)%uint63 ->
            mrd bsegs m (wa (shad (sp0 - to_Z ri - 81920) + i)) = Some z8)
    by (rewrite Hshadow_len; exact Z_stk).
  refine (zero_region_ok_d rho 3 _ 11 m _ Hrho3 _ _ _ _ _ Hshadow_run).
  all: rewrite ?Hshadow_len; unfold two63; lia.
Qed.

Lemma eg2_ok : region_ok bsegs rho 2%uint63 (eg_2 ri) m.
Proof.
  pose proof sz2 as Hframe_len.
  pose proof Hri01 as Hri_cases.
  pose proof Hsp47 as Hsp_top. unfold USTACK_TOP in Hsp_top.
  destruct B0_facts as (Hframe_lo & Hframe_align & _ & _).
  destruct STKH as (_ & _ & Hstk_cell).
  rewrite <- Hrho2 in Hframe_lo, Hframe_align.
  assert (Hframe_pos : 0 < rho 2%uint63) by lia.
  assert (Hframe_top : rho 2%uint63 + to_Z (ESTK + ri)%uint63 < two63) by (rewrite Hframe_len; unfold two63; lia).
  assert (Hframe_cap : to_Z (ESTK + ri)%uint63 < 2 ^ 62) by (rewrite Hframe_len; lia).
  assert (Hframe_depth : to_Z (ESTK + ri)%uint63 <= 8 * 2 ^ Z.of_nat 14) by (rewrite Hframe_len; lia).
  assert (Hframe_bytes : forall i, 0 <= i < to_Z (ESTK + ri)%uint63 ->
            (exists b, mrd bsegs m (wa (rho 2%uint63 + i)) = Some b) /\ (true = true -> wview bsegs m (wa (rho 2%uint63 + i)) <> None)).
  { intros i Hi_span. rewrite Hframe_len in Hi_span.
    destruct (Hstk_cell (rho 2%uint63 + i)) as [Hview_some Hread_some]; [lia |].
    split; [exact Hread_some | intros _; exact Hview_some]. }
  refine (region_ok_fresh bsegs rho 2 None (ESTK + ri)%uint63 5 true 14 m
            Hframe_pos Hframe_top Hframe_cap Hframe_depth _ _ Hframe_align Hframe_bytes); closed_side.
Qed.

(* [comment removed for export] *)
Lemma chunk_learn (t : int) (rg : region) (A n : Z) (fs : list fact) :
  rg_abs rg = None -> rho t = A -> to_Z (rg_size rg) = n -> to_Z (rg_al rg) = 4 -> chunk_rng lo A n -> 0 < n < 2 ^ 20 ->
  n <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 ->
  wr_at bsegs m A n -> Forall (fact_holds bsegs rho m A) fs -> learn_check bsegs rg fs 0 (Z.to_nat n) = true ->
  region_ok bsegs rho t rg m.
Proof.
  intros Habs_none Htag_base Hsize_n Hal_four Hrng_A Hn_bounds Hn_depth Hdepth_cap Hwr_span Hfacts Hcheck.
  pose proof lo_hi as Hlo_cap.
  destruct Hrng_A as (Hpos_A & Halign_A & Hfits_lo & _).
  assert (Hrbase_A : rbase rho t rg = A) by (unfold rbase; rewrite Habs_none; exact Htag_base).
  pose proof Hwr_span as (_ & _ & Hview_all).
  apply (region_ok_learn bsegs rho t rg m fs); rewrite ?Hrbase_A, ?Hsize_n, ?Hal_four.
  - exact Hpos_A.
  - unfold two63; lia.
  - lia.
  - exact Hn_depth.
  - exact Hdepth_cap.
  - closed_side.
  - exact Halign_A.
  - intros i Hi_span. exact (wview_mrd bsegs m (wa (A + i)) asegs_wr_rd (Hview_all i Hi_span)).
  - intros _ i Hi_span. exact (Hview_all i Hi_span).
  - exact Hfacts.
  - exact Hcheck.
Qed.

(* [comment removed for export] *)
Lemma chunk_shadow (t n : int) (d : nat) (A : Z) :
  rho t = shad A -> 0 < A -> A + 8 * to_Z n <= lo -> to_Z n <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  (forall i, 0 <= i < to_Z n -> mrd bsegs m (wa (shad A + i)) = Some z8) ->
  region_ok bsegs rho t (RG None n 0 false DZero d IEmpty) m.
Proof.
  intros Hsh_tag Hpos_A Hroom Hdepth_fit Hdepth_cap Hzero_bytes.
  pose proof lo_hi as Hlo_cap.
  pose proof (to_Z_bounded n) as Hn_range.
  destruct (shad_chunk A (to_Z n) Hpos_A ltac:(lia) ltac:(lia)) as [Hsh_floor Hsh_top].
  apply (zero_region_ok_d rho t n d m (shad A) Hsh_tag).
  - lia.
  - unfold two63; lia.
  - lia.
  - exact Hdepth_fit.
  - exact Hdepth_cap.
  - exact Hzero_bytes.
Qed.

(* [comment removed for export] *)
Variables (MK SA ND ES : Z) (pad : list byte).
Hypothesis C_slot : ro_cells bsegs m 0xbfc210 [C8 (Z_to_bv 64 MK)].
Hypothesis C_mk : ro_cells bsegs m (MK + 24) [C8 (Z_to_bv 64 SA)].
Hypothesis C_sa : ro_cells bsegs m SA [C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 ND)].
Hypothesis C_nd : ro_cells bsegs m ND [C8 (Z_to_bv 64 ES)].
Hypothesis C_es : rw_cells bsegs m ES [CB 904 (repeat (Z_to_bv 8 0) 704 ++ repeat (Z_to_bv 8 255) 64 ++ repeat (Z_to_bv 8 0) 136)].
Hypothesis W_mk : wr_at bsegs m MK 72.
Hypothesis W_sa : wr_at bsegs m SA 32.
Hypothesis W_nd : wr_at bsegs m ND 128.
Hypothesis Z_mk : forall i, 0 <= i < 9 -> mrd bsegs m (wa (shad MK + i)) = Some z8.
Hypothesis Z_sa : forall i, 0 <= i < 4 -> mrd bsegs m (wa (shad SA + i)) = Some z8.
Hypothesis Z_nd : forall i, 0 <= i < 16 -> mrd bsegs m (wa (shad ND + i)) = Some z8.
Hypothesis Z_es : forall i, 0 <= i < 113 -> mrd bsegs m (wa (shad ES + i)) = Some z8.
Hypothesis Hrho32 : rho 32%uint63 = MK.  Hypothesis Hrho33 : rho 33%uint63 = shad MK.
Hypothesis Hrho34 : rho 34%uint63 = SA.  Hypothesis Hrho35 : rho 35%uint63 = shad SA.
Hypothesis Hrho36 : rho 36%uint63 = ND.  Hypothesis Hrho37 : rho 37%uint63 = shad ND.
Hypothesis Hrho38 : rho 38%uint63 = ES.  Hypothesis Hrho39 : rho 39%uint63 = shad ES.
Hypothesis R_mk : chunk_rng lo MK 72.
Hypothesis R_sa : chunk_rng lo SA 32.
Hypothesis R_nd : chunk_rng lo ND 128.
Hypothesis R_es : chunk_rng lo ES 904.
Hypothesis D_mk : apart ES 904 MK 72.
Hypothesis D_sa : apart ES 904 SA 32.
Hypothesis D_nd : apart ES 904 ND 128.

Lemma chunk_word (A n : Z) : chunk_rng lo A n -> 0 <= n -> 0 <= A < 2 ^ 64.
Proof. intros (H0 & _ & H1 & _) Hn. pose proof lo_hi. lia. Qed.

Lemma eg10_ok : region_ok bsegs rho 10%uint63 eg_10 m.
Proof.
  pose proof (chunk_word MK 72 R_mk ltac:(closed_side)) as Hmk_word.
  lit_learn 12567040 64 seg_rw_tsdmain [(16, kbs_ptr 32)].
Qed.

Lemma eg32_ok : region_ok bsegs rho 32%uint63 eg_32 m.
Proof.
  pose proof (chunk_word SA 32 R_sa ltac:(closed_side)) as Hsa_word.
  pose proof (c8_bytes m (MK + 24) (Z_to_bv 64 SA) C_mk) as Hmk_link_bytes.
  pose proof (fact_ptr rho m MK 24 34 SA Hrho34 Hsa_word Hmk_link_bytes) as Hmk_link.
  apply (chunk_learn 32 eg_32 MK 72 [(24, kbs_ptr 34)]);
    [ closed_side | exact Hrho32 | closed_side | closed_side | exact R_mk | split; closed_side | closed_side | closed_side
    | exact W_mk | constructor; [exact Hmk_link | constructor] | closed_side ].
Qed.

Lemma eg34_ok : region_ok bsegs rho 34%uint63 eg_34 m.
Proof.
  pose proof (chunk_word ND 128 R_nd ltac:(closed_side)) as Hnd_word.
  pose proof C_sa as [Hsa_shape Hsa_raw].
  cbn [cells_wf cell_wf] in Hsa_shape. destruct Hsa_shape as (_ & Hpad_len & _).
  cbn [cells_bytes cbytes] in Hsa_raw. rewrite app_nil_r in Hsa_raw.
  pose (sa_kbs := kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr 36).
  assert (Hsa_fact : fact_holds bsegs rho m SA (0, sa_kbs)).
  { unfold sa_kbs, fact_holds; cbn [fst snd]. rewrite Z.add_0_r.
    exists (le4 (Z_to_bv 64 1) ++ pad ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 ND)).
    split; [|exact Hsa_raw].
    apply Forall2_app; [apply kbs_Z_intro; closed_side |].
    apply Forall2_app; [rewrite <- Hpad_len; apply kbs_any_intro |].
    apply Forall2_app; [apply kbs_Z_intro; closed_side |].
    apply Forall2_app; [apply kbs_Z_intro; closed_side |].
    exact (kbs_ptr_intro rho 36 ND Hrho36 Hnd_word). }
  apply (chunk_learn 34 eg_34 SA 32 [(0, sa_kbs)]);
    [ closed_side | exact Hrho34 | closed_side | closed_side | exact R_sa | split; closed_side | closed_side | closed_side
    | exact W_sa | constructor; [exact Hsa_fact | constructor] | unfold sa_kbs; closed_side ].
Qed.

Lemma eg36_ok : region_ok bsegs rho 36%uint63 eg_36 m.
Proof.
  pose proof (chunk_word ES 904 R_es ltac:(closed_side)) as Hes_word.
  assert (Hnd_link : fact_holds bsegs rho m ND (0, kbs_ptr 38)).
  { apply (fact_ptr rho m ND 0 38 ES Hrho38 Hes_word). rewrite Z.add_0_r. exact (c8_bytes m ND _ C_nd). }
  apply (chunk_learn 36 eg_36 ND 128 [(0, kbs_ptr 38)]);
    [ closed_side | exact Hrho36 | closed_side | closed_side | exact R_nd | split; closed_side | closed_side | closed_side
    | exact W_nd | constructor; [exact Hnd_link | constructor] | closed_side ].
Qed.

Definition ES_ZS : list Z := repeat 0 704 ++ repeat 255 64 ++ repeat 0 136.

Lemma eg38_ok : region_ok bsegs rho 38%uint63 eg_38 m.
Proof.
  pose proof C_es as [[_ Hes_raw] Hes_wr].
  cbn [cells_bytes cbytes] in Hes_raw. rewrite app_nil_r in Hes_raw.
  assert (Hzs_bytes : Forall (fun z => 0 <= z < 256) ES_ZS).
  { unfold ES_ZS. apply Forall_app; split; [|apply Forall_app; split];
      apply Forall_forall; intros z Hz_in; apply repeat_spec in Hz_in; subst z; split; closed_side. }
  assert (Hes_fact : fact_holds bsegs rho m ES (0, kbs_bytes ES_ZS)).
  { exists (map (Z_to_bv 8) ES_ZS). cbn [fst snd]. rewrite Z.add_0_r.
    exact (conj (kbs_bytes_intro rho ES_ZS Hzs_bytes) Hes_raw). }
  apply (chunk_learn 38 eg_38 ES 904 [(0, kbs_bytes ES_ZS)]);
    [ closed_side | exact Hrho38 | closed_side | closed_side | exact R_es | split; closed_side | closed_side | closed_side
    | exact Hes_wr | constructor; [exact Hes_fact | constructor] | closed_side ].
Qed.

Lemma eg33_ok : region_ok bsegs rho 33%uint63 eg_33 m.
Proof.
  pose proof R_mk as (Hmk_pos & _ & Hmk_end & _).
  assert (Hmk_room : MK + 8 * to_Z 9%uint63 <= lo) by (change (to_Z 9%uint63) with 9; lia).
  exact (chunk_shadow 33 9 1 MK Hrho33 Hmk_pos Hmk_room ltac:(closed_side) ltac:(closed_side) Z_mk).
Qed.
Lemma eg35_ok : region_ok bsegs rho 35%uint63 eg_35 m.
Proof.
  pose proof R_sa as (Hsa_pos & _ & Hsa_end & _).
  apply (chunk_shadow 35 4 0 SA Hrho35 Hsa_pos); [change (to_Z 4%uint63) with 4; lia | closed_side | closed_side | exact Z_sa].
Qed.
Lemma eg37_ok : region_ok bsegs rho 37%uint63 eg_37 m.
Proof.
  pose proof R_nd as (Hnd_pos & _ & Hnd_end & _).
  refine (chunk_shadow 37 16 1 ND Hrho37 Hnd_pos _ _ _ Z_nd); [change (to_Z 16%uint63) with 16; lia | closed_side ..].
Qed.
Lemma eg39_ok : region_ok bsegs rho 39%uint63 eg_39 m.
Proof.
  pose proof R_es as (Hes_pos & _ & Hes_end & _).
  assert (Hes_room : ES + 8 * to_Z 113%uint63 <= lo) by (change (to_Z 113%uint63) with 113; lia).
  apply (chunk_shadow 39 113 4 ES Hrho39 Hes_pos Hes_room); [closed_side | closed_side | exact Z_es].
Qed.

Definition ivw (t : int) (rg : region) : Z * Z * bool := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg), rg_wr rg).

Local Ltac sepw1 :=
  cbn [fst snd]; first [ intros [X|X]; discriminate X | intros _; lia ].
Local Ltac sepw :=
  unfold ivw, rbase; cbn [rg_abs rg_size rg_wr eg_2 eg_3 eg_4 eg_5 eg_6 eg_7 eg_8 eg_9 eg_10 eg_11 eg_32 eg_33 eg_34 eg_35 eg_36 eg_37 eg_38 eg_39];
  rewrite ?Hrho2, ?Hrho3, ?Hrho32, ?Hrho33, ?Hrho34, ?Hrho35, ?Hrho36, ?Hrho37, ?Hrho38, ?Hrho39, ?sz2, ?sz3;
  repeat match goal with |- context [to_Z ?x] => lazymatch x with ri => fail | _ => idtac end; is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [sepw1|]); constructor.

(* [comment removed for export] *)
Lemma rmemE : Rmem bsegs rho (ME ri) m.
Proof.
  pose proof Hri01 as Hri_cases.
  pose proof lo_hi as Hlo_cap.
  pose proof B0_facts as (Hstk_floor & _ & Hstk_sh_floor & Hstk_sh_top).
  pose proof Hsp47 as Hsp_top. unfold USTACK_TOP in Hsp_top.
  assert (Hstk_span : sp0 - to_Z ri - 81920 + 8 * ((81920 + to_Z ri) / 8) < 2 ^ 47) by lia.
  destruct (shad_chunk (sp0 - to_Z ri - 81920) ((81920 + to_Z ri) / 8) ltac:(lia) ltac:(lia) Hstk_span) as [_ Hstk_sh_cap].
  pose proof R_mk as (Hmk_pos & _ & Hmk_end & _).
  pose proof R_sa as (Hsa_pos & _ & Hsa_end & _).
  pose proof R_nd as (Hnd_pos & _ & Hnd_end & _).
  pose proof R_es as (Hes_pos & _ & Hes_end & Hes_img & Hes_sh).
  destruct (shad_chunk MK 9 Hmk_pos ltac:(lia) ltac:(lia)) as [Hmk_sh_floor Hmk_sh_top].
  destruct (shad_chunk SA 4 Hsa_pos ltac:(lia) ltac:(lia)) as [Hsa_sh_floor Hsa_sh_top].
  destruct (shad_chunk ND 16 Hnd_pos ltac:(lia) ltac:(lia)) as [Hnd_sh_floor Hnd_sh_top].
  destruct (shad_chunk ES 113 Hes_pos ltac:(lia) ltac:(lia)) as [Hes_sh_floor Hes_sh_top].
  pose proof D_mk as Hes_mk_apart. pose proof D_sa as Hes_sa_apart. pose proof D_nd as Hes_nd_apart.
  unfold apart in Hes_mk_apart, Hes_sa_apart, Hes_nd_apart.
  pose proof eg4_ok as Hreg4. pose proof eg5_ok as Hreg5. pose proof eg6_ok as Hreg6. pose proof eg7_ok as Hreg7.
  pose proof eg8_ok as Hreg8. pose proof eg9_ok as Hreg9. pose proof eg10_ok as Hreg10. pose proof eg11_ok as Hreg11.
  pose proof eg32_ok as Hreg32. pose proof eg33_ok as Hreg33. pose proof eg34_ok as Hreg34. pose proof eg35_ok as Hreg35.
  pose proof eg36_ok as Hreg36. pose proof eg37_ok as Hreg37. pose proof eg38_ok as Hreg38. pose proof eg39_ok as Hreg39.
  pose proof eg3_ok as Hreg3. pose proof eg2_ok as Hreg2.
  pose proof (fun M t rg L (Hpair : Rmem bsegs rho M m /\ dir_inw rho M L) =>
                Rmem_add_sepw bsegs rho M t rg m L (proj1 Hpair) (proj2 Hpair)) as Hextend.
  enough (Hchain : exists L, Rmem bsegs rho (ME ri) m /\ dir_inw rho (ME ri) L)
    by (destruct Hchain as (dirs & Hrmem & _); exact Hrmem).
  eexists.
  unfold ME, ME_3, ME_abs, ME_39, ME_38, ME_37, ME_36, ME_35, ME_34, ME_33, ME_32, ME_11, ME_10, ME_9, ME_8, ME_7, ME_6, ME_5, ME_4.
  let rec grow :=
    lazymatch goal with
    | |- Rmem _ _ IEmpty _ /\ dir_inw _ IEmpty _ => exact (conj (Rmem_empty bsegs rho m) (dir_inw_empty rho))
    | |- Rmem _ _ (mset ?M ?t ?rg) _ /\ _ =>
        eapply (Hextend M t rg);
        [ grow
        | vm_compute; reflexivity
        | closed_side
        | match goal with Hreg_known : region_ok bsegs rho t rg m |- _ => exact Hreg_known end
        | sepw ]
    end
  in grow.
Qed.

End Handoff.
