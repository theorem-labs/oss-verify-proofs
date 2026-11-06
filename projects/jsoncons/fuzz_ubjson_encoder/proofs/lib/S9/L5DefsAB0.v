(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct
     HeapIface HeapIfaceA HeapIfaceAEx BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5LazyA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5A.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

Lemma segs_below : segs_below_b RSEGS 0x69c000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wx_nowrap : wx_segs_nowrap RSEGS. Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma land_m2_even r : 0 <= r -> r mod 2 = 0 -> Z.land r (-2) = r.
Proof.
  intros Hr He. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  change (-2) with (Z.lnot 1). rewrite Z.lnot_spec by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.bit0_eqb. change (Z.testbit 1 0) with true. cbn [negb]. rewrite Bool.andb_false_r. symmetry. apply Z.eqb_neq. lia.
  - replace (Z.testbit 1 i) with false. rewrite Bool.andb_true_r. reflexivity. symmetry. rewrite <- (Z.pow_0_r 2). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma ret_to fx R M (pc : Z) (W : bv 32) r :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R pc M) (st fx R r M).
Proof.
  intros HF HEC HD H1 Hr He. eapply mst_step; [reflexivity | | apply mst_refl].
  assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
  rewrite (step_jalr_x0 RSEGS R _ M (seg_rom RSEGS) _ (reg 1) (0%bv : bv 12) (Z_to_bv 64 r) HF HEC D H1).
  f_equal. f_equal. unfold v_jalr. f_equal. unfold jalr_tgtZ. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r.
  rewrite BG.unsigned_lit by lia. apply land_m2_even; lia.
Qed.

Lemma hull_lo_eq : L5.hull_lo RSEGS = 0x10000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_hi_eq : L5.hull_hi RSEGS = 0x69c000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_apart_of a n : (a + n <= 0x10000 \/ 0x69c000 <= a) -> L5.hull_apart RSEGS a n.
Proof. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.
Lemma hull_apart_lit a n : L5.hull_apart RSEGS a n -> (a + n <= 0x10000 \/ 0x69c000 <= a).
Proof. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.

Definition avis (H : word -> bool) (a n : Z) : Prop := forall i, 0 <= i < n -> H (Z_to_bv 64 (a + i)) = false.
Lemma avis_sub H a n a' n' : avis H a n -> a <= a' -> a' + n' <= a + n -> avis H a' n'.
Proof. intros V H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply V. lia. Qed.
Lemma range_avoids_of_avis H a (n : nat) : avis H a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros V Ha Hn k Hk. unfold woff. rewrite BG.unsigned_lit by lia. apply V. lia.
Qed.

Section WithH.
Variable H : word -> bool.
Lemma u64_at_vis M a v : avis H a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS (mrestrict H M) a v <-> L5.u64_at RSEGS M a v.
Proof. intros V Ha Hn. unfold L5.u64_at. rewrite (rdn_mrestrict_eq RSEGS H 8 M _ (range_avoids_of_avis H a 8 V Ha Hn)). tauto. Qed.
Lemma u32_at_vis M a v : avis H a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS (mrestrict H M) a v <-> L5.u32_at RSEGS M a v.
Proof. intros V Ha Hn. unfold L5.u32_at. rewrite (rdn_mrestrict_eq RSEGS H 4 M _ (range_avoids_of_avis H a 4 V Ha Hn)). tauto. Qed.
Lemma u8_at_vis M a v : avis H a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> L5.u8_at RSEGS (mrestrict H M) a v <-> L5.u8_at RSEGS M a v.
Proof. intros V Ha Hn. unfold L5.u8_at. rewrite (rdn_mrestrict_eq RSEGS H 1 M _ (range_avoids_of_avis H a 1 V Ha Hn)). tauto. Qed.
Lemma writable_vis M a n : avis H a n -> 0 <= a -> a + n <= 2 ^ 64 -> L5.writable RSEGS (mrestrict H M) a n <-> L5.writable RSEGS M a n.
Proof.
  intros V Ha Hn. unfold L5.writable. split; intros W d k Hd Hk.
  - rewrite <- (store_ok_mrestrict_eq RSEGS H k M). apply W; lia. apply range_avoids_of_avis. eapply avis_sub. exact V. lia. lia. lia. lia.
  - rewrite (store_ok_mrestrict_eq RSEGS H k M). apply W; lia. apply range_avoids_of_avis. eapply avis_sub. exact V. lia. lia. lia. lia.
Qed.
Lemma defined_vis M a n : avis H a n -> L5.defined (mrestrict H M) a n <-> L5.defined M a n.
Proof. intros V. unfold L5.defined. split; intros D i Hi; specialize (D i Hi); rewrite (mrestrict_visible H M _ (V i Hi)) in *; exact D. Qed.
Lemma zeros_at_vis M a n : avis H a n -> L5KA.zeros_at (mrestrict H M) a n <-> L5KA.zeros_at M a n.
Proof. intros V. unfold L5KA.zeros_at. split; intros D i Hi; specialize (D i Hi); rewrite (mrestrict_visible H M _ (V i Hi)) in *; exact D. Qed.
Lemma img_clear_mrestrict M lo hi : L5.img_clear M lo hi -> L5.img_clear (mrestrict H M) lo hi.
Proof. intros C i Hi. unfold mrestrict. destruct (H _); [reflexivity | apply C; exact Hi]. Qed.

Lemma mrestrict_agree M lo hi : (forall i, lo <= i < hi -> H (Z_to_bv 64 i) = false) -> forall i, lo <= i < hi -> mrestrict H M (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof. intros V i Hi. apply mrestrict_visible. apply V. exact Hi. Qed.
End WithH.

Lemma ahid_not_lazy A m w : page_in_ranges (page_base w) (m_vm_lazy m) = false -> ahid A m w = false.
Proof. intros E. unfold ahid, mkH. rewrite E. reflexivity. Qed.
Lemma ahid_allowed A m w : page_allowedb A (page_base w) = true -> ahid A m w = false.
Proof. intros E. unfold ahid, mkH. rewrite E. cbn. apply Bool.andb_false_r. Qed.

Lemma avis_of_not_lazy A m (P : Z -> Prop) a n :
  (forall w : word, page_in_ranges (page_base w) (m_vm_lazy m) = true -> P (bv_unsigned w)) ->
  (forall i, 0 <= i < n -> ~ P (a + i)) -> 0 <= a -> a + n <= 2 ^ 64 -> avis (ahid A m) a n.
Proof.
  intros HL HP Ha Hn i Hi. apply ahid_not_lazy. destruct (page_in_ranges _ _) eqn:E; [|reflexivity].
  exfalso. apply (HP i Hi). specialize (HL _ E). rewrite BG.unsigned_lit in HL by lia. exact HL.
Qed.
Lemma avis_of_shadow_allowed A m p k a n :
  shadow_allowed A p k -> (forall i, 0 <= i < n -> in_shadow_of p k (a + i)) -> avis (ahid A m) a n.
Proof. intros SA HI i Hi. apply ahid_allowed. apply SA. apply HI. exact Hi. Qed.

Definition SM1 : Z := 0x5edb0. Definition SM2 : Z := 0x5ef40. Definition SM3 : Z := 0x5f0dc.

Definition AS0_ALY_CELLS_D4 : list (Z * Z * Z) :=
  [ (0x1460f8, 8, SB); (0x146100, 4, 1); (0x13f8d8, 8, 0x130034); (0x13f868, 8, 0x116acc);
    (0x13d8c8, 8, 0x1460f8);
    (0x13d8d0, 8, 0x146de8); (0x146de8, 8, 0); (0x13d8d8, 8, 0x146df0); (0x146df0, 8, 0);
    (0x13d8e0, 8, 0x146de0); (0x146de0, 8, 0x7fffffffffff);
    (0x13e430, 8, 0x146dd9); (0x146dd9, 1, 1);
    (0x13f8d0, 8, 0x12fc30);
    (0x146dd8, 1, 1);
    (0x13f7c8, 8, 0x130c14);
    (0x67a178, 8, 0x67a1a0); (0x67a1a8, 8, 0x67a980);
    (0x145960, 1, 1); (0x145964, 4, 0);
    (0x67a128, 8, 0x69b638);
    (0x13d8b8, 8, 0x1d7c28); (0x1d7cb1, 1, 1);
    (0x13d918, 8, 0x1d5b98); (0x1d5b98, 4, 0);
    (0x13e6d0, 8, 8) ].
Lemma AS0_ALY_CELLS_D4_nodup : List.NoDup (map (fun c => fst (fst c)) AS0_ALY_CELLS_D4).
Proof.
  unfold AS0_ALY_CELLS_D4; cbn [map fst].
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H |]). apply List.NoDup_nil.
Qed.
Lemma AS0_ALY_CELLS_D4_img : Forall (fun c => 0x10000 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= 0x69c000) AS0_ALY_CELLS_D4.
Proof. repeat constructor; cbn; lia. Qed.

Record as0_layout (L : asan_layout) (C : asan_statics_cells) : Prop := ALY {
  aly_segs : hl_segs L = RSEGS;
  aly_sm1 : hl_stack_malloc L 1 = SM1; aly_sm2 : hl_stack_malloc L 2 = SM2; aly_sm3 : hl_stack_malloc L 3 = SM3;
  aly_nr : hl_handle_no_return L = 0x82394;
  aly_memset : hl_asan_memset L = 0x792dc; aly_memcpy : hl_asan_memcpy L = 0x78e40; aly_memmove : hl_asan_memmove L = 0x7951c;
  aly_malloc : hl_malloc L = 0x7a9c4; aly_free : hl_free L = 0x7a9c0; aly_aligned : hl_aligned_alloc L = 0x7a9cc;
  aly_img_lo : hl_img_lo L = 0x10000; aly_img_hi : hl_img_hi L = 0x69c000;
  aly_scr_sm : hl_scr_stack_malloc L = 512; aly_scr_nr : hl_scr_no_return L = 4160; aly_scr_mem : hl_scr_mem L = 2560;
  aly_scr_malloc : hl_scr_malloc L = 4096; aly_scr_free : hl_scr_free L = 4096; aly_scr_aligned : hl_scr_aligned L = 4096;
  aly_got_lo : asc_got_lo C = 0x137000; aly_got_hi : asc_got_hi C = 0x13f000;
  aly_cells : incl AS0_ALY_CELLS_D4 (asc_cells C);
  aly_static_img : forall a, hl_rt_static L a -> 0x10000 <= a < 0x69c000;
  aly_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x69c000;

  aly_static_lo : forall a, hl_rt_static L a -> 0x13f000 <= a;
  aly_cost : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L
}.

Lemma u64_at_of_cell M a v : cell_is RSEGS M a 8 v -> L5.u64_at RSEGS M a v. Proof. intros H; exact H. Qed.
Lemma u32_at_of_cell M a v : cell_is RSEGS M a 4 v -> L5.u32_at RSEGS M a v. Proof. intros H; exact H. Qed.
Lemma statics_facts L C M : as0_layout L C -> asan_statics RSEGS C M ->
  L5.img_clear M 0x137000 0x13f000 /\ L5.u64_at RSEGS M 0x1460f8 SB /\ L5.u32_at RSEGS M 0x146100 1
  /\ L5.u64_at RSEGS M 0x13f8d8 0x130034 /\ L5.u64_at RSEGS M 0x13f868 0x116acc.
Proof.
  intros LY (G & CS). rewrite (aly_got_lo L C LY), (aly_got_hi L C LY) in G. rewrite Forall_forall in CS.
  pose proof (aly_cells L C LY) as IC.
  split. exact G.
  split. exact (CS _ (IC _ (or_introl eq_refl))).
  split. exact (CS _ (IC _ (or_intror (or_introl eq_refl)))).
  split. exact (CS _ (IC _ (or_intror (or_intror (or_introl eq_refl))))). exact (CS _ (IC _ (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
Qed.
End SCFG_1.
End L5A.
