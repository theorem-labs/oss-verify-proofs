(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.
Module L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5A.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
Lemma segs_below : segs_below_b RSEGS 0x6b6000 = true. Proof. vm_compute. reflexivity. Qed.
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
Lemma hull_hi_eq : L5.hull_hi RSEGS = 0x6b6000. Proof. vm_compute. reflexivity. Qed.
Lemma hull_apart_of a n : (a + n <= 0x10000 \/ 0x6b6000 <= a) -> L5.hull_apart RSEGS a n.
Proof. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.
Lemma hull_apart_lit a n : L5.hull_apart RSEGS a n -> (a + n <= 0x10000 \/ 0x6b6000 <= a).
Proof. unfold L5.hull_apart. rewrite hull_lo_eq, hull_hi_eq. tauto. Qed.

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma mrestrict_agree M lo hi : (forall i, lo <= i < hi -> H (Z_to_bv 64 i) = false) -> forall i, lo <= i < hi -> mrestrict H M (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof. intros V i Hi. apply mrestrict_visible. apply V. exact Hi. Qed.
End WithH.

(* [comment removed for export] *)
Lemma ahid_not_lazy A m w : page_in_ranges (page_base w) (m_vm_lazy m) = false -> ahid A m w = false.
Proof. intros E. unfold ahid, mkH. rewrite E. reflexivity. Qed.
Lemma ahid_allowed A m w : page_allowedb A (page_base w) = true -> ahid A m w = false.
Proof. intros E. unfold ahid, mkH. rewrite E. cbn. apply Bool.andb_false_r. Qed.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition SM1 : Z := 0x64960. Definition SM2 : Z := 0x64af0. Definition SM3 : Z := 0x64c8c.
(* [comment removed for export] *)
Definition AS0_ALY_CELLS_D4 : list (Z * Z * Z) :=
  [ (0x15fa78, 8, SB); (0x15fa80, 4, 1); (0x158da8, 8, 0x14916c); (0x158d38, 8, 0x12fbf0);                     (* [comment removed for export] *)
    (0x156d98, 8, 0x15fa78);                                                                                (* [comment removed for export] *)
    (0x156da0, 8, 0x160768); (0x160768, 8, 0); (0x156da8, 8, 0x160770); (0x160770, 8, 0);                        (* [comment removed for export] *)
    (0x156db0, 8, 0x160760); (0x160760, 8, 0x7fffffffffff);                                                  (* [comment removed for export] *)
    (0x157900, 8, 0x160759); (0x160759, 1, 1);                                                               (* [comment removed for export] *)
    (0x158da0, 8, 0x148d68);                                                                                (* [comment removed for export] *)
    (0x160758, 1, 1);                                                                                      (* [comment removed for export] *)
    (0x158c98, 8, 0x149d4c);                                                                                (* [comment removed for export] *)
    (0x693af8, 8, 0x693b20); (0x693b28, 8, 0x694300);                                                     (* [comment removed for export] *)
    (0x15f2e0, 1, 1); (0x15f2e4, 4, 0);                                                                     (* [comment removed for export] *)
    (0x693aa8, 8, 0x6b4fb8);                                                                              (* [comment removed for export] *)
    (0x156d88, 8, 0x1f15a8); (0x1f1631, 1, 1);                                                             (* [comment removed for export] *)
    (0x156de8, 8, 0x1ef518); (0x1ef518, 4, 0);                                                             (* [comment removed for export] *)
    (0x157ba0, 8, 8) ].                                                                                    (* [comment removed for export] *)
Lemma AS0_ALY_CELLS_D4_nodup : List.NoDup (map (fun c => fst (fst c)) AS0_ALY_CELLS_D4).
Proof.
  unfold AS0_ALY_CELLS_D4; cbn [map fst].
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H |]). apply List.NoDup_nil.
Qed.
Lemma AS0_ALY_CELLS_D4_img : Forall (fun c => 0x10000 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= 0x6b6000) AS0_ALY_CELLS_D4.
Proof. repeat constructor; cbn; lia. Qed.

Record as0_layout (L : asan_layout) (C : asan_statics_cells) : Prop := ALY {
  aly_segs : hl_segs L = RSEGS;
  aly_sm1 : hl_stack_malloc L 1 = SM1; aly_sm2 : hl_stack_malloc L 2 = SM2; aly_sm3 : hl_stack_malloc L 3 = SM3;
  aly_nr : hl_handle_no_return L = 0x88110;
  aly_memset : hl_asan_memset L = 0x7f058; aly_memcpy : hl_asan_memcpy L = 0x7ebbc; aly_memmove : hl_asan_memmove L = 0x7f298;
  aly_malloc : hl_malloc L = 0x80740; aly_free : hl_free L = 0x8073c; aly_aligned : hl_aligned_alloc L = 0x80748;
  aly_img_lo : hl_img_lo L = 0x10000; aly_img_hi : hl_img_hi L = 0x6b6000;
  aly_scr_sm : hl_scr_stack_malloc L = 512; aly_scr_nr : hl_scr_no_return L = 4160; aly_scr_mem : hl_scr_mem L = 2560;
  aly_scr_malloc : hl_scr_malloc L = 4096; aly_scr_free : hl_scr_free L = 4096; aly_scr_aligned : hl_scr_aligned L = 4096;
  aly_got_lo : asc_got_lo C = 0x150000; aly_got_hi : asc_got_hi C = 0x158000;
  aly_cells : incl AS0_ALY_CELLS_D4 (asc_cells C);                                       (* [comment removed for export] *)
  aly_static_img : forall a, hl_rt_static L a -> 0x10000 <= a < 0x6b6000;
  aly_ro_img : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x6b6000;
  (* [comment removed for export] *)
  aly_static_lo : forall a, hl_rt_static L a -> 0x158000 <= a;                          (* [comment removed for export] *)
  aly_cost : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Lemma u64_at_of_cell M a v : cell_is RSEGS M a 8 v -> L5.u64_at RSEGS M a v. Proof. intros H; exact H. Qed.
Lemma u32_at_of_cell M a v : cell_is RSEGS M a 4 v -> L5.u32_at RSEGS M a v. Proof. intros H; exact H. Qed.
Lemma statics_facts L C M : as0_layout L C -> asan_statics RSEGS C M ->
  L5.img_clear M 0x150000 0x158000 /\ L5.u64_at RSEGS M 0x15fa78 SB /\ L5.u32_at RSEGS M 0x15fa80 1
  /\ L5.u64_at RSEGS M 0x158da8 0x14916c /\ L5.u64_at RSEGS M 0x158d38 0x12fbf0.
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

End L5DefsA.
From Stdlib Require ZArith List Lia.
Module PnAImgGap.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMAGAP.
Definition GAP_LO : Z := 0x26e20.
Definition GAP_HI : Z := 0x26f40.
Definition GAPB_LO : Z := 0x265c0.
Definition GAPB_HI : Z := 0x26660.
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x6b6000.
Definition rt_img_gap (HI : asan_iface) : Prop :=
  forall LB FF LK cr A M V, ri_inv HI LB FF LK cr A M V ->
    ((forall x, HeapIfaceA.S GAP_LO <= x < HeapIfaceA.S GAP_HI -> byte_at M x 0) /\ shadow_allowed A GAP_LO (GAP_HI - GAP_LO))
    /\ (forall x, HeapIfaceA.S GAPB_LO <= x < HeapIfaceA.S GAPB_HI -> byte_at M x 0)
    /\ shadow_allowed A IMG_LO (IMG_HI - IMG_LO).

(* [comment removed for export] *)
Lemma gap_vis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147470788 36.
Proof.
  intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as ((Z0 & SA) & _).
  assert (INS : forall j, 0 <= j < 36 -> in_shadow_of GAP_LO (GAP_HI - GAP_LO) (2147470788 + j)).
  { intros j Hj. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI.
    change (0x26e20 / 8 + 2147450880) with 2147470788. change ((0x26e20 + (0x26f40 - 0x26e20) - 1) / 8 + 2147450880) with 2147470823. lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ 36 (L5A.avis_of_shadow_allowed Aw model GAP_LO (GAP_HI - GAP_LO) 2147470788 36 SA INS))).
  intros j Hj. pose proof (Z0 (2147470788 + j)) as B. unfold byte_at in B. apply B.
  unfold HeapIfaceA.S, HeapIfaceA.SB, GAP_LO, GAP_HI. change (0x26e20 / 8 + 2147450880) with 2147470788. change (0x26f40 / 8 + 2147450880) with 2147470824. lia.
Qed.

(* [comment removed for export] *)
Lemma img_shallowed HI (GAP : rt_img_gap HI) LB FF LK cr Aw M V : ri_inv HI LB FF LK cr Aw M V -> shadow_allowed Aw 0x10000 (0x6b6000 - 0x10000).
Proof. intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as (_ & _ & SA). exact SA. Qed.
Lemma img_sh_avis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model a n x g :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> 0x10000 <= a -> a + n <= 0x6b6000 -> 0 < n ->
  (forall j, 0 <= j < g -> in_shadow_of a n (x + j)) -> L5A.avis (ahid Aw model) x g.
Proof.
  intros HH H1 H2 Hn INS.
  apply (L5A.avis_of_shadow_allowed Aw model 0x10000 (0x6b6000 - 0x10000) x g (img_shallowed HI GAP _ _ _ _ _ _ _ HH)).
  intros j Hj. pose proof (INS j Hj) as X. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in *.
  pose proof (Z.div_le_mono 0x10000 a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (a + n - 1) (0x10000 + (0x6b6000 - 0x10000) - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma gapB_vis HI (GAP : rt_img_gap HI) LB FF LK cr Aw M model : ri_inv HI LB FF LK cr Aw M (vml_of model) ->
  L5KA.zeros_at (mrestrict (ahid Aw model) M) 2147470520 20.
Proof.
  intros HH. destruct (GAP _ _ _ _ _ _ _ HH) as (_ & Z0 & _).
  assert (INS : forall j, 0 <= j < 20 -> in_shadow_of GAPB_LO (GAPB_HI - GAPB_LO) (2147470520 + j)).
  { intros j Hj. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, GAPB_LO, GAPB_HI.
    change (0x265c0 / 8 + 2147450880) with 2147470520. change ((0x265c0 + (0x26660 - 0x265c0) - 1) / 8 + 2147450880) with 2147470539. lia. }
  apply (proj2 (L5A.zeros_at_vis _ M _ 20 (img_sh_avis HI GAP _ _ _ _ _ _ _ GAPB_LO (GAPB_HI - GAPB_LO) 2147470520 20 HH
            ltac:(unfold GAPB_LO; lia) ltac:(unfold GAPB_LO, GAPB_HI; lia) ltac:(unfold GAPB_LO, GAPB_HI; lia) INS))).
  intros j Hj. pose proof (Z0 (2147470520 + j)) as B. unfold byte_at in B. apply B.
  unfold HeapIfaceA.S, HeapIfaceA.SB, GAPB_LO, GAPB_HI. change (0x265c0 / 8 + 2147450880) with 2147470520. change (0x26660 / 8 + 2147450880) with 2147470540. lia.
Qed.
End PMAGAP.

End PnAImgGap.
