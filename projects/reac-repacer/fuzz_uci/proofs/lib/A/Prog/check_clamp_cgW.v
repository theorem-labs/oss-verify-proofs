(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* check_clamp_cgW: Theorem uci_check_clamp_cg_holds : uci_check_clamp_cg_holds_stmt.
   The walk has five pieces, at the offsets of the audited listing lib/A/Prog/UciPList.v:
     +0x000 .. +0x064  the frame, the eleven saves, the 32-byte realign, the two runtime cells and the
                       `jal __asan_stack_malloc_1` of class 1 (the statement's astack_malloc_realizes premise);
     +0x068 .. +0x114  the fake frame taken, its header and its shadow written, and the
                       `jal __asan_memcpy` of 20 bytes into it (the statement's aintrin_realizes premise);
     +0x118 .. +0x120  `jal rp_hot_clamp` on the copy (the statement's uci_leaf_wr_at premise);
     +0x124 .. +0x240  the five field comparisons, each guarded by a shadow check whose report call the
                       statement's range_addressable premise refutes;
     +0x244 .. +0x314  the frame's shadow and header set to released, the flag byte cleared (the frame is given
                       back), the eleven reloads and the `ret`.
   The pieces that need no allocator model are in lib/A/Prog/UciCcKit.v; the leaf's footprint premises come from
   lib/A/Prog/UciCcLeafb.v; the five comparisons are lib/A/Prog/UciCcCmp.v and the release and return
   lib/A/Prog/UciCcRel.v. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import
UciPSyms UciPList UciPAddr UciPPa UciPImg UciPPaLib UciPCJ.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k AsanCells AF0x.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import Cells Step Frame ExecF Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciCg UciCcKit UciCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import check_clamp_cg UciCcCut UciCcCmp UciCcRel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_hot_clamp_cg LeafCgKit.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_hot_clamp_c AsanKA.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_hot_clamp_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module UCells := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.AsanCells.
Module LHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_hot_clamp_cg.
Module PHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_hot_clamp_c.
Module LCK := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.LeafCgKit.
Module AHC := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_hot_clamp_c.
Module AKA := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.AsanKA.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The shadow band the token engine is told about (the donor's YC4b.v Bspan at this unit's shadow base). *)
Definition CBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The empty span, for the runs that read no shadow byte (the donor's seg_early E_B0). *)
Definition CC_B0 : Z * Z := (0, 0).

(* The ten words check_clamp's prologue saves, as (offset below the entry stack pointer, register). *)
Definition cc_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv);
   (-48, 20%bv); (-56, 21%bv); (-64, 22%bv); (-72, 23%bv); (-80, 24%bv)].

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at the entry                                  *)
(* ------------------------------------------------------------------ *)

(* The use-after-return flag: its GOT word (object 2) holds the cell (object 9), which holds 1 in every state, so
   the `beqz a2` at +0x5c never takes the no-fake-stack arm. *)
Definition cc_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 9) 0))].
Definition cc_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 9)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
(* The four image regions every piece of the walk re-derives from uci_cells after a call. *)
Definition cc_img_regions : smem := [got_regionP; bcell_regionP 32; cc_got_uar; cc_uar_cell].
Definition cc_regions : smem := stack_region CC_FRAME :: cc_img_regions.
Definition cc_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_cc : sstate := mkSS AF_check_clamp sr_atoms cc_regions None cc_facts.

Section cc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

Lemma cc_vals : VAL (A_OBJ 0) = UCells.GOT_CELL_K /\ VAL (A_OBJ 8) = UCells.CELL_K /\
  VAL (A_OBJ 2) = UCells.GOT_UAR /\ VAL (A_OBJ 9) = UCells.UAR /\ VAL A_TEXT = uci_sigma US_check_clamp - AF_check_clamp.
Proof. vm_compute. repeat split. Qed.

(* One byte, between its view value and its one-byte memory value. *)
Lemma cc_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
  intros v Hv.
  assert (HB : 0 <= le_byte v 1 0 < 256) by (unfold le_byte; apply Z.mod_pos_bound; lia).
  assert (EU : bv_unsigned (Z_to_bv 8 v) = v).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    apply Z.mod_small. lia. }
  assert (EQ : Z_to_bv 8 (le_byte v 1 0) = Z_to_bv 8 v).
  { pose proof (ucc_leafb_le_byte1 (Z_to_bv 8 v)) as H. rewrite EU in H. exact H. }
  apply (f_equal bv_unsigned) in EQ. rewrite !Z_to_bv_unsigned in EQ.
  unfold bv_wrap, bv_modulus in EQ. change (2 ^ Z.of_N 8) with 256 in EQ.
  rewrite !Z.mod_small in EQ by lia. exact EQ.
Qed.

Lemma cc_aview_val1 : forall H m a v, 0 <= v < 256 ->
  val_mem segs (mrestrict H m) a 1 v -> aview segs H m a = Some v.
Proof.
  intros H m a v Hv HV. rewrite (ucc_aview_of_val1 _ _ _ _ _ HV), (cc_le_byte1 v Hv). reflexivity.
Qed.

Lemma cc_val1_aview : forall H m a v, 0 <= v < 256 ->
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
  intros H m a v Hv Ha k Hk. assert (k = 0%nat) as -> by lia.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Ha. destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:E; [|discriminate].
  cbn in Ha. injection Ha as Ha. subst v. f_equal. symmetry. apply ucc_leafb_le_byte1.
Qed.

(* A visible byte reads the same through the world as it does raw, so a record of cells the raw memory
   holds is one the world's memory holds. *)
Lemma cc_mrd_restrict : forall (H : word -> bool) mem a, H (Z_to_bv 64 a) = false ->
  mrd rsegs (mrestrict H mem) (wa a) = mrd rsegs mem (wa a).
Proof.
  intros H mem a Hh. unfold mrd, wa, mrestrict.
  destruct (find_segment rsegs a 1); (try rewrite Hh); reflexivity.
Qed.

Lemma cc_cells_at_restrict : forall (W : world segs) mem p cs,
  cells_at rsegs mem p cs ->
  (forall i, (i < length (cells_bytes cs))%nat -> w_H W (Z_to_bv 64 (p + Z.of_nat i)) = false) ->
  cells_at rsegs (mrestrict (w_H W) mem) p cs.
Proof.
  intros W mem p cs (Hwf & H0 & Ht & Hb) Hvis.
  split; [exact Hwf|]. split; [exact H0|]. split; [exact Ht|].
  intros i Hi. rewrite (cc_mrd_restrict (w_H W) mem (p + Z.of_nat i) (Hvis i Hi)). exact (Hb i Hi).
Qed.

(* An eight-byte word of the view, and a byte of the view, kept by a step that writes elsewhere. *)
Lemma cc_rdword_frame : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a Hk. unfold rdword.
  pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
          (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

Lemma cc_aview_out : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview segs H m' a = aview segs H m a.
Proof.
  intros E rs H m m' a HF Ha Hno. apply aview_eq_of. apply HF.
  rewrite unsigned_lit_small by lia. exact Hno.
Qed.
(* The four image regions hold what uci_cells says they hold, at any AR state. *)
Lemma cc_img_ok : forall ly S (W : world segs) mem md (E : env),
  uci_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8)) ->
  ew E (A_OBJ 2) = Z_to_bv 64 (VAL (A_OBJ 2)) -> ew E (A_OBJ 9) = Z_to_bv 64 (VAL (A_OBJ 9)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) cc_img_regions /\
  pairwise_disjoint E cc_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E0 E8 E2 E9 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct cc_vals as (V0 & V8 & V2 & V9 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) UCells.CELL_K = Some UCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold UCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) UCells.GOT_CELL_K = Some UCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold UCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) UCells.GOT_UAR = Some UCells.UAR)
    by (apply (rdword_cell B ly); [unfold UCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) UCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold UCells.GOT_CELL_K; lia).
  assert (R8 : 0 <= VAL (A_OBJ 8) < 2 ^ 47) by (rewrite V8; unfold UCells.CELL_K; lia).
  assert (R2 : 0 <= VAL (A_OBJ 2) < 2 ^ 47) by (rewrite V2; unfold UCells.GOT_UAR; lia).
  assert (R9 : 0 <= VAL (A_OBJ 9) < 2 ^ 47) by (rewrite V9; unfold UCells.UAR; lia).
  split.
  - unfold cc_img_regions, got_regionP, bcell_regionP, cc_got_uar, cc_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 8) 0) (VAL (A_OBJ 8)));
      [cbn [sv_denot]; rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V8. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 8) (VAL (A_OBJ 8)) E8) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 8)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V8. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 2) (VAL (A_OBJ 2)) E2) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 2)) 0 8 (SOff (A_OBJ 9) 0) (VAL (A_OBJ 9)));
      [cbn [sv_denot]; rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V2, V9. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 9) (VAL (A_OBJ 9)) E9) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 9)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V9. exact (ucc_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold cc_img_regions, got_regionP, bcell_regionP, cc_got_uar, cc_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 8) (VAL (A_OBJ 8)) E8),
      (VB (A_OBJ 2) (VAL (A_OBJ 2)) E2), (VB (A_OBJ 9) (VAL (A_OBJ 9)) E9) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V0, V8, V2, V9. unfold UCells.GOT_CELL_K, UCells.CELL_K, UCells.GOT_UAR, UCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The environment of the walk: the thirty-two registers as atoms 0 .. 31, the shadow base as atom 32, and the
   image's own values above A_TEXT. *)
Definition cc_E (regs : bvmap 5 word) : env := Eimg (PI := PI_uci) (Ereg regs [w64 SHADOW_OFF]).

Lemma cc_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cc_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold cc_E. apply ucc_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma cc_ew_32 : forall regs, ew (cc_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
  intros regs. unfold cc_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
Qed.

Lemma cc_ew_obj : forall regs i, (i < 10)%nat -> ew (cc_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold cc_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

Lemma cc_env_img : forall regs, img_env VAL A_LIM (cc_E regs).
Proof. intros regs. unfold cc_E. apply Eimg_env. Qed.

(* The symbolic state the walk starts from (the eleven saves go into the stack region). *)
Lemma cc_entry : forall ly S (W : world segs) regs mem md,
  uci_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - CC_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (cc_E regs) ss_cc
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_check_clamp)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_cc, cc_regions.
  assert (Usp : bv_unsigned (ew (cc_E regs) 2) = spZ regs)
    by (rewrite (cc_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (cc_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply cc_ew_32.
  destruct (cc_img_ok ly S W mem md (cc_E regs) HCELLS HAR
    (cc_ew_obj regs 0 ltac:(lia)) (cc_ew_obj regs 8 ltac:(lia))
    (cc_ew_obj regs 2 ltac:(lia)) (cc_ew_obj regs 9 ltac:(lia)) E32) as [HRs HPd].
  destruct cc_vals as (V0 & V8 & V2 & V9 & _).
  assert (VB : forall n v0, ew (cc_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (cc_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc uci_listing PI_uci).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold CC_FRAME.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. unfold CC_FRAME. lia.
  - unfold cc_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, cc_got_uar, cc_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (cc_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold UCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 8) (VAL (A_OBJ 8)) (cc_ew_obj regs 8 ltac:(lia)))
      by (rewrite V8; unfold UCells.CELL_K; lia).
    rewrite (VB (A_OBJ 2) (VAL (A_OBJ 2)) (cc_ew_obj regs 2 ltac:(lia)))
      by (rewrite V2; unfold UCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 9) (VAL (A_OBJ 9)) (cc_ew_obj regs 9 ltac:(lia)))
      by (rewrite V9; unfold UCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V0, V8, V2, V9. unfold UCells.GOT_CELL_K, UCells.CELL_K, UCells.GOT_UAR, UCells.UAR, CC_FRAME.
    repeat split; first [exact I | lia].
  - unfold cc_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The symbolic state the walk takes up again at +0x068, with the fake frame in a0 (atom 10), the realigned sp in
   s1 (atom 9) and the shadow base in s8 (atom 24). The function writes the eight-byte slot at s1 + 8 and the
   frame's 24-byte ASan header. *)
Definition cc_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 8 16 [].
Definition cc_rg_frame : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition cc_regions2 : smem := [cc_rg_slot; cc_rg_frame].
Definition cc_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 5); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition CC_C1 : Z := AF_check_clamp + 0x68.
Definition ss_cc2 : sstate := mkSS CC_C1 sr_atoms cc_regions2 None cc_facts2.

Lemma cc_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 128 <= spv - 4096 -> F mod 32 = 0 ->
  (forall a, spv + 8 <= a < spv + 16 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (cc_E regs) ss_cc2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CC_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R24 Hsp Hsp32 HF0 HFs HF32 Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_cc2, cc_regions2.
  assert (U2 : bv_unsigned (ew (cc_E regs) 2) = spv)
    by (rewrite (cc_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (cc_E regs) 9) = spv)
    by (rewrite (cc_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (cc_E regs) 10) = F)
    by (rewrite (cc_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew (cc_E regs) 24) = SHADOW_OFF)
    by (rewrite (cc_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (cc_E regs) 32) = SHADOW_OFF)
    by (rewrite (cc_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc uci_listing PI_uci).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold cc_rg_slot, cc_rg_frame, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold cc_rg_slot, cc_rg_frame, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold cc_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U24, U32.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The symbolic state at +0x0d8, where s6 (atom 22) holds the shadow address of the frame: the twelve shadow
   bytes the function writes for the frame are this region. *)
Definition cc_rg_sh : YP09.region := YP09.mkRegion (Some 22%nat) 0 12 0 12 [].
Definition cc_regions3 : smem := [cc_rg_sh].
Definition cc_facts3 : facts := mkFacts [(22%nat, mkAF SHADOW_OFF (2 ^ 47) 0)] [] [].
Definition CC_C2 : Z := AF_check_clamp + 0xd8.
Definition ss_cc3 : sstate := mkSS CC_C2 sr_atoms cc_regions3 None cc_facts3.

Lemma cc_entry3 : forall (W : world segs) regs mem (SH6 : Z),
  YK11.getr regs 22 = w64 SH6 -> SHADOW_OFF <= SH6 -> SH6 + 12 <= 2 ^ 47 ->
  (forall a, SH6 <= a < SH6 + 12 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (cc_E regs) ss_cc3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CC_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH6 R22 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_cc3, cc_regions3.
  assert (U22 : bv_unsigned (ew (cc_E regs) 22) = SH6)
    by (rewrite (cc_ew_reg regs 22 22%bv eq_refl), R22; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc uci_listing PI_uci).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold cc_rg_sh, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold cc_rg_sh, extent_of_region. cbn [map]. cbn [zpairwise_disjoint zall_disjoint].
    repeat split; exact I.
  - unfold cc_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* The symbolic state at +0x118: three register moves and the leaf call, so no region and no fact. *)
Definition CC_C3 : Z := AF_check_clamp + 0x118.
Definition ss_cc4 : sstate := mkSS CC_C3 sr_atoms [] None (mkFacts [] [] []).

Lemma cc_entry4 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (cc_E regs) ss_cc4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CC_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_cc4.
  apply (@pa_entry_st_ok_full fx rc uci_listing PI_uci).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cc_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac cc_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac cc_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; cc_ro_rec ].

(* Where the ten saved words (spr - 80 .. spr) and the frame's flag word (F + 120 .. F + 128) lie: below 2 ^ 64,
   outside the slot at sp1 + 8, the frame's 24-byte header, the frame's twelve shadow bytes, the 20-byte local and
   the 4096 bytes below sp1 that a callee of this function may use. *)
Lemma cc_kp_geom : forall spr sp1 F a,
  2 ^ 46 <= spr <= 2 ^ 47 -> spr - 112 <= sp1 <= spr - 96 -> 4096 <= F -> F + 128 <= sp1 - 4096 ->
  in_app F 128 ->
  spr - 80 <= a < spr \/ F + 120 <= a < F + 128 ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 + 8 <= a < sp1 + 16) /\ ~ (F + 0 <= a < F + 24) /\
  ~ (SHADOW_OFF + F / 8 + 0 <= a < SHADOW_OFF + F / 8 + 12) /\ ~ (F + 32 <= a < F + 32 + 20) /\
  ~ (sp1 - 4096 <= a < sp1).
Proof.
  intros spr sp1 F a Hs H1 HF0 HFs Happ Ha.
  assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct Happ as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg in *; unfold SHADOW_OFF;
  repeat split; lia.
Qed.

(* The walk, with the two pieces after the leaf call (the five comparisons, lib/A/Prog/UciCcCmp.v, and
   the release and return, lib/A/Prog/UciCcRel.v) taken as their cut statements of
   lib/A/Prog/UciCcCut.v. *)
Lemma cc_holds_of : @cc_cmp_stmt fx rc B -> @cc_rel_stmt fx rc B MT ->
  @uci_check_clamp_cg_holds_stmt fx rc B MT.
Proof.
intros CMP REL.
unfold uci_check_clamp_cg_holds_stmt.
intros HPCS HCELLS LAWS MTL MTF SMP ASF FFL ASM0 AI0 LEAF0.
unfold uci_check_clamp_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pin mm p
  HJ0 Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hint Hmm Hpin1 Hpin2 Hgarr HRA HHULL Hcnt Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJ0 as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres0 & Hstk & _ & HQT).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hcc : CC_STK = 4208) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia).
assert (Hpres1 : forall a, spZ regs - CC_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; unfold CC_FRAME, CC_STK, CC_ALIGN in *; lia).
(* The walk's own journal: the caller's, re-based at this call's sp with this function's stack budget. *)
assert (HJ1 : @ajournal rc tfib_sink_head segs B CC_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
{ eapply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k CC_STK (spZ regs) []
    (spZ regs - sp0) HJ0);
  [lia | rewrite Zminus_mod, Hsp16, Hsp0a; reflexivity | lia | unfold CC_STK, CC_FRAME, CC_ALIGN; lia
  | unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia]. }
pose proof (cc_entry lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hspr Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (cc_E regs)) by apply cc_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (cc_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (cc_E regs) 2) = spZ regs)
  by (rewrite (cc_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (paj_run (SK := tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_check_clamp)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* +0x000 .. +0x060: the frame, the eleven saves, s0, the 32-byte realign into s1, the two runtime cells, the
   never-taken `beqz a2` and `li a0, 0x60`, up to the `jal __asan_stack_malloc_1` at +0x064. *)
paj_run_tok RUN HS HJ1 SHOK CBspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack _ _ _ _ _ _ _ _ _ _ 2%nat);
  [reflexivity | rewrite Usp; reflexivity | cbn; unfold CC_STK, CC_FRAME, CC_ALIGN; lia | cbn; lia |].
  cc_ro_rec. }
(* sp after `addi sp,sp,-0x60` and `andi sp,sp,-0x20`. *)
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (ucc_sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by (clear - Hsp1r; lia).
assert (E2' : ew (cc_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (cc_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
cc_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1544)) R1 ltac:(apply codeptr_val; exact HEI).
cc_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (ucc_denot_and_m32 (cc_E regs) 2 (spZ regs) (-96) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
cc_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
cc_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
cc_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
cc_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (ucc_denot_and_m32_add0 (cc_E regs) 2 (spZ regs) (-96) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
cc_reg HS (19%bv : bv 5) (w64 pin) R19
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
cc_reg HS (20%bv : bv 5) (w64 mm) R20
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
cc_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) R24
  ltac:(cbn [sv_denot]; rewrite (cc_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (25%bv : bv 5) (YK11.getr regs 25) R25
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 25 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (26%bv : bv 5) (YK11.getr regs 26) R26
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (27%bv : bv 5) (YK11.getr regs 27) R27
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs 27 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The ten words the prologue saved, read back from the stack region the run wrote. *)
lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  assert (HRsk : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
    by (apply (ucc_region_nth Ex ssx (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity)
end.
cbn [ms_mem restrict] in HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) cc_saved -> -80 <= o <= -8).
{ intros o r Hin. unfold cc_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) cc_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold cc_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(cc_u64 (YK11.getr regs r))).
  apply (ucc_field_of_region (cc_E regs) _ 2 (spZ regs) _ (-96) 0 (-96) 0 o 8%N (SOff (Z.to_nat (bv_unsigned r)) 0)
    (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (cc_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; cc_u64 (YK11.getr regs r)
  | cbn; lia ]. }
(* +0x064: the class-1 fake-stack call, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (uci_sigma US___asan_stack_malloc_1)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (ucc_stack_malloc_at segs B LAWS uci_segs_low SMP CC_CID ASM ltac:(unfold CC_CID; lia)
    W rg mm CC_STK (spZ regs) (@nil (Z * Z)) lyc Sc W memc mdc (@nil (Z * Z)) lyc Sc mdx 0
    (sp1 - spZ regs) (Z_to_bv 64 (BASE + 1544)) HJ1) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, CC_STK, CC_FRAME, CC_ALIGN. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_uci)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
(* The fake frame the call handed back: its address, its alignment and its bytes. *)
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (CC_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ CC_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ CC_CID pos HAR2 Hin2) as (HF0 & HFc & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _).
pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & _).
(* the ten saved words and the frame's flag pointer, kept by the class-1 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) cc_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  assert (Hfr : forall i, 0 <= i < 8 ->
    aview segs (w_H W) mem2 (spZ regs + o + i) = aview segs (w_H W) (ms_mem ms) (spZ regs + o + i)).
  { intros i Hi. apply (proj1 HK1).
    - unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *. lia.
    - intros Hc. unfold ESTACK, CC_STK, CC_FRAME, CC_ALIGN in *. lia. }
  rewrite (cc_rdword_frame _ _ _ Hfr). exact (HSV o r Hin). }
change (fs_frame_bytes CC_CID) with 128 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc CC_CID pos) in *.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 pin)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 mm)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q24 : YK11.getr regs2 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]).
assert (HFsp : F + 128 <= sp1 - 4096) by (unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia).
assert (GF0 : 4096 <= F) by lia.
pose proof (cc_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q24 ltac:(lia) Hsp1al ltac:(lia) HFsp HFal
  ltac:(intros a Ha; apply Hpres2; unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS2.
clear HS. rename HS2 into HS.
assert (HEI2 : img_env VAL A_LIM (cc_E regs2)) by apply cc_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 24 0) (@nil shent) (cc_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9' : bv_unsigned (ew (cc_E regs2) 9) = sp1)
  by (rewrite (cc_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (cc_E regs2) 10) = F)
  by (rewrite (cc_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; unfold w64; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CC_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
(* +0x068 .. +0x0d4: the fake frame taken, the slot at s1 + 8, the frame's 24-byte ASan header and the shadow
   address in s6, up to the first shadow store at +0x0d8. *)
paj_run_tok RUN HS HJ2 SHOK CC_B0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - spZ regs));
  [reflexivity | rewrite U9'; lia | cbn; unfold CC_STK, CC_FRAME, CC_ALIGN; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10' | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi cc_rg_frame]. intros a Ha.
  right; right; right. exists CC_CID, pos. split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CC_CID) with 128. lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms3 := msx) in * end.
(* The ten saved words and the flag word, kept by this run: it writes the slot at s1 + 8 and the frame's header. *)
assert (KA : forall a, spZ regs - 80 <= a < spZ regs \/ F + 120 <= a < F + 128 ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
{ intros a Ha.
  destruct (cc_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp Ha) as (G0 & G1 & G2 & _ & _ & _).
  match goal with HFx : frame_of _ (ss_mem ss_cc2) (mrestrict (w_H W) mem2) (mrestrict (w_H W) _) |- _ =>
    apply (cc_aview_out _ _ (w_H W) mem2 _ a HFx G0) end.
  intros (r & Hr & Hb). unfold ss_cc2, cc_regions2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]];
  cbn [cc_rg_slot cc_rg_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
  - rewrite U9' in Hb. exact (G1 Hb).
  - rewrite U10' in Hb. exact (G2 Hb). }
(* The registers at +0x0d8: the local (s5), the frame's shadow address (s6) and the frame (s7). *)
assert (EF10 : ew (cc_E regs2) 10 = Z_to_bv 64 F)
  by (rewrite (cc_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF24 : ew (cc_E regs2) 24 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (cc_ew_reg regs2 24 24%bv eq_refl); exact Q24).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
cc_reg HS (21%bv : bv 5) (Z_to_bv 64 (F + 32)) T21
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
        rewrite (unsigned_lit_small F HFbv); reflexivity).
cc_reg HS (22%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T22
  ltac:(exact (ucc_denot_shadow (cc_E regs2) 10 24 F SHADOW_OFF EF10 EF24 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia));
                     unfold SHADOW_OFF; lia))).
cc_reg HS (19%bv : bv 5) (w64 pin) T19
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 19 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q19).
cc_reg HS (20%bv : bv 5) (w64 mm) T20
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 20 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q20).
cc_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) T24
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 24 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q24).
cc_reg HS (18%bv : bv 5) (Z_to_bv 64 F) T18
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
        rewrite (unsigned_lit_small F HFbv), Z.add_0_r; reflexivity).
cc_reg HS (23%bv : bv 5) (Z_to_bv 64 F) T23
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
        rewrite (unsigned_lit_small F HFbv), Z.add_0_r; reflexivity).
cc_reg HS (25%bv : bv 5) (YK11.getr regs2 25) T25
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 25 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cc_reg HS (26%bv : bv 5) (YK11.getr regs2 26) T26
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cc_reg HS (27%bv : bv 5) (YK11.getr regs2 27) T27
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 27 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
cc_reg HS (8%bv : bv 5) (w64 (spZ regs)) T8b
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 8 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q8).
cc_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
cc_reg HS (8%bv : bv 5) (w64 (spZ regs)) T8
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 8 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q8).
cc_reg HS (3%bv : bv 5) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
cc_reg HS (4%bv : bv 5) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs2 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
cc_reg HS (10%bv : bv 5) (w64 4) T10 ltac:(reflexivity).
(* Take the state up again at +0x0d8 with the shadow address as its own atom. *)
pmkst HS.
pose proof (proj1 HJ2) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ CC_CID pos HAR3 Hin2) as (_ & _ & _ & HFsh3).
change (fs_frame_bytes CC_CID / 8) with 16 in HFsh3.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
pose proof (cc_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) T22
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by (rewrite ESH; lia);
        exact (proj1 (HFsh3 (a - shadow_addr F) ltac:(rewrite ESH; lia))))) as HS3.
clear HS. rename HS3 into HS.
assert (HEI3 : img_env VAL A_LIM (cc_E (ms_regs ms3))) by apply cc_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 24 0) (@nil shent) (cc_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U22' : bv_unsigned (ew (cc_E (ms_regs ms3)) 22) = SHADOW_OFF + F / 8)
  by (rewrite (cc_ew_reg (ms_regs ms3) 22 22%bv eq_refl), T22; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
(* +0x0d8 .. +0x110: the twelve shadow bytes of the frame, then `jal __asan_memcpy` at +0x114. *)
paj_run_tok RUN HS HJ2 SHOK CC_B0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat (SHADOW_OFF + F / 8));
  [reflexivity | exact U22' | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi cc_rg_sh]. intros a Ha.
  right; right; right. exists CC_CID, pos. split; [left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CC_CID / 8) with 16.
  unfold shadow_addr. unfold F in *. lia. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => set (ms4 := msx) in * end.
(* The ten saved words and the flag word, kept by this run: it writes the frame's twelve shadow bytes only. *)
assert (KB : forall a, spZ regs - 80 <= a < spZ regs \/ F + 120 <= a < F + 128 ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha.
  destruct (cc_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp Ha) as (G0 & _ & _ & G3 & _ & _).
  match goal with HFx : frame_of _ (ss_mem ss_cc3) (mrestrict (w_H W) _) (mrestrict (w_H W) _) |- _ =>
    apply (cc_aview_out _ _ (w_H W) _ _ a HFx G0) end.
  intros (r & Hr & Hb). unfold ss_cc3, cc_regions3 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []].
  cbn [cc_rg_sh YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
  rewrite U22' in Hb. exact (G3 Hb). }
(* The registers and the three shadow bytes of the local at the __asan_memcpy call. *)
cc_reg HS (10%bv : bv 5) (Z_to_bv 64 (F + 32)) M10
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 21 21%bv eq_refl), T21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (11%bv : bv 5) (w64 pin) M11
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 19 19%bv eq_refl), T19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (12%bv : bv 5) (w64 20) M12 ltac:(reflexivity).
cc_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1720)) M1 ltac:(apply codeptr_val; exact HEI).
cc_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) M2
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 2 2%bv eq_refl), T2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (3%bv : bv 5) (w64 (as_gp B)) M3
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 3 3%bv eq_refl), T3, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (4%bv : bv 5) (w64 (as_tp B)) M4
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 4 4%bv eq_refl), T4, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (19%bv : bv 5) (w64 pin) M19
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 19 19%bv eq_refl), T19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (20%bv : bv 5) (w64 mm) M20
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 20 20%bv eq_refl), T20, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (21%bv : bv 5) (Z_to_bv 64 (F + 32)) M21
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 21 21%bv eq_refl), T21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) M24
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 24 24%bv eq_refl), T24, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (22%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) M22
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 22 22%bv eq_refl), T22, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (18%bv : bv 5) (Z_to_bv 64 F) M18
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 18 18%bv eq_refl), T18, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (23%bv : bv 5) (Z_to_bv 64 F) M23
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 23 23%bv eq_refl), T23, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (8%bv : bv 5) (w64 (spZ regs)) M8
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 8 8%bv eq_refl), T8b, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (25%bv : bv 5) (YK11.getr regs2 25) M25
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 25 25%bv eq_refl), T25, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (26%bv : bv 5) (YK11.getr regs2 26) M26
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 26 26%bv eq_refl), T26, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (27%bv : bv 5) (YK11.getr regs2 27) M27
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 27 27%bv eq_refl), T27, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
lazymatch type of HS with st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  assert (HR0 : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
    by (apply (ucc_region_nth Ex ssx (restrict Hh msx) 0 r0 HS); vm_compute; reflexivity)
end.
cbn [ms_mem restrict] in HR0.
(* The three shadow bytes of the 20-byte local: 0, 0 and 4, so the local is exactly addressable. *)
assert (L0 : le_byte 0 1 0 = 0) by reflexivity.
assert (L4 : le_byte 4 1 0 = 4) by reflexivity.
assert (VS4 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (SHADOW_OFF + F / 8 + 4) 1 0).
{ apply (ucc_field_of_region (cc_E (ms_regs ms3)) _ 22 (SHADOW_OFF + F / 8) _ 0 12 0 12 4 1%N (SLit 0) 0 HR0 U22');
  [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia]. }
assert (VS5 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (SHADOW_OFF + F / 8 + 5) 1 0).
{ apply (ucc_field_of_region (cc_E (ms_regs ms3)) _ 22 (SHADOW_OFF + F / 8) _ 0 12 0 12 5 1%N (SLit 0) 0 HR0 U22');
  [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia]. }
assert (VS6 : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (SHADOW_OFF + F / 8 + 6) 1 4).
{ apply (ucc_field_of_region (cc_E (ms_regs ms3)) _ 22 (SHADOW_OFF + F / 8) _ 0 12 0 12 6 1%N (SOff 10 0) 4 HR0 U22');
  [cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite (cc_ew_reg (ms_regs ms3) 10 10%bv eq_refl), T10; unfold w64;
    rewrite (unsigned_lit_small 4 ltac:(lia)), Z.add_0_r; reflexivity
  | cbn; lia | cbn; lia]. }
pose proof (ucc_aview_of_val1 _ _ _ _ _ VS4) as AS4. rewrite L0 in AS4.
pose proof (ucc_aview_of_val1 _ _ _ _ _ VS5) as AS5. rewrite L0 in AS5.
pose proof (ucc_aview_of_val1 _ _ _ _ _ VS6) as AS6. rewrite L4 in AS6.
(* geometry: the frame is eight-aligned, so the local's granules are the shadow bytes 4, 5 and 6 *)
assert (HF8 : F mod 8 = 0)
  by (pose proof (Z.div_mod F 32 ltac:(lia)) as D32; replace F with (F / 32 * 4 * 8) by lia; apply Z_mod_mult).
assert (Hdiv : forall d, (F + d) / 8 = F / 8 + d / 8).
{ intros d. replace (F + d) with (F / 8 * 8 + d) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
  apply Z.div_add_l. lia. }
assert (Hmod : forall d, (F + d) mod 8 = d mod 8)
  by (intros d; rewrite Zplus_mod, HF8, Z.add_0_l, Z.mod_mod by lia; reflexivity).
assert (HRAd : range_addressable (aview segs (w_H W) (ms_mem ms4)) SHADOW_OFF (F + 32) 20).
{ intros x Hx. unfold shadow_of_addr, saddr_ok.
  assert (Hd : 32 <= x - F < 52) by lia.
  assert (Emod : x mod 8 = (x - F) mod 8) by (replace x with (F + (x - F)) at 1 by lia; apply Hmod).
  assert (Ediv : forall q, (x - F) / 8 = q -> x / 8 = F / 8 + q).
  { intros q Hq. replace x with (F + (x - F)) at 1 by lia. rewrite Hdiv, Hq. reflexivity. }
  destruct (Z.ltb_spec (x - F) 40) as [Hlt|Hge].
  - exists 0. rewrite (Ediv 4 ltac:(symmetry; apply Z.div_unique_pos with (r := x - F - 32); lia)).
    split; [rewrite Z.add_assoc; exact AS4 | left; reflexivity].
  - destruct (Z.ltb_spec (x - F) 48) as [Hlt2|Hge2].
    + exists 0. rewrite (Ediv 5 ltac:(symmetry; apply Z.div_unique_pos with (r := x - F - 40); lia)).
      split; [rewrite Z.add_assoc; exact AS5 | left; reflexivity].
    + exists 4. rewrite (Ediv 6 ltac:(symmetry; apply Z.div_unique_pos with (r := x - F - 48); lia)).
      split; [rewrite Z.add_assoc; exact AS6 | right].
      rewrite Emod.
      assert (Em2 : (x - F) mod 8 = x - F - 48).
      { pose proof (Z.div_mod (x - F) 8 ltac:(lia)) as Dm.
        assert (Hq : 6 = (x - F) / 8) by (apply Z.div_unique_pos with (r := x - F - 48); lia).
        rewrite <- Hq in Dm. lia. }
      rewrite Em2. lia. }
(* The hull of the local's shadow lies inside the frame's own sixteen shadow bytes. *)
pose proof (proj1 HJ2) as HAR4.
destruct (al_frames _ _ LAWS _ _ _ _ _ CC_CID pos HAR4 Hin2) as (_ & _ & HFb4 & HFsh4).
change (fs_frame_bytes CC_CID / 8) with 16 in HFsh4.
change (fs_frame_bytes CC_CID) with 128 in HFb4.
assert (HSHm : (SHADOW_OFF + F / 8 + 4) mod 8 <= 4).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D32.
  assert (EF8 : F / 8 = F / 32 * 4)
    by (replace F with (F / 32 * 4 * 8) at 1 by lia; apply Z.div_mul; lia).
  rewrite EF8. pose proof (Z.div_mod (F / 32) 2 ltac:(lia)) as Dq.
  pose proof (Z.mod_pos_bound (F / 32) 2 ltac:(lia)) as Mq.
  assert (HH : F / 32 mod 2 = 0 \/ F / 32 mod 2 = 1) by lia.
  unfold SHADOW_OFF. destruct HH as [H0|H0].
  - replace (2147450880 + F / 32 * 4 + 4) with (4 + (268431360 + F / 32 / 2) * 8) by lia.
    rewrite Z.mod_add by lia. lia.
  - replace (2147450880 + F / 32 * 4 + 4) with ((268431361 + F / 32 / 2) * 8) by lia.
    rewrite Z_mod_mult. lia. }
assert (E32d : (F + 32) / 8 = F / 8 + 4) by (rewrite Hdiv; reflexivity).
assert (E51d : (F + 51) / 8 = F / 8 + 6) by (rewrite Hdiv; reflexivity).
assert (HHULLd : shadow_hull_vis (aview segs (w_H W) (ms_mem ms4)) (F + 32) 20).
{ intros s Hs. unfold shadow_addr in Hs.
  replace (F + 32 + 20 - 1) with (F + 51) in Hs by lia.
  rewrite E32d, E51d, !Z.add_assoc in Hs.
  pose proof (Z.div_mod (SHADOW_OFF + F / 8 + 4) 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod (SHADOW_OFF + F / 8 + 6) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + F / 8 + 6) 8 ltac:(lia)) as M2b.
  apply ucc_aview_vis.
  replace s with (shadow_addr F + (s - shadow_addr F)) by (rewrite ESH; lia).
  exact (proj1 (HFsh4 (s - shadow_addr F) ltac:(rewrite ESH; lia))). }
(* The source: the caller's twenty bytes are untouched, and the machine stack's shadow is zero. *)
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop0 & Eslo0 & Eshi0 & _).
assert (HRHS : PHC.RP_HOT_SIZE = 20) by reflexivity.
rewrite HRHS in Hpin2, HRA, HHULL.
assert (Hsp4 : spZ (ms_regs ms4) = sp1)
  by (unfold spZ; rewrite M2; apply unsigned_lit_small; lia).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
assert (Hkeep : forall a, spZ regs <= a < 2 ^ 64 ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) memc a)
  by (intros a Ha; apply K1; unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia).
assert (Hlen20 : length (uci_hot_bytes p) = 20%nat)
  by (unfold uci_hot_bytes; rewrite length_map; reflexivity).
assert (Hgarr4 : garr8 segs (mrestrict (w_H W) (ms_mem ms4)) pin (uci_hot_bytes p)).
{ eapply garr8_frame; [exact Hgarr|]. intros a Ha. rewrite Hlen20 in Ha.
  apply ucc_mbyte_of_aview. apply Hkeep. lia. }
assert (Hsrc : src_ok segs W (ms_regs ms4) (ms_mem ms4) pin 20).
{ intros a Ha. split.
  - destruct (Hgarr4 (Z.to_nat (a - pin)) ltac:(rewrite Hlen20; lia)) as (HV & _).
    rewrite Z2Nat.id in HV by lia. replace (pin + (a - pin)) with a in HV by lia.
    rewrite (ucc_aview_of_val1 _ _ _ _ _ HV). discriminate.
  - rewrite Hsp4. unfold CC_STK, CC_FRAME, CC_ALIGN, ESTACK in *. lia. }
pose proof (ucc_stack_addressable segs B lyc S2 W (ms_mem ms4) _ pin 20 HAR4
  ltac:(unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia) ltac:(lia) ltac:(lia)) as HRAs.
pose proof (ucc_stack_hull segs B lyc S2 W (ms_mem ms4) _ pin 20 HAR4
  ltac:(unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia) ltac:(lia) ltac:(lia)) as HHULLs.
(* +0x114: the twenty-byte copy of the caller's record into the local. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (uci_sigma US___asan_memcpy)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (aj_intrin_at segs B LAWS uci_segs_low OCpy (uci_sigma US___asan_memcpy) (AI0 fx)
    W (ms_regs ms4) (ms_mem ms4) CC_STK (spZ regs) (@nil (Z * Z)) lyc Sc W memc mdc
    [(CC_CID, pos)] lyc S2 _ 0 (F + 32) pin 20 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 1720)) HJ2).
  - exact M10.
  - exact M11.
  - exact M12.
  - lia.
  - lia.
  - lia.
  - rewrite Hsp4. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, CC_STK, CC_FRAME, CC_ALIGN. lia.
  - exact M3.
  - exact M4.
  - exact M1.
  - apply (ret_ok_codeptr_v (PI := PI_uci)); [lia | reflexivity].
  - intros a Ha. split.
    + right; right; right. exists CC_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CC_CID) with 128.
      unfold CC_STK, CC_FRAME, CC_ALIGN in *. lia.
    + unfold ESTACK, alloc_ceiling in *. unfold CC_STK, CC_FRAME, CC_ALIGN in *. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
    destruct HFapp as (Hap1 & [HL | [HH1 HH2]]).
    + left. unfold kLowShadowBeg in HL. lia.
    + right. unfold kHighMemBeg in HH1. unfold ASAN_CEIL, alloc_ceiling in HH2. lia.
  - exact HRAd.
  - intros _. exact HHULLd.
  - split; [lia|]. split; [unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia|].
    split; [exact Hsrc|].
    split; [left; unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *; lia|].
    split.
    + right. split; [unfold kHighMemBeg, alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *; lia
                    | unfold kHighMemEnd in *; lia].
    + split; [exact HRAs | intros _; exact HHULLs]. }
cbv beta.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Hcopy & Hframe5 & Hpres5).
(* +0x118 .. +0x120: the two argument moves and `jal rp_hot_clamp`. *)
assert (N2 : YK11.getr regs5 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms4) 2); [exact (HP5 2 ltac:(unfold acallee_saved; lia)) | exact M2]).
assert (N3 : YK11.getr regs5 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms4) 3); [exact (HP5 3 ltac:(unfold acallee_saved; lia)) | exact M3]).
assert (N4 : YK11.getr regs5 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms4) 4); [exact (HP5 4 ltac:(unfold acallee_saved; lia)) | exact M4]).
assert (N19 : YK11.getr regs5 19 = w64 pin)
  by (transitivity (YK11.getr (ms_regs ms4) 19); [exact (HP5 19 ltac:(unfold acallee_saved; lia)) | exact M19]).
assert (N20 : YK11.getr regs5 20 = w64 mm)
  by (transitivity (YK11.getr (ms_regs ms4) 20); [exact (HP5 20 ltac:(unfold acallee_saved; lia)) | exact M20]).
assert (N21 : YK11.getr regs5 21 = Z_to_bv 64 (F + 32))
  by (transitivity (YK11.getr (ms_regs ms4) 21); [exact (HP5 21 ltac:(unfold acallee_saved; lia)) | exact M21]).
assert (N22 : YK11.getr regs5 22 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (transitivity (YK11.getr (ms_regs ms4) 22); [exact (HP5 22 ltac:(unfold acallee_saved; lia)) | exact M22]).
assert (N24 : YK11.getr regs5 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms4) 24); [exact (HP5 24 ltac:(unfold acallee_saved; lia)) | exact M24]).
assert (N18 : YK11.getr regs5 18 = Z_to_bv 64 F)
  by (transitivity (YK11.getr (ms_regs ms4) 18); [exact (HP5 18 ltac:(unfold acallee_saved; lia)) | exact M18]).
assert (N23 : YK11.getr regs5 23 = Z_to_bv 64 F)
  by (transitivity (YK11.getr (ms_regs ms4) 23); [exact (HP5 23 ltac:(unfold acallee_saved; lia)) | exact M23]).
assert (N8 : YK11.getr regs5 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms4) 8); [exact (HP5 8 ltac:(unfold acallee_saved; lia)) | exact M8]).
assert (N25 : YK11.getr regs5 25 = YK11.getr regs2 25)
  by (transitivity (YK11.getr (ms_regs ms4) 25); [exact (HP5 25 ltac:(unfold acallee_saved; lia)) | exact M25]).
assert (N26 : YK11.getr regs5 26 = YK11.getr regs2 26)
  by (transitivity (YK11.getr (ms_regs ms4) 26); [exact (HP5 26 ltac:(unfold acallee_saved; lia)) | exact M26]).
assert (N27 : YK11.getr regs5 27 = YK11.getr regs2 27)
  by (transitivity (YK11.getr (ms_regs ms4) 27); [exact (HP5 27 ltac:(unfold acallee_saved; lia)) | exact M27]).
pose proof (cc_entry4 W regs5 mem5) as HS6.
clear HS. rename HS6 into HS.
assert (HEI6 : img_env VAL A_LIM (cc_E regs5)) by apply cc_env_img.
clear HEI. rename HEI6 into HEI.
assert (SHOK6 : sh_ok segs (SOff 24 0) (@nil shent) (cc_E regs5) (mrestrict (w_H W) mem5)) by constructor.
clear SHOK. rename SHOK6 into SHOK.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs5 (Z_to_bv 64 (BASE + CC_C3)) mem5
    (YK11.seg_rom segs)) md5) Q) end.
paj_run_tok RUN HS HJ5 SHOK CC_B0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_nil. }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => set (ms6 := msx) in * end.
cc_reg HS (10%bv : bv 5) (Z_to_bv 64 (F + 32)) P10
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 21 21%bv eq_refl), N21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (11%bv : bv 5) (w64 mm) P11
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 20 20%bv eq_refl), N20, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 1732)) P1 ltac:(apply codeptr_val; exact HEI).
cc_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) P2
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 2 2%bv eq_refl), N2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 3 3%bv eq_refl), N3, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 4 4%bv eq_refl), N4, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (19%bv : bv 5) (w64 pin) P19
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 19 19%bv eq_refl), N19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (20%bv : bv 5) (w64 mm) P20
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 20 20%bv eq_refl), N20, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (21%bv : bv 5) (Z_to_bv 64 (F + 32)) P21
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 21 21%bv eq_refl), N21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) P24
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 24 24%bv eq_refl), N24, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (18%bv : bv 5) (Z_to_bv 64 F) P18
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 18 18%bv eq_refl), N18, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (23%bv : bv 5) (Z_to_bv 64 F) P23
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 23 23%bv eq_refl), N23, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (22%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) P22
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 22 22%bv eq_refl), N22, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (8%bv : bv 5) (w64 (spZ regs)) P8
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 8 8%bv eq_refl), N8, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (25%bv : bv 5) (YK11.getr regs2 25) P25
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 25 25%bv eq_refl), N25, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (26%bv : bv 5) (YK11.getr regs2 26) P26
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 26 26%bv eq_refl), N26, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (27%bv : bv 5) (YK11.getr regs2 27) P27
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 27 27%bv eq_refl), N27, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
(* The leaf's premises at the call. *)
pose proof (proj1 HJ5) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ CC_CID pos HAR6 Hin2) as (_ & _ & HFb6 & HFsh6).
change (fs_frame_bytes CC_CID) with 128 in HFb6.
change (fs_frame_bytes CC_CID / 8) with 16 in HFsh6.
assert (Hsame6 : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) mem5 a).
{ match goal with
  | HFx : frame_of ?E ?rs (mrestrict (w_H W) mem5) (mrestrict (w_H W) (ms_mem ms6)) |- _ =>
      exact (ucc_aview_kept_frame E rs (w_H W) mem5 (ms_mem ms6) 0 HFx ltac:(lia)
               ltac:(intros a Ha; unfold in_wrange; intros (r & [] & _)))
  end. }
assert (Hshsafe : forall y, SHADOW_OFF <= y < SHADOW_OFF + 2 ^ 44 ->
  aview segs (w_H W) (ms_mem ms6) y = aview segs (w_H W) (ms_mem ms4) y).
{ intros y Hy. rewrite Hsame6 by (unfold SHADOW_OFF in *; lia).
  apply Hframe5.
  - unfold SHADOW_OFF in *. lia.
  - intros Hc. destruct HFapp as (Hap1 & [HL | [HH1 HH2]]);
    [unfold kLowShadowBeg in HL | unfold kHighMemBeg in HH1]; unfold SHADOW_OFF in *; lia.
  - intros Hc. unfold ESTACK, SHADOW_OFF in *. lia. }
assert (HRAd6 : range_addressable (aview segs (w_H W) (ms_mem ms6)) SHADOW_OFF (F + 32) 20).
{ intros x Hx. destruct (HRAd x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite Hshsafe; [exact Hs|]. unfold shadow_of_addr.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(unfold alloc_ceiling in *; lia)). lia. }
assert (Hgarr6 : garr8 segs (mrestrict (w_H W) (ms_mem ms6)) (F + 32) (uci_hot_bytes p)).
{ intros j Hj. rewrite Hlen20 in Hj.
  destruct (Hgarr4 j ltac:(rewrite Hlen20; lia)) as (HV & HR).
  split; [|exact HR]. apply cc_val1_aview; [exact HR|].
  rewrite Hsame6 by lia. rewrite (Hcopy (Z.of_nat j) ltac:(lia)).
  exact (cc_aview_val1 _ _ _ _ HR HV). }
assert (HlenB : length (cells_bytes (PHC.hot_cells p)) = 20%nat) by reflexivity.
assert (HRW6 : rw_cells rsegs (ms_mem ms6) (F + 32) (PHC.hot_cells p)).
{ split.
  - split; [cbn; repeat split; lia|].
    apply (ucc_leafb_bytes_garr8 W (ms_mem ms6) (F + 32) (cells_bytes (PHC.hot_cells p)));
    [exact Hgarr6 | lia | rewrite HlenB; lia].
  - replace (Z.of_nat (cells_size (PHC.hot_cells p))) with 20 by reflexivity.
    apply (ucc_leafb_wr_at W (ms_mem ms6) (F + 32) 20); [lia | lia |].
    intros i Hi. exact (proj1 (HFb6 (F + 32 + i) ltac:(lia))). }
pose proof (ucc_leafb_asan_cells B HCELLS lyc S2 W (ms_mem ms6) _ HAR6) as HAC6.
assert (HADDR6 : UCells.addressable (ms_mem ms6) (F + 32) 20).
{ apply (ucc_leafb_addressable W (ms_mem ms6) (F + 32) 20 HRAd6);
  [lia | lia | unfold UCells.APPMEM_END, ASAN_CEIL, alloc_ceiling in *; lia |].
  intros i Hi. replace (F + 32 + i) with (F + (32 + i)) by lia.
  exact (ucc_leafb_app_of_in_app F 128 (32 + i) HFapp ltac:(lia)). }
assert (Hsp6 : spZ (ms_regs ms6) = sp1)
  by (unfold spZ; rewrite P2; apply unsigned_lit_small; lia).
cc_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 32)) Q10
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 21 21%bv eq_refl), N21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (Z_to_bv 5 2) (Z_to_bv 64 sp1) Z2
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 2 2%bv eq_refl), N2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
cc_reg HS (Z_to_bv 5 11) (w64 mm) Q11
  ltac:(cbn [sv_denot]; rewrite (cc_ew_reg regs5 20 20%bv eq_refl), N20, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
assert (EA0 : bv_unsigned (YK11.getr (ms_regs ms6) (Z_to_bv 5 10)) = F + 32)
  by (rewrite Q10; apply unsigned_lit_small; lia).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms6) (Z_to_bv 5 2)) = sp1)
  by (rewrite Z2; apply unsigned_lit_small; lia).
assert (EA1 : bv_unsigned (YK11.getr (ms_regs ms6) (Z_to_bv 5 11)) = mm)
  by (rewrite Q11; unfold w64; apply unsigned_lit_small; unfold INT_MAX in *; lia).
(* +0x120: the leaf writes the local in place; its post becomes the caller's journal at the return. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm2 ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (uci_sigma US_rp_hot_clamp)) mm2 rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (ucc_leafb_journal B LAWS W (ms_regs ms6) (ms_mem ms6) CC_STK (spZ regs) (@nil (Z * Z))
    lyc Sc W memc mdc [(CC_CID, pos)] lyc S2 _ 0 (sp1 - spZ regs) (uci_sigma US_rp_hot_clamp) None
    (LHC.uci_rhc_wr (F + 32))
    (fun m2 => rw_cells rsegs m2 (F + 32) (PHC.hot_cells (rp_hot_clamp_m p mm))) HJ5).
  - rewrite Hsp6. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp16. reflexivity.
  - lia.
  - unfold ESTACK, CC_STK, CC_FRAME, CC_ALIGN. lia.
  - rewrite P1. apply (ret_ok_codeptr_v (PI := PI_uci)); [lia | reflexivity].
  - exact P3.
  - exact P4.
  - intros a Ha. unfold LHC.uci_rhc_wr, LCK.in_wr in Ha.
    apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha].
    cbn [fst snd] in Ha. unfold PHC.RP_HOT_SIZE in Ha.
    right; right; right. exists CC_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CC_CID) with 128.
    unfold CC_STK, CC_FRAME, CC_ALIGN in *. lia.
  - intros HPRE.
    pose proof (LEAF0 fx) as LF.
    unfold uci_leaf_wr_at, LHC.uci_rp_hot_clamp_cg in LF.
    specialize (LF lyc S2 W (ms_regs ms6) (ms_mem ms6) _ p mm (sp1 - 16) HPRE). cbv zeta in LF.
    rewrite EA0, ESP in LF. unfold AHC.RP_HOT_CLAMP_FRAME in LF.
    apply LF; clear LF.
    + exact Hint.
    + exact Hmm.
    + exact EA1.
    + exact HRW6.
    + eapply (ucc_leafb_stk_journal B); [exact HJ5 | unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia | lia].
    + lia.
    + unfold AKA.off_stk. rewrite ESP. left. unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *. lia.
    + apply (@ucc_leafb_app_stack rc). unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *. lia.
    + apply (@ucc_leafb_app_stack rc). unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *. lia.
    + exact HAC6.
    + unfold AKA.off_stk. rewrite ESP. left. unfold UCells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite ESP. left. unfold UCells.CELL_K. lia.
    + exact HADDR6.
    + eapply (ucc_leafb_rng_journal B); [exact HJ5 | unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia | lia].
    + exact (proj1 (ucc_leafb_rng_cells W)).
    + exact (proj2 (ucc_leafb_rng_cells W)).
    + apply (ucc_leafb_rng_vis W (ms_mem ms6)); [lia | lia |].
      intros a Ha. exact (proj1 (HFb6 a ltac:(lia))).
    + apply (ucc_leafb_rng_shadow W (ms_mem ms6) (F + 32) 20 HRAd6); [lia | lia | lia].
    + intros x Hx. unfold LHC.uci_rhc_wr, LCK.in_wr in Hx.
      apply Exists_cons in Hx. destruct Hx as [Hx | Hx]; [|inversion Hx].
      cbn [fst snd] in Hx. unfold PHC.RP_HOT_SIZE in Hx. split.
      * exact (proj2 (HFb6 x ltac:(lia))).
      * assert (HxF : F <= x < F + 128) by lia.
        exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ x HAR6
          (or_intror (or_introl (ex_intro _ CC_CID (ex_intro _ pos (conj Hin2 HxF))))))). }
cbv beta.
intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & HP7 & _ & Heff7 & Hpres7 & HRW7).
(* +0x124: the five comparisons, from their cut statement. *)
pose proof (proj1 HJ7) as HAR7.
destruct (al_frames _ _ LAWS _ _ _ _ _ CC_CID pos HAR7 Hin2) as (_ & _ & HFb7 & HFsh7).
change (fs_frame_bytes CC_CID) with 128 in HFb7.
change (fs_frame_bytes CC_CID / 8) with 16 in HFsh7.
assert (Q19' : YK11.getr regs7 19 = w64 pin)
  by (transitivity (YK11.getr (ms_regs ms6) 19); [exact (HP7 19 ltac:(unfold acallee_saved; lia)) | exact P19]).
assert (Q20' : YK11.getr regs7 20 = w64 mm)
  by (transitivity (YK11.getr (ms_regs ms6) 20); [exact (HP7 20 ltac:(unfold acallee_saved; lia)) | exact P20]).
assert (Q21' : YK11.getr regs7 21 = Z_to_bv 64 (F + 32))
  by (transitivity (YK11.getr (ms_regs ms6) 21); [exact (HP7 21 ltac:(unfold acallee_saved; lia)) | exact P21]).
assert (Q24' : YK11.getr regs7 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms6) 24); [exact (HP7 24 ltac:(unfold acallee_saved; lia)) | exact P24]).
rewrite P1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm2 ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CC_CMP)) mm2 rom) mdx) Q) end.
eapply (CMP W regs7 mem7 md7 _ lyc Sc memc mdc S2 (spZ regs) pos pin F mm p HJ7
  Q19' Q20' Q21' Q24' ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold alloc_ceiling in *; lia)
  ltac:(unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *; lia) Hint Hmm).
(* the caller's record, unchanged since the copy read it *)
- assert (Hpin7 : forall a, pin <= a < pin + 20 ->
    aview segs (w_H W) mem7 a = aview segs (w_H W) (ms_mem ms4) a).
  { intros a Ha.
    rewrite (Heff7 a ltac:(lia)
      ltac:(rewrite Hsp6; intros Hc; unfold ESTACK, CC_STK, CC_FRAME, CC_ALIGN in *; lia)
      ltac:(intros Hc; unfold LHC.uci_rhc_wr, LCK.in_wr in Hc; apply Exists_cons in Hc;
            destruct Hc as [Hc | Hc]; [cbn [fst snd] in Hc; unfold PHC.RP_HOT_SIZE in Hc;
              unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *; lia | inversion Hc])).
    rewrite Hsame6 by lia. apply Hframe5.
    - lia.
    - intros Hc. unfold alloc_ceiling, CC_STK, CC_FRAME, CC_ALIGN in *. lia.
    - intros Hc. unfold ESTACK, CC_STK, CC_FRAME, CC_ALIGN in *. lia. }
  assert (Hgarr7 : garr8 segs (mrestrict (w_H W) mem7) pin (uci_hot_bytes p)).
  { eapply garr8_frame; [exact Hgarr4|]. intros a Ha. rewrite Hlen20 in Ha.
    apply ucc_mbyte_of_aview. apply Hpin7. lia. }
  apply cc_cells_at_restrict.
  + split; [cbn; repeat split; lia|].
    apply (ucc_leafb_bytes_garr8 W mem7 pin (cells_bytes (PHC.hot_cells p)));
    [exact Hgarr7 | lia | rewrite HlenB; lia].
  + intros i Hi. rewrite HlenB in Hi.
    exact (ucc_leafb_mbyte_vis W mem7 (pin + Z.of_nat i) _
      (garr8_mbyte segs (mrestrict (w_H W) mem7) pin (uci_hot_bytes p) i Hgarr7
        ltac:(rewrite Hlen20; lia))).
(* the local copy, as the leaf left it *)
- apply cc_cells_at_restrict; [exact (proj1 HRW7)|].
  assert (HlenC : length (cells_bytes (PHC.hot_cells (rp_hot_clamp_m p mm))) = 20%nat) by reflexivity.
  intros i Hi. rewrite HlenC in Hi.
  exact (proj1 (proj1 (HFb7 (F + 32 + Z.of_nat i) ltac:(lia)))).
(* the caller's record is on the machine stack, whose shadow is zero *)
- exact (ucc_stack_addressable segs B lyc S2 W mem7 _ pin 20 HAR7
    ltac:(unfold CC_STK, CC_FRAME, CC_ALIGN in *; lia) ltac:(lia) ltac:(lia)).
(* +0x244: the frame given back, the reloads and the `ret`, from their cut statement. *)
- intros regs8 mat8 HP8.
  (* the registers at +0x244: the comparisons keep the callee-saved ones *)
  assert (V : forall r, acallee_saved r ->
    YK11.getr regs8 (Z_to_bv 5 r) = YK11.getr (ms_regs ms6) (Z_to_bv 5 r)).
  { intros r Hr. transitivity (YK11.getr regs7 (Z_to_bv 5 r)); [exact (HP8 r Hr) | exact (HP7 r Hr)]. }
  assert (V2 : YK11.getr regs8 2 = Z_to_bv 64 sp1) by exact (eq_trans (V 2 ltac:(hnf; lia)) P2).
  assert (V8 : YK11.getr regs8 8 = w64 (spZ regs)) by exact (eq_trans (V 8 ltac:(hnf; lia)) P8).
  assert (V18 : YK11.getr regs8 18 = Z_to_bv 64 F) by exact (eq_trans (V 18 ltac:(hnf; lia)) P18).
  assert (V22 : YK11.getr regs8 22 = Z_to_bv 64 (SHADOW_OFF + F / 8))
    by exact (eq_trans (V 22 ltac:(hnf; lia)) P22).
  assert (V23 : YK11.getr regs8 23 = Z_to_bv 64 F) by exact (eq_trans (V 23 ltac:(hnf; lia)) P23).
  assert (V3 : YK11.getr regs8 3 = YK11.getr regs 3)
    by exact (eq_trans (eq_trans (V 3 ltac:(hnf; lia)) P3) (eq_sym Hgp)).
  assert (V4 : YK11.getr regs8 4 = YK11.getr regs 4)
    by exact (eq_trans (eq_trans (V 4 ltac:(hnf; lia)) P4) (eq_sym Htp)).
  assert (V25 : YK11.getr regs8 25 = YK11.getr regs 25)
    by exact (eq_trans (eq_trans (V 25 ltac:(hnf; lia)) P25) (eq_trans (HP2 25 ltac:(hnf; lia)) R25)).
  assert (V26 : YK11.getr regs8 26 = YK11.getr regs 26)
    by exact (eq_trans (eq_trans (V 26 ltac:(hnf; lia)) P26) (eq_trans (HP2 26 ltac:(hnf; lia)) R26)).
  assert (V27 : YK11.getr regs8 27 = YK11.getr regs 27)
    by exact (eq_trans (eq_trans (V 27 ltac:(hnf; lia)) P27) (eq_trans (HP2 27 ltac:(hnf; lia)) R27)).
  (* the ten saved words and the flag word, carried from the class-1 call to +0x244: the two runs, the copy
     and the leaf each write elsewhere *)
  assert (K7 : forall a, spZ regs - 80 <= a < spZ regs \/ F + 120 <= a < F + 128 ->
    aview segs (w_H W) mem7 a = aview segs (w_H W) mem2 a).
  { intros a Ha.
    destruct (cc_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp Ha) as (G0 & _ & _ & _ & G4 & G5).
    rewrite (Heff7 a G0 ltac:(rewrite Hsp6; exact G5)
      ltac:(intros Hc; unfold LHC.uci_rhc_wr, LCK.in_wr in Hc; apply Exists_cons in Hc;
            destruct Hc as [Hc | Hc];
            [cbn [fst snd] in Hc; unfold PHC.RP_HOT_SIZE in Hc; apply G4; clear - Hc; lia | inversion Hc])).
    rewrite (Hsame6 a G0).
    rewrite (Hframe5 a G0 G4 ltac:(intros Hc; apply G5; clear - Hc; unfold ESTACK in Hc; lia)).
    rewrite (KB a Ha). exact (KA a Ha). }
  assert (HSV7 : forall (o : Z) (r : bv 5), In (o, r) cc_saved ->
    rdword (aview segs (w_H W) mem7) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
  { intros o r Hin. pose proof (HSVo o r Hin) as Ho.
    rewrite <- (HSV2 o r Hin). apply cc_rdword_frame.
    intros i Hi. apply K7. left. clear - Ho Hi. lia. }
  assert (HFW : Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem7) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o)))))
    [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24)]).
  { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
      replace (spZ regs - o) with (spZ regs + - o) by ring;
      apply (HSV7 (- o) (Z_to_bv 5 r)); unfold cc_saved; cbn [In];
      repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
  assert (HFL7 : rdword (aview segs (w_H W) mem7) (F + 120) = Some (flag_addr lyc CC_CID pos)).
  { replace (F + 120) with (F + 128 - 8) by ring. rewrite <- Hflag. apply cc_rdword_frame.
    intros i Hi. apply K7. right. clear - Hi. lia. }
  (* the fake frame changed the allocator state's st_fs only *)
  assert (HMO : mo_le MT Sc S2 0).
  { destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
  assert (HJ8 : @ajournal rc tfib_sink_head segs B CC_STK (spZ regs) [] lyc Sc W memc mdc [(CC_CID, pos)] lyc S2
      W mem7 (with_vm_backing (m_vm_lazy md7) mat8 md7) 0).
  { eapply ajournal_materialize; first [exact HJ7 | exact LAWS | exact uci_segs_low]. }
  exact (REL ASF FFL MTL MTF STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs8 mem7
    (with_vm_backing (m_vm_lazy md7) mat8 md7) S2 pos sp1 F HJ0 HJ8 Hfrs2 Eab2 Hnev2 eq_refl
    V2 V8 V18 V22 V23 V3 V4 V25 V26 V27 Hra HFW HFL7 HMO Hsp16 Hsp1al Gsp1 Hlo Hhi GF0 HFal
    ltac:(lia) HCELLS LAWS Hcnt).
Qed.

(* The contract at US_check_clamp: the walk above with the five comparisons of lib/A/Prog/UciCcCmp.v and the
   release piece of lib/A/Prog/UciCcRel.v. *)
Theorem uci_check_clamp_cg_holds : @uci_check_clamp_cg_holds_stmt fx rc B MT.
Proof. exact (cc_holds_of (@cc_cmp fx rc B) (@cc_rel fx rc B MT)). Qed.

End cc.
