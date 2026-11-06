(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 299 of its 411 lines of code are new or changed and 1027 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_entry: Lemma lc_entry_ok : lc_entry_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment ENTRY of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput (transport_text = 0x81264,
   AF_LLVMFuzzerTestOneInput = 0 of lib/A/Prog/DgnTransportList.v), from the slot's pre to the cut SM (+0x074, the
   return of __asan_stack_malloc_2).

   The walk holds the slot's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 [] from the entry: ajournal_gx_init
   at the slot's afn_pre). One position-abstract run (lib/A/Prog/TransportGRunA.v paj_run_x) covers the 28 slots
   +0x000 .. +0x06c:
     +0x000 `addi sp, sp, -320`, +0x004 `sd zero, 0(sp)`, +0x008 .. +0x038 the 13 saves of ra, s0 .. s11 at the entry
            sp - 8 .. - 104; +0x03c `addi s0, sp, 320` (s0 = the entry sp); +0x040 `andi sp, sp, -32` and +0x044
            `mv s1, sp` (sp1 = 32 * ((sp0 - 320) / 32));
     +0x048 `mv s5, a1` (n), +0x064 `mv s3, a0` (p);
     +0x04c .. +0x060 the GOT words of objects 0 and 1 (transport_cells rows 7 and 2), the 4-byte flag cell (object 94,
            row 6: it holds 1) and the shadow-base cell (object 93, row 1) they point at, the last into s10;
     +0x068 `beqz a2`: the flag word is 1, so the run does not branch (the real-stack arm +0x078 is not reached);
     +0x06c `li a0, 256`.
   At +0x070 the `jal __asan_stack_malloc_2` is the statement's class-2 astack_malloc_realizes premise (lp_smalloc) at
   the pc lp_pc_smalloc names, composed into the G journal by lib/A/Prog/TransportGFrame.v gx_stack_malloc_at. The
   frame position it picks is the existential of the post. What the cut SM states of memory comes from the run's
   frame_of (the run writes only the 320 bytes below the entry sp) and the call's acall_kept: the saved words, the
   bytes of G (TransportGCg.v gx_kept_of_acall_kept) and the input bytes (a heap block, kept by acall_kept's block
   clause). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition LCE_B0 : Z * Z := (0, 0).

(* The run +0x000 .. +0x06c: the 320 bytes below the entry sp (atom 2) that the prologue writes, the GOT word of
   object 1 and the shadow-base cell (object 93) it points at, whose value is atom 32 (the shadow base), and the GOT
   word of object 0 and the 4-byte flag cell (object 94) it points at, which holds 1. *)
Definition lce_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 94) 0))].
Definition lce_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition lce_img_regions : smem := [got_regionP; bcell_regionP 32; lce_got_uar; lce_uar_cell].
Definition lce_regions : smem := stack_region LF_FRAME :: lce_img_regions.
Definition lce_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_lce : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms lce_regions None lce_facts.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma lce_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_LLVMFuzzerTestOneInput = A_LLVMF /\ BASE + 116 = transport_text + LO_SM.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma lce_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) lce_img_regions /\
  pairwise_disjoint E lce_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct lce_vals as (V1 & V93 & V0 & V94 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 94) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold lce_img_regions, got_regionP, bcell_regionP, lce_got_uar, lce_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 94) 0) (VAL (A_OBJ 94)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 94)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold lce_img_regions, got_regionP, bcell_regionP, lce_got_uar, lce_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation at the entry: the 32 registers and the shadow base (atom 32). *)
Definition lce_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

Lemma lce_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lce_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold lce_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lce_ew_32 : forall regs, ew (lce_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold lce_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma lce_ew_obj : forall regs i, (i < 95)%nat -> ew (lce_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold lce_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma lce_env_img : forall regs, img_env VAL A_LIM (lce_E regs).
Proof. intros regs. unfold lce_E. apply Eimg_env. Qed.

(* The entry state of the run (the saves go into the stack region). *)
Lemma lce_entry : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - LF_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (lce_E regs) ss_lce
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_lce, lce_regions.
  assert (Usp : bv_unsigned (ew (lce_E regs) 2) = spZ regs)
    by (rewrite (lce_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (lce_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply lce_ew_32.
  destruct (lce_img_ok ly S W mem md (lce_E regs) HCELLS HAR
    (lce_ew_obj regs 1 ltac:(lia)) (lce_ew_obj regs 93 ltac:(lia))
    (lce_ew_obj regs 0 ltac:(lia)) (lce_ew_obj regs 94 ltac:(lia)) E32) as [HRs HPd].
  destruct lce_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (lce_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (lce_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold LF_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold lce_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, lce_got_uar, lce_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (lce_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (lce_ew_obj regs 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (lce_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (lce_ew_obj regs 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, LF_FRAME.
    repeat split; first [exact I | lia].
  - unfold lce_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.
End h.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac lce_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac lce_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac lce_u64 x := let Hrg := fresh "Hrg" in pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
(* The awr obligation's regions, computed. *)
Ltac lce_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* Name the machine state of HS. *)
Ltac lce_name HS x :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.
(* One saved word of lc_saved, read back from the stack region HR the run wrote (the chunk at - off holds atom r,
   the entry value of register r). *)
Ltac lce_saved_one HR Usp :=
  lazymatch goal with
  | |- rdword (aview _ ?H ?m) (spZ ?rg - ?off) = Some (bv_unsigned (YK11.getr ?rg (Z_to_bv 5 ?r))) =>
    let rn := eval vm_compute in (Z.to_nat r) in
    apply (AF0x.val_mem_rdword H m (spZ rg - off) (bv_unsigned (YK11.getr rg (Z_to_bv 5 r)))
      ltac:(lce_u64 (YK11.getr rg (Z_to_bv 5 r))));
    replace (spZ rg - off) with (spZ rg + (- off)) by lia;
    apply (can_field_of_region (lce_E rg) _ 2 (spZ rg) _ (-320) 0 (-320) 0 (- off) 8%N (SOff rn 0)
      (bv_unsigned (YK11.getr rg (Z_to_bv 5 r))) HR Usp);
    [ repeat (first [left; reflexivity | right])
    | cbn [sv_denot]; rewrite (lce_ew_reg rg rn (Z_to_bv 5 r) eq_refl); rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      reflexivity
    | change (2 ^ (8 * Z.of_N 8%N)) with (2 ^ 64); lce_u64 (YK11.getr rg (Z_to_bv 5 r))
    | change (Z.of_N 8%N) with 8; lia ]
  end.

Section sg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma lc_entry_ok : @lc_entry_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_entry_stmt.
intros HP fx ly S W regs mem md p n pl M HPRE.
pose proof (lp_pc_smalloc _ _ _ _ _ HP) as HPCS.
pose proof (lp_cells _ _ _ _ _ HP) as HCELLS.
pose proof (lp_g_unowned _ _ _ _ _ HP) as HGU.
pose proof (lp_g_no_errno _ _ _ _ _ HP) as HGN.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (lp_meter_fs_laws _ _ _ _ _ HP) as MTF.
pose proof (lp_smp _ _ _ _ _ HP) as SMP.
pose proof (lp_smalloc _ _ _ _ _ HP fx) as ASM.
pose proof (lp_cost _ _ _ _ _ HP) as HXL.
clear HP.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGN) as HGNE.
destruct HPRE as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta & Hmo).
pose proof HAFN as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : LLVMF_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite Hstkv in Hslo; lia).
(* The file-pointer list of the cut's journal, named from the cut and kept opaque (only HFP relates it to the cut's
   list): nothing here reads it. *)
unfold lc_st_sm.
lazymatch goal with |- context [@W_journalG.ajournal_gx _ _ _ _ _ _ _ _ _ ?FPx _ _ _ _ _ _ _ _ _ _ _ _] =>
  pose (FP := FPx); assert (HFP : FP = FPx) by reflexivity end.
clearbody FP.
(* The slot's G journal from the entry. *)
assert (HJ : @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (spZ regs)
  FP ly S W mem md [] ly S W mem md 0).
{ eapply ajournal_gx_init; [exact HAFN | lia | reflexivity | lia | intros a Ha; lia]. }
assert (Hpres1 : forall a, spZ regs - LF_FRAME <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; unfold LF_FRAME in Ha; rewrite Hstkv; lia).
pose proof (@lce_entry fx rc B ly S W regs mem md HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (lce_E regs)) by apply lce_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lce_E regs) (mrestrict (w_H W) mem)) by constructor.
assert (Usp : bv_unsigned (ew (lce_E regs) 2) = spZ regs)
  by (rewrite (lce_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
destruct lce_vals as (_ & _ & _ & _ & VA & VR).
unfold cfg_at. rewrite <- VA.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem
    (YK11.seg_rom segs)) md) Q) end.
(* +0x000 .. +0x06c: the frame, the saves, s0 / s1, the realign, s5 = n, the GOT and cell loads (s10 = the shadow
   base), s3 = p, the `beqz a2` the flag word decides, `li a0, 256`, up to the `jal __asan_stack_malloc_2`. *)
paj_run_tok RUN HS HJ SHOK LCE_B0.
{ lce_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
lce_name HS ms1.
set (sp1 := 32 * ((spZ regs + -320) / 32)).
destruct (can_sp1_facts (spZ regs + -320) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (E2' : ew (lce_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (lce_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
lce_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 116)) R1 ltac:(apply codeptr_val; exact HEI).
lce_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (lce_E regs) 2 (spZ regs) (-320) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
lce_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (lce_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
lce_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (lce_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
lce_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
lce_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (lce_E regs) 2 (spZ regs) (-320) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
lce_reg HS (19%bv : bv 5) (w64 p) R19
  ltac:(cbn [sv_denot]; rewrite (lce_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
lce_reg HS (21%bv : bv 5) (w64 n) R21
  ltac:(cbn [sv_denot]; rewrite (lce_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
lce_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) R26
  ltac:(cbn [sv_denot]; rewrite (lce_ew_32 regs); reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
lce_region HS 0%nat HRsk.
assert (HSV : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem ms1)) (spZ regs - fst o) =
  Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) LF_SAVED).
{ unfold LF_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lce_saved_one HRsk Usp. }
clear HRsk.
assert (HSVb : Forall (fun o : Z * Z => 8 <= fst o <= 104) LF_SAVED)
  by (unfold LF_SAVED; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
(* +0x070: the class-2 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_2)) mm rom) mdx) Q) end.
rewrite <- HPCS.
assert (Hcnt : count_cid LF_CID (frames S) < fs_frames LF_CID) by (rewrite Hfrs; vm_compute; reflexivity).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP LF_CID ASM
    ltac:(unfold LF_CID; lia) TG.G_HARNESS W rg mm LLVMF_STK (spZ regs) FP ly S W mem md [] ly S mdx 0
    (sp1 - spZ regs) (Z_to_bv 64 (BASE + 116)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp16. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (LF_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds segs B LAWS _ _ _ _ _ LF_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ LF_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes LF_CID) with 256 in HFc, Hz, Hflag, Hfpres.
rewrite Zplus_minus in HK1.
set (memT := ms_mem ms1) in *. set (regsT := ms_regs ms1) in *.
(* The run wrote only the 320 bytes below the entry sp. *)
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 320 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) mem a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 320 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
(* The thirteen saved words, kept by the class-2 call (they lie above sp1). *)
assert (HSV2 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) mem2) (spZ regs - fst o) =
  Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) LF_SAVED).
{ apply Forall_forall. intros o Hin.
  pose proof (proj1 (Forall_forall _ _) HSVb o Hin) as Ho. cbv beta in Ho.
  rewrite <- (proj1 (Forall_forall _ _) HSV o Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
(* The bytes of G: the run writes none, the call keeps them. *)
assert (GK : forall a, W_journalG.inG TG.G_HARNESS a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha.
  rewrite (gx_kept_of_acall_kept segs B TG.G_HARNESS ly S W memT W mem2 _ _ _ HGX HGNE HK1 a Ha).
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
  apply KT; lia. }
(* The input bytes: a heap block of the entry, below alloc_ceiling; the call keeps every block. *)
assert (HIN : forall i, 0 <= i < n -> aview segs (w_H W) mem2 (p + i) = aview segs (w_H W) mem (p + i)).
{ intros i Hi. destruct Hpn as [[Hn0 _] | [_ Hin]]; [lia|].
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpc & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  rewrite (proj1 (proj2 HK1) p n i Hin ltac:(lia) ltac:(intros HH; exact HH)).
  apply KT; lia. }
exists pos.
unfold lc_cfg, lc_saved, lc_sp1, lc_sp0, lc_F, lc_FL, lc_input, lc_meter, LF_CID, LF_FRAME, LF_FBYTES.
cbn [l_fx l_ly l_S l_W l_regs l_mem l_md l_p l_n l_pl l_M l_fpos].
replace (spZ regs - 320) with (spZ regs + -320) by lia. fold sp1.
exists ly, S2, regs2, mem2, md2.
split; [rewrite VR; reflexivity|].
split; [rewrite HFP in HJ2; exact HJ2|].
split; [rewrite Hfrs2, Hfrs; reflexivity|].
split; [reflexivity|].
split; [exact Eab2|].
split; [transitivity (YK11.getr regsT 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]|].
split; [transitivity (YK11.getr regsT 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
split; [transitivity (YK11.getr regsT 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
split; [transitivity (YK11.getr regsT 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
split; [transitivity (YK11.getr regsT 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
split; [exact Ha0|].
split; [transitivity (YK11.getr regsT 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
split; [transitivity (YK11.getr regsT 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
split; [transitivity (YK11.getr regsT 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
split; [lia|].
split; [exact Hsp1al|].
split; [exact HSV2|].
split; [exact HF0|].
split; [exact HF64|].
split; [exact HFc|].
split; [exact Hfpres|].
split; [exact Hflag|].
split; [exact Hz|].
split; [exact GK|].
split.
{ split; [|exact HIN].
  apply (lc_garr8_kept (w_H W) (w_H W) mem mem2 p _); [| exact Hgarr].
  intros j Hj. rewrite length_map, <- Hlen in Hj. apply HIN. lia. }
destruct Hset2 as (f & ES2). rewrite ES2.
split.
- rewrite Z.mul_0_l. apply (mo_le_set_fs_r MT MTF). apply (mo_le_refl MT MTL).
- apply (mo_ok_set_fs MT MTF). apply (mo_ok_le MT MTL S _ (XL n) Hmo).
  rewrite Z.sub_0_r, <- (lf_cost_eq MT n). apply HXL.
  destruct Hpn as [[Hn0 _] | [Hn0 _]]; lia.
Qed.
End sg.
