(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 803 of its 979 lines of code are new or changed and 963 lines of the source are left out. *)
(* set_state_seg_head (image B): Lemma sstb_head : sstb_head_stmt (lib/B/Prog/set_state_segs.v), the head piece of
   the image-B ASan walk of set_state (fuzz_transport.asan-ubsan 0x872cc = transportb_sigma TB_set_state,
   AF_set_state = 0x602c of lib/B/Prog/DgnTransportBList.v), from the entry to the two cuts sstb_ntc_at (+0x154) and
   sstb_rel_at (+0x214). The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []); the
   runs are lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x, the split lib/B/Prog/DgnTransportBPaLib.v
   paj_branch. Image B's form of lib/A/Prog/SlostHead.v (the same class-2 frame), with the image-B prologue and
   alignment check of lib/B/Prog/diginet_session_wake_seg_head.v:
     run 1   +0x000 .. +0x070  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1 (sp1), s2 = why, s3 = st, the flag word through its GOT word (1, so `beqz a2` is not
                               taken), s10 = the shadow base, s4 = s, a0 = 160, up to `jal __asan_stack_malloc_2`;
     +0x074                    the class-2 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x078 .. +0x0dc  `bnez a0` taken (the real-stack arm is not reached), s9 = F, the frame word at s1 + 48,
                               the frame's 24-byte header, s8 = the frame's shadow address, up to the first shadow
                               store;
     run 2b  +0x0e0 .. +0x134  the frame's shadow bytes 0 .. 19 and the UBSan alignment check `andi a1, s4, 7; bnez a1`
                               (s4 = s is 64-aligned: not taken, so the trap word at +0x344 is unreached);
     run 2c  +0x138 .. +0x14c  s6 = s + 112, s11 = its shadow address, the checked 4-byte load of s5 = S_state Bw (the
                               record's zero shadow of g_s: trans_sstate_cells, decode_zshadow_rd);
     +0x150                    `beq s5, s3`, taken up from a state with no region: S_state Bw = st runs one instruction
                               to +0x214 and concludes by sstb_rel_at with a0 = F (the model's world is Bw:
                               sstate_model's first branch); any other state runs one instruction to +0x154 and
                               concludes by sstb_ntc_at.
   The facts the cuts carry are proved once at +0x150 (sstb_cur at that memory, the world relation at Bw, G kept) and
   moved to the cut's memory, whose view is the same (ssh_cur_move). What the call keeps (acall_kept_g) runs from the
   entry to the stack malloc's return (TransportGCg.v dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept)
   and from there over the three written ranges (dk_kept_own_g: the frame's header and shadow bytes, the slot s1 + 48
   in the call's window). The head stores no byte of G. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg set_state_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module YF0x := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YF0x.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition SSH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x070: the stack frame and the four image cells (the shadow-base GOT word and its cell, the
   side-stack flag's GOT word and its cell). *)
Definition ssh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 96) 0))].
Definition ssh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition ssh_img_regions : smem := [got_regionP; bcell_regionP 32; ssh_got_uar; ssh_uar_cell].
Definition ssh_regions1 : smem := stack_region SSTATE_FRAME :: ssh_img_regions.
Definition ssh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ssh1 : sstate := mkSS AF_set_state sr_atoms ssh_regions1 None ssh_facts1.

(* run 2a, +0x078 .. +0x0dc: after the stack malloc, the frame F in a0 (atom 10); the run stores the frame word at
   s1 + 48, writes the frame's 24-byte header and stops at the first shadow store (+0x0e0). *)
Definition SSH_C1 : Z := AF_set_state + 0x78.
Definition SSH_C2 : Z := AF_set_state + 0xe0.
Definition ssh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition ssh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition ssh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ssh2 : sstate := mkSS SSH_C1 sr_atoms [ssh_rg_slot; ssh_rg_hdr] None ssh_facts2.

(* run 2b, +0x0e0 .. +0x134: s8 (atom 24) holds the frame's shadow address; the run writes the frame's 20 shadow bytes
   and decides the alignment check of s4 (atom 20, pinned to SSTATE_S: 64-aligned), up to +0x138. *)
Definition SSH_C3 : Z := AF_set_state + 0x138.
Definition ssh_rg_sh : YP09.region := YP09.mkRegion (Some 24%nat) 0 20 0 20 [].
Definition ssh_facts3 : facts :=
  mkFacts [(20%nat, mkAF SSTATE_S SSTATE_S 6); (24%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_ssh3 : sstate := mkSS SSH_C2 sr_atoms [ssh_rg_sh] None ssh_facts3.

(* run 2c, +0x138 .. +0x14c: the checked 4-byte load of s + 112 (atom 33, the 4 bytes of S_state), up to `beq s5, s3`
   at +0x150. s4 (atom 20) is s, s10 (atom 26) the shadow base. *)
Definition ssh_rg_st : YP09.region :=
  YP09.mkRegion (Some 20%nat) 112 116 0 0 [YP09.mkChunk 112 (YP09.CVal 4 (SOff 33 0))].
Definition ssh_facts4 : facts :=
  mkFacts [(20%nat, mkAF SSTATE_S SSTATE_S 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_ssh4 : sstate := mkSS SSH_C3 sr_atoms [ssh_rg_st] None ssh_facts4.
Definition SSH_SH4 : list shent := [mkSHE 20 112 116].
Definition SSH_Bx : sv := SOff 26 0.

(* +0x150, `beq s5, s3`, taken up from a state with no region. *)
Definition SSH_C4 : Z := AF_set_state + 0x150.
Definition ss_ssh0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* ------------------------------------------------------------------ *)
(* The model                                                           *)
(* ------------------------------------------------------------------ *)

(* g_s's state at its numeral offset (s + 112). *)
Lemma ssh_st_num : forall Bw, TW.S_state Bw = bv_swrap 32 (TW.u_at Bw (TW.OFF_g_s + 112) 4).
Proof.
intros Bw. unfold TW.S_state, TW.s32_at.
replace TW.A_S_state with (TW.OFF_g_s + 112) by reflexivity. reflexivity.
Qed.

(* The state unchanged: the model's world is Bw (sstate_model's first branch). *)
Lemma ssh_model_eq : forall I Fr Bw st why Bw', TW.S_state Bw = st ->
  TSS.set_state_m I Fr Bw st why = Some (Bw', tt) -> Bw' = Bw.
Proof.
intros I Fr Bw st why Bw' Hs Hm. rewrite sstate_model in Hm. rewrite (proj2 (Z.eqb_eq _ _) Hs) in Hm.
symmetry. exact (sstb_some_inv _ _ Hm).
Qed.

(* `beq s5, s3` on the sign-extended state and st: the model's S_state = st test. *)
Lemma ssh_eqb : forall v w, - 2 ^ 31 <= v < 2 ^ 31 -> 0 <= w < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
intros v w Hv Hw. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small w (2 ^ 64)) by lia.
destruct (Z.eqb_spec v w) as [-> | Hne]; [rewrite Z.mod_small by lia; apply Z.eqb_refl|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma ssh_state_range : forall Bw, - 2 ^ 31 <= TW.S_state Bw < 2 ^ 31.
Proof.
intros Bw. pose proof (bv_swrap_in_range 32 (TW.u_at Bw TW.A_S_state 4) ltac:(discriminate)) as R.
change (bv_swrap 32 (TW.u_at Bw TW.A_S_state 4)) with (TW.S_state Bw) in R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* The sign-extended 4-byte load of a field whose bytes are atom 33. *)
Lemma ssh_sext : forall E u, 0 <= u < 2 ^ 32 -> ew E 33 = Z_to_bv 64 u ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E u R H. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ssh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_set_state = transportb_sigma TB_set_state.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma ssh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) ssh_img_regions /\
  pairwise_disjoint E ssh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E0 E96 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct ssh_vals as (V1 & V95 & V0 & V96 & _).
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
  split.
  - unfold ssh_img_regions, got_regionP, bcell_regionP, ssh_got_uar, ssh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V95; unfold FCells.CELL_K; lia | lia |].
      rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
      split; [rewrite V95; unfold FCells.CELL_K; lia|].
      split; [rewrite V95; unfold FCells.CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 96) 0) (VAL (A_OBJ 96)));
      [cbn [sv_denot]; rewrite E96, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V96; unfold FCells.UAR; lia | lia |].
      rewrite Z.add_0_r, V0, V96. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
      split; [rewrite V96; unfold FCells.UAR; lia|].
      split; [rewrite V96; unfold FCells.UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 96)) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
      rewrite Z.add_0_r, V96. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold ssh_img_regions, got_regionP, bcell_regionP, ssh_got_uar, ssh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation: the 32 registers and the shadow base (atom 32). *)
Definition ssh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma ssh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ssh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold ssh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ssh_ew_32 : forall regs, ew (ssh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold ssh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma ssh_ew_obj : forall regs i, (i < 97)%nat -> ew (ssh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold ssh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma ssh_env_img : forall regs, img_env VAL A_LIM (ssh_E regs).
Proof. intros regs. unfold ssh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma ssh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SSTATE_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (ssh_E regs) ss_ssh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_set_state)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_ssh1, ssh_regions1.
  assert (Usp : bv_unsigned (ew (ssh_E regs) 2) = spZ regs)
    by (rewrite (ssh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (ssh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply ssh_ew_32.
  destruct (ssh_img_ok ly S W mem md (ssh_E regs) HCELLS HAR
    (ssh_ew_obj regs 1 ltac:(lia)) (ssh_ew_obj regs 95 ltac:(lia))
    (ssh_ew_obj regs 0 ltac:(lia)) (ssh_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct ssh_vals as (V1 & V95 & V0 & V96 & _).
  assert (VB : forall n v0, ew (ssh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (ssh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold SSTATE_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold ssh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, ssh_got_uar, ssh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (ssh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (ssh_ew_obj regs 95 ltac:(lia)))
      by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (ssh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (ssh_ew_obj regs 96 ltac:(lia)))
      by (rewrite V96; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, SSTATE_FRAME.
    repeat split; first [exact I | lia].
  - unfold ssh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: s1 (atom 9) = sp1, a0 (atom 10) = F, s10 (atom 26) = the shadow base; the frame word
   slot [sp1 + 48, sp1 + 56) and the header [F, F + 24). *)
Lemma ssh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 - 64 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F mod 64 = 0 -> F + 256 <= spv ->
  (forall a, spv + 48 <= a < spv + 56 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ssh_E regs) ss_ssh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SSH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R26 Hsp Hsp32 HF0 HFs HF64 HFsp Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_ssh2.
  assert (U2 : bv_unsigned (ew (ssh_E regs) 2) = spv)
    by (rewrite (ssh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (ssh_E regs) 9) = spv)
    by (rewrite (ssh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (ssh_E regs) 10) = F)
    by (rewrite (ssh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew (ssh_E regs) 26) = SHADOW_OFF)
    by (rewrite (ssh_ew_reg regs 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (ssh_E regs) 32) = SHADOW_OFF)
    by (rewrite (ssh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [ssh_rg_slot ssh_rg_hdr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ssh_rg_slot, ssh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold ssh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U26, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma ssh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 24 = w64 SH -> YK11.getr regs 20 = w64 SSTATE_S -> SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ssh_E regs) ss_ssh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SSH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R24 R20 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_ssh3.
  assert (CS : SSTATE_S = 6157888) by reflexivity.
  assert (U24 : bv_unsigned (ew (ssh_E regs) 24) = SH)
    by (rewrite (ssh_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (U20 : bv_unsigned (ew (ssh_E regs) 20) = SSTATE_S)
    by (rewrite (ssh_ew_reg regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; rewrite CS; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ssh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ssh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ssh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U24.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF in *;
    first [lia | reflexivity].
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma ssh_inG : forall a, SSTATE_S <= a < SSTATE_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, SSTATE_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* Every byte of g_s's payload is addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma ssh_ra : forall ly S (W : world segs) mem md lo n,
  trans_sstate_cells B -> @AR rc segs B ly S W mem md ->
  0 <= lo -> lo + n <= TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (SSTATE_S + lo) n.
Proof.
intros ly S W mem md lo n HZ HAR Hlo Hn x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : SSTATE_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= SSTATE_S + TW.SZ_g_s)
  by (unfold SSTATE_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md SSTATE_S (SSTATE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The valuation of run 2c: the 32 registers, the shadow base (atom 32) and the 4 bytes of g_s's state (atom 33). *)
Definition ssh_Ev (regs : bvmap 5 word) (v : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 v]).

Lemma ssh_ev_reg : forall regs v n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ssh_Ev regs v) n = YK11.getr regs r.
Proof. intros regs v n r Hn. unfold ssh_Ev. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ssh_ev_33 : forall regs v, ew (ssh_Ev regs v) 33 = Z_to_bv 64 v.
Proof. intros regs v. unfold ssh_Ev. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.

Lemma ssh_entry4 : forall ly S (W : world segs) regs mem md Bw,
  trans_sstate_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 20 = w64 SSTATE_S -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (ssh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 112) 4)) ss_ssh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SSH_C3)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SSH_Bx SSH_SH4 (ssh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 112) 4)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R20 R26.
set (v := TW.u_at Bw (TW.OFF_g_s + 112) 4).
assert (CS : SSTATE_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (ssh_Ev regs v) 20) = SSTATE_S)
  by (rewrite (ssh_ev_reg regs v 20 20%bv eq_refl), R20; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (ssh_Ev regs v) 26) = SHADOW_OFF)
  by (rewrite (ssh_ev_reg regs v 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= v < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (ssh_Ev regs v) 33) = v)
  by (rewrite ssh_ev_33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_ssh4.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [ssh_rg_st YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [rewrite CS; lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ SSTATE_S 112 4 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold ssh_rg_st, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold ssh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U26, U33.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (ssh_ra ly S W mem md 112 4 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U (ssh_Ev regs v) SSH_Bx = SHADOW_OFF).
  { unfold U, SSH_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, SSH_SH4. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ SSH_Bx 20 (SSTATE_S + 112) 4 SSTATE_S 112 116 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* A state with no region at a branch point. *)
Lemma ssh_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (ssh_E regs) (ss_ssh0 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_ssh0.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ssh_reg HS r v H tac :=
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
Ltac ssh_region HS i HR :=
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
Ltac ssh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac ssh_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac ssh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A register at the machine state of HS, from the equation Q of its value at the run's start (valuation ssh_E rg). *)
Ltac ssh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    ssh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same, at a state whose valuation agrees with E0 below atom 1024 (Elo), E0's registers by EE. *)
Ltac ssh_kreg5 HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    ssh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* After the one instruction to a cut (a run from a state with no region): every byte of the view as at +0x150
   (KD), presence grown (GR). *)
Ltac ssh_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition ssh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma ssh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem'
    md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The facts the cuts carry move to a later memory whose view is the same at every address. *)
Lemma ssh_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  sstb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((SSTATE_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  sstb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b m i Hb Hi Hn. rewrite KD. exact (K2 b m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

Lemma ssh_holds : @sstb_head_stmt fx rc B MT.
Proof.
unfold sstb_head_stmt. intros NTC REL.
unfold transport_set_state_cg_holds_stmt.
intros HPCS HCELLS HSC HROU HRNE LAWS MTL MTF SMP ASF FFL HGX HGNE ASM0 AI0 NT0.
unfold transport_set_state_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Htw Hfn Hm Hst Hwhy HTF HROM HAP Hcnt Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SSTATE_STK = 8416) by reflexivity.
assert (FF : SSTATE_FRAME = 160) by reflexivity.
assert (CS : SSTATE_S = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - SSTATE_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (ssh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (ssh_E regs)) by apply ssh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ssh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (ssh_E regs) 2) = spZ regs)
  by (rewrite (ssh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_set_state)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x070 *)
paj_run_tok RUN HS HJ SHOK SSH_B0.
{ ssh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (can_sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
assert (E2' : ew (ssh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (ssh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
ssh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 24740)) R1 ltac:(apply codeptr_val; exact HEI).
ssh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (ssh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
ssh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ssh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ssh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
ssh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (ssh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
ssh_reg HS (18%bv : bv 5) (w64 why) R18
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg regs 12 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
ssh_reg HS (19%bv : bv 5) (w64 st) R19
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
ssh_reg HS (20%bv : bv 5) (w64 SSTATE_S) R20
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
ssh_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) R26
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
ssh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) ssh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold ssh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) ssh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold ssh_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(ssh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (ssh_E regs) _ 2 (spZ regs) _ (-160) 0 (-160) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (ssh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; ssh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* +0x074: the class-2 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_2)) mm rom) mdx)
    Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (TransportGFrame.gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP SSTATE_CID
    ASM ltac:(unfold SSTATE_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 24740)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - exact Hcnt. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (SSTATE_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ SSTATE_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ SSTATE_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ SSTATE_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes SSTATE_CID / 8) with 32 in HFsh.
change (fs_frame_bytes SSTATE_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc SSTATE_CID pos) in *.
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) ssh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q18 : YK11.getr regs2 18 = w64 why)
  by (transitivity (YK11.getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact R18]).
assert (Q19 : YK11.getr regs2 19 = w64 st)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 SSTATE_S)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q26 : YK11.getr regs2 26 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]).
clear HS.
set (memT := ms_mem ms) in *. set (regsT := ms_regs ms) in *. clearbody memT regsT. clear ms.
(* +0x078 .. +0x0dc: the frame taken, the frame word at s1 + 48, the 24-byte header, s8 = the frame's shadow
   address. *)
assert (Hpslot : forall a, sp1 + 48 <= a < sp1 + 56 -> apresent (w_H W) mem2 a)
  by (intros a Ha; apply (ssh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia).
pose proof (ssh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q26 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64 ltac:(lia)
  Hpslot ltac:(intros a Ha; apply Hfpres; lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (ssh_E regs2)) by apply ssh_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (ssh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9' : bv_unsigned (ew (ssh_E regs2) 9) = sp1)
  by (rewrite (ssh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (ssh_E regs2) 10) = F)
  by (rewrite (ssh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SSH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
pose proof HJ2 as HJm2. clear HJ. rename HJ2 into HJ.
paj_run_to_tok RUNTO HS HJ SHOK SSH_B0 SSH_C2.
{ ssh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9' in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (TransportGFrame.awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SSTATE_CID pos);
    [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SSTATE_CID) with 256.
  change (frame_addr lyc SSTATE_CID pos) with F. lia. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms end.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - SSTATE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 160 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - SSTATE_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - SSTATE_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 160 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - SSTATE_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - SSTATE_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* the registers at +0x0e0 *)
assert (EF10 : ew (ssh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (ssh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF26 : ew (ssh_E regs2) 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ssh_ew_reg regs2 26 26%bv eq_refl); exact Q26).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
ssh_reg HS (24%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T24
  ltac:(exact (can_denot_shadow (ssh_E regs2) 10 26 F SHADOW_OFF EF10 EF26 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
ssh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. ssh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
ssh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. ssh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
ssh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. ssh_kreg HS regs2 (10%bv : bv 5) 10%nat Ha0 T10.
ssh_kreg HS regs2 (18%bv : bv 5) 18%nat Q18 T18. ssh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
ssh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. ssh_kreg HS regs2 (26%bv : bv 5) 26%nat Q26 T26.
ssh_reg HS (25%bv : bv 5) (w64 F) T25
  ltac:(cbn [sv_denot]; rewrite (ssh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* run 2a wrote the frame word slot and the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 48 <= x < sp1 + 56 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9', ?U10' in Hx;
    first [left; lia | right; lia] |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* +0x0e0 .. +0x134: the frame's 20 shadow bytes and the alignment check of s. *)
pmkst HS.
set (ms3 := ms) in *. clearbody ms3. clear HS.
pose proof (ssh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) T24 T20
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI3 : img_env VAL A_LIM (ssh_E (ms_regs ms3))) by apply ssh_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (ssh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U24 : bv_unsigned (ew (ssh_E (ms_regs ms3)) 24) = SHADOW_OFF + F / 8)
  by (rewrite (ssh_ew_reg (ms_regs ms3) 24 24%bv eq_refl), T24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SSH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK SSH_B0 SSH_C3.
{ ssh_awr_rs.
  eapply (TransportGFrame.awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SSTATE_CID pos);
    [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SSTATE_CID / 8) with 32.
  change (frame_addr lyc SSTATE_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms0 end.
(* run 2b wrote the frame's 20 shadow bytes only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U24 in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
(* the registers at +0x138 *)
ssh_kreg HS (ms_regs ms3) (2%bv : bv 5) 2%nat T2 V2. ssh_kreg HS (ms_regs ms3) (3%bv : bv 5) 3%nat T3 V3.
ssh_kreg HS (ms_regs ms3) (4%bv : bv 5) 4%nat T4 V4. ssh_kreg HS (ms_regs ms3) (8%bv : bv 5) 8%nat T8 V8.
ssh_kreg HS (ms_regs ms3) (9%bv : bv 5) 9%nat T9 V9. ssh_kreg HS (ms_regs ms3) (10%bv : bv 5) 10%nat T10 V10.
ssh_kreg HS (ms_regs ms3) (18%bv : bv 5) 18%nat T18 V18. ssh_kreg HS (ms_regs ms3) (19%bv : bv 5) 19%nat T19 V19.
ssh_kreg HS (ms_regs ms3) (20%bv : bv 5) 20%nat T20 V20. ssh_kreg HS (ms_regs ms3) (24%bv : bv 5) 24%nat T24 V24.
ssh_kreg HS (ms_regs ms3) (25%bv : bv 5) 25%nat T25 V25. ssh_kreg HS (ms_regs ms3) (26%bv : bv 5) 26%nat T26 V26.
(* the bytes of G at +0x138 are the entry's *)
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ SSTATE_CID pos a HAR2 Hin2
    ltac:(change (fs_frame_bytes SSTATE_CID) with 256; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (Htw4 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms0)) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K2b (b + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (K2a (b + i) ltac:(lia) ltac:(intros [Hx | Hx]; [lia | exact (NGF (b + i) ltac:(lia) Hg)])).
  exact (GK2 (b + i) Hg). }
(* +0x138 .. +0x14c: s6 = s + 112, s11 = its shadow address, the checked load of s5 = S_state, up to `beq s5, s3`. *)
pmkst HS.
set (ms4 := ms0) in *. clearbody ms4. clear HS SHOK.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
destruct (ssh_entry4 lyc S2 W (ms_regs ms4) (ms_mem ms4) _ Bw HSC HAR4 Htw4 V20 V26) as [HS SHOK].
clear HEI.
set (vst := TW.u_at Bw (TW.OFF_g_s + 112) 4) in *.
assert (HEI : img_env VAL A_LIM (ssh_Ev (ms_regs ms4) vst)) by (unfold ssh_Ev; apply Eimg_env).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SSH_C3)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ssh_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HF2c, HFr into HFr2c, HG into HG2c.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in * end.
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ssh_Ev (ms_regs ms4) vst) n = YK11.getr (ms_regs ms4) r)
  by (intros n r Hn; apply ssh_ev_reg; exact Hn).
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (ssh_Ev (ms_regs ms4) vst) n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms end.
set (m5 := ms_mem ms) in *.
(* run 2c wrote no byte *)
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) m5 a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr2c); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. lia. }
(* the registers at +0x150 *)
ssh_kreg5 HS E5lo EE4 (2%bv : bv 5) 2%nat V2 X2. ssh_kreg5 HS E5lo EE4 (3%bv : bv 5) 3%nat V3 X3.
ssh_kreg5 HS E5lo EE4 (4%bv : bv 5) 4%nat V4 X4. ssh_kreg5 HS E5lo EE4 (8%bv : bv 5) 8%nat V8 X8.
ssh_kreg5 HS E5lo EE4 (9%bv : bv 5) 9%nat V9 X9. ssh_kreg5 HS E5lo EE4 (10%bv : bv 5) 10%nat V10 X10.
ssh_kreg5 HS E5lo EE4 (18%bv : bv 5) 18%nat V18 X18. ssh_kreg5 HS E5lo EE4 (19%bv : bv 5) 19%nat V19 X19.
ssh_kreg5 HS E5lo EE4 (20%bv : bv 5) 20%nat V20 X20. ssh_kreg5 HS E5lo EE4 (24%bv : bv 5) 24%nat V24 X24.
ssh_kreg5 HS E5lo EE4 (25%bv : bv 5) 25%nat V25 X25. ssh_kreg5 HS E5lo EE4 (26%bv : bv 5) 26%nat V26 X26.
assert (E33 : ew E5 33 = Z_to_bv 64 vst) by (rewrite E5lo by lia; apply ssh_ev_33).
assert (R33 : 0 <= vst < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
ssh_reg HS (21%bv : bv 5) (w64 (TW.S_state Bw)) X21
  ltac:(rewrite ssh_st_num; exact (ssh_sext E5 vst R33 E33)).
ssh_reg HS (22%bv : bv 5) (w64 (SSTATE_S + 112)) X22
  ltac:(cbn [sv_denot]; rewrite (E5lo 20%nat ltac:(lia)), (EE4 20%nat 20%bv eq_refl), V20; unfold w64;
        rewrite (unsigned_lit_small SSTATE_S) by (rewrite CS; lia); reflexivity).
ssh_reg HS (27%bv : bv 5) (w64 (SHADOW_OFF + (SSTATE_S + 112) / 8)) X27
  ltac:(cbn [sv_denot]; rewrite (E5lo 20%nat ltac:(lia)), (E5lo 26%nat ltac:(lia)), (EE4 20%nat 20%bv eq_refl),
        (EE4 26%nat 26%bv eq_refl), V20, V26; unfold w64, SSTATE_S, TB_g_s, SHADOW_OFF; vm_compute; reflexivity).
(* ---- the facts both cuts carry, at the memory of +0x150 ---- *)
(* every byte outside the three written ranges is the one the stack malloc left *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (K2c a Ha).
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2c). apply (apresent_grows _ _ _ a G2b).
  exact (apresent_grows _ _ _ a G2a Ha). }
assert (NGS : forall a, F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56 ->
  ~ inG TG.G_HARNESS_B a).
{ intros a [X | [X | X]]; [apply NGF; lia | apply NGH; unfold SHADOW_OFF in *; lia | apply NGH; unfold SHADOW_OFF; lia]. }
(* the world relation at Bw *)
assert (TW5 : tw_at TMAP_B (aview segs (w_H W) m5) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KF5 (b + i) ltac:(lia) ltac:(intros X; exact (NGS _ X Hg))).
  exact (GK2 (b + i) Hg). }
(* the bytes of G outside the written range *)
assert (GXE5 : gx_kept_ex segs TG.G_HARNESS_B (sstate_wr Bw st why) W memc W m5).
{ intros a Hg _. rewrite <- (GK2 a Hg).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros X. exact (NGS a X Hg). }
(* what the call keeps, at m5 *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - SSTATE_STK) (spZ regs)
  (sstate_wr Bw st why)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - SSTATE_STK) (spZ regs)
    (fun _ => False) (sstate_wr Bw st why)); [tauto|].
  apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - SSTATE_STK) (spZ regs) SSTATE_CID pos F (flag_addr lyc SSTATE_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes SSTATE_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes SSTATE_CID / 8) with 32. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
(* the thirteen saved words, at m5 *)
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) ssh_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SSTB_SAVED).
{ unfold SSTB_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold ssh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
(* the frame's last word, at m5 *)
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + SSTB_FBYTES - 8) = Some (flag_addr lyc SSTATE_CID pos)).
{ rewrite <- Hflag. unfold SSTB_FBYTES. apply rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* the class-2 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : sstb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F lyc S2 W m5 md5 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj KG5 (conj HFW5 HFL5)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - unfold SSTATE_EV, NOTICE_EV. lia.
  - rewrite Eab2. apply Permutation_refl. }
(* the record facts and the caller's facts, as the cuts state them *)
assert (HLAWS : sstb_laws B MT)
  by exact (conj HPCS (conj HCELLS (conj HSC (conj HROU (conj HRNE (conj LAWS (conj MTL (conj MTF
    (conj SMP (conj ASF (conj FFL (conj HGX HGNE)))))))))))).
assert (HFIX : sstb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F).
{ unfold sstb_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj Hsp16 (conj Hlo
    (conj Hhi (conj Htw (conj Hfn (conj Hm (conj Hst (conj Hwhy (conj HTF (conj HROM (conj HAP (conj Hcnt (conj Hev
    (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp)))))))))))))))))))))))))).
  unfold sp1, SSTATE_FRAME. replace (spZ regs - 160) with (spZ regs + -160) by lia. reflexivity. }
assert (D21 : sv_denot (ssh_E (ms_regs ms)) (SOff 21 0) = Z_to_bv 64 (TW.S_state Bw))
  by (cbn [sv_denot]; rewrite (ssh_ew_reg (ms_regs ms) 21 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X21).
assert (D19 : sv_denot (ssh_E (ms_regs ms)) (SOff 19 0) = Z_to_bv 64 st)
  by (cbn [sv_denot]; rewrite (ssh_ew_reg (ms_regs ms) 19 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X19).
(* +0x150: `beq s5, s3`, from a state with no region *)
pmkst HS.
clear HS SHOK.
pose proof (ssh_entry0 W (ms_regs ms) m5 SSH_C4) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ssh_E (ms_regs ms)) (mrestrict (w_H W) m5)) by constructor.
assert (HEI5 : img_env VAL A_LIM (ssh_E (ms_regs ms))) by apply ssh_env_img.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SSH_C4)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK SSH_B0.
- (* S_state Bw = st: to the release cut +0x214 *)
  cbn [branch_taken] in Hc. rewrite D21, D19 in Hc.
  rewrite (ssh_eqb _ _ (ssh_state_range Bw) Hst) in Hc. apply Z.eqb_eq in Hc.
  pose proof (ssh_model_eq _ _ _ _ _ _ Hc Hm) as EBw'.
  paj_run_to_tok RUNTO HS HJ SHOK SSH_B0 SSTB_REL.
  { ssh_awr_rs. apply awr_ok_x_nil. }
  ssh_after_cut HS W KD GR m5 msF.
  ssh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Y2. ssh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Y3.
  ssh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Y4. ssh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Y8.
  ssh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Y9. ssh_kreg HS (ms_regs ms) (10%bv : bv 5) 10%nat X10 Y10.
  ssh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Y24. ssh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Y25.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SSTB_REL)) mm rom) mdx) Q) end.
  apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F lyc S2 W
    (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + refine (conj (ssh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F lyc S2 W m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR) (conj _ _)).
    * rewrite EBw'. apply (tw_kept TMAP_B (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KD x)].
    * rewrite EBw'. exact Hfn.
  + unfold sstb_regs_rel. refine (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y10 (conj Y24 Y25))))))).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
- (* S_state Bw <> st: to the notice cut +0x154 *)
  cbn [branch_taken] in Hc. rewrite D21, D19 in Hc.
  rewrite (ssh_eqb _ _ (ssh_state_range Bw) Hst) in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SSH_B0 SSTB_NTC.
  { ssh_awr_rs. apply awr_ok_x_nil. }
  ssh_after_cut HS W KD GR m5 msF.
  ssh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Y2. ssh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Y3.
  ssh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Y4. ssh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Y8.
  ssh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Y9. ssh_kreg HS (ms_regs ms) (10%bv : bv 5) 10%nat X10 Y10.
  ssh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Y24. ssh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Y25.
  ssh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Y18. ssh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat X19 Y19.
  ssh_kreg HS (ms_regs ms) (20%bv : bv 5) 20%nat X20 Y20. ssh_kreg HS (ms_regs ms) (21%bv : bv 5) 21%nat X21 Y21.
  ssh_kreg HS (ms_regs ms) (22%bv : bv 5) 22%nat X22 Y22. ssh_kreg HS (ms_regs ms) (26%bv : bv 5) 26%nat X26 Y26.
  ssh_kreg HS (ms_regs ms) (27%bv : bv 5) 27%nat X27 Y27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SSTB_NTC)) mm rom) mdx) Q) end.
  apply (NTC HLAWS AI0 NT0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs st why TF Bw Bw' pos sp1 F S2
    (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold sstb_ntc_cur.
    refine (conj (ssh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs st why Bw pos F lyc S2 W m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR) (conj Eab2 (conj _ (conj _ Hc)))).
    * intros a Hg Hn. rewrite KD. exact (GXE5 a Hg Hn).
    * apply (tw_kept TMAP_B (aview segs (w_H W) m5)); [exact TW5 | intros x _; exact (KD x)].
  + unfold sstb_regs_ntc, sstb_regs_rel.
    refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y10 (conj Y24 Y25)))))))
      (conj Y18 (conj Y19 (conj Y20 (conj Y21 (conj Y22 (conj Y26 Y27))))))).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
Qed.
End sh.

(* The head piece of the image-B walk of set_state (set_state_segs.v sstb_head_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem sstb_head : forall fx rc B MT, @sstb_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ssh_holds fx rc B MT). Qed.
