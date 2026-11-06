(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 861 of its 1029 lines of code are new or changed and 971 lines of the source are left out. *)
(* diginet_session_close_seg_head: Lemma close_head : close_head_stmt (lib/A/Prog/diginet_session_close_segs.v), the
   head piece of the walk of diginet_session_close on fuzz_transport.asan (0x8713c = transport_sigma
   TS_diginet_session_close, AF_diginet_session_close = 0x5ed8 of lib/A/Prog/DgnTransportList.v), from the entry to
   the two cuts close_send_at (+0x3c4) and close_join_at (+0x18c). The walk holds the caller's G journal
   (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []); the runs are the position-abstract runs of
   lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x (the structure is lib/A/Prog/SlostHead.v's):
     run 1   +0x000 .. +0x06c  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1, the flag word through its GOT word (1, so `beqz a2` is not taken), s9 = the shadow
                               base, s3 = s, a0 = 160, up to `jal __asan_stack_malloc_2`;
     +0x06c                    the class-2 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x070 .. +0x0d4  `bnez s2` taken (the real-stack arm is not reached), the frame word at s1 + 48, the
                               frame's 24-byte header, s7 = the frame's shadow address;
     run 2b  +0x0d8 .. +0x128  the frame's shadow bytes 0 .. 19 (a run to +0x12c);
     run 3   +0x12c ..         `beqz s3` (s3 = s, not taken), the checked loads of s + 116, s + 136 and s + 112 (each
                               check reads a shadow byte 0 of g_s's payload: trans_close_cells, the shadow entry
                               CLH_SH) and the three tests of close_go, each a data-dependent branch taken up at the
                               state the run stopped at (+0x14c `beqz a0`, +0x168 `bnez a0`, +0x184 `bne a0, a1`):
                               close_go Bw = false runs `mv a3, zero` (+0x188) to the join cut, else the run reaches
                               the send cut.
   The head writes no byte of g_s, so the world relation at both cuts is at Bw. The facts the cuts carry are proved
   once at +0x12c (close_cur at that memory) and moved to the cut's memory, whose view is the same (the runs of run 3
   only load: clh_chain). What the call keeps (acall_kept_g) runs from the entry to the stack malloc's return
   (TransportGCg.v dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over the three
   written ranges (dk_kept_own_g: the frame's header and shadow bytes, the slot s1 + 48 in the call's window). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_close_cg diginet_session_close_segs diginet_session_close_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition CLH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x06c *)
Definition clh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 94) 0))].
Definition clh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition clh_img_regions : smem := [got_regionP; bcell_regionP 32; clh_got_uar; clh_uar_cell].
Definition clh_regions1 : smem := stack_region CLOSE_FRAME :: clh_img_regions.
Definition clh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_clh1 : sstate := mkSS AF_diginet_session_close sr_atoms clh_regions1 None clh_facts1.

(* run 2a, +0x070 .. +0x0d4: after the stack malloc, the frame F in a0 (atom 10); the run writes the frame word at
   s1 + 48 (atom 9) and the frame's 24-byte header, and stops at the first shadow store. *)
Definition CLH_C1 : Z := AF_diginet_session_close + 0x70.
Definition clh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition clh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition clh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_clh2 : sstate := mkSS CLH_C1 sr_atoms [clh_rg_slot; clh_rg_hdr] None clh_facts2.

(* run 2b, +0x0d8 .. +0x128: s7 (atom 23) holds the frame's shadow address; the run writes the frame's shadow bytes
   0 .. 19, up to +0x12c. *)
Definition CLH_C2 : Z := AF_diginet_session_close + 0xd8.
Definition CLH_C3 : Z := AF_diginet_session_close + 0x12c.
Definition clh_rg_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 20 0 20 [].
Definition clh_facts3 : facts := mkFacts [(23%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_clh3 : sstate := mkSS CLH_C2 sr_atoms [clh_rg_sh] None clh_facts3.

(* run 3, from +0x12c: s3 (atom 19) is s, s9 (atom 25) the shadow base; the three g_s fields the code loads, read
   only: the 4 bytes of S_state at s + 112 (atom 33), of S_desk_known at s + 116 (atom 34) and of S_foreign at
   s + 136 (atom 35). *)
Definition clh_rg_st : YP09.region :=
  YP09.mkRegion (Some 19%nat) 112 116 0 0 [YP09.mkChunk 112 (YP09.CVal 4 (SOff 33 0))].
Definition clh_rg_dk : YP09.region :=
  YP09.mkRegion (Some 19%nat) 116 120 0 0 [YP09.mkChunk 116 (YP09.CVal 4 (SOff 34 0))].
Definition clh_rg_fo : YP09.region :=
  YP09.mkRegion (Some 19%nat) 136 140 0 0 [YP09.mkChunk 136 (YP09.CVal 4 (SOff 35 0))].
Definition clh_regions4 : smem := [clh_rg_st; clh_rg_dk; clh_rg_fo].
Definition clh_facts4 : facts :=
  mkFacts [(19%nat, mkAF CLOSE_S CLOSE_S 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_clh4 : sstate := mkSS CLH_C3 sr_atoms clh_regions4 None clh_facts4.
(* The shadow entry of the run's three checks ([s + 112, s + 140)), and the shadow base. *)
Definition CLH_SH : list shent := [mkSHE 19 112 140].
Definition CLH_Bx : sv := SOff 25 0.

(* ------------------------------------------------------------------ *)
(* The three tests                                                     *)
(* ------------------------------------------------------------------ *)

(* close_go at the numeral offsets of g_s.desk_known (s + 116), g_s.foreign (s + 136) and g_s.state (s + 112). *)
Lemma clh_go : forall Bw, close_go Bw =
  negb (TW.s32_at Bw (TW.OFF_g_s + 116) =? 0) && (TW.s32_at Bw (TW.OFF_g_s + 136) =? 0) &&
  negb (TW.s32_at Bw (TW.OFF_g_s + 112) =? 3).
Proof. intros Bw. reflexivity. Qed.

(* A test of a sign-extended 32-bit value against a small non-negative literal. *)
Lemma clh_eqb : forall v c, - 2 ^ 31 <= v < 2 ^ 31 -> 0 <= c < 2 ^ 31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 c) = (v =? c).
Proof.
intros v c Hv Hc. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small c (2 ^ 64)) by lia.
destruct (Z.eqb_spec v c) as [Ev | Hne].
- subst v. rewrite (Z.mod_small c (2 ^ 64)) by lia. apply Z.eqb_refl.
- apply Z.eqb_neq. intros HH. apply Hne.
  destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
  + rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
  + rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* The sign-extended 4-byte load of a field of the world: the model's s32_at. *)
Lemma clh_sext : forall E (n : nat) Bw A, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (TW.s32_at Bw A).
Proof.
intros E n Bw A H. assert (R : 0 <= TW.u_at Bw A 4 < 2 ^ 32) by exact (TWL.u_at_range Bw A 4).
cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* `beq` and `bne` of such a load against a literal: the model's test. *)
Lemma clh_beq : forall E (n : nat) Bw A k bt, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) -> 0 <= k < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit k)) = bt ->
  (TW.s32_at Bw A =? k) = bt.
Proof.
intros E n Bw A k bt H Hk Hb. rewrite <- Hb. cbn [branch_taken].
rewrite (clh_sext E n Bw A H).
change (sv_denot E (SLit k)) with (Z_to_bv 64 k).
rewrite (clh_eqb _ k (TWL.s32_range Bw A) Hk). reflexivity.
Qed.

Lemma clh_bne : forall E (n : nat) Bw A k bt, ew E n = Z_to_bv 64 (TW.u_at Bw A 4) -> 0 <= k < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit k)) = bt ->
  (TW.s32_at Bw A =? k) = negb bt.
Proof.
intros E n Bw A k bt H Hk Hb. rewrite <- Hb.
change BC_NE with (neg_bc BC_EQ). rewrite branch_taken_neg, negb_involutive.
exact (clh_beq E n Bw A k _ H Hk eq_refl).
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma clh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_diginet_session_close = transport_sigma TS_diginet_session_close.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma clh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) clh_img_regions /\
  pairwise_disjoint E clh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct clh_vals as (V1 & V93 & V0 & V94 & _).
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
  - unfold clh_img_regions, got_regionP, bcell_regionP, clh_got_uar, clh_uar_cell.
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
    unfold clh_img_regions, got_regionP, bcell_regionP, clh_got_uar, clh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation at the entry: the 32 registers and the shadow base (atom 32). *)
Definition clh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

Lemma clh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (clh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold clh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma clh_ew_32 : forall regs, ew (clh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold clh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma clh_ew_obj : forall regs i, (i < 95)%nat -> ew (clh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold clh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma clh_env_img : forall regs, img_env VAL A_LIM (clh_E regs).
Proof. intros regs. unfold clh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma clh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - CLOSE_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (clh_E regs) ss_clh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_close)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_clh1, clh_regions1.
  assert (Usp : bv_unsigned (ew (clh_E regs) 2) = spZ regs)
    by (rewrite (clh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (clh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply clh_ew_32.
  destruct (clh_img_ok ly S W mem md (clh_E regs) HCELLS HAR
    (clh_ew_obj regs 1 ltac:(lia)) (clh_ew_obj regs 93 ltac:(lia))
    (clh_ew_obj regs 0 ltac:(lia)) (clh_ew_obj regs 94 ltac:(lia)) E32) as [HRs HPd].
  destruct clh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (clh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (clh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold CLOSE_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold clh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, clh_got_uar, clh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (clh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (clh_ew_obj regs 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (clh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (clh_ew_obj regs 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, CLOSE_FRAME.
    repeat split; first [exact I | lia].
  - unfold clh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: the slot s1 + 48 and the frame's header. *)
Lemma clh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 24 <= spv -> F mod 64 = 0 ->
  (forall a, spv + 48 <= a < spv + 56 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (clh_E regs) ss_clh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R25 Hsp Hsp32 HF0 HFsp HF64 Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_clh2.
  assert (U2 : bv_unsigned (ew (clh_E regs) 2) = spv)
    by (rewrite (clh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (clh_E regs) 9) = spv)
    by (rewrite (clh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (clh_E regs) 10) = F)
    by (rewrite (clh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (clh_E regs) 25) = SHADOW_OFF)
    by (rewrite (clh_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (clh_E regs) 32) = SHADOW_OFF)
    by (rewrite (clh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [clh_rg_slot clh_rg_hdr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold clh_rg_slot, clh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold clh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U25, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma clh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 23 = w64 SH -> SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (clh_E regs) ss_clh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R23 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_clh3.
  assert (U23 : bv_unsigned (ew (clh_E regs) 23) = SH)
    by (rewrite (clh_ew_reg regs 23 23%bv eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold clh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold clh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold clh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* g_s's bytes [s + 112, s + 140) are addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma clh_ra : forall ly S (W : world segs) mem md,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (CLOSE_S + 112) 28.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : CLOSE_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= CLOSE_S + TW.SZ_g_s)
  by (unfold CLOSE_S, TA_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md CLOSE_S (CLOSE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The valuation of run 3: the 32 registers at +0x12c, the shadow base (atom 32) and the 4 bytes of g_s's state
   (atom 33), desk_known (atom 34) and foreign (atom 35). *)
Definition clh_E4 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4);
    Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 116) 4); Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 136) 4)]).

Lemma clh_E4_33 : forall regs Bw, ew (clh_E4 regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 112) 4).
Proof. intros regs Bw. unfold clh_E4. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma clh_E4_34 : forall regs Bw, ew (clh_E4 regs Bw) 34 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 116) 4).
Proof. intros regs Bw. unfold clh_E4. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). Qed.
Lemma clh_E4_35 : forall regs Bw, ew (clh_E4 regs Bw) 35 = Z_to_bv 64 (TW.u_at Bw (TW.OFF_g_s + 136) 4).
Proof. intros regs Bw. unfold clh_E4. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3). Qed.

Lemma clh_entry4 : forall ly S (W : world segs) regs mem md Bw,
  trans_close_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 CLOSE_S -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (clh_E4 regs Bw) ss_clh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CLH_C3)) mem (YK11.seg_rom segs))) /\
  sh_ok segs CLH_Bx CLH_SH (clh_E4 regs Bw) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HCC HAR Htw R19 R25.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (clh_E4 regs Bw) n = YK11.getr regs r)
  by (intros n r Hn; unfold clh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (CS : CLOSE_S = 6158784) by reflexivity.
assert (U19 : bv_unsigned (ew (clh_E4 regs Bw) 19) = CLOSE_S)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (clh_E4 regs Bw) 25) = SHADOW_OFF)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 112) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (R34 : 0 <= TW.u_at Bw (TW.OFF_g_s + 116) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (R35 : 0 <= TW.u_at Bw (TW.OFF_g_s + 136) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (clh_E4 regs Bw) 33) = TW.u_at Bw (TW.OFF_g_s + 112) 4)
  by (rewrite clh_E4_33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (clh_E4 regs Bw) 34) = TW.u_at Bw (TW.OFF_g_s + 116) 4)
  by (rewrite clh_E4_34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew (clh_E4 regs Bw) 35) = TW.u_at Bw (TW.OFF_g_s + 136) 4)
  by (rewrite clh_E4_35; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_clh4, clh_regions4.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [clh_rg_st clh_rg_dk clh_rg_fo
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ CLOSE_S 112 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 112) 4));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ CLOSE_S 116 4 (SOff 34 0) (TW.u_at Bw (TW.OFF_g_s + 116) 4));
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | exact R34 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 116 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ CLOSE_S 136 4 (SOff 35 0) (TW.u_at Bw (TW.OFF_g_s + 136) 4));
        [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | exact R35 | lia |].
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 136 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold clh_rg_st, clh_rg_dk, clh_rg_fo, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold clh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U25, U33, U34, U35.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (clh_ra ly S W mem md HCC HAR) as HRA.
  assert (UB : U (clh_E4 regs Bw) CLH_Bx = SHADOW_OFF).
  { unfold U, CLH_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, CLH_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ CLH_Bx 19 (CLOSE_S + 112) 28 CLOSE_S 112 140 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac clh_reg HS r v H tac :=
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
Ltac clh_region HS i HR :=
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
Ltac clh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
(* The awr obligation's regions, computed. *)
Ltac clh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The awr obligation of a run whose regions write no byte. *)
Ltac clh_awr_ro :=
  clh_awr_rs;
  repeat (apply awr_ok_x_cons;
          [let a := fresh "a" in let Ha := fresh "Ha" in
           intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac clh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    clh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (clh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same at a state of run 3, whose valuation agrees with clh_E4 below atom 1024 (EL). *)
Ltac clh_kreg5 HS EL EE4 r n Q H :=
  lazymatch type of Q with _ = ?v =>
    clh_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (EL n ltac:(lia)); rewrite (EE4 n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
(* The valuation of the state HS agrees with E4 below atom 1024. *)
Ltac clh_elo HS E4 H :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (H : forall n, (n < 1024)%nat -> ew Ex n = ew E4 n)
      by (let n := fresh "n" in let Hn := fresh "Hn" in
          intros n Hn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
(* Name the machine state of HS. *)
Ltac clh_name HS x :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.
(* No window of the run's regions holds a byte (every region is read only). *)
Ltac clh_nowin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; exfalso; lia |]);
  destruct Hin.
(* After a run whose regions write no byte: the view at its memory is the view before (KD), presence grown (GR). *)
Ltac clh_kept HFr HG KD GR :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh ?mp) (mrestrict ?Hh2 ?mn) =>
  assert (KD : forall a, aview tfibsegs Hh mn a = aview tfibsegs Hh mp a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ mn a), (aview_wrap64 tfibsegs _ mp a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [clh_nowin | exact Ha | exact (fun HH => HH)]
  | ];
  assert (GR : forall a, apresent Hh mp a -> apresent Hh mn a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG Ha) | ]
  end.
(* Move the chain KDc / GRc (from the memory at +0x12c to the run's start) to the run's end. *)
Ltac clh_chain HFr HG KDc GRc :=
  let KD := fresh "KD" in let GR := fresh "GR" in
  clh_kept HFr HG KD GR;
  let K2 := fresh "K" in let G2 := fresh "G" in
  pose proof (fun a => eq_trans (KD a) (KDc a)) as K2;
  pose proof (fun a Ha => GR a (GRc a Ha)) as G2;
  clear KD GR KDc GRc HFr HG; rename K2 into KDc; rename G2 into GRc.

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition clh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma clh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The facts the cuts carry move to a later memory whose view is the same at every address. *)
Lemma clh_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  close_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((CLOSE_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  close_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
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

Lemma close_head : @close_head_stmt fx rc B MT.
Proof.
unfold close_head_stmt. intros SEND JOIN.
unfold transport_diginet_session_close_cg_holds_stmt.
intros HPCS HCELLS HCC HGU HGN HROU HRNE LAWS MTL MTF SMP ASF FFL ASM0 AI0 NT0 SC0.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGN) as HGNE.
unfold transport_diginet_session_close_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hnow Htw Hfn Hm HTF HROM HAP HTFG Hfly Hcmd Hcnt Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HBS : 4272 <= CLOSE_STK).
{ unfold CLOSE_STK, CLOSE_FRAME, CLOSE_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hmx; assert (Hax : a = 4096) by reflexivity end.
  lia. }
assert (FF : CLOSE_FRAME = 160) by reflexivity.
assert (CS : CLOSE_S = 6158784) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (EV0 : CLOSE_EV = 0) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - CLOSE_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (clh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (clh_E regs)) by apply clh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (clh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (clh_E regs) 2) = spZ regs)
  by (rewrite (clh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_close)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x06c *)
paj_run_tok RUN HS HJ SHOK CLH_B0.
{ clh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
clh_name HS ms1.
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (can_sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
assert (E2' : ew (clh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (clh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
clh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 24392)) R1 ltac:(apply codeptr_val; exact HEI).
clh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (clh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
clh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (clh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
clh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (clh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
clh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
clh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (clh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
clh_reg HS (19%bv : bv 5) (w64 CLOSE_S) R19
  ltac:(cbn [sv_denot]; rewrite (clh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
clh_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) R25
  ltac:(cbn [sv_denot]; rewrite (clh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
clh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) clh_saved -> -104 <= o <= -8).
{ intros o r0 Hin. unfold clh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) clh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms1)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. unfold clh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms1) (spZ regs + o) (bv_unsigned (YK11.getr regs r0))
    ltac:(clh_u64 (YK11.getr regs r0))).
  apply (can_field_of_region (clh_E regs) _ 2 (spZ regs) _ (-160) 0 (-160) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r0)) 0) (bv_unsigned (YK11.getr regs r0)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (clh_ew_reg regs (Z.to_nat (bv_unsigned r0)) r0 ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; clh_u64 (YK11.getr regs r0)
  | cbn; lia ]. }
clear HRsk.
(* +0x06c: the class-2 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_2)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP CLOSE_CID ASM
    ltac:(unfold CLOSE_CID; lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 24392)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (CLOSE_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ CLOSE_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ CLOSE_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ CLOSE_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes CLOSE_CID / 8) with 32 in HFsh.
change (fs_frame_bytes CLOSE_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc CLOSE_CID pos) in *.
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) clh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho.
  rewrite <- (HSV o r0 Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms1) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms1) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms1) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms1) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms1) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 CLOSE_S)
  by (transitivity (YK11.getr (ms_regs ms1) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q25 : YK11.getr regs2 25 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms1) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
clear HS.
set (memT := ms_mem ms1) in *. set (regsT := ms_regs ms1) in *. clearbody memT regsT. clear ms1.
(* +0x070 .. +0x0d4: the frame taken, the frame word at s1 + 48, its 24-byte header, s7 = the frame's shadow
   address. *)
pose proof (clh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q25 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64
  ltac:(intros a Ha; apply (clh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (clh_E regs2)) by apply clh_env_img.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (clh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9' : bv_unsigned (ew (clh_E regs2) 9) = sp1)
  by (rewrite (clh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (clh_E regs2) 10) = F)
  by (rewrite (clh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + CLH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK CLH_B0.
{ clh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9' in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ CLOSE_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CLOSE_CID) with 256.
  change (frame_addr lyc CLOSE_CID pos) with F. lia. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
clh_name HS msA.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - CLOSE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 160 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memT (spZ regs - CLOSE_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
    (spZ regs - CLOSE_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 160 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - CLOSE_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W memT W mem2 (spZ regs - CLOSE_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* the registers at +0x0d8 *)
assert (EF10 : ew (clh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (clh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF25 : ew (clh_E regs2) 25 = Z_to_bv 64 SHADOW_OFF) by (rewrite (clh_ew_reg regs2 25 25%bv eq_refl); exact Q25).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clh_reg HS (23%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T23
  ltac:(exact (can_denot_shadow (clh_E regs2) 10 25 F SHADOW_OFF EF10 EF25 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
clh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. clh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
clh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. clh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
clh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. clh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
clh_kreg HS regs2 (25%bv : bv 5) 25%nat Q25 T25.
clh_reg HS (24%bv : bv 5) (w64 F) T24
  ltac:(cbn [sv_denot]; rewrite (clh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
clh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (clh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* run 2a wrote the slot s1 + 48 and the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem msA) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 48 <= x < sp1 + 56 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9', ?U10' in Hx;
    first [left; lia | right; lia | lia] |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* +0x0d8 .. +0x128: the frame's shadow bytes 0 .. 19. *)
pmkst HS.
clear HS.
pose proof (clh_entry3 W (ms_regs msA) (ms_mem msA) (SHADOW_OFF + F / 8) T23
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (clh_E (ms_regs msA))) by apply clh_env_img.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (clh_E (ms_regs msA)) (mrestrict (w_H W) (ms_mem msA)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U23 : bv_unsigned (ew (clh_E (ms_regs msA)) 23) = SHADOW_OFF + F / 8)
  by (rewrite (clh_ew_reg (ms_regs msA) 23 23%bv eq_refl), T23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK CLH_B0 CLH_C3.
{ clh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ CLOSE_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes CLOSE_CID / 8) with 32.
  change (frame_addr lyc CLOSE_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
clh_name HS msB.
(* run 2b wrote the frame's shadow bytes 0 .. 19 only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem msB) a = aview segs (w_H W) (ms_mem msA) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U23 in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
(* the registers at +0x12c *)
clh_kreg HS (ms_regs msA) (2%bv : bv 5) 2%nat T2 V2. clh_kreg HS (ms_regs msA) (3%bv : bv 5) 3%nat T3 V3.
clh_kreg HS (ms_regs msA) (4%bv : bv 5) 4%nat T4 V4. clh_kreg HS (ms_regs msA) (8%bv : bv 5) 8%nat T8 V8.
clh_kreg HS (ms_regs msA) (9%bv : bv 5) 9%nat T9 V9. clh_kreg HS (ms_regs msA) (18%bv : bv 5) 18%nat T18 V18.
clh_kreg HS (ms_regs msA) (19%bv : bv 5) 19%nat T19 V19.
clh_kreg HS (ms_regs msA) (23%bv : bv 5) 23%nat T23 V23. clh_kreg HS (ms_regs msA) (24%bv : bv 5) 24%nat T24 V24.
clh_kreg HS (ms_regs msA) (25%bv : bv 5) 25%nat T25 V25.
pmkst HS.
clear HS SHOK.
(* the bytes of G at +0x12c are the entry's *)
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ CLOSE_CID pos a HAR2 Hin2 ltac:(change (fs_frame_bytes CLOSE_CID) with 256; lia) Hi). }
assert (Htw4 : tw_at TMAP_A (aview segs (w_H W) (ms_mem msB)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K2b (b + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (K2a (b + i) ltac:(lia) ltac:(intros [Hx | Hx]; [lia | exact (NGF (b + i) ltac:(lia) Hg)])).
  exact (GK2 (b + i) Hg). }
(* ---- the facts both cuts carry, at the memory of +0x12c ---- *)
set (m4 := ms_mem msB) in *.
(* every byte outside the three written ranges is the one the stack malloc left *)
assert (KF4 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56) ->
  aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GF4 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m4 a).
{ intros a Ha. apply (apresent_grows _ _ _ a G2b). exact (apresent_grows _ _ _ a G2a Ha). }
(* what the call keeps, at m4 *)
assert (KG4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W m4 (spZ regs - CLOSE_STK) (spZ regs) (close_wr TF Bw)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W m4 (spZ regs - CLOSE_STK) (spZ regs)
    (fun _ => False) (close_wr TF Bw)); [tauto|].
  apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc mem2 md2 mem2 m4
    (spZ regs - CLOSE_STK) (spZ regs) CLOSE_CID pos F (flag_addr lyc CLOSE_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF4].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes CLOSE_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes CLOSE_CID / 8) with 32. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF4 a Ha Hn). }
(* the thirteen saved words, at m4 *)
assert (HSV4 : forall (o : Z) (r : bv 5), In (o, r) clh_saved ->
  rdword (aview segs (w_H W) m4) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho. rewrite <- (HSV2 o r0 Hin).
  apply rdword_ext. intros i Hi. apply KF4; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW4 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m4) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) CLOSE_SAVED).
{ unfold CLOSE_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV4 (- o) (Z_to_bv 5 r)); unfold clh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
(* the frame's last word, at m4 *)
assert (HFL4 : rdword (aview segs (w_H W) m4) (F + CLOSE_FBYTES - 8) = Some (flag_addr lyc CLOSE_CID pos)).
{ rewrite <- Hflag. unfold CLOSE_FBYTES. apply rdword_ext. intros i Hi. apply KF4; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* the class-2 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r0 ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md4 := md') in * end.
assert (CUR4 : close_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F lyc S2 W m4 md4 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj KG4 (conj HFW4 HFL4)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - rewrite EV0. lia.
  - rewrite Eab2. apply Permutation_refl. }
(* the record facts and the caller's facts, as the cuts state them *)
assert (HLAWS : close_laws B MT)
  by exact (conj HPCS (conj HCELLS (conj HCC (conj HROU (conj HRNE (conj LAWS (conj MTL (conj MTF
    (conj SMP (conj ASF (conj FFL (conj HGX (conj HGNE (conj HGU HGN)))))))))))))).
assert (HFIX : close_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F).
{ unfold close_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
    (conj Hnow (conj Htw (conj Hfn (conj Hm (conj HTF (conj HROM (conj HAP (conj HTFG (conj Hfly (conj Hcmd
    (conj Hcnt (conj Hev (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp))))))))))))))))))))))))))).
  unfold sp1, CLOSE_FRAME. replace (spZ regs - 160) with (spZ regs + -160) by lia. reflexivity. }
(* The join cut, from any of the three paths on which close_go Bw is false: B1 = Bw and r = 0. *)
lazymatch goal with |- SRr _ _ _ ?Q =>
assert (JEND : forall (regsF : bvmap 5 word) (memF : word -> option byte) (mdF : Model),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((CLOSE_CID, pos) :: own) lyc S2 W memF mdF k ->
  (forall a, aview segs (w_H W) memF a = aview segs (w_H W) m4 a) ->
  (forall a, apresent (w_H W) m4 a -> apresent (w_H W) memF a) ->
  close_go Bw = false -> close_regs_send regs regsF sp1 F -> YK11.getr regsF 13 = w64 0 ->
  SRr segs W (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (BASE + CLOSE_JOIN)) memF (YK11.seg_rom segs)) mdF) Q) end.
{ intros regsF memF mdF HJF KDF GRF Hgo HRS H13.
  assert (Er : 0 = r) by exact (close_r_eq timg_A TF Bw now Bw' Bw 0 r Hm (close_sent_nogo timg_A TF Bw Hgo)).
  apply (JOIN HLAWS AI0 NT0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' Bw pos sp1 F
    lyc S2 W memF mdF 0 regsF HFIX).
  - refine (conj (clh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F lyc S2 W m4 md4
      memF mdF 0 CUR4 ltac:(rewrite Z.add_0_r; exact HJF) KDF GRF) (conj _ (conj _ Hfn))).
    + rewrite <- Er. exact (close_sent_nogo timg_A TF Bw Hgo).
    + apply (tw_kept TMAP_A (aview segs (w_H W) m4)); [exact Htw4 | intros x _; exact (KDF x)].
  - refine (conj HRS _). rewrite <- Er. exact H13. }
(* +0x12c ..: `beqz s3`, the checked loads of s + 116, s + 136 and s + 112 and the three tests. *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
destruct (clh_entry4 lyc S2 W (ms_regs msB) m4 _ Bw HCC HAR4 Htw4 V19 V25) as [HS SHOK].
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (clh_E4 (ms_regs msB) Bw)) by (unfold clh_E4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (clh_E4 (ms_regs msB) Bw) n = YK11.getr (ms_regs msB) r)
  by (intros n r0 Hn; unfold clh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
pose proof (clh_E4_33 (ms_regs msB) Bw) as E33.
pose proof (clh_E4_34 (ms_regs msB) Bw) as E34.
pose proof (clh_E4_35 (ms_regs msB) Bw) as E35.
assert (KDc : forall a, aview segs (w_H W) m4 a = aview segs (w_H W) m4 a) by (intros a; reflexivity).
assert (GRc : forall a, apresent (w_H W) m4 a -> apresent (w_H W) m4 a) by (intros a Ha; exact Ha).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLH_C3)) mm rom) mdx) Q) end.
(* run to +0x14c, `beqz a0` on S_desk_known Bw *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ clh_awr_ro. }
clh_chain HFr HG KDc GRc. clear HF.
clh_elo HS (clh_E4 (ms_regs msB) Bw) EL1.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* S_desk_known Bw = 0: close_go Bw is false, `mv a3, zero` and the join cut *)
  pose proof (clh_beq _ 34%nat Bw (TW.OFF_g_s + 116) 0 true (eq_trans (EL1 34%nat ltac:(lia)) E34) ltac:(lia) Hc)
    as Hd1. clear Hc.
  assert (Hgo : close_go Bw = false) by (rewrite clh_go, Hd1; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_JOIN.
  { clh_awr_ro. }
  clh_chain HFr HG KDc GRc. clear HF.
  clh_name HS msF.
  clh_elo HS (clh_E4 (ms_regs msB) Bw) ELF.
  clh_kreg5 HS ELF EE4 (2%bv : bv 5) 2%nat V2 Y2. clh_kreg5 HS ELF EE4 (3%bv : bv 5) 3%nat V3 Y3.
  clh_kreg5 HS ELF EE4 (4%bv : bv 5) 4%nat V4 Y4. clh_kreg5 HS ELF EE4 (8%bv : bv 5) 8%nat V8 Y8.
  clh_kreg5 HS ELF EE4 (9%bv : bv 5) 9%nat V9 Y9. clh_kreg5 HS ELF EE4 (18%bv : bv 5) 18%nat V18 Y18.
  clh_kreg5 HS ELF EE4 (19%bv : bv 5) 19%nat V19 Y19. clh_kreg5 HS ELF EE4 (23%bv : bv 5) 23%nat V23 Y23.
  clh_kreg5 HS ELF EE4 (24%bv : bv 5) 24%nat V24 Y24. clh_kreg5 HS ELF EE4 (25%bv : bv 5) 25%nat V25 Y25.
  clh_reg HS (21%bv : bv 5) (w64 (CLOSE_S + 112)) Y21
    ltac:(cbn [sv_denot]; try rewrite (ELF 19%nat ltac:(lia)); rewrite (EE4 19%nat 19%bv eq_refl), V19; unfold w64;
          rewrite (unsigned_lit_small CLOSE_S) by lia; reflexivity).
  clh_reg HS (13%bv : bv 5) (w64 0) Y13 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
  apply (JEND (ms_regs msF) (ms_mem msF) _ HJ KDc GRc Hgo); [| exact Y13].
  refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))) (conj Y19 (conj Y21 Y25))).
  + rewrite Y3. symmetry. exact Hgp.
  + rewrite Y4. symmetry. exact Htp.
- (* S_desk_known Bw <> 0: on to +0x168, `bnez a0` on S_foreign Bw *)
  pose proof (clh_beq _ 34%nat Bw (TW.OFF_g_s + 116) 0 false (eq_trans (EL1 34%nat ltac:(lia)) E34) ltac:(lia) Hc)
    as Hd1. clear Hc.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { clh_awr_ro. }
  clh_chain HFr HG KDc GRc. clear HF.
  clh_elo HS (clh_E4 (ms_regs msB) Bw) EL2.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* S_foreign Bw <> 0: close_go Bw is false, the join cut *)
    pose proof (clh_bne _ 35%nat Bw (TW.OFF_g_s + 136) 0 true (eq_trans (EL2 35%nat ltac:(lia)) E35) ltac:(lia) Hc)
      as Hd2. clear Hc.
    assert (Hgo : close_go Bw = false) by (rewrite clh_go, Hd1, Hd2; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_JOIN.
    { clh_awr_ro. }
    clh_chain HFr HG KDc GRc. clear HF.
    clh_name HS msF.
    clh_elo HS (clh_E4 (ms_regs msB) Bw) ELF.
    clh_kreg5 HS ELF EE4 (2%bv : bv 5) 2%nat V2 Y2. clh_kreg5 HS ELF EE4 (3%bv : bv 5) 3%nat V3 Y3.
    clh_kreg5 HS ELF EE4 (4%bv : bv 5) 4%nat V4 Y4. clh_kreg5 HS ELF EE4 (8%bv : bv 5) 8%nat V8 Y8.
    clh_kreg5 HS ELF EE4 (9%bv : bv 5) 9%nat V9 Y9. clh_kreg5 HS ELF EE4 (18%bv : bv 5) 18%nat V18 Y18.
    clh_kreg5 HS ELF EE4 (19%bv : bv 5) 19%nat V19 Y19. clh_kreg5 HS ELF EE4 (23%bv : bv 5) 23%nat V23 Y23.
    clh_kreg5 HS ELF EE4 (24%bv : bv 5) 24%nat V24 Y24. clh_kreg5 HS ELF EE4 (25%bv : bv 5) 25%nat V25 Y25.
    clh_reg HS (21%bv : bv 5) (w64 (CLOSE_S + 112)) Y21
      ltac:(cbn [sv_denot]; try rewrite (ELF 19%nat ltac:(lia)); rewrite (EE4 19%nat 19%bv eq_refl), V19; unfold w64;
            rewrite (unsigned_lit_small CLOSE_S) by lia; reflexivity).
    clh_reg HS (13%bv : bv 5) (w64 0) Y13 ltac:(reflexivity).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
    apply (JEND (ms_regs msF) (ms_mem msF) _ HJ KDc GRc Hgo); [| exact Y13].
    refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))) (conj Y19 (conj Y21 Y25))).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
  + (* S_foreign Bw = 0: on to +0x184, `bne a0, a1` on S_state Bw against 3 *)
    pose proof (clh_bne _ 35%nat Bw (TW.OFF_g_s + 136) 0 false (eq_trans (EL2 35%nat ltac:(lia)) E35) ltac:(lia) Hc)
      as Hd2. clear Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { clh_awr_ro. }
    clh_chain HFr HG KDc GRc. clear HF.
    clh_elo HS (clh_E4 (ms_regs msB) Bw) EL3.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* S_state Bw <> S_CLOSED: close_go Bw holds, the send cut *)
      pose proof (clh_bne _ 33%nat Bw (TW.OFF_g_s + 112) 3 true (eq_trans (EL3 33%nat ltac:(lia)) E33) ltac:(lia) Hc)
        as Hd3. clear Hc.
      assert (Hgo : close_go Bw = true) by (rewrite clh_go, Hd1, Hd2, Hd3; reflexivity).
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_SEND.
      { clh_awr_ro. }
      clh_chain HFr HG KDc GRc. clear HF.
      clh_name HS msF.
      clh_elo HS (clh_E4 (ms_regs msB) Bw) ELF.
      clh_kreg5 HS ELF EE4 (2%bv : bv 5) 2%nat V2 Y2. clh_kreg5 HS ELF EE4 (3%bv : bv 5) 3%nat V3 Y3.
      clh_kreg5 HS ELF EE4 (4%bv : bv 5) 4%nat V4 Y4. clh_kreg5 HS ELF EE4 (8%bv : bv 5) 8%nat V8 Y8.
      clh_kreg5 HS ELF EE4 (9%bv : bv 5) 9%nat V9 Y9. clh_kreg5 HS ELF EE4 (18%bv : bv 5) 18%nat V18 Y18.
      clh_kreg5 HS ELF EE4 (19%bv : bv 5) 19%nat V19 Y19. clh_kreg5 HS ELF EE4 (23%bv : bv 5) 23%nat V23 Y23.
      clh_kreg5 HS ELF EE4 (24%bv : bv 5) 24%nat V24 Y24. clh_kreg5 HS ELF EE4 (25%bv : bv 5) 25%nat V25 Y25.
      clh_reg HS (21%bv : bv 5) (w64 (CLOSE_S + 112)) Y21
        ltac:(cbn [sv_denot]; try rewrite (ELF 19%nat ltac:(lia)); rewrite (EE4 19%nat 19%bv eq_refl), V19; unfold w64;
              rewrite (unsigned_lit_small CLOSE_S) by lia; reflexivity).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_SEND)) mm rom) mdx) Q) end.
      apply (SEND HLAWS AI0 NT0 SC0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now r TF Bw Bw' pos sp1 F
        S2 (ms_mem msF) _ (ms_regs msF) HFIX).
      -- unfold close_send_cur.
         refine (conj (clh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs TF Bw pos F lyc S2 W m4 md4
           (ms_mem msF) _ 0 CUR4 ltac:(rewrite Z.add_0_r; exact HJ) KDc GRc) (conj Eab2 (conj _ Hgo))).
         apply (tw_kept TMAP_A (aview segs (w_H W) m4)); [exact Htw4 | intros x _; exact (KDc x)].
      -- unfold close_regs_send, close_regs_base.
         refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))) (conj Y19 (conj Y21 Y25))).
         ++ rewrite Y3. symmetry. exact Hgp.
         ++ rewrite Y4. symmetry. exact Htp.
    * (* S_state Bw = S_CLOSED: close_go Bw is false, `mv a3, zero` and the join cut *)
      pose proof (clh_bne _ 33%nat Bw (TW.OFF_g_s + 112) 3 false (eq_trans (EL3 33%nat ltac:(lia)) E33) ltac:(lia) Hc)
        as Hd3. clear Hc.
      assert (Hgo : close_go Bw = false) by (rewrite clh_go, Hd1, Hd2, Hd3; reflexivity).
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan CLOSE_JOIN.
      { clh_awr_ro. }
      clh_chain HFr HG KDc GRc. clear HF.
      clh_name HS msF.
      clh_elo HS (clh_E4 (ms_regs msB) Bw) ELF.
      clh_kreg5 HS ELF EE4 (2%bv : bv 5) 2%nat V2 Y2. clh_kreg5 HS ELF EE4 (3%bv : bv 5) 3%nat V3 Y3.
      clh_kreg5 HS ELF EE4 (4%bv : bv 5) 4%nat V4 Y4. clh_kreg5 HS ELF EE4 (8%bv : bv 5) 8%nat V8 Y8.
      clh_kreg5 HS ELF EE4 (9%bv : bv 5) 9%nat V9 Y9. clh_kreg5 HS ELF EE4 (18%bv : bv 5) 18%nat V18 Y18.
      clh_kreg5 HS ELF EE4 (19%bv : bv 5) 19%nat V19 Y19. clh_kreg5 HS ELF EE4 (23%bv : bv 5) 23%nat V23 Y23.
      clh_kreg5 HS ELF EE4 (24%bv : bv 5) 24%nat V24 Y24. clh_kreg5 HS ELF EE4 (25%bv : bv 5) 25%nat V25 Y25.
      clh_reg HS (21%bv : bv 5) (w64 (CLOSE_S + 112)) Y21
        ltac:(cbn [sv_denot]; try rewrite (ELF 19%nat ltac:(lia)); rewrite (EE4 19%nat 19%bv eq_refl), V19; unfold w64;
              rewrite (unsigned_lit_small CLOSE_S) by lia; reflexivity).
      clh_reg HS (13%bv : bv 5) (w64 0) Y13 ltac:(reflexivity).
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + CLOSE_JOIN)) mm rom) mdx) Q) end.
      apply (JEND (ms_regs msF) (ms_mem msF) _ HJ KDc GRc Hgo); [| exact Y13].
      refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y23 Y24))))))) (conj Y19 (conj Y21 Y25))).
      -- rewrite Y3. symmetry. exact Hgp.
      -- rewrite Y4. symmetry. exact Htp.
Qed.
End h.
