(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 569 of its 730 lines of code are new or changed and 978 lines of the source are left out. *)
(* on_announce_seg_head: Theorem onann_piece_head : forall fx rc B MT, @onann_head_stmt fx rc B MT
   (lib/A/Prog/OnannCut.v section 8), the head piece of the walk of on_announce on fuzz_transport.asan
   (0x87a74 = transport_sigma TS_on_announce, AF_on_announce = 0x6810 of lib/A/Prog/DgnTransportList.v), from the
   entry to the parse cut onann_lp_at (+0x20c). The walk holds the caller's G journal (lib/A/W_journalG.v
   ajournal_gx G_HARNESS 0 []); the runs are the position-abstract runs of lib/A/Prog/TransportGRunA.v paj_run_x /
   paj_run_to_x:
     run 1   +0x000 .. +0x070  the frame (`addi sp, sp, -0xc0`, `sd zero, 0(sp)`, the 13 saves at sp - 8 .. sp - 104,
                               OnannCut.v ONANN_SAVED), s0 = the entry sp, the realign into s1 = sp1, s10 = now,
                               s6 = fp, the flag word through its GOT word 0xa40e8 (transport_cells row 6 gives 1,
                               so `beqz a2` at +0x06c is not taken), s8 = the shadow base through the GOT word
                               0xa4090, s4 = s, a0 = 576, up to `jal __asan_stack_malloc_4`;
     +0x074                    the class-4 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x078 .. +0x0e4  `mv s7, a0`, `j`, `mv s2, s7`, `bnez s7` taken (the real-stack arm is not reached),
                               the frame word at s1 + 80, s5 = a = F + 256, the frame's 24-byte header (the magic
                               0x41b58ab3, the description string A_OBJ 75, the function's address A_OBJ 76),
                               s3 = (F >> 3) + s8, the frame's first shadow byte;
     run 2b  +0x0e8 .. +0x208  the frame's 72 shadow bytes (576 bytes), a run to the cut +0x20c; its last four
                               stores (`sb zero, 0x20(s3)` .. `sb zero, 0x23(s3)`) and the store at +0x16c
                               (`sb zero, 0x24(s3)`) leave the shadow bytes 32 .. 36 of a at 0.
   The head writes no byte of G, so what the call keeps (acall_kept_g) runs from the entry to the stack malloc's
   return (TransportGCg.v dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over the
   three written ranges (dk_kept_own_g at the empty written range, then acall_kept_g_weaken to onann_wr Bw b: the
   frame's header, its 72 shadow bytes, and the slot s1 + 80 in the call's window). G itself is kept through the
   malloc (gx_kept_of_acall_kept), so the statement's tw_at at Bw holds at the cut's memory.
   Lemmas of note: oh_img_ok (the four runtime cells at any AR state), oh_entry1 / oh_entry2 / oh_entry3 (the three
   runs' entry states), oh_jpres, oh_inG. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
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

Definition OH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x070: the stack frame of 192 bytes, and the four image cells the GOT loads read (the flag
   word 0xaca00 through 0xa40e8, the shadow base 0x7fff8000 through 0xa4090 and 0xac9f8). *)
Definition oh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 94) 0))].
Definition oh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition oh_img_regions : smem := [got_regionP; bcell_regionP 32; oh_got_uar; oh_uar_cell].
Definition oh_regions1 : smem := stack_region ONANN_FRAME :: oh_img_regions.
Definition oh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oh1 : sstate := mkSS AF_on_announce sr_atoms oh_regions1 None oh_facts1.

(* run 2a, +0x078 .. +0x0e4: after the stack malloc, the frame F in a0 (atom 10); the run writes the frame word at
   s1 + 80 (atom 9 is s1 = sp1) and the frame's 24-byte header, and stops at the first shadow store. *)
Definition OH_C1 : Z := AF_on_announce + 0x78.
Definition oh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition oh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 80 88 [].
Definition oh_regions2 : smem := [oh_rg_hdr; oh_rg_slot].
Definition oh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_oh2 : sstate := mkSS OH_C1 sr_atoms oh_regions2 None oh_facts2.

(* run 2b, +0x0e8 .. +0x208: s3 (atom 19) holds the frame's shadow address; the run writes the frame's 72 shadow
   bytes, up to the parse cut +0x20c. *)
Definition OH_C2 : Z := AF_on_announce + 0xe8.
Definition oh_rg_sh : YP09.region := YP09.mkRegion (Some 19%nat) 0 72 0 72 [].
Definition oh_facts3 : facts := mkFacts [(19%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_oh3 : sstate := mkSS OH_C2 sr_atoms [oh_rg_sh] None oh_facts3.

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition oh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma oh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_on_announce = transport_sigma TS_on_announce.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma oh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) oh_img_regions /\
  pairwise_disjoint E oh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct oh_vals as (V1 & V93 & V0 & V94 & _).
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
    intros kk Hk. exact (H6 kk Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 94) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold oh_img_regions, got_regionP, bcell_regionP, oh_got_uar, oh_uar_cell.
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
    unfold oh_img_regions, got_regionP, bcell_regionP, oh_got_uar, oh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation: the 32 registers and the shadow base (atom 32). *)
Definition oh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

Lemma oh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (oh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold oh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma oh_ew_32 : forall regs, ew (oh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold oh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma oh_ew_obj : forall regs i, (i < 95)%nat -> ew (oh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold oh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma oh_env_img : forall regs, img_env VAL A_LIM (oh_E regs).
Proof. intros regs. unfold oh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma oh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - ONANN_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (oh_E regs) ss_oh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_announce)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_oh1, oh_regions1.
  assert (Usp : bv_unsigned (ew (oh_E regs) 2) = spZ regs)
    by (rewrite (oh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (oh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply oh_ew_32.
  destruct (oh_img_ok ly S W mem md (oh_E regs) HCELLS HAR
    (oh_ew_obj regs 1 ltac:(lia)) (oh_ew_obj regs 93 ltac:(lia))
    (oh_ew_obj regs 0 ltac:(lia)) (oh_ew_obj regs 94 ltac:(lia)) E32) as [HRs HPd].
  destruct oh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (oh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (oh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold ONANN_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold oh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, oh_got_uar, oh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (oh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (oh_ew_obj regs 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (oh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (oh_ew_obj regs 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, ONANN_FRAME.
    repeat split; first [exact I | lia].
  - unfold oh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: the frame's header (atom 10 = F) and the slot s1 + 80 (atom 9 = sp1). *)
Lemma oh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 1024 <= 2 ^ 47 -> F mod 64 = 0 -> F + 1024 <= spv ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  (forall a, spv + 80 <= a < spv + 88 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (oh_E regs) ss_oh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R24 Hsp Hsp32 HF0 HFs HF64 HFlt Hpframe Hpslot.
  rewrite restrict_mkst_fx. unfold ss_oh2, oh_regions2.
  assert (U2 : bv_unsigned (ew (oh_E regs) 2) = spv)
    by (rewrite (oh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (oh_E regs) 9) = spv)
    by (rewrite (oh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (oh_E regs) 10) = F)
    by (rewrite (oh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew (oh_E regs) 24) = SHADOW_OFF)
    by (rewrite (oh_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (oh_E regs) 32) = SHADOW_OFF)
    by (rewrite (oh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [oh_rg_hdr oh_rg_slot YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
  - apply pairwise_disjoint_of_extents.
    unfold oh_rg_hdr, oh_rg_slot, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold oh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U24, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2b: the frame's 72 shadow bytes at s3 (atom 19). *)
Lemma oh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 19 = w64 SH -> SHADOW_OFF <= SH -> SH + 72 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 72 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (oh_E regs) ss_oh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R19 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_oh3.
  assert (U19 : bv_unsigned (ew (oh_E regs) 19) = SH)
    by (rewrite (oh_ew_reg regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold oh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold oh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold oh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma oh_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma oh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac oh_reg HS r v H tac :=
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
Ltac oh_region HS i HR :=
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
Ltac oh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac oh_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac oh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac oh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    oh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (oh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The machine state a run stopped at, under a name of ours. *)
Ltac oh_name HS nm :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?msx) =>
      set (nm := msx) in *
  | st_ok_pi _ _ _ _ (restrict _ ?msx) => set (nm := msx) in *
  end.

Lemma oh_holds : @onann_head_stmt fx rc B MT.
Proof.
unfold onann_head_stmt. intros LP.
unfold transport_on_announce_cg_holds_stmt.
intros HPCS HCELLS HSC HGU HGNE0 HROU HRNE LAWS MTL MTF SMP ASF FFL ASM0 LEAF0 PFN0 BCMP0 AI0 NT0 WAKE0 MON0 SS0.
unfold transport_on_announce_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hnow Hdf Htw Hfn Hm HTF HTFG HROM HAP Hri1 Hri2 Hri3
  Hcnt Hcnt2 Hev.
pose proof (ASM0 fx) as ASM.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGNE0) as HGNE.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (FF : ONANN_FRAME = 192) by reflexivity.
assert (CS : ONANN_S = 6158784) by reflexivity.
assert (FS4 : 4304 <= ONANN_STK) by (vm_compute; discriminate).
assert (HEV0 : 0 <= ONANN_EV) by (vm_compute; discriminate).
assert (GEOa : alloc_ceiling <= spZ regs - ONANN_STK) by lia.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - ONANN_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (oh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (oh_E regs)) by apply oh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (oh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (oh_E regs) 2) = spZ regs)
  by (rewrite (oh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_announce)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x070 *)
paj_run_tok RUN HS HJ SHOK OH_B0.
{ oh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
oh_name HS msA.
set (sp1 := 32 * ((spZ regs + -192) / 32)).
destruct (can_sp1_facts (spZ regs + -192) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia).
assert (E2' : ew (oh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (oh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
oh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 26760)) R1 ltac:(apply codeptr_val; exact HEI).
oh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (oh_E regs) 2 (spZ regs) (-192) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
oh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
oh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
oh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
oh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (oh_E regs) 2 (spZ regs) (-192) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
oh_reg HS (20%bv : bv 5) (w64 ONANN_S) R20
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
oh_reg HS (22%bv : bv 5) (w64 fp) R22
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
oh_reg HS (26%bv : bv 5) (w64 now) R26
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs 12 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
oh_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) R24
  ltac:(cbn [sv_denot]; rewrite (oh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
oh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) oh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold oh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) oh_saved ->
  rdword (aview segs (w_H W) (ms_mem msA)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold oh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem msA) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(oh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (oh_E regs) _ 2 (spZ regs) _ (-192) 0 (-192) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (oh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; oh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* +0x074: the class-4 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_4)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP ONANN_CID ASM
    ltac:(unfold ONANN_CID; lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 26760)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
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
assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ ONANN_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ ONANN_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh.
change (fs_frame_bytes ONANN_CID) with 1024 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc ONANN_CID pos) in *.
assert (HF8 : 0 <= F / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (GEOsh : SHADOW_OFF + F / 8 + 128 < 2 ^ 46) by (unfold SHADOW_OFF; lia).
(* the thirteen saved words, kept by the class-4 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) oh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs msA) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs msA) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs msA) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs msA) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs msA) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q20 : YK11.getr regs2 20 = w64 ONANN_S)
  by (transitivity (YK11.getr (ms_regs msA) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q22 : YK11.getr regs2 22 = w64 fp)
  by (transitivity (YK11.getr (ms_regs msA) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22]).
assert (Q24 : YK11.getr regs2 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs msA) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]).
assert (Q26 : YK11.getr regs2 26 = w64 now)
  by (transitivity (YK11.getr (ms_regs msA) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]).
clear HS SHOK.
set (memT := ms_mem msA) in *. set (regsT := ms_regs msA) in *. clearbody memT regsT.
(* +0x078 .. +0x0e4: the frame taken, the frame word at s1 + 80, a = F + 256, the 24-byte header, s3 = the
   frame's first shadow byte. *)
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
pose proof (oh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q24 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64
  ltac:(lia) ltac:(intros a Ha; apply Hfpres; lia)
  ltac:(intros a Ha; apply (oh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)) as HS.
assert (HEI : img_env VAL A_LIM (oh_E regs2)) by apply oh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (oh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
assert (U10' : bv_unsigned (ew (oh_E regs2) 10) = F)
  by (rewrite (oh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (U9' : bv_unsigned (ew (oh_E regs2) 9) = sp1)
  by (rewrite (oh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK OH_B0.
{ oh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONANN_CID) with 1024.
    change (frame_addr lyc ONANN_CID pos) with F. lia. }
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9' in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_nil. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
oh_name HS msB.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - ONANN_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 192 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memT (spZ regs - ONANN_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
    (spZ regs - ONANN_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 192 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b0 m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - ONANN_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W memT W mem2 (spZ regs - ONANN_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* the registers at +0x0e8 *)
assert (EF10 : ew (oh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (oh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF24 : ew (oh_E regs2) 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (oh_ew_reg regs2 24 24%bv eq_refl); exact Q24).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
oh_reg HS (19%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T19
  ltac:(exact (can_denot_shadow (oh_E regs2) 10 24 F SHADOW_OFF EF10 EF24 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
oh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. oh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
oh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. oh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
oh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. oh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20.
oh_kreg HS regs2 (22%bv : bv 5) 22%nat Q22 T22. oh_kreg HS regs2 (24%bv : bv 5) 24%nat Q24 T24.
oh_kreg HS regs2 (26%bv : bv 5) 26%nat Q26 T26.
oh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
oh_reg HS (23%bv : bv 5) (w64 F) T23
  ltac:(cbn [sv_denot]; rewrite (oh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
oh_reg HS (21%bv : bv 5) (w64 (F + ONANN_A)) T21
  ltac:(cbn [sv_denot]; rewrite U10'; reflexivity).
(* run 2a wrote the frame's header and the slot s1 + 80 only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 24 \/ sp1 + 80 <= a < sp1 + 88) ->
  aview segs (w_H W) (ms_mem msB) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _
    (fun x => F <= x < F + 24 \/ sp1 + 80 <= x < sp1 + 88) HFr2a); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U10', ?U9' in Hx; first [left; lia | right; lia] |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* +0x0e8 .. +0x208: the frame's 72 shadow bytes, to the parse cut. *)
pmkst HS.
clear HS SHOK.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
pose proof (oh_entry3 W (ms_regs msB) (ms_mem msB) (SHADOW_OFF + F / 8) T19
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI : img_env VAL A_LIM (oh_E (ms_regs msB))) by apply oh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (oh_E (ms_regs msB)) (mrestrict (w_H W) (ms_mem msB)))
  by constructor.
assert (U19' : bv_unsigned (ew (oh_E (ms_regs msB)) 19) = SHADOW_OFF + F / 8)
  by (rewrite (oh_ew_reg (ms_regs msB) 19 19%bv eq_refl), T19; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK OH_B0 ONANN_LP.
{ oh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19' in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONANN_CID / 8) with 128.
  change (frame_addr lyc ONANN_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
oh_name HS msC.
(* run 2b wrote the frame's 72 shadow bytes only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 72) ->
  aview segs (w_H W) (ms_mem msC) a = aview segs (w_H W) (ms_mem msB) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 72) HFr2b);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19' in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b.
(* the registers at the cut *)
oh_kreg HS (ms_regs msB) (2%bv : bv 5) 2%nat T2 X2. oh_kreg HS (ms_regs msB) (3%bv : bv 5) 3%nat T3 X3.
oh_kreg HS (ms_regs msB) (4%bv : bv 5) 4%nat T4 X4. oh_kreg HS (ms_regs msB) (8%bv : bv 5) 8%nat T8 X8.
oh_kreg HS (ms_regs msB) (9%bv : bv 5) 9%nat T9 X9. oh_kreg HS (ms_regs msB) (18%bv : bv 5) 18%nat T18 X18.
oh_kreg HS (ms_regs msB) (19%bv : bv 5) 19%nat T19 X19. oh_kreg HS (ms_regs msB) (20%bv : bv 5) 20%nat T20 X20.
oh_kreg HS (ms_regs msB) (21%bv : bv 5) 21%nat T21 X21. oh_kreg HS (ms_regs msB) (22%bv : bv 5) 22%nat T22 X22.
oh_kreg HS (ms_regs msB) (23%bv : bv 5) 23%nat T23 X23. oh_kreg HS (ms_regs msB) (24%bv : bv 5) 24%nat T24 X24.
oh_kreg HS (ms_regs msB) (26%bv : bv 5) 26%nat T26 X26.
(* a's five shadow bytes (32 .. 36) are 0: the four `sb zero` at +0x1fc .. +0x208 and the one at +0x16c *)
oh_region HS 0%nat HRsh.
assert (SZ5 : forall i, 32 <= i < 37 -> aview segs (w_H W) (ms_mem msC) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi.
  assert (Hi' : i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | ->]]]];
  match goal with |- aview _ _ _ (_ + ?o) = Some 0 =>
    exact (can_aview_of_val1 _ _ _ _ _ (can_field_of_region (oh_E (ms_regs msB)) _ 19 _ _ 0 72 0 72 o 1%N
      (SLit 0) 0 HRsh U19' ltac:(oh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))) end. }
clear HRsh.
(* ---- the facts the cut carries, at the memory of +0x20c ---- *)
(* every byte outside the three written ranges is the one the stack malloc left *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ sp1 + 80 <= a < sp1 + 88 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 72) ->
  aview segs (w_H W) (ms_mem msC) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem msC) a).
{ intros a Ha. apply (apresent_grows _ _ _ a G2b). exact (apresent_grows _ _ _ a G2a Ha). }
assert (NGF : forall a, F <= a < F + 1024 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONANN_CID pos a HAR2 Hin2
    ltac:(change (fs_frame_bytes ONANN_CID) with 1024; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (NGS : forall a, F <= a < F + 24 \/ sp1 + 80 <= a < sp1 + 88 \/
    SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 72 -> ~ inG TG.G_HARNESS a).
{ intros a [X | [X | X]];
  [apply NGF; lia | apply NGH; unfold SHADOW_OFF; lia | apply NGH; unfold SHADOW_OFF in *; lia]. }
(* the world relation at Bw: the head writes no byte of G *)
assert (Htw2 : tw_at TMAP_A (aview segs (w_H W) mem2) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n i Hin Hi.
  apply GK2. unfold inG. apply Exists_exists. exists (b0, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (TW5 : tw_at TMAP_A (aview segs (w_H W) (ms_mem msC)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) mem2)); [exact Htw2|]. intros b0 n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b0 + i)).
  { unfold inG. apply Exists_exists. exists (b0, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros X. exact (NGS (b0 + i) X Hg). }
(* what the call keeps, at the cut's memory *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem msC) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W (ms_mem msC) (spZ regs - ONANN_STK) (spZ regs)
    (fun _ => False) (onann_wr Bw b)); [tauto|].
  apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc mem2 md2 mem2 (ms_mem msC)
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ sp1 + 80 <= a < sp1 + 88 \/
       SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 72)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    + left. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
(* the thirteen saved words, at the cut's memory *)
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) oh_saved ->
  rdword (aview segs (w_H W) (ms_mem msC)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply rdword_ext. intros i Hi. apply KF5; [lia|].
  intros [X | [X | X]]; [lia | lia |].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem msC)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ unfold ONANN_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold oh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
(* the frame's last word, at the cut's memory *)
assert (HFL5 : rdword (aview segs (w_H W) (ms_mem msC)) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- Hflag. unfold ONANN_FBYTES. apply rdword_ext. intros i Hi. apply KF5; [lia|].
  intros [X | [X | X]]; [lia | lia |].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* the class-4 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
pmkst HS.
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b0 ?g ?xo ?o ?stk ?sp ?fpx ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F lyc S2 W
  (ms_mem msC) md5 0).
{ unfold onann_cur.
  split; [rewrite Z.add_0_r; exact HJ|].
  split; [lia|].
  split; [exact Hfrs2|].
  split; [rewrite Eab2; apply Permutation_refl|].
  split; [reflexivity|].
  split; [exact HMO|].
  split; [exact KG5|].
  split; [exact HFW5 | exact HFL5]. }
(* the record facts, the callee contracts and the caller's facts, as the cut states them *)
assert (HLAWS : onann_laws B MT).
{ unfold onann_laws.
  split; [exact HPCS|]. split; [exact HCELLS|]. split; [exact HSC|]. split; [exact HGU|].
  split; [exact HGNE0|]. split; [exact HROU|]. split; [exact HRNE|]. split; [exact LAWS|].
  split; [exact MTL|]. split; [exact MTF|]. split; [exact SMP|]. split; [exact ASF|].
  split; [exact FFL|]. split; [exact HGX | exact HGNE]. }
assert (HCALL : onann_callees B MT).
{ unfold onann_callees.
  split; [exact ASM0|]. split; [exact LEAF0|]. split; [exact PFN0|]. split; [exact BCMP0|].
  split; [exact AI0|]. split; [exact NT0|]. split; [exact WAKE0|]. split; [exact MON0 | exact SS0]. }
assert (HFIX : onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F).
{ unfold onann_fix.
  split; [exact HJe|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|].
  split; [exact Htp|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  split; [exact Hsp16|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hnow|].
  split; [exact Hdf|]. split; [exact Htw|]. split; [exact Hfn|]. split; [exact Hm|].
  split; [exact HTF|]. split; [exact HTFG|]. split; [exact HROM|]. split; [exact HAP|].
  split; [split; [exact Hri1|]; split; [exact Hri2 | exact Hri3]|].
  split; [exact Hcnt|]. split; [exact Hcnt2|]. split; [exact Hev|].
  split; [unfold sp1, ONANN_FRAME; replace (spZ regs - 192) with (spZ regs + -192) by lia; reflexivity|].
  split; [reflexivity|]. split; [exact HF0|]. split; [exact HF64|]. split; [exact HFc | exact HFapp]. }
assert (RBASE : onann_regs_base regs (ms_regs msC) sp1 F).
{ unfold onann_regs_base.
  split; [exact X2|]. split; [rewrite X3; symmetry; exact Hgp|]. split; [rewrite X4; symmetry; exact Htp|].
  split; [exact X8|]. split; [exact X9|]. split; [exact X18 | exact X19]. }
assert (RPF : onann_regs_pf regs (ms_regs msC) fp now sp1 F).
{ unfold onann_regs_pf, onann_regs_ign, onann_regs_rel.
  split; [split; [split; [exact RBASE | exact X23]|]; split; [exact X20 | exact X24]|].
  split; [exact X21|]. split; [exact X22 | exact X26]. }
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_LP)) mm rom) mdx) Q) end.
apply (LP HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F lyc S2 W (ms_mem msC) md5 (ms_regs msC) HFIX).
- unfold onann_lp_cur. split; [exact CUR5|]. split; [exact TW5 | exact SZ5].
- exact RPF.
Qed.
End sh.

(* The head piece of the walk of on_announce (OnannCut.v onann_head_stmt), at every machine, run ceiling, record
   and meter. *)
Theorem onann_piece_head : forall fx rc B MT, @onann_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@oh_holds fx rc B MT). Qed.
