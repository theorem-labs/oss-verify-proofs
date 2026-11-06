(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 639 of its 811 lines of code are new or changed and 967 lines of the source are left out. *)
(* SrxBHead: the head piece of the walk of diginet_session_rx on image B (fuzz_transport.asan-ubsan 0x87784 =
   transportb_sigma TB_diginet_session_rx, AF_diginet_session_rx = 0x64e4 of lib/B/Prog/DgnTransportBList.v), from
   the entry to the parse cut srxb_parse_at (+0x130) of lib/B/Prog/SrxBCut.v. Image A's lib/A/Prog/SrxHead.v at image
   B's listing; the code of the range is image A's word for word. The walk holds the caller's G journal
   (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []); the runs are the position-abstract runs of
   lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x:
     run 1   +0x000 .. +0x074  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1, s3 = now, s7 = len, s8 = buf, the flag word through its GOT word (object 0 ->
                               object 96, which holds 1, so `beq a2, zero` is not taken), s11 = the shadow base (object 1
                               -> object 95), s4 = s, a0 = 128, up to `jal __asan_stack_malloc_1`;
     +0x078                    the class-1 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x07c .. +0x0dc  s2 = F, `bne s2, zero` taken (F <> 0: the real-stack arm +0x090 .. +0x0a8 is not
                               reached), s10 = F, the frame word at s1 + 48, the frame's 24-byte header and s9 = the
                               frame's shadow address, up to the first shadow store;
     run 2b  +0x0e0 .. +0x12c  the frame's 16 shadow bytes (0 .. 3 := 0xf1, 12 .. 15 := 0xf3, 4 .. 11 := 0: f's 64
                               bytes usable), a0 = -1 and the two NULL tests `beq s4, zero` (s = g_s) and `beq s8,
                               zero` (0 < buf), neither taken; a run to the parse cut +0x130.
   No path of this range reaches an error report or a UBSan trap word. The facts the cut carries are proved at the
   cut's memory as on image A: what the call keeps (acall_kept_g: TransportGCg.v dk_kept_step_g over run 1,
   dk_kept_trans_g with the stack malloc's acall_kept, dk_kept_own_g over runs 2a and 2b), G kept (no byte of G is
   written, so the world relation is at Bw), and the reads the later code hands to its callees (the bytes at buf, TF,
   the guarded OW.dn range), carried from the entry state to the cut's state by lib/B/Prog/TransportGNoticeB.v
   trans_src_ok_kept_gx / trans_tframe_at_kept_gx. srxbh_walk is the walk with the caller's run invariants as
   SrxBCut.v srxb_inv and premise (3) as srxb_ndata (premise (3) itself); srxb_head_ok converts the statement's
   premises into them (the bounds g_ncmd <= CMDS_MAX and S_queued <= QUEUE_MAX srxb_inv holds are the statement's
   premises too). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_cg on_data_cg on_announce_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_mac_is_digidesign_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_rx_cg SrxBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* No shadow byte is read by the three runs. *)
Definition SRXBH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x078: the saves go into the stack region; the flag word's GOT word (object 0) holds the cell
   (object 96), which holds 1; the shadow base's GOT word (object 1) and cell (object 95). *)
Definition srxbh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 96) 0))].
Definition srxbh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition srxbh_img_regions : smem := [got_regionP; bcell_regionP 32; srxbh_got_uar; srxbh_uar_cell].
Definition srxbh_regions1 : smem := stack_region SRX_FRAME :: srxbh_img_regions.
Definition srxbh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbh1 : sstate := mkSS AF_diginet_session_rx sr_atoms srxbh_regions1 None srxbh_facts1.

(* run 2a, +0x07c .. +0x0dc: the frame F in a0 (atom 10), the realigned sp in s1 (atom 9), the shadow base in s11
   (atom 27); the run writes the slot s1 + 48 and the frame's 24-byte header and stops at the first shadow store. *)
Definition SRXBH_C1 : Z := AF_diginet_session_rx + 0x7c.
Definition srxbh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition srxbh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition srxbh_regions2 : smem := [srxbh_rg_slot; srxbh_rg_hdr].
Definition srxbh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_srxbh2 : sstate := mkSS SRXBH_C1 sr_atoms srxbh_regions2 None srxbh_facts2.

(* run 2b, +0x0e0 .. +0x12c: s9 (atom 25) holds the frame's shadow address; the run writes the frame's 16 shadow
   bytes; s4 (atom 20) is s and s8 (atom 24) is buf, both nonzero, so the two NULL tests go on to the cut. *)
Definition SRXBH_C2 : Z := AF_diginet_session_rx + 0xe0.
Definition srxbh_rg_sh : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 0 16 [].
Definition srxbh_facts3 : facts :=
  mkFacts [(20%nat, mkAF SRX_S SRX_S 0); (24%nat, mkAF 1 (2 ^ 64 - 1) 0);
           (25%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_srxbh3 : sstate := mkSS SRXBH_C2 sr_atoms [srxbh_rg_sh] None srxbh_facts3.

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition srxbh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* ------------------------------------------------------------------ *)
(* The walk                                                            *)
(* ------------------------------------------------------------------ *)

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A range trans_src_ok places lies below 2 ^ 63, empty or not (a heap block: below alloc_ceiling; else
   decode_rd_ok). *)
Lemma srxbh_src_hi : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_src_ok B lyc Sc W memc q n -> 0 <= n -> q + n <= 2 ^ 63.
Proof.
  intros LAWS lyc Sc W memc mdc q n HAR [(bA & nA & Hin & H1 & H2) | (_ & (_ & _ & _ & _ & _ & H63))] Hn;
    [|exact H63].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn0).
  pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. lia.
Qed.

(* ---- the symbolic states ---- *)

Lemma srxbh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_diginet_session_rx = transportb_sigma TB_diginet_session_rx.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma srxbh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) srxbh_img_regions /\
  pairwise_disjoint E srxbh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct srxbh_vals as (V1 & V93 & V0 & V94 & _).
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
  assert (R93 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 96) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold srxbh_img_regions, got_regionP, bcell_regionP, srxbh_got_uar, srxbh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E93) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 96) 0) (VAL (A_OBJ 96)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E94) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 96)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold srxbh_img_regions, got_regionP, bcell_regionP, srxbh_got_uar, srxbh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 95) (VAL (A_OBJ 95)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 96) (VAL (A_OBJ 96)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation: the 32 registers and the shadow base (atom 32). *)
Definition srxbh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma srxbh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (srxbh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold srxbh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma srxbh_ew_32 : forall regs, ew (srxbh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold srxbh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma srxbh_ew_obj : forall regs i, (i < 97)%nat -> ew (srxbh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold srxbh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma srxbh_env_img : forall regs, img_env VAL A_LIM (srxbh_E regs).
Proof. intros regs. unfold srxbh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma srxbh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SRX_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (srxbh_E regs) ss_srxbh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_rx)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_srxbh1, srxbh_regions1.
  assert (Usp : bv_unsigned (ew (srxbh_E regs) 2) = spZ regs)
    by (rewrite (srxbh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (srxbh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply srxbh_ew_32.
  destruct (srxbh_img_ok ly S W mem md (srxbh_E regs) HCELLS HAR
    (srxbh_ew_obj regs 1 ltac:(lia)) (srxbh_ew_obj regs 95 ltac:(lia))
    (srxbh_ew_obj regs 0 ltac:(lia)) (srxbh_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct srxbh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (srxbh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (srxbh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold SRX_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold srxbh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, srxbh_got_uar, srxbh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (srxbh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (srxbh_ew_obj regs 95 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (srxbh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (srxbh_ew_obj regs 96 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, SRX_FRAME.
    repeat split; first [exact I | lia].
  - unfold srxbh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The state of run 2a (after the stack malloc): the slot s1 + 48 and the frame's header. *)
Lemma srxbh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 27 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 128 <= spv -> F mod 64 = 0 ->
  (forall a, spv + 48 <= a < spv + 56 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (srxbh_E regs) ss_srxbh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXBH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R27 Hsp Hsp32 HF0 HFs HF64 Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_srxbh2, srxbh_regions2.
  assert (U2 : bv_unsigned (ew (srxbh_E regs) 2) = spv)
    by (rewrite (srxbh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (srxbh_E regs) 9) = spv)
    by (rewrite (srxbh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (srxbh_E regs) 10) = F)
    by (rewrite (srxbh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew (srxbh_E regs) 27) = SHADOW_OFF)
    by (rewrite (srxbh_ew_reg regs 27 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (srxbh_E regs) 32) = SHADOW_OFF)
    by (rewrite (srxbh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold srxbh_rg_slot, srxbh_rg_hdr, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold srxbh_rg_slot, srxbh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold srxbh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U27, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The state of run 2b: the frame's 16 shadow bytes, s = g_s in s4, buf (nonzero) in s8. *)
Lemma srxbh_entry3 : forall (W : world segs) regs mem (SH buf : Z),
  YK11.getr regs 25 = w64 SH -> SHADOW_OFF <= SH -> SH + 16 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 16 -> apresent (w_H W) mem a) ->
  YK11.getr regs 20 = w64 SRX_S -> YK11.getr regs 24 = w64 buf -> 0 < buf < 2 ^ 64 ->
  st_ok_pi segs VAL (srxbh_E regs) ss_srxbh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SRXBH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH buf R25 Hlo Hhi Hpres R20 R24 Hbuf.
  rewrite restrict_mkst_fx. unfold ss_srxbh3.
  assert (CS : SRX_S = 6157888) by reflexivity.
  assert (U25 : bv_unsigned (ew (srxbh_E regs) 25) = SH)
    by (rewrite (srxbh_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (U20 : bv_unsigned (ew (srxbh_E regs) 20) = SRX_S)
    by (rewrite (srxbh_ew_reg regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; rewrite CS; lia).
  assert (U24 : bv_unsigned (ew (srxbh_E regs) 24) = buf)
    by (rewrite (srxbh_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold srxbh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold srxbh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold srxbh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U24, U25. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF in *; lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxbh_reg HS r v H tac :=
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
Ltac srxbh_region HS i HR :=
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
Ltac srxbh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac srxbh_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac srxbh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac srxbh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    srxbh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* Drop the copies of the image-environment fact a run leaves. *)
Ltac srxbh_clear_hei HEI :=
  repeat match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma srxbh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The walk from the entry to the parse cut, with the caller's run invariants as srxb_inv and premise (3) as
   srxb_ndata. *)
Lemma srxbh_walk : @srxb_parse_at fx rc B MT -> srxb_laws B MT -> srxb_calls B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (buf now r : Z) (b : list byte) (TF : option TI.tframe) (Bw Bw' : list byte),
    @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
      mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 SRX_S -> YK11.getr regs 11 = w64 buf ->
    YK11.getr regs 12 = w64 (Z.of_nat (length b)) -> YK11.getr regs 13 = w64 now ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SRX_STK -> spZ regs <= sp0 ->
    0 <= now < 2 ^ 64 ->
    0 < buf ->
    garr8 segs (mrestrict (w_H W) memc) buf (TW.zs b) ->
    trans_src_ok B lyc Sc W memc buf (Z.of_nat (length b)) ->
    decode_off_win regs SRX_STK buf (Z.of_nat (length b)) ->
    srx_buf_off_g buf b ->
    tw_at TMAP_B (aview segs (w_H W) memc) Bw -> TW.g_fail_next Bw <= 1 ->
    TSS.diginet_session_rx_m timg_B TF Bw b now = Some (Bw', r) ->
    trans_tframe_at B lyc Sc W memc regs SRX_STK TF ->
    trans_tf_off_g TF ->
    trans_rom_view_rd W memc ->
    srx_apart TF b ->
    srxb_inv Bw -> srxb_ndata B lyc Sc W memc regs Bw b ->
    count_cid SRX_CID (frames Sc) + 1 < fs_frames SRX_CID ->
    count_cid ONANN_CID (frames Sc) < fs_frames ONANN_CID ->
    count_cid TICK_CID (frames Sc) < fs_frames TICK_CID ->
    count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID ->
    count_cid ONDATA_CID (frames Sc) + 2 < fs_frames ONDATA_CID ->
    st_nev S + k + SRX_EV <= EV_MAX ->
    SRr segs W (@cfg_at fx segs (transportb_sigma TB_diginet_session_rx) regs memc mdc)
      (@transport_srx_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b r).
Proof.
intros PARSE HLAWS HCALLS.
pose proof HLAWS as (HPCS & HCELLS & HSC & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALLS as (ASM0 & _).
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 H12 H13 Hsp16 Hlo Hhi Hnow Hbuf Hg8 Hsrc Hoff Hboff Htw Hfn Hm HTF HTFg HROM HAP
  HINV HND Hcnt HcA HcT HcS HcD Hev.
pose proof (ASM0 fx) as ASM.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hlyle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ESLO & ESHI & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (FF : SRX_FRAME = 160) by reflexivity.
assert (CS : SRX_S = 6157888) by reflexivity.
assert (HSTK0 : 176 + 2 * ESTACK <= SRX_STK).
{ unfold SRX_STK, SRX_FRAME, SRX_ALIGN.
  lazymatch goal with |- context [Z.max (2 * ESTACK) ?rest] => pose proof (Z.le_max_l (2 * ESTACK) rest) end.
  lia. }
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (HSTKLT : ly_stk_lo lyc < ly_stk_hi lyc) by lia.
(* buf, as the code tests it: below 2 ^ 63 (trans_src_ok) *)
assert (Hbuf63 : buf + Z.of_nat (length b) <= 2 ^ 63)
  by exact (srxbh_src_hi LAWS lyc Sc W memc mdc buf _ HAR Hsrc ltac:(lia)).
assert (Hpres1 : forall a, spZ regs - SRX_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (srxbh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (srxbh_E regs)) by apply srxbh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (srxbh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (srxbh_E regs) 2) = spZ regs)
  by (rewrite (srxbh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_rx)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x078 *)
paj_run_tok RUN HS HJ SHOK SRXBH_B0.
{ srxbh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
srxbh_clear_hei HEI.
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (can_sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
assert (E2' : ew (srxbh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (srxbh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
srxbh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 25952)) R1 ltac:(apply codeptr_val; exact HEI).
srxbh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (srxbh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
srxbh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
srxbh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
srxbh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
srxbh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (srxbh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
srxbh_reg HS (19%bv : bv 5) (w64 now) R19
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs 13 13%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H13).
srxbh_reg HS (20%bv : bv 5) (w64 SRX_S) R20
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
srxbh_reg HS (23%bv : bv 5) (w64 (Z.of_nat (length b))) R23
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs 12 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
srxbh_reg HS (24%bv : bv 5) (w64 buf) R24
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
srxbh_reg HS (27%bv : bv 5) (w64 SHADOW_OFF) R27
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
srxbh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) srxbh_saved -> -104 <= o <= -8).
{ intros o r0 Hin. unfold srxbh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) srxbh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. unfold srxbh_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r0))
    ltac:(srxbh_u64 (YK11.getr regs r0))).
  apply (can_field_of_region (srxbh_E regs) _ 2 (spZ regs) _ (-160) 0 (-160) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r0)) 0) (bv_unsigned (YK11.getr regs r0)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (srxbh_ew_reg regs (Z.to_nat (bv_unsigned r0)) r0 ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; srxbh_u64 (YK11.getr regs r0)
  | cbn; lia ]. }
clear HRsk.
(* +0x078: the class-1 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_1)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP SRX_CID ASM
    ltac:(unfold SRX_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 25952)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ SRX_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ SRX_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ SRX_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes SRX_CID / 8) with 16 in HFsh.
change (fs_frame_bytes SRX_CID) with 128 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc SRX_CID pos) in *.
(* the thirteen saved words, kept by the class-1 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) srxbh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho.
  rewrite <- (HSV o r0 Hin). unfold rdword.
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
assert (Q19 : YK11.getr regs2 19 = w64 now)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 SRX_S)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q23 : YK11.getr regs2 23 = w64 (Z.of_nat (length b)))
  by (transitivity (YK11.getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23]).
assert (Q24 : YK11.getr regs2 24 = w64 buf)
  by (transitivity (YK11.getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]).
assert (Q27 : YK11.getr regs2 27 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27]).
clear HS.
set (memT := ms_mem ms) in *. set (regsT := ms_regs ms) in *. clearbody memT regsT. clear ms.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - SRX_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 160 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - SRX_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - SRX_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 160 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b0 m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - SRX_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - SRX_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* +0x07c .. +0x0dc: s2 = F, the frame taken, the slot s1 + 48, the frame's header, s9 = its shadow address. *)
assert (HFsp : F + 128 <= sp1) by lia.
pose proof (srxbh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q27 ltac:(lia) Hsp1al ltac:(lia) HFsp HF64
  ltac:(intros a Ha; apply (srxbh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
clear HEI.
assert (HEI : img_env VAL A_LIM (srxbh_E regs2)) by apply srxbh_env_img.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (srxbh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9' : bv_unsigned (ew (srxbh_E regs2) 9) = sp1)
  by (rewrite (srxbh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (srxbh_E regs2) 10) = F)
  by (rewrite (srxbh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SRXBH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK SRXBH_B0.
{ srxbh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9' in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SRX_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SRX_CID) with 128.
  change (frame_addr lyc SRX_CID pos) with F. lia. }
srxbh_clear_hei HEI.
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
(* run 2a wrote the slot s1 + 48 and the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 48 <= x < sp1 + 56 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9', ?U10' in Hx;
    first [left; lia | right; lia] |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* the registers at +0x0e0 *)
assert (EF10 : ew (srxbh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (srxbh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF27 : ew (srxbh_E regs2) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (srxbh_ew_reg regs2 27 27%bv eq_refl); exact Q27).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
srxbh_reg HS (25%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T25
  ltac:(exact (can_denot_shadow (srxbh_E regs2) 10 27 F SHADOW_OFF EF10 EF27 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
srxbh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. srxbh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
srxbh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. srxbh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
srxbh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. srxbh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
srxbh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. srxbh_kreg HS regs2 (23%bv : bv 5) 23%nat Q23 T23.
srxbh_kreg HS regs2 (24%bv : bv 5) 24%nat Q24 T24. srxbh_kreg HS regs2 (27%bv : bv 5) 27%nat Q27 T27.
srxbh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
srxbh_reg HS (26%bv : bv 5) (w64 F) T26
  ltac:(cbn [sv_denot]; rewrite (srxbh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* +0x0e0 .. +0x12c: the frame's shadow bytes, a0 = -1, the two NULL tests, up to the parse cut. *)
pmkst HS.
set (ms3 := ms) in *. clearbody ms3. clear HS.
assert (Hbuf64 : 0 < buf < 2 ^ 64) by lia.
pose proof (srxbh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) buf T25
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))
  T20 T24 Hbuf64) as HS.
clear HEI.
assert (HEI : img_env VAL A_LIM (srxbh_E (ms_regs ms3))) by apply srxbh_env_img.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (srxbh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U25 : bv_unsigned (ew (srxbh_E (ms_regs ms3)) 25) = SHADOW_OFF + F / 8)
  by (rewrite (srxbh_ew_reg (ms_regs ms3) 25 25%bv eq_refl), T25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXBH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK SRXBH_B0 SRXB_PARSE.
{ srxbh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SRX_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SRX_CID / 8) with 16.
  change (frame_addr lyc SRX_CID pos) with F. unfold shadow_addr. lia. }
srxbh_clear_hei HEI.
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msF := msx) in * end.
(* run 2b wrote the frame's 16 shadow bytes only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) ->
  aview segs (w_H W) (ms_mem msF) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 16) HFr2b);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U25 in Hx; lia |]).
  destruct Hin. }
(* the shadow bytes of f (granules 4 .. 11) are 0 *)
srxbh_region HS 0%nat HRsh.
assert (SZ5 : forall i, 4 <= i < 12 -> aview segs (w_H W) (ms_mem msF) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  match goal with |- aview _ _ _ (_ + ?o) = Some 0 =>
    exact (can_aview_of_val1 _ _ _ _ _ (can_field_of_region (srxbh_E (ms_regs ms3)) _ 25 _ _ 0 16 0 16 o 1%N
      (SLit 0) 0 HRsh U25 ltac:(srxbh_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))) end. }
clear HRsh.
(* the registers at the cut *)
srxbh_kreg HS (ms_regs ms3) (2%bv : bv 5) 2%nat T2 Y2. srxbh_kreg HS (ms_regs ms3) (3%bv : bv 5) 3%nat T3 Y3.
srxbh_kreg HS (ms_regs ms3) (4%bv : bv 5) 4%nat T4 Y4. srxbh_kreg HS (ms_regs ms3) (8%bv : bv 5) 8%nat T8 Y8.
srxbh_kreg HS (ms_regs ms3) (9%bv : bv 5) 9%nat T9 Y9. srxbh_kreg HS (ms_regs ms3) (18%bv : bv 5) 18%nat T18 Y18.
srxbh_kreg HS (ms_regs ms3) (19%bv : bv 5) 19%nat T19 Y19. srxbh_kreg HS (ms_regs ms3) (20%bv : bv 5) 20%nat T20 Y20.
srxbh_kreg HS (ms_regs ms3) (23%bv : bv 5) 23%nat T23 Y23. srxbh_kreg HS (ms_regs ms3) (24%bv : bv 5) 24%nat T24 Y24.
srxbh_kreg HS (ms_regs ms3) (25%bv : bv 5) 25%nat T25 Y25. srxbh_kreg HS (ms_regs ms3) (26%bv : bv 5) 26%nat T26 Y26.
srxbh_kreg HS (ms_regs ms3) (27%bv : bv 5) 27%nat T27 Y27.
(* the cut's machine state, +0x130 *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SRXB_PARSE)) mm rom) mdx) Q) end.
(* ---- the facts the cut carries, at the memory of +0x130 ---- *)
set (m5 := ms_mem msF) in *.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR5.
(* every byte outside the three written ranges is the one the stack malloc left *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16 \/ sp1 + 48 <= a < sp1 + 56) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2b). exact (apresent_grows _ _ _ a G2a Ha). }
(* the bytes of G: the frame is outside the image, the shadow band and the stack above G *)
assert (NGF : forall a, F <= a < F + 128 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ SRX_CID pos a HAR2 Hin2 ltac:(change (fs_frame_bytes SRX_CID) with 128; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (NGS : forall a, F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16 \/
    sp1 + 48 <= a < sp1 + 56 -> ~ inG TG.G_HARNESS_B a).
{ intros a [X | [X | X]]; [apply NGF; lia | apply NGH; unfold SHADOW_OFF in *; lia | apply NGH; unfold SHADOW_OFF; lia]. }
assert (GK5 : gx_kept segs TG.G_HARNESS_B W memc W m5).
{ intros a Hg. rewrite <- (GK2 a Hg).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros X. exact (NGS a X Hg). }
(* what the call keeps, at m5 *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - SRX_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - SRX_STK) (spZ regs) SRX_CID pos F (flag_addr lyc SRX_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16 \/ sp1 + 48 <= a < sp1 + 56)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes SRX_CID) with 128. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes SRX_CID / 8) with 16. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
(* the world relation at Bw *)
assert (Htw5 : tw_at TMAP_B (aview segs (w_H W) m5) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n0 i Hin Hi.
  apply GK5. unfold inG. apply Exists_exists. exists (b0, n0). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
(* the thirteen saved words, at m5 *)
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) srxbh_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho. rewrite <- (HSV2 o r0 Hin).
  apply rdword_ext. intros i Hi. apply KF5; [lia|].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRXB_SAVED).
{ unfold SRXB_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold srxbh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
(* the frame's last word, at m5 *)
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + SRXB_FBYTES - 8) = Some (flag_addr lyc SRX_CID pos)).
{ rewrite <- Hflag. unfold SRXB_FBYTES. apply rdword_ext. intros i Hi. apply KF5; [lia|].
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* the class-1 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r0 ?sk ?sg ?b0 ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : srxb_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F lyc S2 W m5 md5 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj _ (conj HFW5 HFL5)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - rewrite srx_ev_zero. lia.
  - rewrite Eab2. apply Permutation_refl.
  - apply (acall_kept_g_weaken segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - SRX_STK) (spZ regs)
      (fun _ => False) (srx_wr b)); [tauto | exact KG5]. }
(* the reads the later code hands to its callees, at the cut's state (TransportGNoticeB.v trans_src_ok_kept_gx /
   trans_tframe_at_kept_gx: the cut's state has the own frame on top of the entry's frames, nothing written outside
   the call's window and the own frame, every byte of G kept) *)
assert (Hbl5 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B lyc S2)) by (intros bm Hb; rewrite Eab2; exact Hb).
assert (Hfr5 : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfrs2; right; exact Hf).
assert (GKX5 : gx_kept_ex segs TG.G_HARNESS_B (fun _ => False) W memc W m5) by (intros a Hg _; exact (GK5 a Hg)).
assert (HnEs : forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ (fun _ : Z => False) a) by (intros a _ H; exact H).
assert (HRD5 : srxb_rd B lyc S2 W m5 regs buf b TF Bw).
{ destruct (trans_src_ok_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W m5 md5 (spZ regs - SRX_STK) (spZ regs)
    (fun _ => False) buf (Z.of_nat (length b)) HAR HAR5 Hbl5 Hfr5 (fun c p => eq_refl) eq_refl eq_refl HSTKLT KG5 GKX5
    (fun a _ H => H) HnEs Hoff Hsrc ltac:(lia)) as [Hsrc5 KVb].
  refine (conj _ (conj Hsrc5 (conj _ (conj _ _)))).
  - eapply garr8_frame; [exact Hg8|]. intros a Ha. unfold TW.zs in Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). apply KVb. exact Ha.
  - exact (trans_tframe_at_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W m5 md5 (fun _ => False) regs regs
      SRX_STK SRX_STK TF HAR HAR5 Hbl5 Hfr5 (fun c p => eq_refl) eq_refl eq_refl HSTKLT KG5 GKX5
      (fun fr _ a _ H => H) HnEs ltac:(lia) ltac:(lia) HTF).
  - intros a Ha. rewrite <- (HROM a Ha). pose proof KG5 as (_ & _ & K3 & _).
    destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
    apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
    intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
    unfold TransportGB.G_HARNESS_B_LO in Gh. lia.
  - intros H0 HM HK HQ HSt HC HD HKA.
    destruct (HND H0 HM HK HQ HSt HC HD HKA) as [Hs Ho].
    destruct (DSpec.fr_code_ok b H0) as (_ & _ & Hnb & _).
    split; [|exact Ho].
    exact (proj1 (trans_src_ok_kept_gx B LAWS HRU HRE lyc Sc W memc mdc lyc S2 W m5 md5 (spZ regs - SRX_STK)
      (spZ regs) (fun _ => False) _ _ HAR HAR5 Hbl5 Hfr5 (fun c p => eq_refl) eq_refl eq_refl HSTKLT KG5 GKX5
      (fun a _ H => H) HnEs Ho Hs ltac:(unfold DSpec.fr_body_len; lia))). }
(* f's 64 bytes, usable *)
assert (HDR5 : decode_rd_ok W m5 (F + SRX_F) FRAME_F_SIZE).
{ unfold SRX_F, FRAME_F_SIZE.
  destruct (al_frames _ _ LAWS _ _ _ _ _ SRX_CID pos HAR5 Hin2) as (_ & _ & HFb5 & HFsh5).
  change (fs_frame_bytes SRX_CID / 8) with 16 in HFsh5. change (fs_frame_bytes SRX_CID) with 128 in HFb5.
  change (frame_addr lyc SRX_CID pos) with F in HFb5, HFsh5.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply can_aview_vis. exact (proj1 (HFb5 a ltac:(lia))).
  - assert (HF8 : F mod 8 = 0).
    { apply (proj2 (Z.mod_divide F 8 ltac:(lia))). exists (8 * (F / 64)).
      pose proof (Z.div_mod F 64 ltac:(lia)) as D. lia. }
    apply (TGNA.frame_ra_zero _ F (F + 32) 64 4 12); try lia. exact SZ5.
  - apply (TGNA.frame_hull_vis _ F 128 (F + 32) 64);
      [lia | first [exact HF64 | lia] | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis. exact (proj1 (HFsh5 i Hi)).
  - apply (amem_range_sub_app F 128 (F + 32) 64 HFapp HFc); lia.
  - lia.
  - lia. }
(* the record facts and the caller's facts, as the cut states them *)
assert (HFIX : srxb_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F).
{ unfold srxb_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj H12 (conj H13
    (conj Hsp16 (conj Hlo (conj Hhi (conj Hnow (conj Hbuf (conj Hg8 (conj Hsrc (conj Hoff (conj Hboff
    (conj Htw (conj Hfn (conj Hm (conj HTF (conj HTFg (conj HROM (conj HAP (conj HINV (conj HND
    (conj Hcnt (conj HcA (conj HcT (conj HcS (conj HcD (conj Hev
    (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp)))))))))))))))))))))))))))))))))))))).
  unfold sp1, SRX_FRAME. replace (spZ regs - 160) with (spZ regs + -160) by lia. reflexivity. }
apply (PARSE HLAWS HCALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F
  lyc S2 W m5 md5 0 (ms_regs msF) HFIX CUR5 HRD5 HDR5 Htw5).
unfold srxb_regs_parse, srxb_regs_core.
refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y19 (conj Y20 (conj Y25 (conj Y26 Y27))))))))))
  (conj Y23 Y24)).
- rewrite Y3. symmetry. exact Hgp.
- rewrite Y4. symmetry. exact Htp.
Qed.
End sh.

(* The head piece of the walk of diginet_session_rx (SrxBCut.v srxb_head_stmt), at every machine, run ceiling, record
   and meter. *)
Theorem srxb_head_ok : forall fx rc B MT, @srxb_head_stmt fx rc B MT.
Proof.
intros fx rc B MT PARSE.
unfold transport_diginet_session_rx_cg_holds_stmt.
intros HPCS HCELLS HSC HGU HGE HRU HRE LAWS MTL MTF SMP ASF FFL ASM0 FP0 BC0 LF0 CP0 AN0 AK0 LO0 DA0 TI0.
unfold transport_diginet_session_rx_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 H12 H13 Hsp16 Hlo Hhi Hnow Hbuf Hg8 Hsrc Hoff Hboff Htw Hfn Hm HTF HTFg HROM HAP
  I1 I2 IQ I4 IN I5a I5b H3 Hcnt HcA HcT HcS HcD Hev.
assert (HL : srxb_laws B MT).
{ exact (conj HPCS (conj HCELLS (conj HSC (conj HGU (conj HGE (conj HRU (conj HRE (conj LAWS (conj MTL (conj MTF
    (conj SMP (conj ASF (conj FFL (conj (G_HARNESS_gx_ok B HGU) (G_HARNESS_gx_noerrno B HGE))))))))))))))). }
assert (HC : srxb_calls B MT) by exact (conj ASM0 (conj FP0 (conj BC0 (conj LF0 (conj CP0 (conj AN0 (conj AK0
  (conj LO0 (conj DA0 TI0))))))))).
assert (HINV : srxb_inv Bw) by exact (conj I1 (conj I2 (conj I4 (conj I5a (conj I5b (conj IN IQ)))))).
assert (HND : srxb_ndata B lyc Sc W memc regs Bw b) by exact H3.
exact (@srxbh_walk fx rc B MT PARSE HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF
  Bw Bw' HJe Hra Hra4 Hgp Htp H10 H11 H12 H13 Hsp16 Hlo Hhi Hnow Hbuf Hg8 Hsrc Hoff Hboff Htw Hfn Hm HTF HTFg HROM
  HAP HINV HND Hcnt HcA HcT HcS HcD Hev).
Qed.
