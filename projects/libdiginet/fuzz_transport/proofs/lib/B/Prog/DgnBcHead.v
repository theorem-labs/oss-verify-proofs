(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 684 of its 966 lines of code are new or changed and 857 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the entry piece of reac-repacer/fuzz_uci's lib/A/Prog/check_clamp_cgW.v (cc_entry, cc_entry2 - cc_entry4, cc_reg, cc_kp_geom, the class-1 stack malloc, the leaf call and the saved words carried across them) ported to libdiginet/fuzz_frame's diginet_body_check in image A: this unit's listing, image, cells and kit (lib/A/Prog/CanKit.v, CanLeafb.v), the class-2 frame, the leaf diginet_cursor_init, and the loop's cut statement bc_loop_stmt (lib/A/Prog/DgnBcCut.v) in place of the comparisons and the release. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A walk lib/A/Prog/DgnBcHead.v: module paths lib/B (the image-B core's YB1v / YE2k / YF0x / YCbq / YC5d / YImgTop, the listing names of lib/B/Prog/FrameBSyms.v / FrameBList.v / FrameBPa.v / FrameBImg.v / FrameBPaLib.v, the B kit lib/B/Prog/CanKit.v / CanLeafb.v / FrameFevt.v, the B statement texts), the listing instance PI_frameb, image B's two return addresses (+0x74 = 12764, +0x15c = 12996 from the listing's base), the stack budget FRAME_BC_STK = 4272 (image B's diginet_msg_next uses its own 64-byte frame), and the leaf diginet_cursor_init's image-B premise c mod 8 = 0 (c = F + 32, F mod 32 = 0). *)
(* DgnBcHead (image B): Lemma bc_holds_of : bc_loop_stmt -> decode_diginet_body_check_cg_holds_stmt.
   The walk from the entry of diginet_body_check (fuzz_decode.asan-ubsan 0x82970, AF_diginet_body_check = 0x2db0 of
   lib/B/Prog/DgnDecodeBList.v) to the loop head +0x16c, in four runs of the position-abstract engine and two calls. Image
   B's code here is image A's, instruction for instruction, up to relocation (no UBSan guard before +0x16c):
     +0x000 .. +0x070  the frame (`addi sp,sp,-160`, `sd zero,0(sp)`, the 13 saves), s0, the 32-byte realign into s1,
                       s2 = len, the two runtime cells (the flag word 1, so `beqz a2` is not taken), s9 = the shadow
                       base, s3 = body, `li a0,192` and `jal __asan_stack_malloc_2` (the statement's
                       astack_malloc_realizes premise, through CanKit.v can_stack_malloc_at);
     +0x074 .. +0x0dc  the class-2 frame F in a0 (F >= 4096, so `bnez a0` skips the real-stack arm), the slots
                       s1 + 24 and s1 + 48, s5 = F + 32, s6 = F + 96, the frame's 24-byte header and s7 = the frame's
                       shadow address, up to the first shadow store;
     +0x0e0 .. +0x158  the frame's 24 shadow bytes (granules 4 .. 7 and 12 .. 16 marked usable), the slot s1 + 16 = len
                       and `jal diginet_cursor_init` (the statement's decode_leaf_wr_at premise, through CanLeafb.v
                       can_leafb_journal; its premise c mod 8 = 0 from F mod 32 = 0);
     +0x15c .. +0x168  s10 = 1, s11 = 0xf0, s2 = 3, s4 = 0x13, then the loop's cut statement at +0x16c. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib DgnTransportBCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Cells Step Frame ExecF Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg CanKit CanLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_body_check_cg DgnBcCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_cursor_init_cg diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit AsanKA TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_cursor_init_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LCI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_cg.
Module BMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cg.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module FFv := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.TransportFevt.
Module PCur := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_cursor_init_c.
Module ACI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_cursor_init_c.
Module SYP0l := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The shadow band the token engine is told about, and the empty span for the runs that read no shadow byte. *)
Definition BCH_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition BCH_B0 : Z * Z := (0, 0).

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition bch_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The use-after-return flag: its GOT word (object 0) holds the cell (object 18), which holds 1 in every state. *)
Definition bch_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 96) 0))].
Definition bch_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition bch_img_regions : smem := [got_regionP; bcell_regionP 32; bch_got_uar; bch_uar_cell].
Definition bch_regions : smem := stack_region TRANS_BC_FRAME :: bch_img_regions.
Definition bch_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_bch : sstate := mkSS AF_diginet_body_check sr_atoms bch_regions None bch_facts.

(* +0x074, after the stack malloc: the frame in a0 (atom 10), the realigned sp in s1 (atom 9), the shadow base in s9
   (atom 25). The run writes the slots s1 + 24 and s1 + 48 and the frame's 24-byte header. *)
Definition bch_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 16 56 16 56 [].
Definition bch_rg_frame : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition bch_regions2 : smem := [bch_rg_slot; bch_rg_frame].
Definition bch_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 5); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition BCH_C1 : Z := AF_diginet_body_check + 0x74.
Definition ss_bch2 : sstate := mkSS BCH_C1 sr_atoms bch_regions2 None bch_facts2.

(* +0x0e0: s7 (atom 23) holds the frame's shadow address; the run writes the frame's 24 shadow bytes and the slot
   s1 + 16. *)
Definition bch_rg_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 24 0 24 [].
Definition bch_rg_len : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition bch_regions3 : smem := [bch_rg_sh; bch_rg_len].
Definition bch_facts3 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (23%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition BCH_C2 : Z := AF_diginet_body_check + 0xe0.
Definition ss_bch3 : sstate := mkSS BCH_C2 sr_atoms bch_regions3 None bch_facts3.

(* +0x15c, after the leaf: four register loads, no region, no fact. *)
Definition BCH_C3 : Z := AF_diginet_body_check + 0x15c.
Definition ss_bch4 : sstate := mkSS BCH_C3 sr_atoms [] None (mkFacts [] [] []).

Section bch. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma bch_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  VAL A_TEXT = transportb_sigma TB_diginet_body_check - AF_diginet_body_check.
Proof. vm_compute. repeat split. Qed.

(* An eight-byte word of the view kept by a step that keeps its eight bytes. *)
Lemma bch_rdword_frame : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a Hk. unfold rdword.
  pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  rewrite K0, (Hk 1 ltac:(lia)), (Hk 2 ltac:(lia)), (Hk 3 ltac:(lia)), (Hk 4 ltac:(lia)),
          (Hk 5 ltac:(lia)), (Hk 6 ltac:(lia)), (Hk 7 ltac:(lia)). reflexivity.
Qed.

Lemma bch_aview_out : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview segs H m' a = aview segs H m a.
Proof.
  intros E rs H m m' a HF Ha Hno. apply aview_eq_of. apply HF.
  rewrite unsigned_lit_small by lia. exact Hno.
Qed.

(* x / 8 of an address above an eight-aligned frame. *)
Lemma bch_div8 : forall F x, F mod 8 = 0 -> x / 8 = F / 8 + (x - F) / 8.
Proof.
  intros F x HF. pose proof (Z.div_mod F 8 ltac:(lia)) as D.
  replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia.
Qed.

(* The four image regions hold what decode_cells says they hold, at any AR state. *)
Lemma bch_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) bch_img_regions /\
  pairwise_disjoint E bch_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E17 E0 E18 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct bch_vals as (V1 & V17 & V0 & V18 & _).
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
  assert (R17 : 0 <= VAL (A_OBJ 95) < 2 ^ 47) by (rewrite V17; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R18 : 0 <= VAL (A_OBJ 96) < 2 ^ 47) by (rewrite V18; unfold FCells.UAR; lia).
  split.
  - unfold bch_img_regions, got_regionP, bcell_regionP, bch_got_uar, bch_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V17. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E17) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V17. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 96) 0) (VAL (A_OBJ 96)));
      [cbn [sv_denot]; rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V18. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E18) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 96)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V18. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold bch_img_regions, got_regionP, bcell_regionP, bch_got_uar, bch_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 95) (VAL (A_OBJ 95)) E17),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 96) (VAL (A_OBJ 96)) E18) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V17, V0, V18. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The environment of the walk: the thirty-two registers as atoms 0 .. 31, the shadow base as atom 32, and the
   image's own values above A_TEXT. *)
Definition bch_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma bch_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (bch_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold bch_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma bch_ew_32 : forall regs, ew (bch_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof.
  intros regs. unfold bch_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
Qed.

Lemma bch_ew_obj : forall regs i, (i < 97)%nat -> ew (bch_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold bch_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

Lemma bch_env_img : forall regs, img_env VAL A_LIM (bch_E regs).
Proof. intros regs. unfold bch_E. apply Eimg_env. Qed.

(* The symbolic state the walk starts from (the saves go into the stack region). *)
Lemma bch_entry : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - TRANS_BC_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (bch_E regs) ss_bch
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_body_check)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_bch, bch_regions.
  assert (Usp : bv_unsigned (ew (bch_E regs) 2) = spZ regs)
    by (rewrite (bch_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (bch_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply bch_ew_32.
  destruct (bch_img_ok ly S W mem md (bch_E regs) HCELLS HAR
    (bch_ew_obj regs 1 ltac:(lia)) (bch_ew_obj regs 95 ltac:(lia))
    (bch_ew_obj regs 0 ltac:(lia)) (bch_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct bch_vals as (V1 & V17 & V0 & V18 & _).
  assert (VB : forall n v0, ew (bch_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (bch_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold TRANS_BC_FRAME.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. unfold TRANS_BC_FRAME. lia.
  - unfold bch_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, bch_got_uar, bch_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (bch_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (bch_ew_obj regs 95 ltac:(lia)))
      by (rewrite V17; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (bch_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (bch_ew_obj regs 96 ltac:(lia)))
      by (rewrite V18; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V17, V0, V18. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, TRANS_BC_FRAME.
    repeat split; first [exact I | lia].
  - unfold bch_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma bch_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= spv - 4096 -> F mod 32 = 0 ->
  (forall a, spv + 16 <= a < spv + 56 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (bch_E regs) ss_bch2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BCH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R25 Hsp Hsp32 HF0 HFs HF32 Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_bch2, bch_regions2.
  assert (U2 : bv_unsigned (ew (bch_E regs) 2) = spv)
    by (rewrite (bch_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (bch_E regs) 9) = spv)
    by (rewrite (bch_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (bch_E regs) 10) = F)
    by (rewrite (bch_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (bch_E regs) 25) = SHADOW_OFF)
    by (rewrite (bch_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (bch_E regs) 32) = SHADOW_OFF)
    by (rewrite (bch_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold bch_rg_slot, bch_rg_frame, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold bch_rg_slot, bch_rg_frame, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold bch_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U25, U32.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma bch_entry3 : forall (W : world segs) regs mem (SH spv : Z),
  YK11.getr regs 23 = w64 SH -> SHADOW_OFF <= SH -> SH + 24 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 24 -> apresent (w_H W) mem a) ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 16 <= a < spv + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (bch_E regs) ss_bch3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BCH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH spv R23 Hlo Hhi Hpres R9 Hsp Hsp32 Hpslot.
  rewrite restrict_mkst_fx. unfold ss_bch3, bch_regions3.
  assert (U23 : bv_unsigned (ew (bch_E regs) 23) = SH)
    by (rewrite (bch_ew_reg regs 23 23%bv eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (U9 : bv_unsigned (ew (bch_E regs) 9) = spv)
    by (rewrite (bch_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold bch_rg_sh, bch_rg_len, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U23. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
  - apply pairwise_disjoint_of_extents.
    unfold bch_rg_sh, bch_rg_len, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U23, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold bch_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U23.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma bch_entry4 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (bch_E regs) ss_bch4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BCH_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_bch4.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac bch_reg HS r v H tac :=
  lazymatch type of HS with
  | SYP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac bch_region HS i HR :=
  lazymatch type of HS with
  | SYP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac bch_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac bch_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; bch_ro_rec ].
Ltac bch_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* Where the thirteen saved words (spr - 104 .. spr), the frame's flag word (F + 248 .. F + 256) and the two slots
   s1 + 16 and s1 + 24 lie: below 2 ^ 64, outside the frame's header, its 24 shadow bytes, the cursor [F + 32,
   F + 57) and the 4096 bytes below sp1 that a callee of this function may use. *)
Lemma bch_kp_geom : forall spr sp1 F a,
  2 ^ 46 <= spr <= 2 ^ 47 -> spr - 176 <= sp1 <= spr - 160 -> 4096 <= F -> F + 256 <= sp1 - 4096 ->
  in_app F 256 ->
  spr - 104 <= a < spr \/ F + 248 <= a < F + 256 \/ sp1 + 16 <= a < sp1 + 32 ->
  0 <= a < 2 ^ 64 /\ ~ (F + 0 <= a < F + 24) /\
  ~ (SHADOW_OFF + F / 8 + 0 <= a < SHADOW_OFF + F / 8 + 24) /\ ~ (F + 32 <= a < F + 57) /\
  ~ (sp1 - 4096 <= a < sp1).
Proof.
  intros spr sp1 F a Hs H1 HF0 HFs Happ Ha.
  assert (HF8 : 0 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct Happ as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg in *; unfold SHADOW_OFF;
  repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Lemma bc_holds_of : @bc_loop_stmt fx rc B MT -> @transport_diginet_body_check_cg_holds_stmt fx rc B MT.
Proof.
intros LOOP.
unfold transport_diginet_body_check_cg_holds_stmt.
intros HPCS HCELLS HGU HGE HRU HRE LAWS MTL MTF SMP ASF FFL ASM0 LEAF0 MN0.
unfold transport_diginet_body_check_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs body bb
  HJ0 Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hbody0 Hsrc0 Hbw0 Hgarr0 Hcnt Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJ0 as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres0 & Hstk & _ & HQT).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* body as the code uses it: when bb is not empty trans_src_ok places it below 2 ^ 47 (trans_src_ok_place); when bb
   is empty only its register value matters (diginet_cursor_init stores it, no byte at body is read), so the walk
   takes body mod 2 ^ 64, the same register value. *)
assert (NB : exists body', YK11.getr regs 10 = w64 body' /\ 0 <= body' < 2 ^ 64 /\
  Z.of_nat (length bb) <= 2 ^ 47 /\ (body' <> 0 \/ length bb = 0%nat) /\
  ((0 < length bb)%nat -> trans_src_ok B lyc Sc W memc body' (Z.of_nat (length bb)) /\
     decode_off_win regs TRANS_BC_STK body' (Z.of_nat (length bb))) /\
  garr8 segs (mrestrict (w_H W) memc) body' (map bz bb)).
{ destruct (Nat.eq_dec (length bb) 0) as [E0|E0].
  - exists (body mod 2 ^ 64).
    split.
    { rewrite H10. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
    split; [apply Z.mod_pos_bound; lia|]. split; [lia|]. split; [right; exact E0|].
    split; [intros H; lia|].
    apply length_zero_iff_nil in E0. rewrite E0. apply garr8_nil.
  - exists body. split; [exact H10|].
    pose proof (trans_src_ok_place B LAWS lyc Sc W memc mdc body (Z.of_nat (length bb)) HAR
                  (Hsrc0 ltac:(lia)) ltac:(lia)) as Hp.
    split; [destruct Hp as [Hp|Hp]; lia|].
    split; [destruct Hp as [Hp|Hp]; lia|].
    split; [exact Hbody0|].
    split; [intros H; exact (conj (Hsrc0 H) (Hbw0 H))|].
    exact Hgarr0. }
destruct NB as (body' & H10' & Hb64 & Hlen47 & Hbody & Hblk & Hgarr).
clear H10 Hbody0 Hsrc0 Hbw0 Hgarr0. clear body. rename body' into body. rename H10' into H10.
assert (Hbc : TRANS_BC_STK = 4272) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hbf : TRANS_BC_FRAME = 160) by reflexivity.
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - TRANS_BC_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
(* the length of the body *)
set (len := Z.of_nat (length bb)) in *.
assert (Elen : len = Z.of_nat (length bb)) by reflexivity.
assert (Hlen0 : 0 <= len) by lia.
(* The walk's own journal: the caller's, re-based at this call's sp with this function's stack budget. *)
assert (HJ1 : @ajournal rc tfib_sink_head segs B TRANS_BC_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0).
{ eapply (ajournal_sub_init segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k TRANS_BC_STK (spZ regs) []
    (spZ regs - sp0) HJ0);
  [lia | rewrite Zminus_mod, Hsp16, Hsp0a; reflexivity | lia | lia | lia]. }
pose proof (bch_entry lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hspr Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (bch_E regs)) by apply bch_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (bch_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (bch_E regs) 2) = spZ regs)
  by (rewrite (bch_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (paj_run (SK := tfib_sink_head) (PI := PI_transportb) B LAWS) as RUN.
pose proof (paj_run_to (SK := tfib_sink_head) (PI := PI_transportb) B LAWS) as RUNTO.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_body_check)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* +0x000 .. +0x070: the frame, the saves, s0, the realign into s1, s2 = len, the two runtime cells, s9, s3 = body,
   the `beqz a2` not taken, `li a0,192` and `jal __asan_stack_malloc_2`. *)
paj_run_tok RUN HS HJ1 SHOK BCH_Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack _ _ _ _ _ _ _ _ _ _ 2%nat);
  [reflexivity | rewrite Usp; reflexivity | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  bch_ro_rec. }
(* sp after `addi sp,sp,-160` and `andi sp,sp,-32`. *)
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (can_sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
assert (E2' : ew (bch_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (bch_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
bch_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 44752)) R1 ltac:(apply codeptr_val; exact HEI).
bch_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (bch_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
bch_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
bch_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
bch_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
bch_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (bch_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
bch_reg HS (18%bv : bv 5) (w64 len) R18
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
bch_reg HS (19%bv : bv 5) (w64 body) R19
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
bch_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) R25
  ltac:(cbn [sv_denot]; rewrite (bch_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
bch_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) bch_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold bch_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) bch_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold bch_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(bch_u64 (YK11.getr regs r))).
  apply (can_field_of_region (bch_E regs) _ 2 (spZ regs) _ (-160) 0 (-160) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (bch_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; bch_u64 (YK11.getr regs r)
  | cbn; lia ]. }
(* +0x070: the class-2 stack-malloc call, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_2)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (can_stack_malloc_at segs B LAWS transportb_segs_low SMP TRANS_BC_CID ASM ltac:(unfold TRANS_BC_CID; lia)
    W rg mm TRANS_BC_STK (spZ regs) (@nil (Z * Z)) lyc Sc W memc mdc (@nil (Z * Z)) lyc Sc mdx 0
    (sp1 - spZ regs) (Z_to_bv 64 (BASE + 44752)) HJ1) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp16. reflexivity.
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
(* The class-2 frame the call handed back: its address, its alignment and its bytes. *)
pose proof (proj1 HJ2) as HAR2.
assert (Hin2 : In (TRANS_BC_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ TRANS_BC_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ TRANS_BC_CID pos HAR2 Hin2) as (HF0 & HFc & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _).
pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & _).
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) bch_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  assert (Hfr : forall i, 0 <= i < 8 ->
    aview segs (w_H W) mem2 (spZ regs + o + i) = aview segs (w_H W) (ms_mem ms) (spZ regs + o + i)).
  { intros i Hi. apply (proj1 HK1); lia. }
  rewrite (bch_rdword_frame _ _ _ Hfr). exact (HSV o r Hin). }
change (fs_frame_bytes TRANS_BC_CID / 8) with 32 in HFsh.
change (fs_frame_bytes TRANS_BC_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc TRANS_BC_CID pos) in *.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
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
assert (Q18 : YK11.getr regs2 18 = w64 len)
  by (transitivity (YK11.getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact R18]).
assert (Q19 : YK11.getr regs2 19 = w64 body)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q25 : YK11.getr regs2 25 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
assert (HFsp : F + 256 <= sp1 - 4096) by lia.
assert (GF0 : 4096 <= F) by lia.
pose proof (bch_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q25 ltac:(lia) Hsp1al ltac:(lia) HFsp HFal
  ltac:(intros a Ha; apply Hpres2; lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS2.
clear HS. rename HS2 into HS.
assert (HEI2 : img_env VAL A_LIM (bch_E regs2)) by apply bch_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (bch_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9' : bv_unsigned (ew (bch_E regs2) 9) = sp1)
  by (rewrite (bch_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (bch_E regs2) 10) = F)
  by (rewrite (bch_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; unfold w64; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BCH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
(* +0x074 .. +0x0dc: the frame taken, the slots s1 + 24 and s1 + 48, the frame's 24-byte header and the shadow
   address in s7, up to the first shadow store at +0x0e0. *)
paj_run_tok RUN HS HJ2 SHOK BCH_B0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - spZ regs));
  [reflexivity | rewrite U9'; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10' | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
  right; right; right. exists TRANS_BC_CID, pos. split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes TRANS_BC_CID) with 256.
  change (frame_addr lyc TRANS_BC_CID pos) with F. lia. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms3 := msx) in * end.
(* The thirteen saved words and the flag word, kept by this run: it writes the slots and the frame's header. *)
assert (KA : forall a, spZ regs - 104 <= a < spZ regs \/ F + 248 <= a < F + 256 ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
{ intros a Ha.
  destruct (bch_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp ltac:(lia)) as (G0 & G1 & _ & _ & _).
  match goal with HFx : frame_of _ (ss_mem ss_bch2) (mrestrict (w_H W) mem2) (mrestrict (w_H W) _) |- _ =>
    apply (bch_aview_out _ _ (w_H W) mem2 _ a HFx G0) end.
  intros (r & Hr & Hb). unfold ss_bch2, bch_regions2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]];
  cbn [bch_rg_slot bch_rg_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
  - rewrite U9' in Hb. lia.
  - rewrite U10' in Hb. lia. }
(* the slot s1 + 24 holds the frame (`sd a0,24(s1)` at +0x0a0) *)
bch_region HS 0%nat HRsl.
assert (HSF3 : rdword (aview segs (w_H W) (ms_mem ms3)) (sp1 + 24) = Some F).
{ apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms3) (sp1 + 24) F ltac:(lia)).
  apply (can_field_of_region (bch_E regs2) _ 9 sp1 _ 16 56 16 56 24 8%N (SOff 10 0) F HRsl U9');
  [ bch_in
  | cbn [sv_denot]; rewrite (bch_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
    rewrite (unsigned_lit_small F ltac:(lia)), Z.add_0_r; reflexivity
  | cbn; lia | cbn; lia ]. }
(* The registers at +0x0e0: c (s5), m (s6), the frame's shadow address (s7) and the frame (s8). *)
assert (EF10 : ew (bch_E regs2) 10 = Z_to_bv 64 F)
  by (rewrite (bch_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF25 : ew (bch_E regs2) 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (bch_ew_reg regs2 25 25%bv eq_refl); exact Q25).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
bch_reg HS (21%bv : bv 5) (Z_to_bv 64 (F + 32)) T21
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
        rewrite (unsigned_lit_small F HFbv); reflexivity).
bch_reg HS (22%bv : bv 5) (Z_to_bv 64 (F + 96)) T22
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
        rewrite (unsigned_lit_small F HFbv); reflexivity).
bch_reg HS (23%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T23
  ltac:(exact (can_denot_shadow (bch_E regs2) 10 25 F SHADOW_OFF EF10 EF25 HFbv
               ltac:(unfold SHADOW_OFF; lia)
               ltac:(pose proof (Z.div_lt_upper_bound F 8 (2 ^ 61) ltac:(lia) ltac:(lia)); unfold SHADOW_OFF; lia))).
bch_reg HS (24%bv : bv 5) (Z_to_bv 64 F) T24
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 10 10%bv eq_refl), Ha0; unfold w64;
        rewrite (unsigned_lit_small F HFbv), Z.add_0_r; reflexivity).
bch_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q2).
bch_reg HS (3%bv : bv 5) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q3).
bch_reg HS (4%bv : bv 5) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q4).
bch_reg HS (8%bv : bv 5) (w64 (spZ regs)) T8
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 8 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q8).
bch_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) T9
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 9 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q9).
bch_reg HS (18%bv : bv 5) (w64 len) T18
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q18).
bch_reg HS (19%bv : bv 5) (w64 body) T19
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 19 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q19).
bch_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) T25
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs2 25 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q25).
(* Take the state up again at +0x0e0 with the shadow address as its own atom. *)
pmkst HS.
pose proof (proj1 HJ2) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ TRANS_BC_CID pos HAR3 Hin2) as (_ & _ & _ & HFsh3).
change (fs_frame_bytes TRANS_BC_CID / 8) with 32 in HFsh3.
change (frame_addr lyc TRANS_BC_CID pos) with F in HFsh3.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
pose proof (bch_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) sp1 T23
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by (rewrite ESH; lia);
        exact (proj1 (HFsh3 (a - shadow_addr F) ltac:(rewrite ESH; lia))))
  T9 ltac:(lia) Hsp1al ltac:(intros a Ha; apply Hpres3; lia)) as HS3.
clear HS. rename HS3 into HS.
assert (HEI3 : img_env VAL A_LIM (bch_E (ms_regs ms3))) by apply bch_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (bch_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U23' : bv_unsigned (ew (bch_E (ms_regs ms3)) 23) = SHADOW_OFF + F / 8)
  by (rewrite (bch_ew_reg (ms_regs ms3) 23 23%bv eq_refl), T23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U9'' : bv_unsigned (ew (bch_E (ms_regs ms3)) 9) = sp1)
  by (rewrite (bch_ew_reg (ms_regs ms3) 9 9%bv eq_refl), T9; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + BCH_C2)) mm rom) mdx) Q) end.
(* +0x0e0 .. +0x158: the frame's 24 shadow bytes, the slot s1 + 16 = len, and `jal diginet_cursor_init`. *)
paj_run_tok RUN HS HJ2 SHOK BCH_B0.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHADOW_OFF + F / 8)); [reflexivity | exact U23' | |].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right; right; right. exists TRANS_BC_CID, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes TRANS_BC_CID / 8) with 32.
    change (frame_addr lyc TRANS_BC_CID pos) with F. rewrite ESH. lia.
  - eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - spZ regs));
    [reflexivity | rewrite U9''; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch type of HS with SYP0l.st_ok _ _ _ (restrict _ ?msx) => set (ms4 := msx) in * end.
(* The saved words, the flag word and the slot s1 + 24, kept by this run: it writes the shadow bytes and the slot
   s1 + 16 only. *)
assert (KB : forall a, spZ regs - 104 <= a < spZ regs \/ F + 248 <= a < F + 256 \/ sp1 + 24 <= a < sp1 + 32 ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha.
  destruct (bch_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp ltac:(lia)) as (G0 & _ & G2 & _ & _).
  match goal with HFx : frame_of _ (ss_mem ss_bch3) (mrestrict (w_H W) _) (mrestrict (w_H W) _) |- _ =>
    apply (bch_aview_out _ _ (w_H W) _ _ a HFx G0) end.
  intros (r & Hr & Hb). unfold ss_bch3, bch_regions3 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]];
  cbn [bch_rg_sh bch_rg_len YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
  - rewrite U23' in Hb. lia.
  - rewrite U9'' in Hb. lia. }
(* The shadow bytes of c (granules 4 .. 7) and m (12 .. 16) are 0, and the slot s1 + 16 holds len. *)
bch_region HS 0%nat HRsh.
bch_region HS 1%nat HRln.
assert (SZ4 : forall i, (4 <= i < 8 \/ 12 <= i < 17) ->
  aview segs (w_H W) (ms_mem ms4) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi.
  assert (Hi' : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  match goal with |- aview _ _ _ (_ + ?o) = Some 0 =>
    exact (can_aview_of_val1 _ _ _ _ _ (can_field_of_region (bch_E (ms_regs ms3)) _ 23 _ _ 0 24 0 24 o 1%N
      (SLit 0) 0 HRsh U23' ltac:(bch_in) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))) end. }
assert (HSL4 : rdword (aview segs (w_H W) (ms_mem ms4)) (sp1 + 16) = Some len).
{ apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms4) (sp1 + 16) len ltac:(lia)).
  apply (can_field_of_region (bch_E (ms_regs ms3)) _ 9 sp1 _ 16 24 16 24 16 8%N (SOff 18 0) len HRln U9'');
  [ bch_in
  | cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 18 18%bv eq_refl), T18; unfold w64;
    rewrite (unsigned_lit_small len ltac:(lia)), Z.add_0_r; reflexivity
  | cbn; lia | cbn; lia ]. }
(* The registers at the leaf call. *)
bch_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 44984)) P1 ltac:(apply codeptr_val; exact HEI).
bch_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) P2
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 2 2%bv eq_refl), T2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 3 3%bv eq_refl), T3, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 4 4%bv eq_refl), T4, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (8%bv : bv 5) (w64 (spZ regs)) P8
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 8 8%bv eq_refl), T8, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) P9
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 9 9%bv eq_refl), T9, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (19%bv : bv 5) (w64 body) P19
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 19 19%bv eq_refl), T19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (21%bv : bv 5) (Z_to_bv 64 (F + 32)) P21
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 21 21%bv eq_refl), T21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (22%bv : bv 5) (Z_to_bv 64 (F + 96)) P22
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 22 22%bv eq_refl), T22, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (23%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) P23
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 23 23%bv eq_refl), T23, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (24%bv : bv 5) (Z_to_bv 64 F) P24
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 24 24%bv eq_refl), T24, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) P25
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 25 25%bv eq_refl), T25, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 32)) Q10
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 21 21%bv eq_refl), T21, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (Z_to_bv 5 11) (Z_to_bv 64 body) Q11
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 19 19%bv eq_refl), T19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (Z_to_bv 5 12) (Z_to_bv 64 len) Q12
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 18 18%bv eq_refl), T18, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
bch_reg HS (Z_to_bv 5 2) (Z_to_bv 64 sp1) Z2
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg (ms_regs ms3) 2 2%bv eq_refl), T2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms4) (Z_to_bv 5 2)) = sp1)
  by (rewrite Z2; apply unsigned_lit_small; lia).
assert (Hsp4 : spZ (ms_regs ms4) = sp1)
  by (unfold spZ; rewrite P2; apply unsigned_lit_small; lia).
(* The leaf's premises at the call: c = F + 32 lies in the frame, is 8-aligned, its 25 bytes are marked usable. *)
pose proof (proj1 HJ2) as HAR4.
destruct (al_frames _ _ LAWS _ _ _ _ _ TRANS_BC_CID pos HAR4 Hin2) as (_ & _ & HFb4 & _).
change (fs_frame_bytes TRANS_BC_CID) with 256 in HFb4.
change (frame_addr lyc TRANS_BC_CID pos) with F in HFb4.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite D32, HFal, Z.add_0_r.
  replace (32 * (F / 32)) with ((F / 32 * 4) * 8) by lia. apply Z_mod_mult. }
assert (HRAd : range_addressable (aview segs (w_H W) (ms_mem ms4)) SHADOW_OFF (F + 32) 25).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  rewrite (bch_div8 F x HF8), Z.add_assoc. apply SZ4.
  left. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
(* +0x158: the leaf writes the cursor; its post becomes the walk's journal at the return. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm2 ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_diginet_cursor_init)) mm2 rom) mdx) Q) end.
eapply SRr_bind.
{ eapply (can_leafb_journal B LAWS W (ms_regs ms4) (ms_mem ms4) TRANS_BC_STK (spZ regs) (@nil (Z * Z))
    lyc Sc W memc mdc [(TRANS_BC_CID, pos)] lyc S2 _ 0 (sp1 - spZ regs) (transportb_sigma TB_diginet_cursor_init) None
    [(F + 32, F + 32 + 25)]
    (fun m2 => rw_cells rsegs m2 (F + 32) (PCur.cursor_cells body (if body =? 0 then 0 else len) 0 0)) HJ2).
  - rewrite Hsp4. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp16. reflexivity.
  - lia.
  - lia.
  - rewrite P1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - exact P3.
  - exact P4.
  - intros a Ha. unfold LCK.in_wr in Ha.
    apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha].
    cbn [fst snd] in Ha.
    right; right; right. exists TRANS_BC_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes TRANS_BC_CID) with 256.
    change (frame_addr lyc TRANS_BC_CID pos) with F. lia.
  - intros HPRE.
    pose proof (LEAF0 fx) as LF.
    unfold transport_leaf_wr_at, LCI.transport_diginet_cursor_init_cg in LF.
    specialize (LF lyc S2 W (ms_regs ms4) (ms_mem ms4) _ (F + 32) body len (sp1 - 16) HPRE). cbv zeta in LF.
    rewrite ESP in LF. unfold ACI.DIGINET_CURSOR_INIT_FRAME in LF.
    apply LF; clear LF.
    + exact Q10.
    + exact Q11.
    + exact Q12.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite Zplus_mod, HF8. reflexivity.
    + eapply (can_leafb_stk_journal B); [exact HJ2 | lia | lia].
    + lia.
    + apply (can_leafb_wr_at W (ms_mem ms4) (F + 32) 25); [lia | lia |].
      intros i Hi. exact (proj1 (HFb4 (F + 32 + i) ltac:(lia))).
    + unfold AKA.off_stk. rewrite ESP. left. lia.
    + apply (@can_leafb_app_stack rc). lia.
    + apply (@can_leafb_app_stack rc). lia.
    + exact (can_leafb_asan_cells B HCELLS lyc S2 W (ms_mem ms4) _ HAR4).
    + unfold AKA.off_stk. rewrite ESP. left. unfold FCells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite ESP. left. unfold FCells.CELL_K. lia.
    + apply (can_leafb_addressable W (ms_mem ms4) (F + 32) 25 HRAd);
      [lia | lia | unfold FCells.APPMEM_END; lia |].
      intros i Hi. replace (F + 32 + i) with (F + (32 + i)) by lia.
      exact (can_leafb_app_of_in_app F 256 (32 + i) HFapp ltac:(lia)).
    + eapply (can_leafb_rng_journal B); [exact HJ2 | lia | lia].
    + exact (proj1 (can_leafb_rng_cells W)).
    + exact (proj2 (can_leafb_rng_cells W)).
    + apply (can_leafb_rng_vis W (ms_mem ms4)); [lia | lia |].
      intros a Ha. exact (proj1 (HFb4 a ltac:(lia))).
    + apply (can_leafb_rng_shadow W (ms_mem ms4) (F + 32) 25 HRAd); lia.
    + intros x Hx. unfold LCK.in_wr in Hx.
      apply Exists_cons in Hx. destruct Hx as [Hx | Hx]; [|inversion Hx].
      cbn [fst snd] in Hx. split.
      * exact (proj2 (HFb4 x ltac:(lia))).
      * assert (HxF : frame_addr lyc TRANS_BC_CID pos <= x < frame_addr lyc TRANS_BC_CID pos + fs_frame_bytes TRANS_BC_CID)
          by (change (frame_addr lyc TRANS_BC_CID pos) with F; change (fs_frame_bytes TRANS_BC_CID) with 256; lia).
        exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ x HAR4
          (or_intror (or_introl (ex_intro _ TRANS_BC_CID (ex_intro _ pos (conj Hin2 HxF))))))). }
cbv beta.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & _ & Heff5 & Hpres5 & HRW5).
assert (Eif : (if body =? 0 then 0 else len) = len).
{ destruct (Z.eqb_spec body 0) as [E|E]; [|reflexivity].
  destruct Hbody as [Hb|Hb]; [exact (False_ind _ (Hb E)) | lia]. }
rewrite Eif in HRW5.
(* The saved words, the flag word and the two slots, kept by the leaf: it writes the cursor and its own stack
   window only. *)
assert (KC : forall a, spZ regs - 104 <= a < spZ regs \/ F + 248 <= a < F + 256 \/ sp1 + 16 <= a < sp1 + 32 ->
  aview segs (w_H W) mem5 a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha.
  destruct (bch_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp Ha) as (G0 & _ & _ & G3 & G4).
  apply Heff5; [exact G0 | rewrite Hsp4; lia |].
  intros Hc. unfold LCK.in_wr in Hc. apply Exists_cons in Hc.
  destruct Hc as [Hc | Hc]; [cbn [fst snd] in Hc; lia | inversion Hc]. }
(* the frame's 24 shadow bytes, kept by the leaf *)
assert (KS : forall i, 0 <= i < 24 ->
  aview segs (w_H W) mem5 (SHADOW_OFF + F / 8 + i) = aview segs (w_H W) (ms_mem ms4) (SHADOW_OFF + F / 8 + i)).
{ intros i Hi. apply Heff5.
  - unfold SHADOW_OFF; lia.
  - rewrite Hsp4. unfold SHADOW_OFF; lia.
  - intros Hc. unfold LCK.in_wr in Hc. apply Exists_cons in Hc. destruct Hc as [Hc | Hc]; [|inversion Hc].
    cbn [fst snd] in Hc.
    destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* the cursor the leaf wrote: body, len, pos 0, status 0 *)
assert (HlenC : length (BMN.trans_mn_cur_bytes body len 0 0) = 25%nat) by reflexivity.
assert (Hcur5 : garr8 segs (mrestrict (w_H W) mem5) (F + 32) (BMN.trans_mn_cur_bytes body len 0 0)).
{ unfold BMN.trans_mn_cur_bytes.
  apply (FFv.decode_bytes_garr8 (w_H W) mem5 (F + 32)).
  - intros j Hj.
    assert (HlB : length (cells_bytes (PCur.cursor_cells body len 0 0)) = 25%nat) by reflexivity.
    rewrite HlB in Hj.
    exact (proj1 (Hpres5 _ (proj1 (HFb4 (F + 32 + Z.of_nat j) ltac:(lia))))).
  - exact (proj2 (proj1 HRW5)). }
(* +0x15c .. +0x168: s10 = 1, s11 = 0xf0, s2 = 3, s4 = 0x13, up to the loop head +0x16c. *)
rewrite P1.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs5 (Z_to_bv 64 (BASE + BCH_C3)) mem5
    (YK11.seg_rom segs)) md5) Q) end.
pose proof (bch_entry4 W regs5 mem5) as HS5.
clear HS. rename HS5 into HS.
assert (HEI5 : img_env VAL A_LIM (bch_E regs5)) by apply bch_env_img.
clear HEI. rename HEI5 into HEI.
assert (SHOK5 : sh_ok segs (SOff 32 0) (@nil shent) (bch_E regs5) (mrestrict (w_H W) mem5)) by constructor.
clear SHOK. rename SHOK5 into SHOK.
paj_run_to_tok RUNTO HS HJ5 SHOK BCH_B0 BC_LOOP.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_nil. }
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms6 := msx) in * end.
(* this run writes no byte *)
assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) mem5 a).
{ match goal with
  | HFx : frame_of ?E ?rs (mrestrict (w_H W) mem5) (mrestrict (w_H W) (ms_mem ms6)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) mem5 (ms_mem ms6) 0 HFx ltac:(lia)
               ltac:(intros a Ha; unfold in_wrange; intros (r & [] & _)))
  end. }
(* The registers at the loop head. *)
bch_reg HS (2%bv : bv 5) (w64 sp1) V2
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 2 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 2); [exact (HP5 2 ltac:(unfold acallee_saved; lia)) | exact P2]).
bch_reg HS (3%bv : bv 5) (w64 (as_gp B)) V3'
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 3); [exact (HP5 3 ltac:(unfold acallee_saved; lia)) | exact P3]).
bch_reg HS (4%bv : bv 5) (w64 (as_tp B)) V4'
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 4); [exact (HP5 4 ltac:(unfold acallee_saved; lia)) | exact P4]).
bch_reg HS (8%bv : bv 5) (w64 (spZ regs)) V8
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 8 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 8); [exact (HP5 8 ltac:(unfold acallee_saved; lia)) | exact P8]).
bch_reg HS (9%bv : bv 5) (w64 sp1) V9
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 9 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 9); [exact (HP5 9 ltac:(unfold acallee_saved; lia)) | exact P9]).
bch_reg HS (19%bv : bv 5) (w64 body) V19
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 19 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 19); [exact (HP5 19 ltac:(unfold acallee_saved; lia)) | exact P19]).
bch_reg HS (21%bv : bv 5) (w64 (F + 32)) V21
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 21 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 21); [exact (HP5 21 ltac:(unfold acallee_saved; lia)) | exact P21]).
bch_reg HS (22%bv : bv 5) (w64 (F + 96)) V22
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 22 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 22); [exact (HP5 22 ltac:(unfold acallee_saved; lia)) | exact P22]).
bch_reg HS (23%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) V23
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 23 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 23); [exact (HP5 23 ltac:(unfold acallee_saved; lia)) | exact P23]).
bch_reg HS (24%bv : bv 5) (w64 F) V24
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 24 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 24); [exact (HP5 24 ltac:(unfold acallee_saved; lia)) | exact P24]).
bch_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) V25
  ltac:(cbn [sv_denot]; rewrite (bch_ew_reg regs5 25 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        transitivity (YK11.getr (ms_regs ms4) 25); [exact (HP5 25 ltac:(unfold acallee_saved; lia)) | exact P25]).
bch_reg HS (18%bv : bv 5) (w64 3) V18 ltac:(reflexivity).
bch_reg HS (20%bv : bv 5) (w64 19) V20 ltac:(reflexivity).
bch_reg HS (26%bv : bv 5) (w64 1) V26 ltac:(reflexivity).
bch_reg HS (27%bv : bv 5) (w64 240) V27 ltac:(reflexivity).
assert (V3 : YK11.getr (ms_regs ms6) 3 = YK11.getr regs 3) by exact (eq_trans V3' (eq_sym Hgp)).
assert (V4 : YK11.getr (ms_regs ms6) 4 = YK11.getr regs 4) by exact (eq_trans V4' (eq_sym Htp)).
(* The bytes the loop reads, at the loop head: each kept by the runs and calls since it was written. *)
assert (K62 : forall a, spZ regs - 104 <= a < spZ regs \/ F + 248 <= a < F + 256 ->
  aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) mem2 a).
{ intros a Ha. destruct (bch_kp_geom (spZ regs) sp1 F a Hspr Gsp1 GF0 HFsp HFapp ltac:(lia)) as (G0 & _).
  rewrite (KD a G0), (KC a ltac:(lia)), (KB a ltac:(lia)), (KA a Ha). reflexivity. }
assert (K63 : forall a, sp1 + 24 <= a < sp1 + 32 ->
  aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha. rewrite (KD a ltac:(lia)), (KC a ltac:(lia)), (KB a ltac:(lia)). reflexivity. }
assert (K64 : forall a, sp1 + 16 <= a < sp1 + 24 ->
  aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha. rewrite (KD a ltac:(lia)), (KC a ltac:(lia)). reflexivity. }
assert (HSV6 : forall (o : Z) (r : bv 5), In (o, r) bch_saved ->
  rdword (aview segs (w_H W) (ms_mem ms6)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV2 o r Hin). apply bch_rdword_frame.
  intros i Hi. apply K62. lia. }
assert (HFW : Forall (fun o : Z * Z => rdword (aview segs (w_H W) (ms_mem ms6)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) BC_SAVED).
{ unfold BC_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV6 (- o) (Z_to_bv 5 r)); unfold bch_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
assert (HFL6 : rdword (aview segs (w_H W) (ms_mem ms6)) (F + BC_FBYTES - 8) = Some (flag_addr lyc TRANS_BC_CID pos)).
{ rewrite <- Hflag. unfold BC_FBYTES. apply bch_rdword_frame.
  intros i Hi. apply K62. lia. }
assert (HSF6 : rdword (aview segs (w_H W) (ms_mem ms6)) (sp1 + 24) = Some F).
{ rewrite <- HSF3. apply bch_rdword_frame.
  intros i Hi. apply K63. lia. }
assert (HSL6 : rdword (aview segs (w_H W) (ms_mem ms6)) (sp1 + 16) = Some len).
{ rewrite <- HSL4. apply bch_rdword_frame.
  intros i Hi. apply K64. lia. }
assert (HCM6 : bc_cm_zero W (ms_mem ms6) F).
{ intros i Hi. rewrite (KD (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF; lia)), (KS i ltac:(lia)).
  exact (SZ4 i Hi). }
assert (Hcur6 : garr8 segs (mrestrict (w_H W) (ms_mem ms6)) (F + 32) (BMN.trans_mn_cur_bytes body len 0 0)).
{ eapply garr8_frame; [exact Hcur5|]. intros a Ha. rewrite HlenC in Ha.
  apply can_mbyte_of_aview. apply KD. lia. }
(* m: the 40 bytes of the frame at F + 96 the loop starts from, as the view reads them *)
pose proof (proj1 HJ5) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ TRANS_BC_CID pos HAR6 Hin2) as (_ & _ & HFb6 & _).
change (fs_frame_bytes TRANS_BC_CID) with 256 in HFb6.
change (frame_addr lyc TRANS_BC_CID pos) with F in HFb6.
destruct (garr8_of_present segs (mrestrict (w_H W) (ms_mem ms6)) (F + 96) 40) as (lm & Hlm & Hgm).
{ intros a Ha. destruct (proj1 (HFb6 a ltac:(lia))) as (Hh & bq & Hbq).
  exists bq. unfold mrestrict. rewrite Hh. exact Hbq. }
set (mj := map (Z_to_bv 8) lm).
assert (Hmj : map bz mj = lm).
{ unfold mj. rewrite map_map. pose proof (garr8_bytes_ok segs _ _ _ Hgm) as Hok. unfold bytes_ok in Hok.
  clear - Hok. induction lm as [|x lm IH]; [reflexivity|].
  inversion Hok as [|x0 l0 Hx Hl]; subst. cbn [map]. f_equal; [|exact (IH Hl)].
  unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia. }
(* the body bytes, when there are some: kept by the walk's own journal and placed at its state (bc_src_journal) *)
assert (HSRC6 : (0 < length bb)%nat -> trans_src_ok B lyc S2 W (ms_mem ms6) body len /\
  (forall a, body <= a < body + len -> aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) memc a)).
{ intros HL. destruct (Hblk HL) as [Hs Hw].
  exact (bc_src_journal B LAWS HGU HGE HRU HRE TRANS_BC_STK (spZ regs) [(TRANS_BC_CID, pos)] lyc Sc W memc mdc
    lyc S2 W (ms_mem ms6) _ 0 body len HAR HJ5 Hs ltac:(lia) Hw). }
assert (Hgarr6 : garr8 segs (mrestrict (w_H W) (ms_mem ms6)) body (map bz bb)).
{ destruct (Nat.eq_dec (length bb) 0) as [E0|E0].
  - apply length_zero_iff_nil in E0. rewrite E0. apply garr8_nil.
  - eapply garr8_frame; [exact Hgarr|]. intros a Ha. rewrite length_map in Ha.
    apply can_mbyte_of_aview. exact (proj2 (HSRC6 ltac:(lia)) a ltac:(lia)). }
(* the class-2 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
(* +0x16c: the loop, from its cut statement. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + BC_LOOP)) mm rom) mdx) Q) end.
apply (LOOP (conj HCELLS (conj LAWS (conj MTL (conj MTF (conj ASF (conj FFL (conj HGU (conj HGE (conj HRU HRE)))))))))
  MN0 STK sp0 FP ly S W0 mem0 md0 own
  lyc Sc W memc mdc k regs body bb pos sp1 F W (ms_regs ms6) (ms_mem ms6) _ lyc S2 0%nat 0 mj).
- unfold bc_fix.
  refine (conj HJ0 (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj Hsp16 (conj Hlo (conj Hhi (conj Hbody
    (conj Hblk (conj Hcnt (conj Hev (conj _ (conj eq_refl (conj GF0 (conj HFal (conj HFc HFapp))))))))))))))))).
  unfold sp1, TRANS_BC_FRAME. replace (spZ regs - 160) with (spZ regs + -160) by lia. reflexivity.
- unfold bc_cur.
  refine (conj HJ5 (conj _ (conj HMO (conj HFW (conj HSL6 (conj HSF6 (conj HFL6
    (conj Hgarr6 (fun HL => proj1 (HSRC6 HL)))))))))).
  rewrite Eab2. apply Permutation_refl.
- unfold bc_regs_loop, bc_regs_scan, bc_regs_rel.
  refine (conj (conj (conj V2 (conj V3 (conj V4 (conj V8 (conj V9 (conj V23 V24)))))) (conj V19 V25))
    (conj V18 (conj V20 (conj V21 (conj V22 (conj V26 V27)))))).
- lia.
- left. reflexivity.
- exact Hcur6.
- unfold mj. rewrite length_map. exact Hlm.
- rewrite Hmj. exact Hgm.
- exact HCM6.
Qed.

End bch.
