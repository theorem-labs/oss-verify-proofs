(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 839 of its 987 lines of code are new or changed and 991 lines of the source are left out. *)
(* build_and_receive_seg_head: Theorem bar_head_piece : bar_head_stmt (lib/A/Prog/build_and_receive_segs.v), the head
   piece of the image-A walk of build_and_receive (fuzz_transport.asan 0x857e0 = transport_sigma TS_build_and_receive,
   AF_build_and_receive = 0x457c of lib/A/Prog/DgnTransportList.v; statement lib/A/Prog/build_and_receive_cg.v): from the
   entry to the cut bar_mid_at (+0x178).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS 0 []); four runs of the
   position-abstract engine (lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x) and three calls:
     run 1  +0x000 .. +0x084  `addi sp, sp, -192`, the zero word at sp, the 13 saves, s0 = the entry sp, the realign
                              into s1 (the engine's alias of `(sp - 192) & -32` is atom 33, sp1), s3 = len, the slot
                              s1 + 56 (bodyp), s7 = ack, the two runtime cells through their GOT words (the flag word is
                              1, so `beq a3, zero` at +0x080 is not taken), s5 = the shadow base, s6 = dstp, the slots
                              s1 + 48 (cmd), s1 + 40 (retry), s1 + 32 (send) and s1 + 24 (srcp), a0 = 1696, up to
                              `jal __asan_stack_malloc_5`;
     +0x088                   the class-5 stack malloc (lib/A/Prog/TransportGFrame.v gx_stack_malloc_at): the frame F
                              in a0, 4096 <= F;
     run 2  +0x08c .. +0x10c  s4 = s2 = F (`bne s4, zero` taken: the real-stack arm is not reached), the slot s1 + 80,
                              s10 = F + 32, the 24-byte header, s9 = the frame's shadow address (atom 33 by the engine's
                              shadow alias) and its shadow bytes 0 .. 3, s11 = s9 + 4, a1 = 190, a0 = s11, up to
                              `jal __asan_set_shadow_f8` (+0x110; lib/A/Prog/TransportGRt.v gx_set_shadow_at);
     run 3  +0x114 .. +0x164  shadow bytes 194 .. 211 := 0xf3, a1 = 189, a0 = s11, up to `jal __asan_set_shadow_00`
                              (+0x168);
     run 4  +0x16c .. +0x174  a0 = 2, a1 = 30, shadow byte 193 := 2: a run to the cut +0x178.
   After the stack malloc every later step writes only the frame's header, its 256 shadow bytes and the slot s1 + 80
   (BH_ZS); the facts the cut carries are stated at the stack malloc's memory and carried over BH_ZS. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg TransportGRt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import build_and_receive_segs.
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

(* ------------------------------------------------------------------ *)
(* 1. Numerals                                                         *)
(* ------------------------------------------------------------------ *)

Lemma bh_nums : SHADOW_OFF = 2147450880 /\ kLowShadowBeg = 2147446784 /\ kHighMemBeg = 17594333495296 /\
  kLowMemEnd = 2147450880 /\ BAR_FRAME = 192 /\ BAR_STK = 16656 /\ RECV_STK = 16448 /\ ESTACK = 4096 /\
  BAR_CID = 5 /\ BAR_FBYTES = 2048 /\ AF_build_and_receive = 17788 /\ BAR_MID = 18164 /\ BAR_EV = 2.
Proof. repeat split; reflexivity. Qed.
Ltac bh_lia :=
  let HN := fresh "HN" in pose proof bh_nums as HN;
  destruct HN as (?EN1 & ?EN2 & ?EN3 & ?EN4 & ?EN5 & ?EN6 & ?EN7 & ?EN8 & ?EN9 & ?EN10 & ?EN11 & ?EN12 & ?EN13);
  lia.

(* ------------------------------------------------------------------ *)
(* 2. The four symbolic states                                         *)
(* ------------------------------------------------------------------ *)

(* run 1: the entry. Regions: the zero word at the entry sp - 192, the 13 saves below the entry sp, the four slots
   s1 + 24 .. s1 + 64 (atom 33 = sp1, the engine's alias of `(sp - 192) & -32`), and the two runtime cells through
   their GOT words (objects 1 / 93: the shadow base; objects 0 / 94: the use-after-return flag). *)
Definition bh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 94) 0))].
Definition bh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition bh_img_regions : smem := [got_regionP; bcell_regionP 32; bh_got_uar; bh_uar_cell].
Definition bh_rg_zw : YP09.region := YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [].
Definition bh_rg_sv : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition bh_rg_sl : YP09.region := YP09.mkRegion (Some 33%nat) 24 64 24 64 [].
Definition bh_regions1 : smem := bh_rg_zw :: bh_rg_sv :: bh_rg_sl :: bh_img_regions.
Definition bh_alias1 : list (sv * sv) := [(SAlu ALU_AND (SOff 2 (-192)) (SLit (-32)), SOff 33 0)].
Definition bh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] bh_alias1.
Definition ss_bh1 : sstate := mkSS AF_build_and_receive sr_atoms bh_regions1 None bh_facts1.
(* No run uses the token engine: every store goes to a region of its state, and no run checks a byte. *)
Definition BH_B0 : Z * Z := (0, 0).

(* run 2: +0x8c, the frame in a0 (atom 10); atom 33 is its shadow address, which the alias lets the engine reach from
   `(s2 >> 3) + s5`. *)
Definition BH_C2 : Z := AF_build_and_receive + 0x8c.
Definition bh_alias2 : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 21 0), SOff 33 0)].
Definition bh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition bh_rg_fsh : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition bh_rg_fslot : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 80 88 [].
Definition bh_regions2 : smem := [bh_rg_hdr; bh_rg_fsh; bh_rg_fslot].
Definition bh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] bh_alias2.
Definition ss_bh2 : sstate := mkSS BH_C2 sr_atoms bh_regions2 None bh_facts2.

(* run 3: +0x114, s9 (atom 25) the frame's shadow address. *)
Definition BH_C3 : Z := AF_build_and_receive + 0x114.
Definition bh_rg_rg : YP09.region := YP09.mkRegion (Some 25%nat) 194 212 194 212 [].
Definition bh_facts3 : facts := mkFacts [(25%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_bh3 : sstate := mkSS BH_C3 sr_atoms [bh_rg_rg] None bh_facts3.

(* run 4: +0x16c, s9 (atom 25) the frame's shadow address. *)
Definition BH_C4 : Z := AF_build_and_receive + 0x16c.
Definition bh_rg_b193 : YP09.region := YP09.mkRegion (Some 25%nat) 193 194 193 194 [].
Definition ss_bh4 : sstate := mkSS BH_C4 sr_atoms [bh_rg_b193] None bh_facts3.

(* The bytes the head may change after the stack malloc: the frame's header, the frame's 256 shadow bytes, and the
   slot s1 + 80. *)
Definition BH_ZS (F sp1 a : Z) : Prop :=
  (F <= a < F + 24) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 256) \/ (sp1 + 80 <= a < sp1 + 88).

(* The thirteen words the prologue saves, as (offset from the entry sp, register), and the five slots of run 1, as
   (offset from sp1, register). *)
Definition bh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].
Definition bh_slots : list (Z * bv 5) := [(24, 11%bv); (32, 12%bv); (40, 14%bv); (48, 15%bv); (56, 16%bv)].

(* ------------------------------------------------------------------ *)
(* 3. The entry states                                                 *)
(* ------------------------------------------------------------------ *)

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma bh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_build_and_receive = transport_sigma TS_build_and_receive.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma bh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) bh_img_regions /\
  pairwise_disjoint E bh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct bh_vals as (V1 & V93 & V0 & V94 & _).
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
  - unfold bh_img_regions, got_regionP, bcell_regionP, bh_got_uar, bh_uar_cell.
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
    unfold bh_img_regions, got_regionP, bcell_regionP, bh_got_uar, bh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

Definition bh_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).

Lemma bh_env_img : forall regs extra, img_env VAL A_LIM (bh_E regs extra).
Proof. intros regs extra. unfold bh_E. apply Eimg_env. Qed.
Lemma bh_ew_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (bh_E regs extra) n = YK11.getr regs r.
Proof. intros regs extra n r Hn. unfold bh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma bh_ew_extra : forall regs extra j, (j < length extra)%nat -> (j < 200)%nat ->
  ew (bh_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
  intros regs extra j Hj Hj2. unfold bh_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
Lemma bh_ew_obj : forall regs extra i, (i < 95)%nat -> ew (bh_E regs extra) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs extra i Hi. unfold bh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

Lemma bh_den : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity.
Qed.

(* The entry state of run 1. *)
Lemma bh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - 208 <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 + 256 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (bh_E regs [w64 SHADOW_OFF; w64 (32 * ((spZ regs + -192) / 32))]) ss_bh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_build_and_receive)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  destruct (can_sp1_facts (spZ regs + -192) ltac:(lia)
    ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & _).
  set (sp1 := 32 * ((spZ regs + -192) / 32)) in *.
  set (E := bh_E regs [w64 SHADOW_OFF; w64 sp1]).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (bh_ew_extra regs [w64 SHADOW_OFF; w64 sp1] 0 ltac:(cbn; lia) ltac:(lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 sp1)
    by (exact (bh_ew_extra regs [w64 SHADOW_OFF; w64 sp1] 1 ltac:(cbn; lia) ltac:(lia))).
  assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs))
    by (unfold E; rewrite (bh_ew_reg regs _ 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (unfold E; rewrite (bh_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
  assert (U33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  destruct (bh_img_ok ly S W mem md E HCELLS HAR
    (bh_ew_obj regs _ 1 ltac:(lia)) (bh_ew_obj regs _ 93 ltac:(lia))
    (bh_ew_obj regs _ 0 ltac:(lia)) (bh_ew_obj regs _ 94 ltac:(lia)) E32) as [HRs HPd].
  destruct bh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_bh1, bh_regions1.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|exact HRs]]];
    unfold bh_rg_zw, bh_rg_sv, bh_rg_sl, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 2%nat (spZ regs) E2 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + rewrite (VB 2%nat (spZ regs) E2 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    + rewrite (VB 33%nat sp1 E33 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold bh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold bh_rg_zw, bh_rg_sv, bh_rg_sl, got_regionP, bcell_regionP, bh_got_uar, bh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (bh_ew_obj regs _ 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (bh_ew_obj regs _ 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (bh_ew_obj regs _ 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (bh_ew_obj regs _ 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    rewrite (VB 2%nat (spZ regs) E2 ltac:(lia)), (VB 33%nat sp1 E33 ltac:(lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94.
    unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
  - unfold bh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U32, U33.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold bh_alias1. cbn [alias_ok].
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with
    | |- sv_denot _ _ = sv_denot _ _ =>
        rewrite (can_denot_and_m32 E 2 (spZ regs) (-192) E2 ltac:(lia) ltac:(lia) ltac:(lia));
        symmetry; exact (bh_den E 33 sp1 E33 ltac:(lia))
    | |- True => exact I
    | |- spZ regs mod 16 = 0 => exact Hsp16
    | |- sp1 mod 32 = 0 => exact Hsp1al
    | |- _ => unfold SHADOW_OFF; lia
    end.
Qed.

(* The entry state of run 2, at +0x8c. *)
Lemma bh_entry2 : forall (W : world segs) regs2 mem2 F sp1,
  YK11.getr regs2 2 = Z_to_bv 64 sp1 -> YK11.getr regs2 9 = Z_to_bv 64 sp1 ->
  YK11.getr regs2 10 = w64 F -> YK11.getr regs2 21 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 2048 <= 2 ^ 47 -> F + 2048 <= sp1 ->
  (F + 2048 <= kLowShadowBeg \/ kHighMemBeg <= F) ->
  (forall a, sp1 + 80 <= a < sp1 + 88 -> apresent (w_H W) mem2 a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem2 a) ->
  (forall j, 0 <= j < 4 -> apresent (w_H W) mem2 (SHADOW_OFF + F / 8 + j)) ->
  st_ok_pi segs VAL (bh_E regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)]) ss_bh2
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BH_C2)) mem2 (YK11.seg_rom segs))).
Proof.
  intros W regs2 mem2 F sp1 R2 R9 R10 R21 Hsp Hsp32 HF0 HF64 HFc HFsp Happ Hpsl Hphd Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := bh_E regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)]).
  assert (HQ0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (HQc : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 (SHADOW_OFF + F / 8)).
  { exact (bh_ew_extra regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)] 1 ltac:(cbn; lia) ltac:(lia)). }
  assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (unfold E; rewrite (bh_ew_reg regs2 _ 9 9%bv eq_refl); exact R9).
  assert (E2' : ew E 2 = Z_to_bv 64 sp1) by (unfold E; rewrite (bh_ew_reg regs2 _ 2 2%bv eq_refl); exact R2).
  assert (E10 : ew E 10 = Z_to_bv 64 F) by (unfold E; rewrite (bh_ew_reg regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E; rewrite (bh_ew_reg regs2 _ 21 21%bv eq_refl); exact R21).
  assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2'; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; bh_lia).
  assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF + F / 8) by (rewrite E33; apply unsigned_lit_small; bh_lia).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_bh2, bh_regions2.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold bh_rg_hdr, bh_rg_fsh, bh_rg_fslot, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 10%nat F E10 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hphd. lia.
    + rewrite (VB 33%nat (SHADOW_OFF + F / 8) E33 ltac:(bh_lia)).
      split; [bh_lia|]. split; [bh_lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + rewrite (VB 9%nat sp1 E9 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
  - apply pairwise_disjoint_of_extents.
    unfold bh_rg_hdr, bh_rg_fsh, bh_rg_fslot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat F E10 ltac:(lia)), (VB 9%nat sp1 E9 ltac:(lia)),
      (VB 33%nat (SHADOW_OFF + F / 8) E33 ltac:(bh_lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    assert (HD8 : 8 * (F / 8) <= F < 8 * (F / 8) + 8)
      by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
    repeat split; first [exact I | lia].
  - unfold bh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U21, U33.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
      try exact I; try reflexivity; try assumption; try bh_lia.
    unfold bh_alias2. cbn [alias_ok]. split; [|exact I].
    etransitivity;
    [ apply (denot_shx E 10 21 0 F SHADOW_OFF E10 E21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(bh_lia))
    | rewrite Z.add_0_r; symmetry; apply (bh_den E 33%nat (SHADOW_OFF + F / 8) E33 ltac:(bh_lia)) ].
Qed.

(* The entry state of runs 3 and 4 (+0x114, +0x16c): s9 (atom 25) the frame's shadow address. *)
Lemma bh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 25 = w64 SH -> SHADOW_OFF <= SH -> SH + 212 <= 2 ^ 46 ->
  (forall a, SH + 194 <= a < SH + 212 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (bh_E regs []) ss_bh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BH_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R25 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_bh3.
  assert (U25 : bv_unsigned (ew (bh_E regs []) 25) = SH)
    by (rewrite (bh_ew_reg regs [] 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold bh_rg_rg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold bh_rg_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold bh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma bh_entry4 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 25 = w64 SH -> SHADOW_OFF <= SH -> SH + 212 <= 2 ^ 46 ->
  (forall a, SH + 193 <= a < SH + 194 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (bh_E regs []) ss_bh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + BH_C4)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R25 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_bh4.
  assert (U25 : bv_unsigned (ew (bh_E regs []) 25) = SH)
    by (rewrite (bh_ew_reg regs [] 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold bh_rg_b193, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold bh_rg_b193, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold bh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma bh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* A one-byte cell read off its value. *)
Lemma bh_aview_of_val1 : forall H (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
lazymatch goal with |- context [?f v 1%nat 0%nat] => unfold f end.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. repeat rewrite (Z.mod_small v 256) by lia. reflexivity.
Qed.

(* The meter's charge of a frame of n bytes is not negative. *)
Lemma bh_cost_nonneg : forall n, ameter_laws MT -> 0 <= recv_cost MT n.
Proof.
intros n ML. unfold recv_cost.
pose proof (mo_malloc_nonneg MT ML (Z.max 1 n) ltac:(lia)). pose proof (mo_free_nonneg MT ML). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The walk                                                        *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac bh_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "bh_reg: no match for" T; fail
  end.
(* A register whose symbolic value is its own atom n at the run's start, ew Ex n = v (EQ). *)
Ltac bh_kreg HS r EQ H :=
  lazymatch type of EQ with ew _ _ = ?v =>
    bh_reg HS r v H ltac:(cbn [sv_denot]; rewrite EQ, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac bh_region HS i HR :=
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
Ltac bh_u64 x := let Hrg := fresh "Hrg" in pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
(* The awr obligation's regions, computed. *)
Ltac bh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A region write right in the call's own stack window, at base value U. *)
Ltac bh_awr_win U :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
(* A region with no write window. *)
Ltac bh_awr_ro :=
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
(* A region write right in the own frame (its bytes, or its shadow bytes), at base value U. *)
Ltac bh_awr_own U pos Fv :=
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ BAR_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U in Ha;
    first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes BAR_CID) with 2048; fold Fv; lia
          | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes BAR_CID / 8) with 256;
            unfold shadow_addr; fold Fv; lia ] |].

Lemma bh_holds : @bar_head_stmt fx rc B MT.
Proof.
unfold bar_head_stmt. intros c MID. unfold bar_entry. intros HRT HOK.
pose proof HRT as (HPCS & HCELLS & HGU & HGE & HRU & HRE & LAWS & MTL & MTF & SMP & FFL & HGX & HGN
  & ASM0 & ASF80 & ASF00 & _).
pose proof (bar_ok_sp B MT c HOK)
  as (HAR & Hsp & Hceil0 & Hwin0 & Hsp16 & Hsp0a & Hlo & Hhi & Hsp1al & Gsp1 & Hrstk & Hsp1al16).
pose proof HOK as HOK'. unfold bar_ok in HOK'.
destruct HOK' as (HJ & _ & _ & Hgp & Htp & H10 & H11 & _ & _ & H14 & H15 & _ & H17 & _ & _ & _ & _ & _ & _ & _
  & Hrty & Hcmd & _ & _ & _ & _ & _ & _ & Hsrc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & Hc5 & _).
destruct c as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs dstp srcp bodyp send ack retry cmd T
  dst src body Bw ch CTX].
unfold bar_sp1 in *. unfold bar_SP in *.
cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc cx_mdc cx_k cx_regs
  cx_dstp cx_srcp cx_bodyp cx_send cx_ack cx_retry cx_cmd cx_T cx_dst cx_src cx_body cx_Bw cx_ch cx_CTX] in *.
pose proof (ASM0 fx) as ASM. pose proof (ASF80 fx) as ASF8. pose proof (ASF00 fx) as ASF0.
clear ASM0 ASF80 ASF00.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : BAR_STK = 16656) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (ERS : RECV_STK = 16448) by reflexivity.
set (sp1 := 32 * ((spZ regs - BAR_FRAME) / 32)) in *.
assert (Esp1 : 32 * ((spZ regs + -192) / 32) = sp1)
  by (unfold sp1, BAR_FRAME; replace (spZ regs + -192) with (spZ regs - 192) by lia; reflexivity).
(* run 1: the entry to the stack-malloc call *)
pose proof (bh_entry1 lyc Sc W regs memc mdc HCELLS HAR ltac:(intros a Ha; apply Hwin0; lia) ltac:(lia) Hsp16)
  as HS.
rewrite Esp1 in HS.
set (E0 := bh_E regs [w64 SHADOW_OFF; w64 sp1]) in HS.
assert (HEI : img_env VAL A_LIM E0) by apply bh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) E0 (mrestrict (w_H W) memc)) by constructor.
assert (EE2 : ew E0 2 = Z_to_bv 64 (spZ regs))
  by (unfold E0; rewrite (bh_ew_reg regs _ 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs)
  by (unfold E0; rewrite (bh_ew_reg regs _ 2 2%bv eq_refl); reflexivity).
assert (EE3 : ew E0 3 = w64 (as_gp B)) by (unfold E0; rewrite (bh_ew_reg regs _ 3 3%bv eq_refl); exact Hgp).
assert (EE4 : ew E0 4 = w64 (as_tp B)) by (unfold E0; rewrite (bh_ew_reg regs _ 4 4%bv eq_refl); exact Htp).
assert (EE10 : ew E0 10 = w64 dstp) by (unfold E0; rewrite (bh_ew_reg regs _ 10 10%bv eq_refl); exact H10).
assert (EE13 : ew E0 13 = YK11.getr regs 13) by (unfold E0; rewrite (bh_ew_reg regs _ 13 13%bv eq_refl); reflexivity).
assert (EE17 : ew E0 17 = w64 (bar_len body))
  by (unfold E0; rewrite (bh_ew_reg regs _ 17 17%bv eq_refl); exact H17).
assert (EE32 : ew E0 32 = w64 SHADOW_OFF)
  by (exact (bh_ew_extra regs [w64 SHADOW_OFF; w64 sp1] 0 ltac:(cbn; lia) ltac:(lia))).
assert (EE33 : ew E0 33 = Z_to_bv 64 sp1)
  by (exact (bh_ew_extra regs [w64 SHADOW_OFF; w64 sp1] 1 ltac:(cbn; lia) ltac:(lia))).
assert (U33 : bv_unsigned (ew E0 33) = sp1) by (rewrite EE33; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_build_and_receive)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
paj_run_tok RUN HS HJ SHOK BH_B0.
{ bh_awr_rs. bh_awr_win Usp. bh_awr_win Usp. bh_awr_win U33. repeat bh_awr_ro. apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
(* the registers at the call *)
bh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 17928)) R1 ltac:(apply codeptr_val; exact HEI).
bh_kreg HS (2%bv : bv 5) EE33 R2. bh_kreg HS (3%bv : bv 5) EE3 R3. bh_kreg HS (4%bv : bv 5) EE4 R4.
bh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
bh_kreg HS (9%bv : bv 5) EE33 R9. bh_kreg HS (19%bv : bv 5) EE17 R19. bh_kreg HS (21%bv : bv 5) EE32 R21.
bh_kreg HS (22%bv : bv 5) EE10 R22. bh_kreg HS (23%bv : bv 5) EE13 R23.
(* the thirteen saved words and the five slots, read back from the regions the run wrote *)
bh_region HS 1%nat HRsv. bh_region HS 2%nat HRsl.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) bh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold bh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSLo : forall (o : Z) (r : bv 5), In (o, r) bh_slots -> 24 <= o <= 56).
{ intros o r Hin. unfold bh_slots in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) bh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold bh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(bh_u64 (YK11.getr regs r))).
  apply (can_field_of_region E0 _ 2 (spZ regs) _ (-104) 0 (-104) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsv Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; unfold E0; rewrite (bh_ew_reg regs _ (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; bh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
assert (HSL : forall (o : Z) (r : bv 5), In (o, r) bh_slots ->
  rdword (aview segs (w_H W) (ms_mem ms)) (sp1 + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold bh_slots in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (sp1 + o) (bv_unsigned (YK11.getr regs r))
    ltac:(bh_u64 (YK11.getr regs r))).
  apply (can_field_of_region E0 _ 33 sp1 _ 24 64 24 64 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsl U33);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; unfold E0; rewrite (bh_ew_reg regs _ (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; bh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsv HRsl.
(* +0x088: the class-5 stack malloc, at the pc the record names *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_5)) mm rom) mdx) Q)
  end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP BAR_CID ASM
    ltac:(unfold BAR_CID; lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 17928)) HJ) end.
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
assert (Hin2 : In (BAR_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ BAR_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ BAR_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes BAR_CID / 8) with 256 in HFsh.
change (fs_frame_bytes BAR_CID) with 2048 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc BAR_CID pos) in *.
clear Hz Hnev2 HFal.
assert (HFq8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HD8 : 8 * (F / 8) <= F < 8 * (F / 8) + 8)
  by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HappD : F + 2048 <= kLowShadowBeg \/ kHighMemBeg <= F)
  by (destruct HFapp as (_ & [Hx | [Hx _]]); [left; exact Hx | right; exact Hx]).
clear HFapp.
rewrite Zplus_minus in HK1.
(* the saved words and the slots, kept by the call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) bh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword. rewrite !(proj1 HK1) by lia. reflexivity. }
assert (HSL2 : forall (o : Z) (r : bv 5), In (o, r) bh_slots ->
  rdword (aview segs (w_H W) mem2) (sp1 + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSLo o r Hin) as Ho.
  rewrite <- (HSL o r Hin). unfold rdword. rewrite !(proj1 HK1) by lia. reflexivity. }
(* the registers after the call *)
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
assert (Q19 : YK11.getr regs2 19 = w64 (bar_len body))
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q21 : YK11.getr regs2 21 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]).
assert (Q22 : YK11.getr regs2 22 = w64 dstp)
  by (transitivity (YK11.getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22]).
assert (Q23 : YK11.getr regs2 23 = YK11.getr regs 13)
  by (transitivity (YK11.getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23]).
(* run 1 wrote only the 208 bytes below the entry sp *)
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 208 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 208 <= x < spZ regs) HFr1);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?Usp, ?U33 in Hx; lia |]).
  destruct Hin. }
(* what the entry and the call keep of the caller's memory *)
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms) (spZ regs - BAR_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc (ms_mem ms)
    (spZ regs - BAR_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 208 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin0.
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
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - BAR_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms) W mem2 (spZ regs - BAR_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W (ms_mem ms) W mem2).
  - intros a Ha. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W (ms_mem ms) W mem2 _ _ _ HGX HGN HK1). }
assert (GP2 : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W) memc a -> apresent (w_H W) mem2 a).
{ intros a Ha Hp. destruct HK1 as (_ & _ & _ & _ & K5 & K6).
  destruct (Z_lt_le_dec a (sp1 - ESTACK)) as [Hx | Hx]; [|destruct (Z_lt_le_dec a sp1) as [Hy | Hy]].
  - apply K5; [lia | lia | exact (apresent_grows _ _ _ a HG1 Hp)].
  - apply K6. lia.
  - apply K5; [lia | lia | exact (apresent_grows _ _ _ a HG1 Hp)]. }
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
clear HS SHOK. repeat match goal with H : img_env _ _ _ |- _ => clear H end.
clear dependent ms. clear Hset2.
clear EE2 EE3 EE4 EE10 EE13 EE17 EE32 EE33 Usp U33.
(* run 2: +0x8c .. `jal __asan_set_shadow_f8` *)
assert (Hpsl80 : forall a, sp1 + 80 <= a < sp1 + 88 -> apresent (w_H W) mem2 a)
  by (intros a Ha; apply (bh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia).
pose proof (bh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q21 ltac:(lia) Hsp1al HF0 HF64 ltac:(lia) ltac:(lia) HappD Hpsl80
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros j Hj; replace (SHADOW_OFF + F / 8 + j) with (shadow_addr F + j) by reflexivity;
        exact (proj1 (HFsh j ltac:(lia))))) as HS.
set (E1 := bh_E regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)]) in HS.
assert (HEI : img_env VAL A_LIM E1) by apply bh_env_img.
assert (SHOK : sh_ok segs (SOff 21 0) (@nil shent) E1 (mrestrict (w_H W) mem2)) by constructor.
assert (FE2 : ew E1 2 = Z_to_bv 64 sp1) by (unfold E1; rewrite (bh_ew_reg regs2 _ 2 2%bv eq_refl); exact Q2).
assert (FE3 : ew E1 3 = w64 (as_gp B)) by (unfold E1; rewrite (bh_ew_reg regs2 _ 3 3%bv eq_refl); exact Q3).
assert (FE4 : ew E1 4 = w64 (as_tp B)) by (unfold E1; rewrite (bh_ew_reg regs2 _ 4 4%bv eq_refl); exact Q4).
assert (FE8 : ew E1 8 = w64 (spZ regs)) by (unfold E1; rewrite (bh_ew_reg regs2 _ 8 8%bv eq_refl); exact Q8).
assert (FE9 : ew E1 9 = Z_to_bv 64 sp1) by (unfold E1; rewrite (bh_ew_reg regs2 _ 9 9%bv eq_refl); exact Q9).
assert (FE10 : ew E1 10 = Z_to_bv 64 F) by (unfold E1; rewrite (bh_ew_reg regs2 _ 10 10%bv eq_refl); exact Ha0).
assert (FE19 : ew E1 19 = w64 (bar_len body))
  by (unfold E1; rewrite (bh_ew_reg regs2 _ 19 19%bv eq_refl); exact Q19).
assert (FE21 : ew E1 21 = w64 SHADOW_OFF) by (unfold E1; rewrite (bh_ew_reg regs2 _ 21 21%bv eq_refl); exact Q21).
assert (FE22 : ew E1 22 = w64 dstp) by (unfold E1; rewrite (bh_ew_reg regs2 _ 22 22%bv eq_refl); exact Q22).
assert (FE23 : ew E1 23 = YK11.getr regs 13)
  by (unfold E1; rewrite (bh_ew_reg regs2 _ 23 23%bv eq_refl); exact Q23).
assert (FE33 : ew E1 33 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (exact (bh_ew_extra regs2 [w64 SHADOW_OFF; w64 (SHADOW_OFF + F / 8)] 1 ltac:(cbn; lia) ltac:(lia))).
assert (U10' : bv_unsigned (ew E1 10) = F) by (rewrite FE10; apply unsigned_lit_small; lia).
assert (U9' : bv_unsigned (ew E1 9) = sp1) by (rewrite FE9; apply unsigned_lit_small; lia).
assert (U33' : bv_unsigned (ew E1 33) = SHADOW_OFF + F / 8) by (rewrite FE33; apply unsigned_lit_small; bh_lia).
clear Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q23 Ha0.
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + BH_C2)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
paj_run_tok RUN HS HJ2 SHOK BH_B0.
{ bh_awr_rs. bh_awr_own U10' pos F. bh_awr_own U33' pos F. bh_awr_win U9'. apply awr_ok_x_nil. }
rename HF into HF2, HFr into HFr2, HG into HG2.
(* run 2 wrote the slot s1 + 80, the header and shadow bytes 0 .. 3: bytes of BH_ZS *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ BH_ZS F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (BH_ZS F sp1) HFr2); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U10', ?U33', ?U9' in Hx; unfold BH_ZS; lia |]).
  destruct Hin. }
assert (GA2 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem2 (ms_mem ms) a HG2 Ha)).
clear HF2 HFr2 HG2.
(* the registers at the call *)
bh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 18064)) T1 ltac:(apply codeptr_val; exact HEI).
bh_kreg HS (2%bv : bv 5) FE2 T2. bh_kreg HS (3%bv : bv 5) FE3 T3. bh_kreg HS (4%bv : bv 5) FE4 T4.
bh_kreg HS (8%bv : bv 5) FE8 T8. bh_kreg HS (9%bv : bv 5) FE9 T9. bh_kreg HS (18%bv : bv 5) FE10 T18.
bh_kreg HS (19%bv : bv 5) FE19 T19. bh_kreg HS (20%bv : bv 5) FE10 T20. bh_kreg HS (21%bv : bv 5) FE21 T21.
bh_kreg HS (22%bv : bv 5) FE22 T22. bh_kreg HS (23%bv : bv 5) FE23 T23. bh_kreg HS (25%bv : bv 5) FE33 T25.
bh_reg HS (26%bv : bv 5) (w64 (F + 32)) T26
  ltac:(cbn [sv_denot]; rewrite FE10, unsigned_lit_small by lia; reflexivity).
bh_reg HS (27%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 4)) T27
  ltac:(cbn [sv_denot]; rewrite FE33, unsigned_lit_small by bh_lia; reflexivity).
bh_reg HS (10%bv : bv 5) (w64 (SHADOW_OFF + F / 8 + 4)) T10
  ltac:(cbn [sv_denot]; rewrite FE33, unsigned_lit_small by bh_lia; reflexivity).
bh_reg HS (11%bv : bv 5) (w64 190) T11 ltac:(reflexivity).
(* +0x110: __asan_set_shadow_f8 (shadow bytes 4 .. 193 of the frame) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_f8)) mm rom) mdx) Q)
  end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  exact (@gx_set_shadow_at fx rc tfib_sink_head segs B LAWS transport_segs_low
    (transport_sigma TS___asan_set_shadow_f8) 0xf8 ASF8 TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0
    ((BAR_CID, pos) :: own) lyc S2 mdx k BAR_CID pos (SHADOW_OFF + F / 8 + 4) 190 (sp1 - sp0)
    (Z_to_bv 64 (BASE + 18064)) HJ2 (or_introl eq_refl) T10 T11 ltac:(lia)
    ltac:(unfold shadow_addr; fold F; lia)
    ltac:(change (fs_frame_bytes BAR_CID / 8) with 256; unfold shadow_addr; fold F; lia)
    ltac:(unfold spZ at 1; rewrite T2, unsigned_lit_small by lia; lia)
    ltac:(rewrite Zminus_mod, Hsp1al16, Hsp0a; reflexivity)
    ltac:(lia) ltac:(lia) T3 T4 T1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])) end. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hkeep3 & Hgr3).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ BH_ZS F sp1 a ->
  aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite Hkeep3; [exact (K2 a Ha Hn) | exact Ha |].
  intros Hx. apply Hn. unfold BH_ZS. lia. }
assert (GA3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a)
  by (intros a Ha; exact (Hgr3 a (GA2 a Ha))).
assert (P2 : YK11.getr regs3 2 = Z_to_bv 64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) T2).
assert (P3 : YK11.getr regs3 3 = w64 (as_gp B)) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) T3).
assert (P4 : YK11.getr regs3 4 = w64 (as_tp B)) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) T4).
assert (P8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) T8).
assert (P9 : YK11.getr regs3 9 = Z_to_bv 64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) T9).
assert (P18 : YK11.getr regs3 18 = Z_to_bv 64 F) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) T18).
assert (P19 : YK11.getr regs3 19 = w64 (bar_len body)) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) T19).
assert (P20 : YK11.getr regs3 20 = Z_to_bv 64 F) by exact (eq_trans (HP3 20 ltac:(hnf; lia)) T20).
assert (P21 : YK11.getr regs3 21 = w64 SHADOW_OFF) by exact (eq_trans (HP3 21 ltac:(hnf; lia)) T21).
assert (P22 : YK11.getr regs3 22 = w64 dstp) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) T22).
assert (P23 : YK11.getr regs3 23 = YK11.getr regs 13) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) T23).
assert (P25 : YK11.getr regs3 25 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP3 25 ltac:(hnf; lia)) T25).
assert (P26 : YK11.getr regs3 26 = w64 (F + 32)) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) T26).
assert (P27 : YK11.getr regs3 27 = w64 (SHADOW_OFF + F / 8 + 4)) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) T27).
clear K2 GA2 Hkeep3 Hgr3 HP3.
clear HS SHOK. repeat match goal with H : img_env _ _ _ |- _ => clear H end.
clear dependent ms.
clear FE2 FE3 FE4 FE8 FE9 FE10 FE19 FE21 FE22 FE23 FE33 U10' U9' U33'.
(* run 3: +0x114 .. `jal __asan_set_shadow_00` *)
pose proof (bh_entry3 W regs3 mem3 (SHADOW_OFF + F / 8) P25 ltac:(bh_lia) ltac:(bh_lia)
  ltac:(intros a Ha; apply GA3;
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
set (E2 := bh_E regs3 []) in HS.
assert (HEI : img_env VAL A_LIM E2) by apply bh_env_img.
assert (SHOK : sh_ok segs (SOff 21 0) (@nil shent) E2 (mrestrict (w_H W) mem3)) by constructor.
assert (GE2 : ew E2 2 = Z_to_bv 64 sp1) by (unfold E2; rewrite (bh_ew_reg regs3 _ 2 2%bv eq_refl); exact P2).
assert (GE3 : ew E2 3 = w64 (as_gp B)) by (unfold E2; rewrite (bh_ew_reg regs3 _ 3 3%bv eq_refl); exact P3).
assert (GE4 : ew E2 4 = w64 (as_tp B)) by (unfold E2; rewrite (bh_ew_reg regs3 _ 4 4%bv eq_refl); exact P4).
assert (GE8 : ew E2 8 = w64 (spZ regs)) by (unfold E2; rewrite (bh_ew_reg regs3 _ 8 8%bv eq_refl); exact P8).
assert (GE9 : ew E2 9 = Z_to_bv 64 sp1) by (unfold E2; rewrite (bh_ew_reg regs3 _ 9 9%bv eq_refl); exact P9).
assert (GE18 : ew E2 18 = Z_to_bv 64 F) by (unfold E2; rewrite (bh_ew_reg regs3 _ 18 18%bv eq_refl); exact P18).
assert (GE19 : ew E2 19 = w64 (bar_len body))
  by (unfold E2; rewrite (bh_ew_reg regs3 _ 19 19%bv eq_refl); exact P19).
assert (GE20 : ew E2 20 = Z_to_bv 64 F) by (unfold E2; rewrite (bh_ew_reg regs3 _ 20 20%bv eq_refl); exact P20).
assert (GE21 : ew E2 21 = w64 SHADOW_OFF) by (unfold E2; rewrite (bh_ew_reg regs3 _ 21 21%bv eq_refl); exact P21).
assert (GE22 : ew E2 22 = w64 dstp) by (unfold E2; rewrite (bh_ew_reg regs3 _ 22 22%bv eq_refl); exact P22).
assert (GE23 : ew E2 23 = YK11.getr regs 13)
  by (unfold E2; rewrite (bh_ew_reg regs3 _ 23 23%bv eq_refl); exact P23).
assert (GE25 : ew E2 25 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (unfold E2; rewrite (bh_ew_reg regs3 _ 25 25%bv eq_refl); exact P25).
assert (GE26 : ew E2 26 = w64 (F + 32)) by (unfold E2; rewrite (bh_ew_reg regs3 _ 26 26%bv eq_refl); exact P26).
assert (GE27 : ew E2 27 = w64 (SHADOW_OFF + F / 8 + 4))
  by (unfold E2; rewrite (bh_ew_reg regs3 _ 27 27%bv eq_refl); exact P27).
assert (U25b : bv_unsigned (ew E2 25) = SHADOW_OFF + F / 8) by (rewrite GE25; apply unsigned_lit_small; bh_lia).
clear P2 P3 P4 P8 P9 P18 P19 P20 P21 P22 P23 P25 P26 P27.
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + BH_C3)) mem3
    (YK11.seg_rom segs)) md3) Q) end.
paj_run_tok RUN HS HJ3 SHOK BH_B0.
{ bh_awr_rs. bh_awr_own U25b pos F. apply awr_ok_x_nil. }
rename HF into HF3, HFr into HFr3, HG into HG3.
(* run 3 wrote shadow bytes 194 .. 211: bytes of BH_ZS *)
assert (K3b : forall a, 0 <= a < 2 ^ 64 -> ~ BH_ZS F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite <- (K3 a Ha Hn).
  apply (kept_of_frame _ _ _ _ _ (BH_ZS F sp1) HFr3); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U25b in Hx; unfold BH_ZS; lia |]).
  destruct Hin. }
assert (GA3b : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem3 (ms_mem ms) a HG3 (GA3 a Ha))).
clear HF3 HFr3 HG3 K3 GA3.
bh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 18152)) V1 ltac:(apply codeptr_val; exact HEI).
bh_kreg HS (2%bv : bv 5) GE2 V2. bh_kreg HS (3%bv : bv 5) GE3 V3. bh_kreg HS (4%bv : bv 5) GE4 V4.
bh_kreg HS (8%bv : bv 5) GE8 V8. bh_kreg HS (9%bv : bv 5) GE9 V9. bh_kreg HS (18%bv : bv 5) GE18 V18.
bh_kreg HS (19%bv : bv 5) GE19 V19. bh_kreg HS (20%bv : bv 5) GE20 V20. bh_kreg HS (21%bv : bv 5) GE21 V21.
bh_kreg HS (22%bv : bv 5) GE22 V22. bh_kreg HS (23%bv : bv 5) GE23 V23. bh_kreg HS (25%bv : bv 5) GE25 V25.
bh_kreg HS (26%bv : bv 5) GE26 V26. bh_kreg HS (27%bv : bv 5) GE27 V27.
bh_kreg HS (10%bv : bv 5) GE27 V10.
bh_reg HS (11%bv : bv 5) (w64 189) V11 ltac:(reflexivity).
(* +0x168: __asan_set_shadow_00 (shadow bytes 4 .. 192 of the frame) *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_set_shadow_00)) mm rom) mdx) Q)
  end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  exact (@gx_set_shadow_at fx rc tfib_sink_head segs B LAWS transport_segs_low
    (transport_sigma TS___asan_set_shadow_00) 0 ASF0 TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0
    ((BAR_CID, pos) :: own) lyc S2 mdx k BAR_CID pos (SHADOW_OFF + F / 8 + 4) 189 (sp1 - sp0)
    (Z_to_bv 64 (BASE + 18152)) HJ3 (or_introl eq_refl) V10 V11 ltac:(lia)
    ltac:(unfold shadow_addr; fold F; lia)
    ltac:(change (fs_frame_bytes BAR_CID / 8) with 256; unfold shadow_addr; fold F; lia)
    ltac:(unfold spZ at 1; rewrite V2, unsigned_lit_small by lia; lia)
    ltac:(rewrite Zminus_mod, Hsp1al16, Hsp0a; reflexivity)
    ltac:(lia) ltac:(lia) V3 V4 V1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])) end. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfill4 & Hkeep4 & Hgr4).
assert (K4b : forall a, 0 <= a < 2 ^ 64 -> ~ BH_ZS F sp1 a ->
  aview segs (w_H W) mem4 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite Hkeep4; [exact (K3b a Ha Hn) | exact Ha |].
  intros Hx. apply Hn. unfold BH_ZS. lia. }
assert (GA4b : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem4 a)
  by (intros a Ha; exact (Hgr4 a (GA3b a Ha))).
assert (Z4 : forall i, 4 <= i < 193 -> aview segs (w_H W) mem4 (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. replace (SHADOW_OFF + F / 8 + i) with (SHADOW_OFF + F / 8 + 4 + (i - 4)) by lia.
  apply Hfill4. lia. }
assert (G2 : YK11.getr regs4 2 = Z_to_bv 64 sp1) by exact (eq_trans (HP4 2 ltac:(hnf; lia)) V2).
assert (G3 : YK11.getr regs4 3 = w64 (as_gp B)) by exact (eq_trans (HP4 3 ltac:(hnf; lia)) V3).
assert (G4 : YK11.getr regs4 4 = w64 (as_tp B)) by exact (eq_trans (HP4 4 ltac:(hnf; lia)) V4).
assert (G8 : YK11.getr regs4 8 = w64 (spZ regs)) by exact (eq_trans (HP4 8 ltac:(hnf; lia)) V8).
assert (G9 : YK11.getr regs4 9 = Z_to_bv 64 sp1) by exact (eq_trans (HP4 9 ltac:(hnf; lia)) V9).
assert (G18 : YK11.getr regs4 18 = Z_to_bv 64 F) by exact (eq_trans (HP4 18 ltac:(hnf; lia)) V18).
assert (G19 : YK11.getr regs4 19 = w64 (bar_len body)) by exact (eq_trans (HP4 19 ltac:(hnf; lia)) V19).
assert (G20 : YK11.getr regs4 20 = Z_to_bv 64 F) by exact (eq_trans (HP4 20 ltac:(hnf; lia)) V20).
assert (G21 : YK11.getr regs4 21 = w64 SHADOW_OFF) by exact (eq_trans (HP4 21 ltac:(hnf; lia)) V21).
assert (G22 : YK11.getr regs4 22 = w64 dstp) by exact (eq_trans (HP4 22 ltac:(hnf; lia)) V22).
assert (G23 : YK11.getr regs4 23 = YK11.getr regs 13) by exact (eq_trans (HP4 23 ltac:(hnf; lia)) V23).
assert (G25 : YK11.getr regs4 25 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by exact (eq_trans (HP4 25 ltac:(hnf; lia)) V25).
assert (G26 : YK11.getr regs4 26 = w64 (F + 32)) by exact (eq_trans (HP4 26 ltac:(hnf; lia)) V26).
assert (G27 : YK11.getr regs4 27 = w64 (SHADOW_OFF + F / 8 + 4)) by exact (eq_trans (HP4 27 ltac:(hnf; lia)) V27).
clear K3b GA3b Hkeep4 Hgr4 Hfill4 HP4.
clear HS SHOK. repeat match goal with H : img_env _ _ _ |- _ => clear H end.
clear dependent ms.
clear GE2 GE3 GE4 GE8 GE9 GE18 GE19 GE20 GE21 GE22 GE23 GE25 GE26 GE27 U25b.
(* run 4: +0x16c .. the cut +0x178 *)
pose proof (bh_entry4 W regs4 mem4 (SHADOW_OFF + F / 8) G25 ltac:(bh_lia) ltac:(bh_lia)
  ltac:(intros a Ha; apply GA4b;
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
set (E3 := bh_E regs4 []) in HS.
assert (HEI : img_env VAL A_LIM E3) by apply bh_env_img.
assert (SHOK : sh_ok segs (SOff 21 0) (@nil shent) E3 (mrestrict (w_H W) mem4)) by constructor.
assert (HE2 : ew E3 2 = Z_to_bv 64 sp1) by (unfold E3; rewrite (bh_ew_reg regs4 _ 2 2%bv eq_refl); exact G2).
assert (HE3 : ew E3 3 = w64 (as_gp B)) by (unfold E3; rewrite (bh_ew_reg regs4 _ 3 3%bv eq_refl); exact G3).
assert (HE4 : ew E3 4 = w64 (as_tp B)) by (unfold E3; rewrite (bh_ew_reg regs4 _ 4 4%bv eq_refl); exact G4).
assert (HE8 : ew E3 8 = w64 (spZ regs)) by (unfold E3; rewrite (bh_ew_reg regs4 _ 8 8%bv eq_refl); exact G8).
assert (HE9 : ew E3 9 = Z_to_bv 64 sp1) by (unfold E3; rewrite (bh_ew_reg regs4 _ 9 9%bv eq_refl); exact G9).
assert (HE18 : ew E3 18 = Z_to_bv 64 F) by (unfold E3; rewrite (bh_ew_reg regs4 _ 18 18%bv eq_refl); exact G18).
assert (HE19 : ew E3 19 = w64 (bar_len body))
  by (unfold E3; rewrite (bh_ew_reg regs4 _ 19 19%bv eq_refl); exact G19).
assert (HE20 : ew E3 20 = Z_to_bv 64 F) by (unfold E3; rewrite (bh_ew_reg regs4 _ 20 20%bv eq_refl); exact G20).
assert (HE21 : ew E3 21 = w64 SHADOW_OFF) by (unfold E3; rewrite (bh_ew_reg regs4 _ 21 21%bv eq_refl); exact G21).
assert (HE22 : ew E3 22 = w64 dstp) by (unfold E3; rewrite (bh_ew_reg regs4 _ 22 22%bv eq_refl); exact G22).
assert (HE23 : ew E3 23 = YK11.getr regs 13)
  by (unfold E3; rewrite (bh_ew_reg regs4 _ 23 23%bv eq_refl); exact G23).
assert (HE25 : ew E3 25 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (unfold E3; rewrite (bh_ew_reg regs4 _ 25 25%bv eq_refl); exact G25).
assert (HE26 : ew E3 26 = w64 (F + 32)) by (unfold E3; rewrite (bh_ew_reg regs4 _ 26 26%bv eq_refl); exact G26).
assert (HE27 : ew E3 27 = w64 (SHADOW_OFF + F / 8 + 4))
  by (unfold E3; rewrite (bh_ew_reg regs4 _ 27 27%bv eq_refl); exact G27).
assert (U25c : bv_unsigned (ew E3 25) = SHADOW_OFF + F / 8) by (rewrite HE25; apply unsigned_lit_small; bh_lia).
clear G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27.
lazymatch goal with |- SRr _ _ _ ?Q =>
  change (SRr segs W (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (BASE + BH_C4)) mem4
    (YK11.seg_rom segs)) md4) Q) end.
paj_run_to_tok RUNTO HS HJ4 SHOK BH_B0 BAR_MID.
{ bh_awr_rs. bh_awr_own U25c pos F. apply awr_ok_x_nil. }
(* run 4 wrote shadow byte 193 only *)
assert (KF4 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (SHADOW_OFF + F / 8 + 193 <= a < SHADOW_OFF + F / 8 + 194) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem4 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 193 <= x < SHADOW_OFF + F / 8 + 194) HFr);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U25c in Hx; lia |]).
  destruct Hin. }
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ BH_ZS F sp1 a ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (KF4 a Ha ltac:(intros Hx; apply Hn; unfold BH_ZS; lia)). exact (K4b a Ha Hn). }
assert (GF : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA4b a Ha))).
bh_region HS 0%nat HRb.
assert (H193 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 193) = Some 2).
{ apply bh_aview_of_val1; [| lia].
  exact (can_field_of_region E3 _ 25 (SHADOW_OFF + F / 8) _ 193 194 193 194 193 1%N (SLit 2) 2 HRb U25c
    ltac:(repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
clear HRb.
bh_kreg HS (2%bv : bv 5) HE2 X2. bh_kreg HS (3%bv : bv 5) HE3 X3. bh_kreg HS (4%bv : bv 5) HE4 X4.
bh_kreg HS (8%bv : bv 5) HE8 X8. bh_kreg HS (9%bv : bv 5) HE9 X9. bh_kreg HS (18%bv : bv 5) HE18 X18.
bh_kreg HS (19%bv : bv 5) HE19 X19. bh_kreg HS (20%bv : bv 5) HE20 X20. bh_kreg HS (21%bv : bv 5) HE21 X21.
bh_kreg HS (22%bv : bv 5) HE22 X22. bh_kreg HS (23%bv : bv 5) HE23 X23. bh_kreg HS (25%bv : bv 5) HE25 X25.
bh_kreg HS (26%bv : bv 5) HE26 X26. bh_kreg HS (27%bv : bv 5) HE27 X27.
bh_reg HS (11%bv : bv 5) (w64 30) X11 ltac:(reflexivity).
(* ---- the facts the cut carries, at the cut's memory ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + BAR_MID)) mm rom) mdx) Q) end.
set (mF := ms_mem ms) in *.
assert (HSVF : forall (o : Z) (r : bv 5), In (o, r) bh_saved ->
  rdword (aview segs (w_H W) mF) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply rdword_ext. intros i Hi. apply KF; [lia|]. unfold BH_ZS. bh_lia. }
assert (HSLF : forall (o : Z) (r : bv 5), In (o, r) bh_slots ->
  rdword (aview segs (w_H W) mF) (sp1 + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSLo o r Hin) as Ho. rewrite <- (HSL2 o r Hin).
  apply rdword_ext. intros i Hi. apply KF; [lia|]. unfold BH_ZS. bh_lia. }
assert (H11' : YK11.getr regs 11%bv = w64 srcp) by exact H11.
assert (H14' : YK11.getr regs 14%bv = w64 retry) by exact H14.
assert (H15' : YK11.getr regs 15%bv = w64 cmd) by exact H15.
assert (Hsrcr : 0 <= srcp < 2 ^ 64).
{ destruct (trans_src_ok_place B LAWS lyc Sc W memc mdc srcp BAR_MAC HAR Hsrc ltac:(unfold BAR_MAC; lia))
    as [Hp | Hp]; unfold BAR_MAC in Hp; lia. }
apply (MID HRT HOK pos S2 mF _ (ms_regs ms)).
- (* bar_run *)
  unfold bar_run, bar_cur.
  cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc cx_mdc cx_k cx_regs
    cx_dstp cx_srcp cx_bodyp cx_send cx_ack cx_retry cx_cmd cx_T cx_dst cx_src cx_body cx_Bw cx_ch cx_CTX].
  unfold bar_SP, bar_F, bar_N, bar_fr.
  cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc cx_mdc cx_k cx_regs
    cx_dstp cx_srcp cx_bodyp cx_send cx_ack cx_retry cx_cmd cx_T cx_dst cx_src cx_body cx_Bw cx_ch cx_CTX].
  fold F.
  refine (conj (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj _ (conj _ (conj _ _))))))))
    (conj Eab2 (conj HMO (conj _ (conj _ (conj H193 _)))))).
  + rewrite Z.add_0_r. exact HJ4.
  + bh_lia.
  + rewrite Eab2. apply Permutation_refl.
  + apply (mle_weaken MT Sc S2 0 _ MTL HMO). apply bh_cost_nonneg. exact MTL.
  + apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W mF (spZ regs - BAR_STK) (spZ regs)
      (fun _ => False)); [tauto|].
    apply (dk_kept_own_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc S2 W memc mdc mem2 md2 mem2 mF
      (spZ regs - BAR_STK) (spZ regs) BAR_CID pos F (flag_addr lyc BAR_CID pos) (fun _ => False) (BH_ZS F sp1)
      HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | exact KF | exact GF].
    intros a [X | [X | X]].
    * right; right; left. unfold dkg_nf. left. change (fs_frame_bytes BAR_CID) with 2048. lia.
    * right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes BAR_CID / 8) with 256. lia.
    * left. lia.
  + unfold BAR_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
      replace (spZ regs - o) with (spZ regs + - o) by ring;
      apply (HSVF (- o) (Z_to_bv 5 r)); unfold bh_saved; cbn [In];
      repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end.
  + unfold BAR_FBYTES. rewrite <- Hflag. apply rdword_ext. intros i Hi. apply KF; [lia|].
    unfold BH_ZS. intros [X | [X | X]]; [lia | | lia].
    destruct HappD as [Hx1 | Hx1]; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
  + intros a Ha. rewrite <- (GK2 a Ha).
    pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl. unfold kLowMemEnd in Hl.
    apply KF; [lia|]. unfold BH_ZS. intros [X | [X | X]].
    * exact (frm_img segs B LAWS _ _ _ _ _ BAR_CID pos a HAR2 Hin2
        ltac:(change (fs_frame_bytes BAR_CID) with 2048; fold F; lia) (proj1 (HGX a Ha))).
    * unfold SHADOW_OFF in X. lia.
    * lia.
  + intros i Hi. rewrite KF4; [exact (Z4 i Hi) | bh_lia | lia].
  + intros a Ha Hp. apply GF. exact (GP2 a Ha Hp).
- (* bar_rg_run *)
  unfold bar_rg_run, bar_rg, bar_sp1, bar_SP, bar_F.
  cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc cx_mdc cx_k cx_regs
    cx_dstp cx_srcp cx_bodyp cx_send cx_ack cx_retry cx_cmd cx_T cx_dst cx_src cx_body cx_Bw cx_ch cx_CTX].
  exact (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X20 (conj X21 (conj X25
    (conj X26 X27))))))))))
    (conj X19 X23)).
- (* bar_slots *)
  unfold bar_slots, bar_sp1, bar_SP.
  cbn [cx_STK cx_sp0 cx_FP cx_ly cx_S cx_W0 cx_mem0 cx_md0 cx_own cx_lyc cx_Sc cx_W cx_memc cx_mdc cx_k cx_regs
    cx_dstp cx_srcp cx_bodyp cx_send cx_ack cx_retry cx_cmd cx_T cx_dst cx_src cx_body cx_Bw cx_ch cx_CTX].
  fold sp1.
  refine (conj _ (conj (HSLF 32 12%bv ltac:(unfold bh_slots; cbn [In]; repeat (first [left; reflexivity | right])))
    (conj _ (conj _ (HSLF 56 16%bv ltac:(unfold bh_slots; cbn [In]; repeat (first [left; reflexivity | right]))))))).
  + rewrite (HSLF 24 11%bv ltac:(unfold bh_slots; cbn [In]; repeat (first [left; reflexivity | right]))).
    rewrite H11'. f_equal. apply unsigned_lit_small. exact Hsrcr.
  + rewrite (HSLF 40 14%bv ltac:(unfold bh_slots; cbn [In]; repeat (first [left; reflexivity | right]))).
    rewrite H14'. f_equal. apply unsigned_lit_small. lia.
  + rewrite (HSLF 48 15%bv ltac:(unfold bh_slots; cbn [In]; repeat (first [left; reflexivity | right]))).
    rewrite H15'. f_equal. apply unsigned_lit_small. lia.
- exact X22.
- exact X11.
Qed.

End s.

Theorem bar_head_piece : forall fx rc B MT, @bar_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@bh_holds fx rc B MT). Qed.
