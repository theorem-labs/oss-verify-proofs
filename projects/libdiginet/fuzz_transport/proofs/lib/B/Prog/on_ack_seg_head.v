(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1441 of its 1599 lines of code are new or changed and 981 lines of the source are left out. *)
(* on_ack_seg_head: Theorem onack_head : onack_head_stmt (lib/B/Prog/on_ack_segs.v), the head piece of the walk of
   on_ack on fuzz_transport.asan-ubsan (0x8858c = transportb_sigma TB_on_ack, AF_on_ack = 0x72ec of
   lib/B/Prog/DgnTransportBList.v), from the entry to the two cuts onack_ntc_at (+0x190) and onack_ign_at (+0x2c0).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []); the runs are the
   position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x. Image B's form of image A's head
   (the same cuts and carried facts; the offsets and the two UBSan alignment checks are image B's):
     run 1   +0x000 .. +0x070  the frame (`addi sp, sp, -128`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1, s4 = fp, the flag word through its GOT word (1, so `beqz a2` at +0x068 is not
                               taken), s9 = the shadow base, s3 = s, a0 = 160, up to `jal __asan_stack_malloc_2`;
     +0x070                    the class-2 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/B/Prog/on_ack_seg_kit.v oak_gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x074 .. +0x0a4  `bnez s2` taken (the real-stack arm is not reached), s8 = s2 = F, and the frame word
                               at s1 + 16 (image B stores it here, before the header);
     run 2b  +0x0a8 .. +0x0dc  the frame's 24-byte header and s7 = the frame's shadow address;
     run 2c  +0x0e0 .. +0x138  the frame's shadow bytes 0 .. 19, the UBSan alignment check of s (`andi a1, s3, 7`
                               at +0x0f0 and `bnez a1` at +0x134: s = ONACK_S is 64-aligned, so the trap word at
                               +0x418 is not reached), and a0 = s + 212 (a run to +0x13c);
     run 3   +0x13c .. +0x14c  a3 = the shadow address of s + 212, the instrumented check of the 4-byte load there
                               and the load of S_inflight (the shadow byte is 0: trans_onack_cells, the shadow entry
                               OHD_SH3);
     +0x150                    `beqz a1`: S_inflight Bw = 0 runs one instruction to +0x2c0 and concludes by
                               onack_ign_at (onack_ign's first disjunct); else one instruction to +0x154;
     run 4   +0x154 .. +0x184  the UBSan alignment check of f (`andi a1, s4, 7` at +0x154 and `bnez a1` at +0x158:
                               trans_dframe_at's fp mod 8 = 0), the checks of the 4-byte loads at f + 24 and at
                               s + 1744, and s10 = the 4-byte SIGN-EXTENDED load at f + 24 (fr_ack b, through
                               frame_f_bytes: ohd_fack);
     run 5   +0x188            a1 = the 4-byte load at s + 1744 (S_inflight_counter Bw);
     +0x18c                    `bne s10, a1`: the two sign-extended 32-bit values are equal exactly when the values
                               are (ohd_eqb_swrap), so a miss runs one instruction to +0x2c0 and concludes by
                               onack_ign_at (onack_ign's second disjunct), and a hit runs one instruction to +0x190
                               and concludes by onack_ntc_at.
   The head stores no byte of G, so both cuts carry the world relation at the ENTRY world Bw and gx_kept_ex over
   onack_wr Bw b holds of every byte of G. The facts the cuts carry are proved once at the memory after run 2c
   (the three written ranges are the frame's header, the frame's 20 shadow bytes and the slot s1 + 16) and moved to
   the cut's memory, whose view is the same (ohd_cur_move, ohd_kd_of_frame: runs 3, 4, 5 and the two branches write
   no byte). What the call keeps (acall_kept_g) runs from the entry to the stack malloc's return (TransportGCg.v
   dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over the three written ranges
   (dk_kept_own_g), at the empty written range; the cut's acall_kept_g over onack_wr Bw b is that, weakened.
   The notice cut also carries the current heap frame (ohd_tframe: trans_tframe_at across the stack malloc and the
   head's own writes, by DgnTransportBCg.v trans_src_ok_inner with decode_rd_ok_fake_kept_ge0), the read-only bytes
   (ohd_rom) and, until the image-B statement gains the premise, onack_gap's instance at TF. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import maybe_online_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_ack_seg_kit on_ack_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
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
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module YF0x := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YF0x.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states of the runs                                  *)
(* ------------------------------------------------------------------ *)

(* No shadow band: the runs that read no shadow byte. *)
Definition OHD_B0 : Z * Z := (0, 0).
(* The shadow base, s9 (atom 25), in every run that reads a shadow byte. *)
Definition OHD_Bx : sv := SOff 25 0.

(* run 1, +0x000 .. +0x070: the stack frame and the four image cells (the shadow-base GOT word and its cell, the
   side-stack flag's GOT word and its cell). *)
Definition ohd_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 96) 0))].
Definition ohd_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition ohd_img_regions : smem := [got_regionP; bcell_regionP 32; ohd_got_uar; ohd_uar_cell].
Definition ohd_regions1 : smem := stack_region ONACK_FRAME :: ohd_img_regions.
Definition ohd_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ohd1 : sstate := mkSS AF_on_ack sr_atoms ohd_regions1 None ohd_facts1.

(* run 2a, +0x074 .. +0x0a4: the frame F in a0 (atom 10), the frame word at s1 + 16 (atom 9). *)
Definition OHD_C1 : Z := AF_on_ack + 0x74.
Definition OHD_C2 : Z := AF_on_ack + 0xa8.
Definition ohd_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition ohd_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, YC4b.PTR 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ohd2 : sstate := mkSS OHD_C1 sr_atoms [ohd_rg_slot] None ohd_facts2.

(* run 2b, +0x0a8 .. +0x0dc: the frame's 24-byte header at s8 (atom 24) and s7 = the frame's shadow address. *)
Definition OHD_C3 : Z := AF_on_ack + 0xe0.
Definition ohd_rg_hdr : YP09.region := YP09.mkRegion (Some 24%nat) 0 24 0 24 [].
Definition ohd_facts3 : facts :=
  mkFacts [(24%nat, YC4b.PTR 6); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ohd3 : sstate := mkSS OHD_C2 sr_atoms [ohd_rg_hdr] None ohd_facts3.

(* run 2c, +0x0e0 .. +0x138: the frame's shadow bytes 0 .. 19 at s7 (atom 23), the UBSan alignment check of s3
   (atom 19, pinned to ONACK_S: 64-aligned, so `bnez a1` at +0x134 is not taken), a0 = s + 212 (a run to +0x13c). *)
Definition OHD_C4 : Z := AF_on_ack + 0x13c.
Definition ohd_rg_sh : YP09.region := YP09.mkRegion (Some 23%nat) 0 20 0 20 [].
Definition ohd_facts4 : facts :=
  mkFacts [(19%nat, mkAF ONACK_S ONACK_S 6); (23%nat, mkAF SHADOW_OFF (2 ^ 46) 0);
           (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ohd4 : sstate := mkSS OHD_C3 sr_atoms [ohd_rg_sh] None ohd_facts4.

(* run 3, +0x13c .. +0x14c: a3 = the shadow address of a0 = s + 212 (atom 10), the check of the 4-byte load there
   and the load itself (atom 33, the 4 bytes of g_s.inflight). *)
Definition OHD_C5 : Z := AF_on_ack + 0x150.
Definition ohd_rg_inf : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition ohd_facts5 : facts :=
  mkFacts [(10%nat, mkAF (ONACK_S + 212) (ONACK_S + 212) 2); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_ohd5 : sstate := mkSS OHD_C4 sr_atoms [ohd_rg_inf] None ohd_facts5.
Definition OHD_SH3 : list shent := [mkSHE 10 0 4].

(* run 4, +0x154 .. +0x184: the UBSan alignment check of s4 (atom 20 = fp, 8-aligned), the checks of the 4-byte
   loads at f + 24 and at s + 1744, and s10 = the sign-extended 4-byte load at f + 24 (atom 33 = fr_ack b). *)
Definition OHD_C6 : Z := AF_on_ack + 0x154.
Definition OHD_C7 : Z := AF_on_ack + 0x188.
Definition ohd_rg_f24 : YP09.region :=
  YP09.mkRegion (Some 20%nat) 24 28 0 0 [YP09.mkChunk 24 (YP09.CVal 4 (SOff 33 0))].
Definition ohd_facts6 : facts :=
  mkFacts [(19%nat, mkAF ONACK_S ONACK_S 6); (20%nat, YC4b.PTR 3); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_ohd6 : sstate := mkSS OHD_C6 sr_atoms [ohd_rg_f24] None ohd_facts6.
Definition OHD_SH4 : list shent := [mkSHE 20 24 28; mkSHE 19 1744 1748].

(* run 5, +0x188: a1 = the 4-byte load at a2 = s + 1744 (atom 12), the value atom 33. *)
Definition OHD_C8 : Z := AF_on_ack + 0x18c.
Definition ohd_rg_cnt : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition ohd_facts7 : facts :=
  mkFacts [(12%nat, mkAF (ONACK_S + 1744) (ONACK_S + 1744) 2); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_ohd7 : sstate := mkSS OHD_C7 sr_atoms [ohd_rg_cnt] None ohd_facts7.

(* The two branches, taken up again from a state with no region, and the one instruction each runs to its cut. *)
Definition ss_ohd_nil (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* The words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition ohd_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* ------------------------------------------------------------------ *)
(* 2. The model and the two tests                                      *)
(* ------------------------------------------------------------------ *)

(* The world's two fields, at their numeral offsets. *)
Lemma ohd_inflight_eq : forall Bw, TW.S_inflight Bw = bv_swrap 32 (TW.u_at Bw (TW.OFF_g_s + 212) 4).
Proof.
intros Bw. unfold TW.S_inflight, TW.s32_at.
replace TW.A_S_inflight with (TW.OFF_g_s + 212) by reflexivity. reflexivity.
Qed.

Lemma ohd_counter_eq : forall Bw, TW.S_inflight_counter Bw = TW.u_at Bw (TW.OFF_g_s + 1744) 4.
Proof.
intros Bw. unfold TW.S_inflight_counter.
replace TW.A_S_inflight_counter with (TW.OFF_g_s + 1744) by reflexivity. reflexivity.
Qed.

Lemma ohd_swrap_range : forall z, - 2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. pose proof (bv_swrap_in_range 32 z ltac:(discriminate)) as H.
change (bv_half_modulus 32) with (2 ^ 31) in H. lia.
Qed.

Lemma ohd_swrap_inj : forall u v, 0 <= u < 2 ^ 32 -> 0 <= v < 2 ^ 32 -> bv_swrap 32 u = bv_swrap 32 v -> u = v.
Proof.
intros u v Hu Hv E. unfold bv_swrap, bv_wrap in E.
change (bv_half_modulus 32) with (2 ^ 31) in E. change (bv_modulus 32) with (2 ^ 32) in E.
Z.div_mod_to_equations. lia.
Qed.

(* `beqz` on a sign-extended 32-bit value: the model's test against 0. *)
Lemma ohd_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* `bne` on two sign-extended 32-bit values: the model's test between the values. *)
Lemma ohd_eqb_swrap : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 x)) (Z_to_bv 64 (bv_swrap 32 y)) = (x =? y).
Proof.
intros x y Hx Hy.
pose proof (ohd_swrap_range x) as Rx. pose proof (ohd_swrap_range y) as Ry.
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec x y) as [-> | Hne]; [apply Z.eqb_refl|].
apply Z.eqb_neq. intros HH. apply Hne. apply (ohd_swrap_inj x y Hx Hy).
set (u := bv_swrap 32 x) in *. set (v := bv_swrap 32 y) in *.
destruct (Z_lt_le_dec u 0) as [Hu | Hu]; destruct (Z_lt_le_dec v 0) as [Hv | Hv].
- rewrite <- (Z.mod_unique u (2 ^ 64) (-1) (u + 2 ^ 64)) in HH by lia.
  rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite <- (Z.mod_unique u (2 ^ 64) (-1) (u + 2 ^ 64)) in HH by lia.
  rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small u (2 ^ 64)) in HH by lia.
  rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small u (2 ^ 64)) in HH by lia. rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. lia.
Qed.

(* A sign-extending 4-byte load of a value below 2 ^ 32. *)
Lemma ohd_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The 4-byte field of struct diginet_frame at f + 24               *)
(* ------------------------------------------------------------------ *)

(* A parse that answered 0 saw at least the 30 header bytes. *)
Lemma ohd_blen : forall b, DSpec.fr_code b = 0 -> (30 <= length b)%nat.
Proof.
intros b H. destruct (Nat.ltb_spec (length b) 30) as [Hlt | Hge]; [|exact Hge].
exfalso. unfold DSpec.fr_code in H.
replace ((length b <? 30)%nat) with true in H by (symmetry; apply Nat.ltb_lt; exact Hlt).
discriminate H.
Qed.

(* The 64 bytes the parse left at f. *)
Lemma ohd_flen : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  length (frame_f_bytes buf b fj) = 64%nat.
Proof.
intros buf b fj H0 HL. pose proof (ohd_blen b H0) as HB.
assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; apply firstn_length_le; lia).
assert (L2 : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; apply firstn_length_le; rewrite length_skipn; lia).
assert (L4 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (apply firstn_length_le; rewrite length_skipn; lia).
assert (L5 : length (skipn 59 fj) = 5%nat) by (rewrite length_skipn, HL; reflexivity).
unfold frame_f_bytes, frame_f_cells. rewrite H0. cbn [Z.eqb].
rewrite length_map. unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes].
rewrite !length_app, ?LMem.length_le2, ?LMem.length_le4, ?LMem.length_le8, L1, L2, L4, L5.
cbn [length]. lia.
Qed.

(* The bytes the parse left at f + 24 are the little-endian bytes of fr_ack b (parse_cells' eighth cell, after
   6 + 6 + 2 + 2 + 2 + 2 + 4 = 24 bytes). *)
Lemma ohd_fack : forall buf b fj k, DSpec.fr_code b = 0 -> length fj = 64%nat -> (k < 4)%nat ->
  nth (24 + k) (frame_f_bytes buf b fj) 0 = YO0f.le_byte (DSpec.fr_ack b) 4 k.
Proof.
intros buf b fj k H0 HL Hk.
pose proof (ohd_blen b H0) as HB.
assert (L1 : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; apply firstn_length_le; lia).
assert (L2 : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; apply firstn_length_le; rewrite length_skipn; lia).
assert (L4 : length (firstn 2 (skipn 14 fj)) = 2%nat) by (apply firstn_length_le; rewrite length_skipn; lia).
assert (RA : 0 <= DSpec.fr_ack b < 2 ^ 32) by (unfold DSpec.fr_ack; apply DSpec.be32_range).
unfold frame_f_bytes, frame_f_cells. rewrite H0. cbn [Z.eqb].
unfold PParse.parse_cells. cbn [LC.cells_bytes LC.cbytes].
rewrite !map_app.
rewrite app_nth2 by (rewrite length_map, L1; lia). rewrite length_map, L1.
rewrite app_nth2 by (rewrite length_map, L2; lia). rewrite length_map, L2.
rewrite app_nth2 by (rewrite length_map, LMem.length_le2; lia). rewrite length_map, LMem.length_le2.
rewrite app_nth2 by (rewrite length_map, L4; lia). rewrite length_map, L4.
rewrite app_nth2 by (rewrite length_map, LMem.length_le2; lia). rewrite length_map, LMem.length_le2.
rewrite app_nth2 by (rewrite length_map, LMem.length_le2; lia). rewrite length_map, LMem.length_le2.
rewrite app_nth2 by (rewrite length_map, LMem.length_le4; lia). rewrite length_map, LMem.length_le4.
rewrite app_nth1 by (rewrite length_map, LMem.length_le4; lia).
replace (24 + k - 6 - 6 - 2 - 2 - 2 - 2 - 4)%nat with k by lia.
assert (EQ : LMem.le4 (Z_to_bv 64 (DSpec.fr_ack b)) = TW.put 4 (DSpec.fr_ack b)).
{ unfold LMem.le4, TW.put. rewrite unsigned_lit_small by lia. reflexivity. }
rewrite EQ.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, TWL.length_put; lia).
rewrite map_nth. apply tw_le_byte_put. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The engine's readers, as the kit states them                     *)
(* ------------------------------------------------------------------ *)

Ltac ohd_reg HS r v H tac :=
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
Ltac ohd_kreg HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    ohd_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac ohd_region HS i HR :=
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
Ltac ohd_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The machine state a run left, named. *)
Ltac ohd_msname HS nm :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) =>
      rename mf into nm
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into nm
  end.
Ltac ohd_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac ohd_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The set of addresses a run's regions can write, computed; each case is closed by lia from the window's bounds. *)
Ltac ohd_windows Hin Hx :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx | ]).

Section hd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma ohd_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_on_ack = transportb_sigma TB_on_ack.
Proof. vm_compute. repeat split. Qed.

(* The valuation of a run whose only extra atom is the shadow base. *)
Definition ohd_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).
(* The valuation of a run that also reads one 4-byte value (atom 33). *)
Definition ohd_Ev (regs : bvmap 5 word) (v : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 v]).

Lemma ohd_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ohd_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold ohd_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ohd_ew_32 : forall regs, ew (ohd_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold ohd_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma ohd_ew_obj : forall regs i, (i < 97)%nat -> ew (ohd_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold ohd_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma ohd_env_img : forall regs, img_env VAL A_LIM (ohd_E regs).
Proof. intros regs. unfold ohd_E. apply Eimg_env. Qed.
Lemma ohd_ewv_reg : forall regs v n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ohd_Ev regs v) n = YK11.getr regs r.
Proof. intros regs v n r Hn. unfold ohd_Ev. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ohd_ewv_32 : forall regs v, ew (ohd_Ev regs v) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs v. unfold ohd_Ev. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma ohd_ewv_33 : forall regs v, ew (ohd_Ev regs v) 33 = Z_to_bv 64 v.
Proof. intros regs v. unfold ohd_Ev. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma ohd_envv_img : forall regs v, img_env VAL A_LIM (ohd_Ev regs v).
Proof. intros regs v. unfold ohd_Ev. apply Eimg_env. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma ohd_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) ohd_img_regions /\
  pairwise_disjoint E ohd_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E0 E96 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct ohd_vals as (V1 & V95 & V0 & V96 & _).
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
  - unfold ohd_img_regions, got_regionP, bcell_regionP, ohd_got_uar, ohd_uar_cell.
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
    unfold ohd_img_regions, got_regionP, bcell_regionP, ohd_got_uar, ohd_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma ohd_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - ONACK_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (ohd_E regs) ss_ohd1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_ack)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_ohd1, ohd_regions1.
  assert (Usp : bv_unsigned (ew (ohd_E regs) 2) = spZ regs)
    by (rewrite (ohd_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (ohd_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply ohd_ew_32.
  destruct (ohd_img_ok ly S W mem md (ohd_E regs) HCELLS HAR
    (ohd_ew_obj regs 1 ltac:(lia)) (ohd_ew_obj regs 95 ltac:(lia))
    (ohd_ew_obj regs 0 ltac:(lia)) (ohd_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct ohd_vals as (V1 & V95 & V0 & V96 & _).
  assert (VB : forall n v0, ew (ohd_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (ohd_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold ONACK_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold ohd_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, ohd_got_uar, ohd_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (ohd_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (ohd_ew_obj regs 95 ltac:(lia)))
      by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (ohd_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (ohd_ew_obj regs 96 ltac:(lia)))
      by (rewrite V96; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, ONACK_FRAME.
    repeat split; first [exact I | lia].
  - unfold ohd_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: the frame F in a0 (atom 10), the slot s1 + 16 writable. *)
Lemma ohd_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= alloc_ceiling -> F mod 64 = 0 ->
  (forall a, spv + 16 <= a < spv + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ohd_E regs) ss_ohd2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OHD_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R25 Hsp Hsp32 HF0 HFc HF64 Hpres.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx. unfold ss_ohd2.
  assert (U2 : bv_unsigned (ew (ohd_E regs) 2) = spv)
    by (rewrite (ohd_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (ohd_E regs) 9) = spv)
    by (rewrite (ohd_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (ohd_E regs) 10) = F)
    by (rewrite (ohd_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (ohd_E regs) 25) = SHADOW_OFF)
    by (rewrite (ohd_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (ohd_E regs) 32) = SHADOW_OFF)
    by (rewrite (ohd_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ohd_rg_slot, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ohd_rg_slot, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ohd_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U25, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2b: the frame's 24 header bytes at s8 (atom 24). *)
Lemma ohd_entry3 : forall (W : world segs) regs mem (F : Z),
  YK11.getr regs 24 = w64 F -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  4096 <= F -> F + 256 <= alloc_ceiling -> F mod 64 = 0 ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ohd_E regs) ss_ohd3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OHD_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F R24 R25 HF0 HFc HF64 Hpres.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx. unfold ss_ohd3.
  assert (U24 : bv_unsigned (ew (ohd_E regs) 24) = F)
    by (rewrite (ohd_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (ohd_E regs) 25) = SHADOW_OFF)
    by (rewrite (ohd_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ohd_rg_hdr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ohd_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ohd_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite U24, U25. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2c: the frame's 20 shadow bytes at s7 (atom 23), s3 = s (atom 19). *)
Lemma ohd_entry4 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 23 = w64 SH -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ohd_E regs) ss_ohd4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OHD_C3)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R19 R23 R25 Hlo Hhi Hpres.
  assert (CS : ONACK_S = 6157888) by reflexivity.
  rewrite restrict_mkst_fx. unfold ss_ohd4.
  assert (U19 : bv_unsigned (ew (ohd_E regs) 19) = ONACK_S)
    by (rewrite (ohd_ew_reg regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew (ohd_E regs) 23) = SH)
    by (rewrite (ohd_ew_reg regs 23 23%bv eq_refl), R23; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (U25 : bv_unsigned (ew (ohd_E regs) 25) = SHADOW_OFF)
    by (rewrite (ohd_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ohd_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U23. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ohd_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ohd_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U23, U25.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF in *;
    first [lia | reflexivity].
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma ohd_inG : forall a, ONACK_S <= a < ONACK_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONACK_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* Every byte of g_s's payload is addressable at every AR state: a whole granule of the record's zero shadow. *)
Lemma ohd_ra : forall ly S (W : world segs) mem md q n,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  ONACK_S <= q -> q + n <= ONACK_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n HZ HAR Hq Hqn x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONACK_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONACK_S + TW.SZ_g_s)
  by (unfold ONACK_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONACK_S (ONACK_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The entry state of run 3: a0 = s + 212 (atom 10), its 4 bytes read (atom 33), its shadow entry. *)
Lemma ohd_entry5 : forall ly S (W : world segs) regs mem md Bw,
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 10 = w64 (ONACK_S + 212) -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (ohd_Ev regs (TW.u_at Bw (TW.OFF_g_s + 212) 4)) ss_ohd5
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OHD_C4)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OHD_Bx OHD_SH3 (ohd_Ev regs (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R10 R25.
set (E := ohd_Ev regs (TW.u_at Bw (TW.OFF_g_s + 212) 4)) in *.
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (CS' : ONACK_S = TB_g_s) by reflexivity.
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 212) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U10 : bv_unsigned (ew E 10) = ONACK_S + 212)
  by (unfold E; rewrite (ohd_ewv_reg regs _ 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
  by (unfold E; rewrite (ohd_ewv_reg regs _ 25 25%bv eq_refl), R25; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = TW.u_at Bw (TW.OFF_g_s + 212) 4)
  by (unfold E; rewrite (ohd_ewv_33 regs _); apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_ohd5.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold ohd_rg_inf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (ONACK_S + 212) 0 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 212) 4));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    rewrite Z.add_0_r, CS'.
    exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 212 4 TMAP_B_ok Htw TMAP_B_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold ohd_rg_inf, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold ohd_facts5, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, U25, U33.
    change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (ohd_ra ly S W mem md (ONACK_S + 212) 4 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U E OHD_Bx = SHADOW_OFF).
  { unfold U, OHD_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OHD_SH3. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OHD_Bx 10 (ONACK_S + 212) 4 (ONACK_S + 212) 0 4 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U10, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The entry state of run 4: f + 24 (atom 20 = fp) with its 4 bytes (atom 33 = fr_ack b), s3 = s (atom 19), and
   the two shadow entries the run's checks read. *)
Lemma ohd_entry6 : forall ly S (W : world segs) regs mem md (fp buf : Z) (b fj : list byte),
  trans_onack_cells B -> @AR rc segs B ly S W mem md ->
  DSpec.fr_code b = 0 -> length fj = 64%nat ->
  garr8 segs (mrestrict (w_H W) mem) fp (frame_f_bytes buf b fj) ->
  decode_rd_ok W mem fp FRAME_F_SIZE ->
  4096 <= fp -> fp + 64 <= alloc_ceiling -> fp mod 8 = 0 ->
  YK11.getr regs 19 = w64 ONACK_S -> YK11.getr regs 20 = w64 fp -> YK11.getr regs 25 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (ohd_Ev regs (DSpec.fr_ack b)) ss_ohd6
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OHD_C6)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OHD_Bx OHD_SH4 (ohd_Ev regs (DSpec.fr_ack b)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md fp buf b fj HSC HAR H0 HL Hg8 Hrd HF0 HFc HF8 R19 R20 R25.
set (E := ohd_Ev regs (DSpec.fr_ack b)) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (RA : 0 <= DSpec.fr_ack b < 2 ^ 32) by (unfold DSpec.fr_ack; apply DSpec.be32_range).
assert (U19 : bv_unsigned (ew E 19) = ONACK_S)
  by (unfold E; rewrite (ohd_ewv_reg regs _ 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = fp)
  by (unfold E; rewrite (ohd_ewv_reg regs _ 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
  by (unfold E; rewrite (ohd_ewv_reg regs _ 25 25%bv eq_refl), R25; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = DSpec.fr_ack b)
  by (unfold E; rewrite (ohd_ewv_33 regs _); apply unsigned_lit_small; lia).
assert (HV : val_mem segs (mrestrict (w_H W) mem) (fp + 24) 4 (DSpec.fr_ack b)).
{ intros j Hj.
  assert (HJ : (24 + j < length (frame_f_bytes buf b fj))%nat)
    by (rewrite (ohd_flen buf b fj H0 HL); lia).
  pose proof (garr8_mbyte segs (mrestrict (w_H W) mem) fp (frame_f_bytes buf b fj) (24 + j) Hg8 HJ) as HM.
  rewrite (ohd_fack buf b fj j H0 HL Hj) in HM.
  replace (fp + 24 + Z.of_nat j) with (fp + Z.of_nat (24 + j)) by lia. exact HM. }
split.
- rewrite restrict_mkst_fx. unfold ss_ohd6.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold ohd_rg_f24, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ fp 24 4 (SOff 33 0) (DSpec.fr_ack b));
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact RA | lia | exact HV].
  + apply pairwise_disjoint_of_extents.
    unfold ohd_rg_f24, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold ohd_facts6, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2]. rewrite U19, U20, U25, U33.
    change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U E OHD_Bx = SHADOW_OFF).
  { unfold U, OHD_Bx. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  pose proof (proj1 (proj2 Hrd)) as HRAf.
  pose proof (ohd_ra ly S W mem md (ONACK_S + 1744) 4 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRAs.
  unfold sh_ok, OHD_SH4. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range segs (w_H W) mem _ OHD_Bx 20 fp FRAME_F_SIZE fp 24 28 HRAf UB).
    * unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
    * unfold FRAME_F_SIZE. lia.
    * unfold FRAME_F_SIZE. lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx.
      pose proof (proj1 (proj2 (proj2 (proj2 Hrd)))) as HAM.
      unfold amem_range, kLowMemEnd, kHighMemBeg, SHADOW_OFF, FRAME_F_SIZE in HAM |- *. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ OHD_Bx 19 (ONACK_S + 1744) 4 ONACK_S 1744 1748 HRAs UB).
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The entry state of run 5: a2 = s + 1744 (atom 12) with its 4 bytes (atom 33). *)
Lemma ohd_entry7 : forall (W : world segs) regs mem Bw,
  tw_at TMAP_B (aview segs (w_H W) mem) Bw -> YK11.getr regs 12 = w64 (ONACK_S + 1744) ->
  st_ok_pi segs VAL (ohd_Ev regs (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) ss_ohd7
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OHD_C7)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem Bw Htw R12.
set (E := ohd_Ev regs (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) in *.
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (CS' : ONACK_S = TB_g_s) by reflexivity.
assert (R33 : 0 <= TW.u_at Bw (TW.OFF_g_s + 1744) 4 < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U12 : bv_unsigned (ew E 12) = ONACK_S + 1744)
  by (unfold E; rewrite (ohd_ewv_reg regs _ 12 12%bv eq_refl), R12; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = TW.u_at Bw (TW.OFF_g_s + 1744) 4)
  by (unfold E; rewrite (ohd_ewv_33 regs _); apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_ohd7.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold ohd_rg_cnt, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val segs E _ (ONACK_S + 1744) 0 4 (SOff 33 0) (TW.u_at Bw (TW.OFF_g_s + 1744) 4));
    [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
  rewrite Z.add_0_r, CS'.
  exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 1744 4 TMAP_B_ok Htw TMAP_B_g_s
    ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
- apply pairwise_disjoint_of_extents.
  unfold ohd_rg_cnt, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- unfold ohd_facts7, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U12, U33.
  change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; first [lia | reflexivity].
Qed.

(* A state with no region, at any pc of the listing: the two branches and the one instruction each runs. *)
Lemma ohd_entry_nil : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (ohd_E regs) (ss_ohd_nil pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_ohd_nil.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma ohd_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' kk,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem'
    md' kk ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' kk HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* A run whose regions have empty write windows changes no byte of the view. *)
Lemma ohd_kd_of_frame : forall (W : world segs) E rs (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b0 wlo whi a, In (b0, wlo, whi) (windows rs) ->
     base_val E b0 + wlo <= a < base_val E b0 + whi -> False) ->
  forall a, aview segs (w_H W) m' a = aview segs (w_H W) m a.
Proof.
intros W E rs m m' HFr HW a.
rewrite (aview_wrap64 segs _ m' a), (aview_wrap64 segs _ m a).
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
apply (kept_of_frame E rs (w_H W) m m' (fun _ : Z => False) HFr HW); [exact Ha | tauto].
Qed.

(* The bytes of a value in memory, read byte by byte through the view. *)
Lemma ohd_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. What the cuts carry, across the head's own writes                *)
(* ------------------------------------------------------------------ *)

(* The current heap frame TF, as trans_tframe_at states it at the entry, at the state after the stack malloc and
   the head's own writes: the call changed no byte of TF's range and no shadow byte of the caller's frames. *)
Lemma ohd_tframe : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc S2 memN mdN (regs : bvmap 5 word) (TF : option TI.tframe) cid pos,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B lyc S2 W memN mdN ->
  frames S2 = (cid, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memN (spZ regs - ONACK_STK) (spZ regs) (fun _ => False) ->
  gx_kept segs TG.G_HARNESS_B W memc W memN ->
  trans_tframe_at B lyc Sc W memc regs ONACK_STK TF ->
  trans_tframe_at B lyc S2 W memN regs ONACK_STK TF.
Proof.
intros LAWS HRU HRE lyc Sc W memc mdc S2 memN mdN regs TF cid pos HARc HAR2 Hfr Hbl
  (K1 & K2 & K3 & K4 & K5 & K6) HGK HT.
destruct TF as [fr|]; [|exact I].
destruct HT as (Ha0 & Hg8 & Hsrc & Hoff).
set (q := TI.tf_addr fr) in *. set (n := Z.of_nat (length (TI.tf_bytes fr))) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : forall f, In f (frames Sc) -> In f (frames S2)) by (intros f Hf; rewrite Hfr; right; exact Hf).
(* the bytes of TF's range are the entry's *)
assert (KV : forall a, q <= a < q + n -> aview segs (w_H W) memN a = aview segs (w_H W) memc a).
{ intros a Ha. destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & _)].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HARc HinA) as (_ & _ & _ & _ & _ & _ & Hn1).
    pose proof (req_size_pos nA (proj1 Hn1)) as [_ Hreq].
    replace a with (bA + (a - bA)) by lia.
    apply (K2 bA nA (a - bA) HinA ltac:(lia)). tauto.
  - destruct HL as [(c & p & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + apply (K4 c p a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | tauto].
    + exact (HGK a (HG a Ha)).
    + destruct (trans_stk_bounds B lyc Sc W memc mdc HARc) as [T1 T2].
      apply K1; [lia | unfold decode_off_win in Hoff; lia].
    + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
      apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
      intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
      unfold TG.G_HARNESS_B_LO in Gh. lia. }
(* the caller's frames' shadow bytes are the entry's *)
assert (KS : forall c p s, In (c, p) (frames Sc) ->
   in_zr s (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8) ->
   aview segs (w_H W) memN s = aview segs (w_H W) memc s).
{ intros c p s Hin Hs. exact (K4 c p s Hin (or_intror Hs) ltac:(tauto)). }
split; [exact Ha0|]. split.
{ eapply garr8_frame; [exact Hg8|]. intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview segs). apply KV. exact Ha. }
split; [|unfold decode_off_win in *; lia].
destruct Hsrc as [(bA & nA & HinA & B1 & B2) | (HL & Hrd)].
- left. exists bA, nA. rewrite Hbl. split; [exact HinA | lia].
- assert (Hrd2 : decode_rd_ok W memN q n).
  { destruct HL as [HF | [(_ & Hsh) | [(S1 & S3) | (_ & Hsh)]]].
    - exact (decode_rd_ok_fake_kept_ge0 B LAWS lyc Sc W W memc memN mdc q n HARc HF Hrd Hn0 KV KS).
    - destruct (Hsh lyc S2 W memN mdN HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W memc memN q n Hrd KV Ha Hh).
    - destruct (stack_zshadow_ra_ge0 B lyc S2 W memN mdN q n HAR2 Hn0 ltac:(lia) ltac:(lia)) as [Ha Hh].
      exact (trans_rd_ok_sh W W memc memN q n Hrd KV Ha Hh).
    - destruct (Hsh lyc S2 W memN mdN HAR2) as [Ha Hh]. exact (trans_rd_ok_sh W W memc memN q n Hrd KV Ha Hh). }
  right. split; [|exact Hrd2].
  destruct HL as [(c & p & Hin & F1 & F2) | [HG | [HS | HR]]].
  + left. exists c, p. split; [exact (Hfin _ Hin) | lia].
  + right; left; exact HG.
  + right; right; left; exact HS.
  + right; right; right; exact HR.
Qed.

(* The read-only bytes notice's callees read, at the same state. *)
Lemma ohd_rom : trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc memN slo shi,
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memN slo shi (fun _ => False) ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W memN.
Proof.
intros HRU HRE lyc Sc W memc memN slo shi (K1 & K2 & K3 & K4 & K5 & K6) HROM a Ha.
rewrite <- (HROM a Ha). destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_B_LO in Gh. lia.
Qed.

(* The facts a cut carries move to a later memory whose view is the same at every address. *)
Lemma ohd_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc kk regs b Bw pos F S2
    mem2 md2 mem3 md3,
  onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc kk regs b Bw pos F lyc S2 W mem2 md2 0 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONACK_CID, pos) :: own) lyc S2 W mem3 md3 (kk + 0) ->
  (forall a, aview segs (w_H W) mem3 a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc kk regs b Bw pos F lyc S2 W mem3 md3 0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc kk regs b Bw pos F S2 mem2 md2 mem3 md3
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. cbv beta in Ho |- *.
  rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (YCbq.rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Lemma ohd_holds : @onack_head_stmt fx rc B MT.
Proof.
unfold onack_head_stmt. intros NTC IGN.
unfold transport_on_ack_cg_holds_stmt.
intros HPCS HCELLS HSC HGU HGNE HROU HRNE LAWS MTL MTF SMP ASF FFL ASM0 AI0 NT0 MO0.
unfold transport_on_ack_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi HDF Htw Hfn Hm HTF HTFG HROM HAP Hcnt Hev.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof (G_HARNESS_gx_ok B HGU) as HGX.
pose proof (G_HARNESS_gx_noerrno B HGNE) as HGN.
assert (HLAWS : @onack_laws rc B MT).
{ unfold onack_laws.
  split; [exact HPCS|]. split; [exact HCELLS|]. split; [exact HSC|]. split; [exact HGU|].
  split; [exact HGNE|]. split; [exact HROU|]. split; [exact HRNE|]. split; [exact LAWS|].
  split; [exact MTL|]. split; [exact MTF|]. split; [exact SMP|]. split; [exact ASF|].
  split; [exact FFL|]. split; [exact HGX | exact HGN]. }
pose proof HDF as (HFC0 & Hbuf0 & Hbufg & Hbufsrc & Hbufwin & HbufG & Hfp0 & Hfp8 & Hfjlen & Hfgarr & Hffake &
  Hfrd & Hfwin).
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FF : ONACK_FRAME = 128) by reflexivity.
assert (CS : ONACK_S = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HBS : 4240 <= ONACK_STK).
{ unfold ONACK_STK, ONACK_FRAME, ONACK_ALIGN.
  lazymatch goal with |- _ <= _ + _ + Z.max ?a ?b =>
    pose proof (Z.le_max_l a b) as Hm0; assert (Ha : a = 4096) by reflexivity end.
  lia. }
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - ONACK_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (ohd_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (ohd_E regs)) by apply ohd_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ohd_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (ohd_E regs) 2) = spZ regs)
  by (rewrite (ohd_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_ack)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* ---- run 1, +0x000 .. +0x070 ---- *)
paj_run_tok RUN HS HJ SHOK OHD_B0.
{ ohd_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1. ohd_msname HS ms1.
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia).
assert (E2' : ew (ohd_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (ohd_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
ohd_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 29536)) R1 ltac:(apply codeptr_val; exact HEI).
ohd_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (ohd_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
ohd_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (ohd_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ohd_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (ohd_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ohd_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
ohd_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (ohd_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
ohd_reg HS (19%bv : bv 5) (w64 ONACK_S) R19
  ltac:(cbn [sv_denot]; rewrite (ohd_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
ohd_reg HS (20%bv : bv 5) (w64 fp) R20
  ltac:(cbn [sv_denot]; rewrite (ohd_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
ohd_reg HS (25%bv : bv 5) (w64 SHADOW_OFF) R25
  ltac:(cbn [sv_denot]; rewrite (ohd_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* the thirteen words the prologue saved, read back from the stack region the run wrote *)
ohd_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) ohd_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold ohd_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) ohd_saved ->
  rdword (aview segs (w_H W) (ms_mem ms1)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold ohd_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms1) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(ohd_u64 (YK11.getr regs r))).
  apply (can_field_of_region (ohd_E regs) _ 2 (spZ regs) _ (-128) 0 (-128) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (ohd_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; ohd_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* ---- +0x070: the class-2 stack malloc ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_2)) mm rom)
    mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (oak_gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP ONACK_CID ASM
    ltac:(unfold ONACK_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 29536)) HJ) end.
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
assert (Hin2 : In (ONACK_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONACK_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ ONACK_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ ONACK_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes ONACK_CID / 8) with 32 in HFsh.
change (fs_frame_bytes ONACK_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc ONACK_CID pos) in *.
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) ohd_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword. rewrite !(proj1 HK1) by lia. reflexivity. }
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
assert (Q19 : YK11.getr regs2 19 = w64 ONACK_S)
  by (transitivity (YK11.getr (ms_regs ms1) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 fp)
  by (transitivity (YK11.getr (ms_regs ms1) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q25 : YK11.getr regs2 25 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms1) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact R25]).
clear HS.
set (memT := ms_mem ms1) in *. set (regsT := ms_regs ms1) in *. clearbody memT regsT. clear ms1.
(* what the call keeps from memc to mem2 (the memory the stack malloc returned) *)
assert (Hwin : forall a, spZ regs - ONACK_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 128 <= x < spZ regs) HFr1);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [rewrite ?Usp in Hx; lia | destruct Hin]. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - ONACK_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - ONACK_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 128 <= x < spZ regs) HAR).
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
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - ONACK_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - ONACK_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGN HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* ---- run 2a, +0x074 .. +0x0a4: the frame word at s1 + 16 ---- *)
pose proof (ohd_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q25 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64
  ltac:(intros a Ha; apply (ohd_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (ohd_E regs2)) by apply ohd_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (ohd_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9a : bv_unsigned (ew (ohd_E regs2) 9) = sp1)
  by (rewrite (ohd_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + OHD_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 OHD_C2.
{ ohd_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9a in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_nil. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a. ohd_msname HS ms3.
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 24) ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 16 <= x < sp1 + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [rewrite ?U9a in Hx; lia | destruct Hin]. }
pose proof HG2a as G2a.
clear HF2a HFr2a HG2a.
(* the registers at +0x0a8 *)
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (Ea := EF) in * end.
assert (Ealo : forall n, (n < 1024)%nat -> ew Ea n = ew (ohd_E regs2) n)
  by (intros n Hn; unfold Ea; rewrite ?ew_ewset_other by lia; reflexivity).
ohd_kreg HS Ealo (ohd_ew_reg regs2) (2%bv : bv 5) 2%nat Q2 T2.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (3%bv : bv 5) 3%nat Q3 T3.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (4%bv : bv 5) 4%nat Q4 T4.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (8%bv : bv 5) 8%nat Q8 T8.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (9%bv : bv 5) 9%nat Q9 T9.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (19%bv : bv 5) 19%nat Q19 T19.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (20%bv : bv 5) 20%nat Q20 T20.
ohd_kreg HS Ealo (ohd_ew_reg regs2) (25%bv : bv 5) 25%nat Q25 T25.
ohd_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (Ealo 10%nat ltac:(lia)), (ohd_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Ha0).
ohd_reg HS (24%bv : bv 5) (w64 F) T24
  ltac:(cbn [sv_denot]; rewrite (Ealo 10%nat ltac:(lia)), (ohd_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Ha0).
(* ---- run 2b, +0x0a8 .. +0x0dc: the frame's 24-byte header, s7 = its shadow address ---- *)
pmkst HS.
clear HS SHOK HEI.
pose proof (ohd_entry3 W (ms_regs ms3) (ms_mem ms3) F T24 T25 ltac:(lia) ltac:(lia) HF64
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a); apply Hfpres; lia)) as HS.
assert (HEI : img_env VAL A_LIM (ohd_E (ms_regs ms3))) by apply ohd_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ohd_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
assert (U24 : bv_unsigned (ew (ohd_E (ms_regs ms3)) 24) = F)
  by (rewrite (ohd_ew_reg (ms_regs ms3) 24 24%bv eq_refl), T24; apply unsigned_lit_small; lia).
assert (U25b : ew (ohd_E (ms_regs ms3)) 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ohd_ew_reg (ms_regs ms3) 25 25%bv eq_refl); exact T25).
assert (U24b : ew (ohd_E (ms_regs ms3)) 24 = Z_to_bv 64 F)
  by (rewrite (ohd_ew_reg (ms_regs ms3) 24 24%bv eq_refl); exact T24).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 OHD_C3.
{ ohd_awr_rs.
  eapply (oak_awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONACK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONACK_CID) with 256.
  change (frame_addr lyc ONACK_CID pos) with F. lia. }
rename HF into HF2b, HFr into HFr2b, HG into HG2b. ohd_msname HS ms4.
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => F <= x < F + 24) HFr2b); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [rewrite ?U24 in Hx; lia | destruct Hin]. }
pose proof HG2b as G2b.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (Eb := EF) in * end.
assert (Eblo : forall n, (n < 1024)%nat -> ew Eb n = ew (ohd_E (ms_regs ms3)) n)
  by (intros n Hn; unfold Eb; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
ohd_reg HS (23%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) V23
  ltac:(exact (can_denot_shadow (ohd_E (ms_regs ms3)) 24 25 F SHADOW_OFF U24b U25b HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (2%bv : bv 5) 2%nat T2 V2.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (3%bv : bv 5) 3%nat T3 V3.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (4%bv : bv 5) 4%nat T4 V4.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (8%bv : bv 5) 8%nat T8 V8.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (9%bv : bv 5) 9%nat T9 V9.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (18%bv : bv 5) 18%nat T18 V18.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (19%bv : bv 5) 19%nat T19 V19.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (20%bv : bv 5) 20%nat T20 V20.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (24%bv : bv 5) 24%nat T24 V24.
ohd_kreg HS Eblo (ohd_ew_reg (ms_regs ms3)) (25%bv : bv 5) 25%nat T25 V25.
(* ---- run 2c, +0x0e0 .. +0x138: the frame's shadow bytes, the alignment check of s ---- *)
pmkst HS.
clear HS SHOK HEI.
pose proof (ohd_entry4 W (ms_regs ms4) (ms_mem ms4) (SHADOW_OFF + F / 8) V19 V23 V25
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2b); apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI : img_env VAL A_LIM (ohd_E (ms_regs ms4))) by apply ohd_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ohd_E (ms_regs ms4)) (mrestrict (w_H W) (ms_mem ms4)))
  by constructor.
assert (U23 : bv_unsigned (ew (ohd_E (ms_regs ms4)) 23) = SHADOW_OFF + F / 8)
  by (rewrite (ohd_ew_reg (ms_regs ms4) 23 23%bv eq_refl), V23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U19c : bv_unsigned (ew (ohd_E (ms_regs ms4)) 19) = ONACK_S)
  by (rewrite (ohd_ew_reg (ms_regs ms4) 19 19%bv eq_refl), V19; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C3)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 OHD_C4.
{ ohd_awr_rs.
  eapply (oak_awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONACK_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U23 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONACK_CID / 8) with 32.
  change (frame_addr lyc ONACK_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF2c, HFr into HFr2c, HG into HG2c. ohd_msname HS ms5.
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2c);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [rewrite ?U23 in Hx; lia | destruct Hin]. }
pose proof HG2c as G2c.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (Ec := EF) in * end.
assert (Eclo : forall n, (n < 1024)%nat -> ew Ec n = ew (ohd_E (ms_regs ms4)) n)
  by (intros n Hn; unfold Ec; rewrite ?ew_ewset_other by lia; reflexivity).
ohd_reg HS (10%bv : bv 5) (w64 (ONACK_S + 212)) X10
  ltac:(cbn [sv_denot]; rewrite (Eclo 19%nat ltac:(lia)), (ohd_ew_reg (ms_regs ms4) 19 19%bv eq_refl), V19;
        unfold w64; rewrite (unsigned_lit_small ONACK_S) by lia; reflexivity).
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (2%bv : bv 5) 2%nat V2 X2.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (3%bv : bv 5) 3%nat V3 X3.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (4%bv : bv 5) 4%nat V4 X4.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (8%bv : bv 5) 8%nat V8 X8.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (9%bv : bv 5) 9%nat V9 X9.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (18%bv : bv 5) 18%nat V18 X18.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (19%bv : bv 5) 19%nat V19 X19.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (20%bv : bv 5) 20%nat V20 X20.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (23%bv : bv 5) 23%nat V23 X23.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (24%bv : bv 5) 24%nat V24 X24.
ohd_kreg HS Eclo (ohd_ew_reg (ms_regs ms4)) (25%bv : bv 5) 25%nat V25 X25.
(* ---- the facts both cuts carry, at the memory of +0x13c ---- *)
pmkst HS.
set (m5 := ms_mem ms5) in *. set (r5 := ms_regs ms5) in *. clearbody m5 r5. clear HS SHOK HEI.
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?bb ?g ?xo ?o ?stk ?sp ?fpp ?l ?s ?w0 ?m0
    ?d0 ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2c a Ha ltac:(intros X; apply Hn; tauto)).
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros X; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a G2c). apply (apresent_grows _ _ _ a G2b).
  exact (apresent_grows _ _ _ a G2a Ha). }
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONACK_CID pos a HAR2 Hin2
    ltac:(change (fs_frame_bytes ONACK_CID) with 256; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (NGS : forall a, F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/
  sp1 + 16 <= a < sp1 + 24 -> ~ inG TG.G_HARNESS_B a).
{ intros a [X | [X | X]];
  [apply NGF; lia | apply NGH; unfold SHADOW_OFF in *; lia | apply NGH; unfold SHADOW_OFF; lia]. }
assert (Htw2 : tw_at TMAP_B (aview segs (w_H W) mem2) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n i Hin Hi.
  apply GK2. unfold inG. apply Exists_exists. exists (b0, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (GXE5 : forall a, inG TG.G_HARNESS_B a -> aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Hg.
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KF5; [lia|]. intros X. exact (NGS a X Hg). }
assert (Htw5 : tw_at TMAP_B (aview segs (w_H W) m5) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) mem2)); [exact Htw2|]. intros b0 n i Hin Hi.
  apply GXE5. unfold inG. apply Exists_exists. exists (b0, n).
  split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (GK5 : gx_kept segs TG.G_HARNESS_B W memc W m5)
  by (intros a Hg; rewrite (GXE5 a Hg); exact (GK2 a Hg)).
(* what the call keeps, at m5: the three ranges are the own frame's bytes, its shadow bytes and the slot *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - ONACK_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - ONACK_STK) (spZ regs) ONACK_CID pos F (flag_addr lyc ONACK_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 16 <= a < sp1 + 24)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes ONACK_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes ONACK_CID / 8) with 32.
      unfold shadow_addr. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
(* the thirteen saved words and the frame's last word, at m5 *)
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) ohd_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply YCbq.rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONACK_SAVED).
{ unfold ONACK_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold ohd_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + ONACK_FBYTES - 8) = Some (flag_addr lyc ONACK_CID pos)).
{ rewrite <- Hflag. unfold ONACK_FBYTES. apply YCbq.rdword_ext. intros i Hi. apply KF5; [lia|].
  pose proof (Z.div_pos F 8 ltac:(lia)) as HF8.
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
assert (CUR5 : onack_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W m5 md5 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj _ (conj HFW5 HFL5)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - split; [lia|]. vm_compute. discriminate.
  - rewrite Eab2. apply Permutation_refl.
  - apply (acall_kept_g_weaken segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - ONACK_STK) (spZ regs)
      (fun _ => False) (onack_wr Bw b)); [tauto | exact KG5]. }
(* the record facts and the caller's facts, as the cuts state them *)
assert (HFIX : onack_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw'
  pos sp1 F).
{ unfold onack_fix.
  split; [exact HJe|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|].
  split; [exact Htp|]. split; [exact H10|]. split; [exact H11|]. split; [exact Hsp16|].
  split; [exact Hlo|]. split; [exact Hhi|]. split; [exact HDF|]. split; [exact Htw|].
  split; [exact Hfn|]. split; [exact Hm|]. split; [exact HTF|]. split; [exact HROM|].
  split; [exact HAP|]. split; [exact Hcnt|]. split; [exact Hev|].
  split; [unfold sp1, ONACK_FRAME; replace (spZ regs - 128) with (spZ regs + -128) by lia; reflexivity|].
  split; [reflexivity|]. split; [exact HF0|]. split; [exact HF64|].
  split; [unfold ONACK_FBYTES; lia | unfold ONACK_FBYTES; exact HFapp]. }
(* the heap frame and the read-only bytes, at m5 *)
assert (HTF5 : trans_tframe_at B lyc S2 W m5 regs ONACK_STK TF)
  by exact (ohd_tframe LAWS HROU HRNE lyc Sc W memc mdc S2 m5 md5 regs TF ONACK_CID pos HAR
      (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfrs2 Eab2 KG5 GK5 HTF).
assert (HROM5 : trans_rom_view_rd W m5)
  by exact (ohd_rom HROU HRNE lyc Sc W memc m5 _ _ KG5 HROM).
(* f's 64 bytes and their shadow, at m5: the call kept every byte of the caller's frames *)
destruct Hffake as (cf & pf & Hinf & HFF1 & HFF2).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cf pf HAR Hinf) as (HfF1 & HfF2 & _).
pose proof (fs_frame_bytes_nonneg cf) as Hfsf.
unfold FRAME_F_SIZE in HFF2.
assert (Hfp4096 : 4096 <= fp) by lia.
assert (HfpC : fp + 64 <= alloc_ceiling) by lia.
assert (KVf : forall a, fp <= a < fp + FRAME_F_SIZE -> aview segs (w_H W) m5 a = aview segs (w_H W) memc a).
{ intros a Ha. destruct KG5 as (_ & _ & _ & K4f & _).
  apply (K4f cf pf a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; unfold FRAME_F_SIZE in Ha; lia | tauto]. }
assert (KSf : forall cid pos0 s, In (cid, pos0) (frames Sc) ->
  in_zr s (shadow_addr (frame_addr lyc cid pos0), fs_frame_bytes cid / 8) ->
  aview segs (w_H W) m5 s = aview segs (w_H W) memc s).
{ intros cid pos0 s Hin Hs. destruct KG5 as (_ & _ & _ & K4f & _).
  exact (K4f cid pos0 s Hin (or_intror Hs) ltac:(tauto)). }
assert (HFG5 : garr8 segs (mrestrict (w_H W) m5) fp (frame_f_bytes buf b fj)).
{ eapply garr8_frame; [exact Hfgarr|]. intros a Ha. rewrite (ohd_flen buf b fj HFC0 Hfjlen) in Ha.
  apply (mbyte_of_aview segs). apply KVf. unfold FRAME_F_SIZE. lia. }
assert (HRD5 : decode_rd_ok W m5 fp FRAME_F_SIZE)
  by exact (decode_rd_ok_fake_kept_ge0 B LAWS lyc Sc W W memc m5 mdc fp FRAME_F_SIZE HAR
      ltac:(exists cf, pf; split; [exact Hinf | unfold FRAME_F_SIZE; lia]) Hfrd
      ltac:(unfold FRAME_F_SIZE; lia) KVf KSf).
assert (RInf : - 2 ^ 31 <= TW.S_inflight Bw < 2 ^ 31)
  by (rewrite ohd_inflight_eq; apply ohd_swrap_range).
assert (RAck : 0 <= DSpec.fr_ack b < 2 ^ 32) by (unfold DSpec.fr_ack; apply DSpec.be32_range).
assert (RCnt : 0 <= TW.S_inflight_counter Bw < 2 ^ 32)
  by (rewrite ohd_counter_eq; exact (TWL.u_at_range Bw _ 4)).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR5.
(* ---- run 3, +0x13c .. +0x14c: the check of s + 212 and the load of S_inflight ---- *)
destruct (ohd_entry5 lyc S2 W r5 m5 md5 Bw HSC HAR5 Htw5 X10 X25) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (ohd_Ev r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4))) by apply ohd_envv_img.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C4)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ohd_awr_rs.
  repeat (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF3, HFr into HFr3, HG into HG3. ohd_msname HS ms6.
assert (KD3 : forall a, aview segs (w_H W) (ms_mem ms6) a = aview segs (w_H W) m5 a).
{ apply (ohd_kd_of_frame W _ _ m5 (ms_mem ms6) HFr3).
  intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
assert (GR3 : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem ms6) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG3 Ha)).
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E3 := EF) in * end.
assert (E3lo : forall n, (n < 1024)%nat -> ew E3 n = ew (ohd_Ev r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) n)
  by (intros n Hn; unfold E3; rewrite ?ew_ewset_other by lia; reflexivity).
assert (EV10 : ew (ohd_Ev r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) 10 = Z_to_bv 64 (ONACK_S + 212))
  by (rewrite (ohd_ewv_reg r5 _ 10 10%bv eq_refl); exact X10).
assert (EV25 : ew (ohd_Ev r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ohd_ewv_reg r5 _ 25 25%bv eq_refl); exact X25).
ohd_reg HS (13%bv : bv 5) (w64 (SHADOW_OFF + (ONACK_S + 212) / 8)) Z13
  ltac:(cbn [sv_denot]; rewrite (E3lo 10%nat ltac:(lia)), (E3lo 25%nat ltac:(lia)), EV10, EV25;
        unfold w64, ONACK_S, TB_g_s, SHADOW_OFF; vm_compute; reflexivity).
ohd_reg HS (11%bv : bv 5) (Z_to_bv 64 (TW.S_inflight Bw)) Z11
  ltac:(rewrite ohd_inflight_eq;
        exact (ohd_sext E3 33 (TW.u_at Bw (TW.OFF_g_s + 212) 4)
                 ltac:(rewrite (E3lo 33%nat ltac:(lia)); exact (ohd_ewv_33 r5 _))
                 (TWL.u_at_range Bw _ 4))).
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (2%bv : bv 5) 2%nat X2 Z2.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (3%bv : bv 5) 3%nat X3 Z3.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (4%bv : bv 5) 4%nat X4 Z4.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (8%bv : bv 5) 8%nat X8 Z8.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (9%bv : bv 5) 9%nat X9 Z9.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (18%bv : bv 5) 18%nat X18 Z18.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (19%bv : bv 5) 19%nat X19 Z19.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (20%bv : bv 5) 20%nat X20 Z20.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (23%bv : bv 5) 23%nat X23 Z23.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (24%bv : bv 5) 24%nat X24 Z24.
ohd_kreg HS E3lo (ohd_ewv_reg r5 (TW.u_at Bw (TW.OFF_g_s + 212) 4)) (25%bv : bv 5) 25%nat X25 Z25.
(* ---- +0x150: `beqz a1` ---- *)
pmkst HS.
clear HS SHOK HEI.
pose proof (ohd_entry_nil W (ms_regs ms6) (ms_mem ms6) OHD_C5) as HS.
assert (HEI : img_env VAL A_LIM (ohd_E (ms_regs ms6))) by apply ohd_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ohd_E (ms_regs ms6)) (mrestrict (w_H W) (ms_mem ms6)))
  by constructor.
assert (D11 : sv_denot (ohd_E (ms_regs ms6)) (SOff 11 0) = Z_to_bv 64 (TW.S_inflight Bw))
  by (cbn [sv_denot]; rewrite (ohd_ew_reg (ms_regs ms6) 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
      exact Z11).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C5)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOK OHD_B0.
- (* S_inflight Bw = 0: the ignored cut, by onack_ign's first disjunct *)
  cbn [branch_taken] in Hc. rewrite D11 in Hc.
  change (sv_denot (ohd_E (ms_regs ms6)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (ohd_eqb0 _ RInf) in Hc. apply Z.eqb_eq in Hc.
  assert (HIGN : onack_ign Bw b = true)
    by (unfold onack_ign; rewrite (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 ONACK_IGN.
  { ohd_awr_rs. apply awr_ok_x_nil. }
  rename HF into HFi, HFr into HFri, HG into HGi.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (Ei := EF) in *; rename mf into msI end.
  assert (Eilo : forall n, (n < 1024)%nat -> ew Ei n = ew (ohd_E (ms_regs ms6)) n)
    by (intros n Hn; unfold Ei; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (KDi : forall a, aview segs (w_H W) (ms_mem msI) a = aview segs (w_H W) (ms_mem ms6) a).
  { apply (ohd_kd_of_frame W _ _ (ms_mem ms6) (ms_mem msI) HFri).
    intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
  assert (KDt : forall a, aview segs (w_H W) (ms_mem msI) a = aview segs (w_H W) m5 a)
    by (intros a; rewrite KDi; exact (KD3 a)).
  assert (GRt : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msI) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HGi (GR3 a Ha))).
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (2%bv : bv 5) 2%nat Z2 P2.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (3%bv : bv 5) 3%nat Z3 P3.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (4%bv : bv 5) 4%nat Z4 P4.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (8%bv : bv 5) 8%nat Z8 P8.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (9%bv : bv 5) 9%nat Z9 P9.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (18%bv : bv 5) 18%nat Z18 P18.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (19%bv : bv 5) 19%nat Z19 P19.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (23%bv : bv 5) 23%nat Z23 P23.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (24%bv : bv 5) 24%nat Z24 P24.
  ohd_kreg HS Eilo (ohd_ew_reg (ms_regs ms6)) (25%bv : bv 5) 25%nat Z25 P25.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_IGN)) mm rom) mdx) Q) end.
  apply (IGN HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F S2
    (ms_mem msI) _ (ms_regs msI) HFIX).
  + unfold onack_ign_cur.
    refine (conj (ohd_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F S2 m5 md5
      (ms_mem msI) _ CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KDt GRt) (conj Eab2 (conj _ (conj _ HIGN)))).
    * intros a Hg Hn. rewrite KDt. exact (GK5 a Hg).
    * apply (tw_kept TMAP_B (aview segs (w_H W) m5)); [exact Htw5 | intros x _; exact (KDt x)].
  + unfold onack_regs_ign, onack_regs_rel.
    refine (conj (conj P2 (conj _ (conj _ (conj P8 (conj P9 (conj P18 (conj P23 P24)))))))
      (conj P19 P25)).
    * rewrite P3. symmetry. exact Hgp.
    * rewrite P4. symmetry. exact Htp.
- (* S_inflight Bw <> 0: on to the check of f + 24 *)
  cbn [branch_taken] in Hc. rewrite D11 in Hc.
  change (sv_denot (ohd_E (ms_regs ms6)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (ohd_eqb0 _ RInf) in Hc. apply Z.eqb_neq in Hc. rename Hc into HNE0.
  paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 OHD_C6.
  { ohd_awr_rs. apply awr_ok_x_nil. }
  rename HF into HF7, HFr into HFr7, HG into HG7.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (Ea4 := EF) in *; rename mf into ms7 end.
  assert (Ea4lo : forall n, (n < 1024)%nat -> ew Ea4 n = ew (ohd_E (ms_regs ms6)) n)
    by (intros n Hn; unfold Ea4; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (KD7 : forall a, aview segs (w_H W) (ms_mem ms7) a = aview segs (w_H W) m5 a).
  { intros a. transitivity (aview segs (w_H W) (ms_mem ms6) a); [|exact (KD3 a)].
    apply (ohd_kd_of_frame W _ _ (ms_mem ms6) (ms_mem ms7) HFr7).
    intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
  assert (GR7 : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem ms7) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG7 (GR3 a Ha))).
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (2%bv : bv 5) 2%nat Z2 Q2'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (3%bv : bv 5) 3%nat Z3 Q3'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (4%bv : bv 5) 4%nat Z4 Q4'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (8%bv : bv 5) 8%nat Z8 Q8'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (9%bv : bv 5) 9%nat Z9 Q9'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (13%bv : bv 5) 13%nat Z13 Q13'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (18%bv : bv 5) 18%nat Z18 Q18'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (19%bv : bv 5) 19%nat Z19 Q19'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (20%bv : bv 5) 20%nat Z20 Q20'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (23%bv : bv 5) 23%nat Z23 Q23'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (24%bv : bv 5) 24%nat Z24 Q24'.
  ohd_kreg HS Ea4lo (ohd_ew_reg (ms_regs ms6)) (25%bv : bv 5) 25%nat Z25 Q25'.
  (* ---- run 4, +0x154 .. +0x184: the alignment check of f and the two instrumented loads ---- *)
  pmkst HS.
  set (ms8 := ms7) in *. clearbody ms8. clear HS SHOK HEI.
  assert (HFG7 : garr8 segs (mrestrict (w_H W) (ms_mem ms8)) fp (frame_f_bytes buf b fj)).
  { eapply garr8_frame; [exact HFG5|]. intros a Ha. apply (mbyte_of_aview segs). rewrite KD7. reflexivity. }
  assert (HRD7 : decode_rd_ok W (ms_mem ms8) fp FRAME_F_SIZE)
    by exact (trans_rd_ok_view W W m5 (ms_mem ms8) fp FRAME_F_SIZE HRD5
                (fun a _ => KD7 a) (fun s _ => KD7 s)).
  destruct (ohd_entry6 lyc S2 W (ms_regs ms8) (ms_mem ms8) _ fp buf b fj HSC
    (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
    HFC0 Hfjlen HFG7 HRD7 Hfp4096 HfpC Hfp8 Q19' Q20' Q25') as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (ohd_Ev (ms_regs ms8) (DSpec.fr_ack b))) by apply ohd_envv_img.
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C6)) mm rom) mdx) Q) end.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OHD_C7.
  { ohd_awr_rs.
    repeat (apply awr_ok_x_cons;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  rename HF into HF9, HFr into HFr9, HG into HG9.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E4 := EF) in *; rename mf into ms9 end.
  assert (E4lo : forall n, (n < 1024)%nat -> ew E4 n = ew (ohd_Ev (ms_regs ms8) (DSpec.fr_ack b)) n)
    by (intros n Hn; unfold E4; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (KD9 : forall a, aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) m5 a).
  { intros a. transitivity (aview segs (w_H W) (ms_mem ms8) a); [|exact (KD7 a)].
    apply (ohd_kd_of_frame W _ _ (ms_mem ms8) (ms_mem ms9) HFr9).
    intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
  assert (GR9 : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem ms9) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG9 (GR7 a Ha))).
  ohd_reg HS (26%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (DSpec.fr_ack b))) Z26
    ltac:(exact (ohd_sext E4 33 (DSpec.fr_ack b)
                   ltac:(rewrite (E4lo 33%nat ltac:(lia)); exact (ohd_ewv_33 (ms_regs ms8) _)) RAck)).
  ohd_reg HS (12%bv : bv 5) (w64 (ONACK_S + 1744)) Z12
    ltac:(cbn [sv_denot]; rewrite (E4lo 19%nat ltac:(lia)),
          (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b) 19 19%bv eq_refl), Q19';
          unfold w64, ONACK_S, TB_g_s; vm_compute; reflexivity).
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (2%bv : bv 5) 2%nat Q2' N2.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (3%bv : bv 5) 3%nat Q3' N3.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (4%bv : bv 5) 4%nat Q4' N4.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (8%bv : bv 5) 8%nat Q8' N8.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (9%bv : bv 5) 9%nat Q9' N9.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (13%bv : bv 5) 13%nat Q13' N13.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (18%bv : bv 5) 18%nat Q18' N18.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (19%bv : bv 5) 19%nat Q19' N19.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (20%bv : bv 5) 20%nat Q20' N20.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (23%bv : bv 5) 23%nat Q23' N23.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (24%bv : bv 5) 24%nat Q24' N24.
  ohd_kreg HS E4lo (ohd_ewv_reg (ms_regs ms8) (DSpec.fr_ack b)) (25%bv : bv 5) 25%nat Q25' N25.
  (* ---- run 5, +0x188: the load of S_inflight_counter ---- *)
  pmkst HS.
  set (msA := ms9) in *. clearbody msA. clear HS SHOK HEI.
  assert (HtwA : tw_at TMAP_B (aview segs (w_H W) (ms_mem msA)) Bw)
    by (apply (tw_kept TMAP_B (aview segs (w_H W) m5)); [exact Htw5 | intros x _; exact (KD9 x)]).
  pose proof (ohd_entry7 W (ms_regs msA) (ms_mem msA) Bw HtwA Z12) as HS.
  assert (HEI : img_env VAL A_LIM (ohd_Ev (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)))
    by apply ohd_envv_img.
  assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent)
    (ohd_Ev (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (mrestrict (w_H W) (ms_mem msA))) by constructor.
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C7)) mm rom) mdx) Q) end.
  paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 OHD_C8.
  { ohd_awr_rs.
    repeat (apply awr_ok_x_cons;
      [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
    apply awr_ok_x_nil. }
  rename HF into HFq, HFr into HFrq, HG into HGq.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E5 := EF) in *; rename mf into msB end.
  assert (E5lo : forall n, (n < 1024)%nat ->
    ew E5 n = ew (ohd_Ev (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) n)
    by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (KDB : forall a, aview segs (w_H W) (ms_mem msB) a = aview segs (w_H W) m5 a).
  { intros a. transitivity (aview segs (w_H W) (ms_mem msA) a); [|exact (KD9 a)].
    apply (ohd_kd_of_frame W _ _ (ms_mem msA) (ms_mem msB) HFrq).
    intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
  assert (GRB : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HGq (GR9 a Ha))).
  ohd_reg HS (11%bv : bv 5) (Z_to_bv 64 (bv_swrap 32 (TW.S_inflight_counter Bw))) ZB11
    ltac:(rewrite ohd_counter_eq;
          exact (ohd_sext E5 33 (TW.u_at Bw (TW.OFF_g_s + 1744) 4)
                   ltac:(rewrite (E5lo 33%nat ltac:(lia)); exact (ohd_ewv_33 (ms_regs msA) _))
                   (TWL.u_at_range Bw _ 4))).
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (2%bv : bv 5) 2%nat N2 M2.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (3%bv : bv 5) 3%nat N3 M3.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (4%bv : bv 5) 4%nat N4 M4.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (8%bv : bv 5) 8%nat N8 M8.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (9%bv : bv 5) 9%nat N9 M9.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (13%bv : bv 5) 13%nat N13 M13.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (18%bv : bv 5) 18%nat N18 M18.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (19%bv : bv 5) 19%nat N19 M19.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (20%bv : bv 5) 20%nat N20 M20.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (23%bv : bv 5) 23%nat N23 M23.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (24%bv : bv 5) 24%nat N24 M24.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (25%bv : bv 5) 25%nat N25 M25.
  ohd_kreg HS E5lo (ohd_ewv_reg (ms_regs msA) (TW.u_at Bw (TW.OFF_g_s + 1744) 4)) (26%bv : bv 5) 26%nat Z26 M26.
  (* ---- +0x18c: `bne s10, a1` ---- *)
  pmkst HS.
  set (msC := msB) in *. clearbody msC. clear HS SHOK HEI.
  pose proof (ohd_entry_nil W (ms_regs msC) (ms_mem msC) OHD_C8) as HS.
  assert (HEI : img_env VAL A_LIM (ohd_E (ms_regs msC))) by apply ohd_env_img.
  assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (ohd_E (ms_regs msC)) (mrestrict (w_H W) (ms_mem msC)))
    by constructor.
  assert (D26 : sv_denot (ohd_E (ms_regs msC)) (SOff 26 0) = Z_to_bv 64 (bv_swrap 32 (DSpec.fr_ack b)))
    by (cbn [sv_denot]; rewrite (ohd_ew_reg (ms_regs msC) 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact M26).
  assert (DB11 : sv_denot (ohd_E (ms_regs msC)) (SOff 11 0)
    = Z_to_bv 64 (bv_swrap 32 (TW.S_inflight_counter Bw)))
    by (cbn [sv_denot]; rewrite (ohd_ew_reg (ms_regs msC) 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact ZB11).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OHD_C8)) mm rom) mdx) Q) end.
  psrr_branch_tok RUN BR HS SHOK OHD_B0.
  + (* fr_ack b <> S_inflight_counter Bw: the ignored cut, by onack_ign's second disjunct *)
    cbn [branch_taken] in Hc. rewrite D26, DB11 in Hc.
    rewrite (ohd_eqb_swrap _ _ RAck RCnt) in Hc.
    apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
    assert (HIGN : onack_ign Bw b = true).
    { unfold onack_ign. rewrite (proj2 (Z.eqb_neq _ _) Hc). cbn [negb]. apply Bool.orb_true_r. }
    paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 ONACK_IGN.
    { ohd_awr_rs. apply awr_ok_x_nil. }
    rename HF into HFz, HFr into HFrz, HG into HGz.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (Ej := EF) in *; rename mf into msD end.
    assert (Ejlo : forall n, (n < 1024)%nat -> ew Ej n = ew (ohd_E (ms_regs msC)) n)
      by (intros n Hn; unfold Ej; rewrite ?ew_ewset_other by lia; reflexivity).
    assert (KDD : forall a, aview segs (w_H W) (ms_mem msD) a = aview segs (w_H W) m5 a).
    { intros a. transitivity (aview segs (w_H W) (ms_mem msC) a); [|exact (KDB a)].
      apply (ohd_kd_of_frame W _ _ (ms_mem msC) (ms_mem msD) HFrz).
      intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
    assert (GRD : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msD) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HGz (GRB a Ha))).
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (2%bv : bv 5) 2%nat M2 K2.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (3%bv : bv 5) 3%nat M3 K3.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (4%bv : bv 5) 4%nat M4 K4.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (8%bv : bv 5) 8%nat M8 K8.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (9%bv : bv 5) 9%nat M9 K9.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (18%bv : bv 5) 18%nat M18 K18.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (19%bv : bv 5) 19%nat M19 K19.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (23%bv : bv 5) 23%nat M23 K23.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (24%bv : bv 5) 24%nat M24 K24.
    ohd_kreg HS Ejlo (ohd_ew_reg (ms_regs msC)) (25%bv : bv 5) 25%nat M25 K25.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_IGN)) mm rom) mdx) Q) end.
    apply (IGN HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw' pos sp1 F S2
      (ms_mem msD) _ (ms_regs msD) HFIX).
    * unfold onack_ign_cur.
      refine (conj (ohd_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F S2 m5 md5
        (ms_mem msD) _ CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KDD GRD) (conj Eab2 (conj _ (conj _ HIGN)))).
      -- intros a Hg Hn. rewrite KDD. exact (GK5 a Hg).
      -- apply (tw_kept TMAP_B (aview segs (w_H W) m5)); [exact Htw5 | intros x _; exact (KDD x)].
    * unfold onack_regs_ign, onack_regs_rel.
      refine (conj (conj K2 (conj _ (conj _ (conj K8 (conj K9 (conj K18 (conj K23 K24)))))))
        (conj K19 K25)).
      -- rewrite K3. symmetry. exact Hgp.
      -- rewrite K4. symmetry. exact Htp.
  + (* fr_ack b = S_inflight_counter Bw: the notice cut *)
    cbn [branch_taken] in Hc. rewrite D26, DB11 in Hc.
    rewrite (ohd_eqb_swrap _ _ RAck RCnt) in Hc.
    apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
    assert (HNIGN : onack_ign Bw b = false).
    { unfold onack_ign. rewrite (proj2 (Z.eqb_neq _ _) HNE0). rewrite (proj2 (Z.eqb_eq _ _) Hc). reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK OHD_B0 ONACK_NTC.
    { ohd_awr_rs. apply awr_ok_x_nil. }
    rename HF into HFn, HFr into HFrn, HG into HGn.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (En := EF) in *; rename mf into msN end.
    assert (Enlo : forall n, (n < 1024)%nat -> ew En n = ew (ohd_E (ms_regs msC)) n)
      by (intros n Hn; unfold En; rewrite ?ew_ewset_other by lia; reflexivity).
    assert (KDN : forall a, aview segs (w_H W) (ms_mem msN) a = aview segs (w_H W) m5 a).
    { intros a. transitivity (aview segs (w_H W) (ms_mem msC) a); [|exact (KDB a)].
      apply (ohd_kd_of_frame W _ _ (ms_mem msC) (ms_mem msN) HFrn).
      intros b0 wlo whi x Hin Hx. ohd_windows Hin Hx; first [lia | destruct Hin]. }
    assert (GRN : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msN) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HGn (GRB a Ha))).
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (2%bv : bv 5) 2%nat M2 J2.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (3%bv : bv 5) 3%nat M3 J3.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (4%bv : bv 5) 4%nat M4 J4.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (8%bv : bv 5) 8%nat M8 J8.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (9%bv : bv 5) 9%nat M9 J9.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (13%bv : bv 5) 13%nat M13 J13.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (18%bv : bv 5) 18%nat M18 J18.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (19%bv : bv 5) 19%nat M19 J19.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (20%bv : bv 5) 20%nat M20 J20.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (23%bv : bv 5) 23%nat M23 J23.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (24%bv : bv 5) 24%nat M24 J24.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (25%bv : bv 5) 25%nat M25 J25.
    ohd_kreg HS Enlo (ohd_ew_reg (ms_regs msC)) (26%bv : bv 5) 26%nat M26 J26.
    (* the heap frame, the read-only bytes and the gap's instance at the cut's memory *)
    assert (HTFN : trans_tframe_at B lyc S2 W (ms_mem msN) regs ONACK_STK TF).
    { destruct TF as [fr|]; [|exact I].
      destruct HTF5 as (Hta & Htg & Hts & Hto).
      split; [exact Hta|]. split.
      - eapply garr8_frame; [exact Htg|]. intros a Ha. apply (mbyte_of_aview segs). rewrite KDN. reflexivity.
      - split; [|exact Hto].
        apply (trans_src_ok_view B lyc S2 W W m5 (ms_mem msN) (TI.tf_addr fr)
                 (Z.of_nat (length (TI.tf_bytes fr))) Hts);
          intros; rewrite KDN; reflexivity. }
    assert (HROMN : trans_rom_view_rd W (ms_mem msN))
      by (intros a Ha; rewrite KDN; exact (HROM5 a Ha)).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONACK_NTC)) mm rom) mdx) Q) end.
    apply (NTC HLAWS AI0 NT0 MO0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf b fj TF Bw Bw'
      pos sp1 F S2 (ms_mem msN) _ (ms_regs msN) HFIX).
    * unfold onack_ntc_cur.
      refine (conj (ohd_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F S2 m5 md5
        (ms_mem msN) _ CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KDN GRN)
        (conj Eab2 (conj _ (conj _ (conj HTFN (conj HTFG (conj HROMN HNIGN))))))).
      -- intros a Hg Hn. rewrite KDN. exact (GK5 a Hg).
      -- apply (tw_kept TMAP_B (aview segs (w_H W) m5)); [exact Htw5 | intros x _; exact (KDN x)].
    * unfold onack_regs_ntc, onack_regs_ign, onack_regs_rel.
      refine (conj (conj (conj J2 (conj _ (conj _ (conj J8 (conj J9 (conj J18 (conj J23 J24)))))))
        (conj J19 J25)) (conj J13 (conj J20 J26))).
      -- rewrite J3. symmetry. exact Hgp.
      -- rewrite J4. symmetry. exact Htp.
Qed.

End hd.

(* The head piece of the walk of on_ack (on_ack_segs.v onack_head_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onack_head : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onack_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ohd_holds fx rc B MT). Qed.

Print Assumptions onack_head.
