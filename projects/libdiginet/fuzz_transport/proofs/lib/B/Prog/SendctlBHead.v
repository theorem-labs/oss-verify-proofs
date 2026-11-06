(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1398 of its 1567 lines of code are new or changed and 970 lines of the source are left out. *)
(* SendctlBHead: Lemma sendctl_head : sendctl_head_stmt (lib/B/Prog/SendctlBCut.v), the head piece of image B's walk
   of send_control (fuzz_transport.asan-ubsan 0x86ed4 = transportb_sigma TB_send_control, AF_send_control = 0x5c34 of
   lib/B/Prog/DgnTransportBList.v), from the entry to the frame-build cut sendctl_fb_at (+0x1ac). It also opens the
   walk: it takes the premises of send_control_cg.v transport_send_control_cg_holds_stmt, builds SendctlBCut.v
   sendctl_laws and sendctl_callees out of them and hands the cut sendctl_fix, sendctl_fb_cur and sendctl_regs_fb.
   The twin of image A's lib/A/Prog/SendctlHead.v; image B stores the frame pointer at s1 + 24 EARLY (+0x0ac, before
   the frame header, where image A stores it at +0x14c) and adds the UBSan alignment check of s (+0x12c `andi a0,
   s3, 7`, +0x144 `bnez a0` to the trap word 0xc0001073 at +0x3bc = 0x87290).
   The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 []); the runs are the
   position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x:
     run 1   +0x000 .. +0x078  the frame (`addi sp, sp, -128`, `sd zero, 0(sp)`, the 12 saves of SENDCTL_SAVED),
                               s0 = the entry sp, the realign into s1, s4 = klp, s6 = kp, s7 = ack, s5 = cmd, the two
                               runtime cells through their GOT words (the UAR flag word is 1, so `beqz a2` at +0x070
                               is not taken), s10 = the shadow base, s3 = s, a0 = 160, up to `jal
                               __asan_stack_malloc_2`;
     +0x078                    the class-2 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F). The
                               count premise count_cid 2 (frames Sc) + 1 < fs_frames 2 gives its count premise, so
                               the call returns a frame and the real-stack arm at +0x090 .. +0x0a8 is not taken;
     run 2a  +0x07c .. +0x0dc  s2 = s9 = F, `bnez s2` taken, the 8-byte store of the frame pointer at s1 + 24
                               (image B's early slot store) and the frame's 24-byte header (0x41b58ab3, the
                               description string, the function's address), s8 = SHADOW_OFF + F / 8;
     run 2b  +0x0e0 .. +0x13c  the frame's shadow bytes 0 .. 3 := 0xf1, 12 .. 15 := 0xf2, 16 .. 17 := 0,
                               18 .. 19 := 0xf3, 8 .. 10 := 0, 11 := 4, 4 .. 7 := 0 (a run to +0x140), and
                               a0 = s & 7, which is 0: the run's atom fact pins s3 to TB_g_s = 0x5df640, a multiple
                               of 8;
     run 2c  +0x140 .. +0x1a8  the 4-byte store of 0 at F + 128, `bnez a0` (a0 = 0: the UBSan alignment check of s
                               does not reach the trap word), the checked 4-byte load at s + 160, the five stores
                               into h (the 12 bytes at F + 132 are diginet_frame_build_cg.v frame_fb_hdr_bytes
                               (S_host_counter Bw) ack 0 cmd 0), the checked 4-byte load at s + 20, a7 = the sum
                               mode, s7 = f = F + 32 and the eight argument registers, to the cut. Its two
                               instrumented checks read a shadow byte of g_s's payload, 0 at every AR state
                               (trans_sendctl_cells), so neither `bnez` is taken; the engine decides them from the
                               shadow entries SCH_SH.
   What the call keeps (acall_kept_g) runs from the entry to the stack malloc's return (TransportGCg.v
   dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over the four written ranges
   (dk_kept_own_g: the slot s1 + 24 in the call's window, the frame's header, its shadow bytes, h), and is read at
   the memory with the out cell put back (SendctlBCut.v acall_kept_g_gover; at the entry the two memories are the
   same, so TransportGCg.v acall_kept_g_mem_ext and sch_kept_mem1 carry it with no presence reasoning). The out
   cell's own bytes are a write right of the caller's journal (transport_twr_ok_g), so each is kept by the clause of
   acall_kept_g its placement names, and its shadow byte is the AR state's: the machine stack's is 0
   (CanKit.v can_stack_addressable), a block's is the block's (YCbq.v al_shadow at both states, the blocks and the
   chunks being the call's), a caller frame's is kept (DgnTransportBCg.v decode_rd_ok_fake_kept). *)
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
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h YC1i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGFrameB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg SendctlBCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
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
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The four symbolic runs                                           *)
(* ------------------------------------------------------------------ *)

Definition SCH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x078: the two runtime cells are the GOT word 0xa3d48 -> 0xac680 (the UAR flag word, 1) and
   the GOT word 0xa3cf0 -> 0xac678 (the shadow base, atom 32). *)
Definition sch_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 96) 0))].
Definition sch_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition sch_img_regions : smem := [got_regionP; bcell_regionP 32; sch_got_uar; sch_uar_cell].
Definition sch_regions1 : smem := stack_region SENDCTL_FRAME :: sch_img_regions.
Definition sch_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sch1 : sstate := mkSS AF_send_control sr_atoms sch_regions1 None sch_facts1.

(* run 2a, +0x07c .. +0x0dc: after the stack malloc the frame F is in a0 (atom 10); the run writes the frame
   pointer into the slot at s1 + 24 (atom 9 = sp1; image B stores it here, before the header, where image A
   stores it at +0x14c) and the frame's 24-byte header, and stops at the first shadow store. *)
Definition SCH_C1 : Z := AF_send_control + 0x7c.
Definition sch_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition sch_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition sch_regions2 : smem := [sch_rg_slot; sch_rg_hdr].
Definition sch_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sch2 : sstate := mkSS SCH_C1 sr_atoms sch_regions2 None sch_facts2.

(* run 2b, +0x0e0 .. +0x13c: s8 (atom 24) holds the frame's shadow address; the run writes its shadow bytes
   0 .. 19, up to +0x140. Its `andi a0, s3, 7` at +0x12c (image B's UBSan alignment check of s) folds to 0, since
   atom 19 (s3 = s) is pinned to TB_g_s, a multiple of 8; the run leaves a0 = 0, which run 2c's fact carries, so
   the `bnez a0` at +0x144 does not reach the trap word at +0x3bc. *)
Definition SCH_C2 : Z := AF_send_control + 0xe0.
Definition SCH_C3 : Z := AF_send_control + 0x140.
Definition sch_rg_sh : YP09.region := YP09.mkRegion (Some 24%nat) 0 20 0 20 [].
Definition sch_facts3 : facts :=
  mkFacts [(19%nat, mkAF SENDCTL_S SENDCTL_S 6); (24%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_sch3 : sstate := mkSS SCH_C2 sr_atoms [sch_rg_sh] None sch_facts3.

(* run 2c, +0x140 .. +0x1a8: the 4 bytes of g_s at s + 20 (atom 34, the sum mode) and at s + 160 (atom 33, the
   host counter), and h at F + 128 (atom 25 = F). a0 (atom 10) is 0, the value run 2b left: the `bnez a0` at
   +0x144 is not taken. The two instrumented checks read the shadow entries SCH_SH. *)
Definition sch_rg_s20 : YP09.region :=
  YP09.mkRegion (Some 19%nat) 20 24 0 0 [YP09.mkChunk 20 (YP09.CVal 4 (SOff 34 0))].
Definition sch_rg_s160 : YP09.region :=
  YP09.mkRegion (Some 19%nat) 160 164 0 0 [YP09.mkChunk 160 (YP09.CVal 4 (SOff 33 0))].
Definition sch_rg_h : YP09.region := YP09.mkRegion (Some 25%nat) 128 144 128 144 [].
Definition sch_regions4 : smem := [sch_rg_s20; sch_rg_s160; sch_rg_h].
Definition sch_facts4 : facts :=
  mkFacts [(10%nat, mkAF 0 0 0); (19%nat, mkAF SENDCTL_S SENDCTL_S 6);
           (25%nat, mkAF 4096 (2 ^ 47 - 256) 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
(* a0 holds the literal 0 that run 2b's `andi a0, s3, 7` left (s = TB_g_s is a multiple of 8), so the engine
   decides the `bnez a0` at +0x144 and the trap word at +0x3bc is unreached. *)
Definition sch_regs4 : list sv := sr_set sr_atoms 10%bv (SLit 0).
Definition ss_sch4 : sstate := mkSS SCH_C3 sch_regs4 sch_regions4 None sch_facts4.
(* The shadow entries of run 2c's two checks: g_s's payload at [s + 16, s + 168) (its shadow is 0 at every AR
   state) and h's two granules at [F + 128, F + 144) (run 2b set their shadow bytes 16 and 17 to 0). *)
Definition SCH_SH : list shent := [mkSHE 19 16 168; mkSHE 25 128 144].
Definition SCH_Bx : sv := SOff 26 0.

(* ------------------------------------------------------------------ *)
(* 2. Small arithmetic and byte lemmas                                 *)
(* ------------------------------------------------------------------ *)

(* `srli a1, a0, 3` on s + 160. *)
Lemma sch_srl3 : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 ->
  sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)) = Z_to_bv 64 ((v + c) / 8).
Proof.
intros E n c v Hn Hv Hc0 Hc.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_SRL (SOff n c) (SLit 3)))). f_equal.
change (U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn. rewrite !unsigned_lit_small by lia.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (YP0m.zcanon_small (v + c)) by lia. rewrite YP0m.zcanon_small by lia. lia.
Qed.

(* The 4-byte sign-extended load of a g_s field is the model's signed field. *)
Lemma sch_sext : forall E n Bw o, ew E n = Z_to_bv 64 (TW.u_at Bw o 4) ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (TW.s32_at Bw o).
Proof.
intros E n Bw o H. pose proof (TWL.u_at_range Bw o 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The hull of an 8-byte aligned cell is the hull of its first byte. *)
Lemma sch_hull8 : forall (rd : reader) q, q mod 8 = 0 -> shadow_hull_vis rd q 1 -> shadow_hull_vis rd q 8.
Proof.
intros rd q Hq H s Hs. apply H.
assert (E : (q + 7) / 8 = q / 8).
{ pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq, Z.add_0_r in D.
  rewrite D at 1. replace (8 * (q / 8) + 7) with (7 + (q / 8) * 8) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small 7 8) by lia. lia. }
unfold shadow_hull_vis in *. unfold shadow_addr in *.
replace (q + 8 - 1) with (q + 7) in Hs by lia. replace (q + 1 - 1) with q by lia.
rewrite E in Hs. exact Hs.
Qed.

(* Two addresses of one granule have one shadow byte. *)
Lemma sch_same_gran : forall q x, q mod 8 = 0 -> q <= x < q + 8 -> x / 8 = q / 8.
Proof.
intros q x Hq Hx. pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq, Z.add_0_r in D.
replace x with (x - q + (q / 8) * 8) by lia. rewrite Z.div_add by lia.
rewrite (Z.div_small (x - q) 8) by lia. lia.
Qed.

(* TW.zs of TW.bs is the identity on byte values. *)
Lemma sch_zs_bs : forall l, bytes_ok l -> TW.zs (TW.bs l) = l.
Proof.
intros l H. unfold TW.zs, TW.bs. rewrite map_map.
induction H as [|x l Hx Hl IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hx.
Qed.

(* The 12 bytes of the header the code stores, as a list. *)
Lemma sch_hdr_list : forall send ack cmd, 0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= cmd < 2 ^ 8 ->
  frame_fb_hdr_bytes send ack 0 cmd 0 =
  [send mod 256; send / 256 mod 256; send / 65536 mod 256; send / 16777216 mod 256;
   ack mod 256; ack / 256 mod 256; ack / 65536 mod 256; ack / 16777216 mod 256;
   0; 0; cmd mod 256; 0].
Proof.
intros send ack cmd Hs Ha Hc.
unfold frame_fb_hdr_bytes, frame_fb_hdr_cells.
cbn [LC.cells_bytes LC.cbytes app map].
unfold LMem.le4, LMem.le2, DSpec.b8, DSpec.bz.
change (bv_unsigned (w64 send)) with (send mod 2 ^ 64).
change (bv_unsigned (w64 ack)) with (ack mod 2 ^ 64).
change (bv_unsigned (w64 0)) with (0 mod 2 ^ 64).
rewrite (Z.mod_small send (2 ^ 64)) by lia. rewrite (Z.mod_small ack (2 ^ 64)) by lia.
change (0 mod 2 ^ 64) with 0.
cbn [Z_to_le_bytes map app].
rewrite ?Z.shiftr_0_l.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite ?Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite ?Z.div_div by lia. change (256 * 256) with 65536. change (65536 * 256) with 16777216.

reflexivity.
Qed.

(* The twelve words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition sch_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv)].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac sch_reg HS r v H tac :=
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
Ltac sch_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac sch_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac sch_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section head. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma sch_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_send_control = transportb_sigma TB_send_control.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma sch_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) sch_img_regions /\
  pairwise_disjoint E sch_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct sch_vals as (V1 & V93 & V0 & V94 & _).
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
  - unfold sch_img_regions, got_regionP, bcell_regionP, sch_got_uar, sch_uar_cell.
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
    unfold sch_img_regions, got_regionP, bcell_regionP, sch_got_uar, sch_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 95) (VAL (A_OBJ 95)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 96) (VAL (A_OBJ 96)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The valuations: the 32 registers, the shadow base (atom 32) and, in run 2c, the two 4-byte fields of g_s the
   code loads (atoms 33 and 34). *)
Definition sch_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).
Definition sch_E4 (regs : bvmap 5 word) (Bw : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF;
    Z_to_bv 64 (TW.u_at Bw TW.A_S_host_counter 4); Z_to_bv 64 (TW.u_at Bw TW.A_S_cfg_sum_mode 4)]).

Lemma sch_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (sch_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold sch_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma sch_ew_32 : forall regs, ew (sch_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold sch_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma sch_ew_obj : forall regs i, (i < 97)%nat -> ew (sch_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold sch_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma sch_env_img : forall regs, img_env VAL A_LIM (sch_E regs).
Proof. intros regs. unfold sch_E. apply Eimg_env. Qed.
Lemma sch_ew4_reg : forall regs Bw n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (sch_E4 regs Bw) n = YK11.getr regs r.
Proof. intros regs Bw n r Hn. unfold sch_E4. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma sch_ew4_x : forall regs Bw j, (j < 3)%nat ->
  ew (sch_E4 regs Bw) (32 + j) = nth j [w64 SHADOW_OFF;
    Z_to_bv 64 (TW.u_at Bw TW.A_S_host_counter 4); Z_to_bv 64 (TW.u_at Bw TW.A_S_cfg_sum_mode 4)] (Z_to_bv 64 0).
Proof. intros regs Bw j Hj. unfold sch_E4. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma sch_env_img4 : forall regs Bw, img_env VAL A_LIM (sch_E4 regs Bw).
Proof. intros regs Bw. unfold sch_E4. apply Eimg_env. Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma sch_inG : forall a, SENDCTL_S <= a < SENDCTL_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, SENDCTL_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma sch_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* A one-byte region cell holding a literal, read through the view. *)
Lemma sch_chunk1 : forall E (H : word -> bool) (m : word -> option byte) n b cs lo hi wlo whi od v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (YP09.CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
  aview segs H m (b + od) = Some v.
Proof.
intros E H m n b cs lo hi wlo whi od v HR Hb Hin Hv.
pose proof (can_field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 1%N (SLit v) v HR Hb Hin
  eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
rewrite (can_aview_of_val1 segs H m (b + od) v HV). f_equal.
try unfold YO0f.le_byte; try unfold YG0f.le_byte; try unfold le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity.
Qed.

(* The bytes of a cell the run keeps keep their values. *)
Lemma sch_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H m' (q + j) = aview segs H m (q + j)) ->
  garr8 segs (mrestrict H m) q l -> garr8 segs (mrestrict H m') q l.
Proof.
intros H m m' q l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (val_mem_kept segs H H m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros i Hi. change (Z.of_nat 1) with 1 in Hi. replace (q + Z.of_nat j + i) with (q + Z.of_nat j) by lia.
apply Hk. lia.
Qed.

(* acall_kept_g reads its FIRST memory only byte by byte too. *)
Lemma sch_kept_mem1 : forall G lyc Sc (W W2 : world segs) (ma mb mem2 : word -> option byte) slo shi (E : Z -> Prop),
  (forall x, mb x = ma x) ->
  acall_kept_g segs B G lyc Sc W ma W2 mem2 slo shi E ->
  acall_kept_g segs B G lyc Sc W mb W2 mem2 slo shi E.
Proof.
intros G lyc Sc W W2 ma mb mem2 slo shi E Hx (K1 & K2 & K3 & K4 & K5 & K6).
assert (HV : forall a, aview segs (w_H W) mb a = aview segs (w_H W) ma a)
  by (intros a; apply (aview_eq_of segs); unfold mrestrict; rewrite Hx; reflexivity).
assert (HP : forall a, apresent (w_H W) mb a -> apresent (w_H W) ma a)
  by (intros a (Hh & b0 & Hb0); split; [exact Hh | exists b0; rewrite <- Hx; exact Hb0]).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite HV. exact (K1 a Ha Hw).
- intros b0 n i Hb Hi Hn. rewrite HV. exact (K2 b0 n i Hb Hi Hn).
- intros a Hi HnG Hno He. rewrite HV. exact (K3 a Hi HnG Hno He).
- intros cid pos a Hin Hr Hn. rewrite HV. exact (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. exact (K5 a Ha Hw (HP a Hp)).
- intros a Ha. exact (K6 a Ha).
Qed.

(* gover outs m m is m. *)
Lemma sch_gover_same : forall (outs : list (Z * Z)) (m : word -> option byte) x, gover outs m m x = m x.
Proof. intros outs m x. unfold gover. destruct (inGb outs (bv_unsigned x)); reflexivity. Qed.

(* (F + c) / 8 when both are 8-aligned. *)
Lemma sch_div8_add : forall F c, F mod 8 = 0 -> c mod 8 = 0 -> (F + c) / 8 = F / 8 + c / 8.
Proof.
intros F c HF Hc. pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF, Z.add_0_r in DF.
pose proof (Z.div_mod c 8 ltac:(lia)) as DC. rewrite Hc, Z.add_0_r in DC.
replace (F + c) with ((F / 8 + c / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* ---- the entry states of the four runs ---- *)

Lemma sch_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - SENDCTL_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (sch_E regs) ss_sch1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_send_control)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_sch1, sch_regions1.
  assert (Usp : bv_unsigned (ew (sch_E regs) 2) = spZ regs)
    by (rewrite (sch_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (sch_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply sch_ew_32.
  destruct (sch_img_ok ly S W mem md (sch_E regs) HCELLS HAR
    (sch_ew_obj regs 1 ltac:(lia)) (sch_ew_obj regs 95 ltac:(lia))
    (sch_ew_obj regs 0 ltac:(lia)) (sch_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct sch_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (sch_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (sch_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold SENDCTL_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold sch_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, sch_got_uar, sch_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (sch_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (sch_ew_obj regs 95 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (sch_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (sch_ew_obj regs 96 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, SENDCTL_FRAME.
    repeat split; first [exact I | lia].
  - unfold sch_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma sch_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F + 256 <= spv -> F mod 64 = 0 ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  (forall a, spv + 24 <= a < spv + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sch_E regs) ss_sch2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SCH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R26 Hsp Hsp32 HF0 HFs HFsp HF64 Hpframe Hpslot.
  rewrite restrict_mkst_fx. unfold ss_sch2, sch_regions2.
  assert (U2 : bv_unsigned (ew (sch_E regs) 2) = spv)
    by (rewrite (sch_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (sch_E regs) 9) = spv)
    by (rewrite (sch_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (sch_E regs) 10) = F)
    by (rewrite (sch_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew (sch_E regs) 26) = SHADOW_OFF)
    by (rewrite (sch_ew_reg regs 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (sch_E regs) 32) = SHADOW_OFF)
    by (rewrite (sch_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold sch_rg_slot, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + unfold sch_rg_hdr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold sch_rg_slot, sch_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold sch_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U26, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma sch_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 19 = w64 SENDCTL_S -> YK11.getr regs 24 = w64 SH ->
  SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (sch_E regs) ss_sch3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SCH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R19 R24 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_sch3.
  assert (CS : SENDCTL_S = 6157888) by reflexivity.
  assert (U19 : bv_unsigned (ew (sch_E regs) 19) = SENDCTL_S)
    by (rewrite (sch_ew_reg regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; rewrite CS; lia).
  assert (U24 : bv_unsigned (ew (sch_E regs) 24) = SH)
    by (rewrite (sch_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold sch_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold sch_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold sch_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U24. change (2 ^ 6) with 64.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    rewrite ?CS; unfold SHADOW_OFF in *; first [reflexivity | lia].
Qed.

Lemma sch_entry4 : forall ly2 S2 (W : world segs) regs mem md2 Bw (spv F : Z),
  trans_sendctl_cells B -> @AR rc segs B ly2 S2 W mem md2 ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 9 = w64 spv -> 2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  (forall a, spv + 24 <= a < spv + 32 -> apresent (w_H W) mem a) ->
  YK11.getr regs 10 = w64 0 ->
  YK11.getr regs 19 = w64 SENDCTL_S -> YK11.getr regs 25 = w64 F -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F + 256 <= spv -> F mod 64 = 0 -> in_app F 256 ->
  (F + 256 <= SENDCTL_S \/ SENDCTL_S + TW.SZ_g_s <= F) ->
  (forall a, F + 128 <= a < F + 144 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 2 -> aview segs (w_H W) mem (SHADOW_OFF + F / 8 + 16 + i) = Some 0) ->
  st_ok_pi segs VAL (sch_E4 regs Bw) ss_sch4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + SCH_C3)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SCH_Bx SCH_SH (sch_E4 regs Bw) (mrestrict (w_H W) mem).
Proof.
intros ly2 S2 W regs mem md2 Bw spv F HSC HAR Htw R9 Hsp Hsp32 Hpslot R10 R19 R25 R26 HF0 HFs HFsp HF64 HFapp
  HFG Hph Hsh16.
assert (CS : SENDCTL_S = 6157888) by reflexivity.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (U9 : bv_unsigned (ew (sch_E4 regs Bw) 9) = spv)
  by (rewrite (sch_ew4_reg regs Bw 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew (sch_E4 regs Bw) 10) = 0)
  by (rewrite (sch_ew4_reg regs Bw 10 10%bv eq_refl), R10; reflexivity).
assert (U19 : bv_unsigned (ew (sch_E4 regs Bw) 19) = SENDCTL_S)
  by (rewrite (sch_ew4_reg regs Bw 19 19%bv eq_refl), R19; apply unsigned_lit_small; rewrite CS; lia).
assert (U25 : bv_unsigned (ew (sch_E4 regs Bw) 25) = F)
  by (rewrite (sch_ew4_reg regs Bw 25 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew (sch_E4 regs Bw) 26) = SHADOW_OFF)
  by (rewrite (sch_ew4_reg regs Bw 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E33 : ew (sch_E4 regs Bw) 33 = Z_to_bv 64 (TW.u_at Bw TW.A_S_host_counter 4))
  by exact (sch_ew4_x regs Bw 1 ltac:(lia)).
assert (E34 : ew (sch_E4 regs Bw) 34 = Z_to_bv 64 (TW.u_at Bw TW.A_S_cfg_sum_mode 4))
  by exact (sch_ew4_x regs Bw 2 ltac:(lia)).
pose proof (TWL.u_at_range Bw TW.A_S_host_counter 4) as R33r.
pose proof (TWL.u_at_range Bw TW.A_S_cfg_sum_mode 4) as R34r.
assert (U33 : bv_unsigned (ew (sch_E4 regs Bw) 33) = TW.u_at Bw TW.A_S_host_counter 4)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew (sch_E4 regs Bw) 34) = TW.u_at Bw TW.A_S_cfg_sum_mode 4)
  by (rewrite E34; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_sch4, sch_regions4.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + intros rr. destruct (Z.eq_dec (bv_unsigned rr) 10) as [E10|E10].
    * assert (Err : rr = 10%bv) by (apply bv_eq; rewrite E10; reflexivity). subst rr.
      unfold sch_regs4. rewrite sr_get_set_same by reflexivity.
      rewrite R10. reflexivity.
    * unfold sch_regs4. rewrite sr_get_set_other by (intros ->; apply E10; vm_compute; reflexivity).
      exact (regs_ok_Eimg_Ereg regs _ rr).
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [sch_rg_s20 sch_rg_s160 sch_rg_h
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [rewrite CS; lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ SENDCTL_S 20 4 (SOff 34 0) (TW.u_at Bw TW.A_S_cfg_sum_mode 4));
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | exact R34r | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 20 4 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * rewrite U19. split; [rewrite CS; lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ SENDCTL_S 160 4 (SOff 33 0) (TW.u_at Bw TW.A_S_host_counter 4));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33r | lia |].
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_s TB_g_s TW.SZ_g_s 160 4 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    * rewrite U25. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hph. lia.
  + apply pairwise_disjoint_of_extents.
    unfold sch_rg_s20, sch_rg_s160, sch_rg_h, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19, U25. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold TW.SZ_g_s in HFG. rewrite CS in *.
    repeat split; first [exact I | lia].
  + unfold sch_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U19, U25, U26, U33, U34.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    rewrite ?CS; unfold SHADOW_OFF; first [reflexivity | lia].
- assert (UB : U (sch_E4 regs Bw) SCH_Bx = SHADOW_OFF).
  { unfold U, SCH_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  unfold sh_ok, SCH_SH. constructor; [|constructor; [|constructor]].
  + (* g_s's payload: its shadow is 0 at every AR state *)
    assert (HRA : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (SENDCTL_S + 16) 152).
    { destruct (decode_zshadow_ra B ly2 S2 W mem md2 SENDCTL_S (SENDCTL_S + TW.SZ_g_s) (SENDCTL_S + 16) 152
        HAR HSC ltac:(lia) ltac:(rewrite CS; vm_compute; discriminate)
        ltac:(rewrite CS; unfold TW.SZ_g_s; vm_compute; discriminate)) as [HA _]. exact HA. }
    apply (shent_ok_of_range segs (w_H W) mem _ SCH_Bx 19 (SENDCTL_S + 16) 152 SENDCTL_S 16 168 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. rewrite CS in Hx. unfold SHADOW_OFF. lia.
  + (* h's two granules: run 2b set their shadow bytes to 0 *)
    assert (HRA : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (F + 128) 16).
    { intros x Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr.
      destruct (Z_lt_le_dec x (F + 136)) as [Hx1|Hx1].
      - replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 16 + 0); [apply Hsh16; lia|].
        rewrite (sch_same_gran (F + 128) x ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)).
        rewrite (sch_div8_add F 128 HF8 eq_refl). change (128 / 8) with 16. lia.
      - replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 16 + 1); [apply Hsh16; lia|].
        rewrite (sch_same_gran (F + 136) x ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)).
        rewrite (sch_div8_add F 136 HF8 eq_refl). change (136 / 8) with 17. lia. }
    apply (shent_ok_of_range segs (w_H W) mem _ SCH_Bx 25 (F + 128) 16 F 128 144 HRA UB).
    * unfold U. cbn [sv_denot]. rewrite U25, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx.
      pose proof (proj1 alloc_ceiling_val) as AC.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac sch_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    sch_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (sch_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac sch_kreg4 HS rg Bwx r n Q H :=
  lazymatch type of Q with _ = ?v =>
    sch_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (sch_ew4_reg rg Bwx n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* The stack bounds of a later layout are the journal's. *)
Lemma sch_ly_stk : forall n ly1 ly2, layout_le n ly1 ly2 ->
  ly_stk_lo ly2 = ly_stk_lo ly1 /\ ly_stk_hi ly2 = ly_stk_hi ly1.
Proof. intros n ly1 ly2 H. unfold layout_le in H. tauto. Qed.

(* (q + c) / 8 * 8 at an 8-aligned q. *)
Lemma sch_align8 : forall q c, q mod 8 = 0 -> 0 <= c < 8 -> (q + c) / 8 * 8 = q.
Proof.
intros q c Hq Hc. rewrite (sch_same_gran q (q + c) Hq ltac:(lia)).
pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq, Z.add_0_r in D. lia.
Qed.

(* bv_unsigned of a 64-bit literal, read modulo a smaller width. *)
Lemma sch_umod : forall z w, 0 < w <= 64 -> bv_unsigned (Z_to_bv 64 z) mod 2 ^ w = z mod 2 ^ w.
Proof.
intros z w Hw. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | apply Z.pow_pos_nonneg; lia | apply Z.pow_pos_nonneg; lia |].
exists (2 ^ (64 - w)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma sch_swrap32 : forall z, 0 <= z < 2 ^ 32 -> bv_swrap 32 z mod 2 ^ 32 = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
Z.div_mod_to_equations. lia.
Qed.

(* The 4-byte sign-extended load of a 32-bit value. *)
Lemma sch_sext_g : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u H Hu. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma sch_sext_mod : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ 32 = u.
Proof.
intros E n u H Hu. rewrite (sch_sext_g E n u H Hu).
rewrite (sch_umod (bv_swrap 32 u) 32 ltac:(lia)). apply sch_swrap32. exact Hu.
Qed.

Lemma sch_off0_mod : forall E n u w, 0 < w <= 64 -> ew E n = Z_to_bv 64 u ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ w = u mod 2 ^ w.
Proof.
intros E n u w Hw H. cbn [sv_denot]. rewrite H.
rewrite (sch_umod (bv_unsigned (Z_to_bv 64 u) + 0) w Hw), Z.add_0_r.
exact (sch_umod u w Hw).
Qed.

(* One byte of a val_mem cell. *)
Lemma sch_vm_byte : forall (m : word -> option byte) a (n : nat) v j,
  0 <= v < 2 ^ (8 * Z.of_nat n) -> (j < n)%nat -> val_mem segs m a n v ->
  val_mem segs m (a + Z.of_nat j) 1 (v / 2 ^ (8 * Z.of_nat j) mod 256) /\
  0 <= v / 2 ^ (8 * Z.of_nat j) mod 256 < 256.
Proof.
intros m a n v j Hv Hj HV. split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (Hk0 : (k = 0)%nat) by lia. subst k.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, (HV j Hj). f_equal. f_equal.
try unfold YO0f.le_byte; try unfold YG0f.le_byte; try unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat n))) by exact Hv.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite !Z.shiftr_div_pow2 by lia.
rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma sch_vm_byte' : forall (m : word -> option byte) a (n : nat) v j b t,
  0 <= v < 2 ^ (8 * Z.of_nat n) -> (j < n)%nat -> val_mem segs m a n v ->
  b = a + Z.of_nat j -> t = v / 2 ^ (8 * Z.of_nat j) mod 256 ->
  val_mem segs m b 1 t /\ 0 <= t < 256.
Proof. intros m a n v j b t Hv Hj HV -> ->. exact (sch_vm_byte m a n v j Hv Hj HV). Qed.

Lemma sendctl_head : @sendctl_head_stmt fx rc B MT.
Proof.
unfold sendctl_head_stmt. intros FB.
unfold transport_send_control_cg_holds_stmt.
intros HPCS HCELLS HSC HROU HRNE LAWS MTL MTF SMP ASF FFL HGX HGNE ASM0 FBC CPY IOS.
unfold transport_send_control_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 Hsp16 Hlo Hhi Hcmd Hack HKP Htw Hfn Hmodel HROM HFLY HCMDL Hcnt Hev.
pose proof (ASM0 fx) as ASM.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (sch_ly_stk _ _ _ Hly) as [ELO EHI].
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SENDCTL_STK = 8656) by reflexivity.
assert (CS : SENDCTL_S = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* ---- run 1 ---- *)
assert (Hpres1 : forall a, spZ regs - SENDCTL_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; unfold SENDCTL_FRAME in Ha; lia).
pose proof (sch_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (sch_E regs)) by apply sch_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (sch_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (sch_E regs) 2) = spZ regs)
  by (rewrite (sch_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUNTO.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_send_control)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
paj_run_tok RUN HS HJ SHOK SCH_B0.
{ sch_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia).
assert (E2' : ew (sch_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (sch_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
sch_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 23728)) R1 ltac:(apply codeptr_val; exact HEI).
sch_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (sch_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
sch_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
sch_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
sch_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
sch_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (sch_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
sch_reg HS (19%bv : bv 5) (w64 SENDCTL_S) R19
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
sch_reg HS (20%bv : bv 5) (w64 klp) R20
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 14 14%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H14).
sch_reg HS (21%bv : bv 5) (w64 cmd) R21
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
sch_reg HS (22%bv : bv 5) (w64 kp) R22
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 13 13%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H13).
sch_reg HS (23%bv : bv 5) (w64 (bv_swrap 32 ack)) R23
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 12 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
sch_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) R26
  ltac:(cbn [sv_denot]; rewrite (sch_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sch_reg HS (27%bv : bv 5) (YK11.getr regs 27) R27
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs 27 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
sch_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r0 : bv 5), In (o, r0) sch_saved -> -96 <= o <= -8).
{ intros o r0 Hin. unfold sch_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r0 : bv 5), In (o, r0) sch_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r0))).
{ intros o r0 Hin. unfold sch_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r0))
    ltac:(pose proof (bv_unsigned_in_range 64 (YK11.getr regs r0)) as Hrg; unfold bv_modulus in Hrg;
          change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia)).
  apply (can_field_of_region (sch_E regs) _ 2 (spZ regs) _ (-128) 0 (-128) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r0)) 0) (bv_unsigned (YK11.getr regs r0)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (sch_ew_reg regs (Z.to_nat (bv_unsigned r0)) r0 ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; pose proof (bv_unsigned_in_range 64 (YK11.getr regs r0)) as Hrg; unfold bv_modulus in Hrg;
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia
  | cbn; lia ]. }
clear HRsk.
(* ---- the class-2 stack malloc ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_2)) mm rom) mdx) Q)
  end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP SENDCTL_CID ASM
    ltac:(unfold SENDCTL_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 23728)) HJ) end.
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
assert (Hin2 : In (SENDCTL_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ SENDCTL_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ SENDCTL_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ SENDCTL_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes SENDCTL_CID / 8) with 32 in HFsh.
change (fs_frame_bytes SENDCTL_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc SENDCTL_CID pos) in *.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (HS8 : (SHADOW_OFF + F / 8) mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  assert (E8 : F / 8 = 8 * (F / 64))
    by (rewrite D at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
  rewrite E8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia.
  apply Z_mod_mult. }
assert (HFG : F + 256 <= SENDCTL_S \/ SENDCTL_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) SENDCTL_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (SENDCTL_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso. unfold TW.SZ_g_s in h2.
  apply (frm_img segs B LAWS lyc S2 W mem2 md2 SENDCTL_CID pos (Z.max F SENDCTL_S) HAR2 Hin2);
  [change (fs_frame_bytes SENDCTL_CID) with 256; fold F; rewrite CS in *; lia|].
  apply trans_g_img. apply sch_inG. unfold TW.SZ_g_s. rewrite CS in *. lia. }
assert (HFsp : F + 256 <= sp1) by lia.
assert (HSV2 : forall (o : Z) (r0 : bv 5), In (o, r0) sch_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r0))).
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
assert (Q19 : YK11.getr regs2 19 = w64 SENDCTL_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 klp)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q21 : YK11.getr regs2 21 = w64 cmd)
  by (transitivity (YK11.getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]).
assert (Q22 : YK11.getr regs2 22 = w64 kp)
  by (transitivity (YK11.getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22]).
assert (Q23 : YK11.getr regs2 23 = w64 (bv_swrap 32 ack))
  by (transitivity (YK11.getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23]).
assert (Q26 : YK11.getr regs2 26 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]).
assert (Q27 : YK11.getr regs2 27 = YK11.getr regs 27)
  by (transitivity (YK11.getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27]).
clear HS.
set (memT := ms_mem ms) in *. set (regsT := ms_regs ms) in *. clearbody memT regsT. clear ms.
assert (Hwin : forall a, spZ regs - SENDCTL_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => spZ regs - 128 <= x < spZ regs) HFr1);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - SENDCTL_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - SENDCTL_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 128 <= x < spZ regs) HAR).
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
    pose proof (Z.div_pos (frame_addr lyc cid pos0) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - SENDCTL_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - SENDCTL_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ SENDCTL_CID pos a HAR2 Hin2
    ltac:(change (fs_frame_bytes SENDCTL_CID) with 256; fold F; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
(* ---- run 2a: the frame pointer in the slot at s1 + 24, then the frame header ---- *)
pose proof (sch_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q26 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) ltac:(lia) HF64
  ltac:(intros a Ha; apply Hfpres; lia)
  ltac:(intros a Ha; apply (sch_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (sch_E regs2)) by apply sch_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (sch_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U10' : bv_unsigned (ew (sch_E regs2) 10) = F)
  by (rewrite (sch_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (U9' : bv_unsigned (ew (sch_E regs2) 9) = sp1)
  by (rewrite (sch_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SCH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK SCH_B0.
{ sch_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9' in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDCTL_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDCTL_CID) with 256.
  change (frame_addr lyc SENDCTL_CID pos) with F. lia. }
clear HEI0 HEI1. rename HF into HF2a, HFr into HFr2a, HG into HG2a.
assert (EF10 : ew (sch_E regs2) 10 = Z_to_bv 64 F) by (rewrite (sch_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF26 : ew (sch_E regs2) 26 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (sch_ew_reg regs2 26 26%bv eq_refl); exact Q26).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
sch_reg HS (24%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T24
  ltac:(exact (can_denot_shadow (sch_E regs2) 10 26 F SHADOW_OFF EF10 EF26 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
sch_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. sch_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
sch_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. sch_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
sch_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. sch_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
sch_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. sch_kreg HS regs2 (21%bv : bv 5) 21%nat Q21 T21.
sch_kreg HS regs2 (22%bv : bv 5) 22%nat Q22 T22. sch_kreg HS regs2 (23%bv : bv 5) 23%nat Q23 T23.
sch_kreg HS regs2 (26%bv : bv 5) 26%nat Q26 T26. sch_kreg HS regs2 (27%bv : bv 5) 27%nat Q27 T27.
sch_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
sch_reg HS (25%bv : bv 5) (w64 F) T25
  ltac:(cbn [sv_denot]; rewrite (sch_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
pose proof HG2a as G2a.
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 32 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => sp1 + 24 <= x < sp1 + 32 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U9', ?U10' in Hx; first [left; lia | right; lia | lia] |]).
  destruct Hin. }
clear HF2a HFr2a HG2a.
(* ---- run 2b: the frame's shadow bytes 0 .. 19 ---- *)
pmkst HS.
set (MS3 := ms) in *. clearbody MS3. clear HS. clear ms.
pose proof (sch_entry3 W (ms_regs MS3) (ms_mem MS3) (SHADOW_OFF + F / 8) T19 T24
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI3 : img_env VAL A_LIM (sch_E (ms_regs MS3))) by apply sch_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (sch_E (ms_regs MS3)) (mrestrict (w_H W) (ms_mem MS3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U24 : bv_unsigned (ew (sch_E (ms_regs MS3)) 24) = SHADOW_OFF + F / 8)
  by (rewrite (sch_ew_reg (ms_regs MS3) 24 24%bv eq_refl), T24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SCH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK SCH_B0 SCH_C3.
{ sch_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDCTL_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDCTL_CID / 8) with 32.
  change (frame_addr lyc SENDCTL_CID pos) with F. unfold shadow_addr. lia. }
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
pose proof HG2b as G2b.
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) (ms_mem MS3) a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U24 in Hx; lia |]).
  destruct Hin. }
clear HF2b HFr2b HG2b.
sch_region HS 0%nat HRsh.
assert (SH4 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 4) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 4 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH5 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 5) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 5 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH6 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 6) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 6 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH7 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 7) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 7 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH8 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 8) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 8 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH9 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 9) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 9 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH10 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 10) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 10 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH11 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 11) = Some 4)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 11 4
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH16 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 16) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 16 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
assert (SH17 : aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + F / 8 + 17) = Some 0)
  by (apply (sch_chunk1 (sch_E (ms_regs MS3)) (w_H W) (ms_mem ms) 24 (SHADOW_OFF + F / 8) _ 0 20 0 20 17 0
       HRsh U24 ltac:(sch_in) ltac:(lia))).
clear HRsh.
sch_kreg HS (ms_regs MS3) (2%bv : bv 5) 2%nat T2 V2. sch_kreg HS (ms_regs MS3) (3%bv : bv 5) 3%nat T3 V3.
sch_kreg HS (ms_regs MS3) (4%bv : bv 5) 4%nat T4 V4. sch_kreg HS (ms_regs MS3) (8%bv : bv 5) 8%nat T8 V8.
sch_kreg HS (ms_regs MS3) (9%bv : bv 5) 9%nat T9 V9. sch_kreg HS (ms_regs MS3) (18%bv : bv 5) 18%nat T18 V18.
sch_kreg HS (ms_regs MS3) (19%bv : bv 5) 19%nat T19 V19. sch_kreg HS (ms_regs MS3) (20%bv : bv 5) 20%nat T20 V20.
sch_kreg HS (ms_regs MS3) (21%bv : bv 5) 21%nat T21 V21. sch_kreg HS (ms_regs MS3) (22%bv : bv 5) 22%nat T22 V22.
sch_kreg HS (ms_regs MS3) (23%bv : bv 5) 23%nat T23 V23. sch_kreg HS (ms_regs MS3) (24%bv : bv 5) 24%nat T24 V24.
sch_kreg HS (ms_regs MS3) (25%bv : bv 5) 25%nat T25 V25. sch_kreg HS (ms_regs MS3) (26%bv : bv 5) 26%nat T26 V26.
sch_kreg HS (ms_regs MS3) (27%bv : bv 5) 27%nat T27 V27.
(* image B's `andi a0, s3, 7` at +0x12c: s = TB_g_s is a multiple of 8, so the run left a0 = 0 and the `bnez a0`
   at +0x144 does not reach the trap word. *)
sch_reg HS (10%bv : bv 5) (w64 0) V10
  ltac:(first [reflexivity
              | cbn [sv_denot]; rewrite (sch_ew_reg (ms_regs MS3) 19 19%bv eq_refl), T19;
                apply bv_eq; vm_compute; reflexivity]).
(* ---- run 2c: h, the two checked loads and the argument registers ---- *)
pmkst HS.
set (MS4 := ms) in *. clearbody MS4. clear HS SHOK. clear ms.
assert (Htw4 : tw_at TMAP_B (aview segs (w_H W) (ms_mem MS4)) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K2b (b + i) ltac:(lia) ltac:(unfold SHADOW_OFF in *; lia)).
  rewrite (K2a (b + i) ltac:(lia)
    ltac:(intros [Hx | Hx]; [lia | exact (NGF (b + i) ltac:(lia) Hg)])).
  exact (GK2 (b + i) Hg). }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
destruct (sch_entry4 lyc S2 W (ms_regs MS4) (ms_mem MS4) _ Bw sp1 F HSC HAR4 Htw4 V9 ltac:(lia) Hsp1al
  ltac:(intros a Ha; apply (sch_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia)
  V10 V19 V25 V26 ltac:(lia) ltac:(lia) ltac:(lia) HF64 HFapp HFG
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2b); apply (apresent_grows _ _ _ a G2a); apply Hfpres; lia)
  ltac:(intros i Hi; assert (Hi2 : i = 0 \/ i = 1) by lia;
        destruct Hi2 as [-> | ->];
        [rewrite Z.add_0_r; exact SH16
        | replace (SHADOW_OFF + F / 8 + 16 + 1) with (SHADOW_OFF + F / 8 + 17) by lia; exact SH17]))
  as [HS SHOK].
clear HEI.
assert (HEI : img_env VAL A_LIM (sch_E4 (ms_regs MS4) Bw)) by apply sch_env_img4.
assert (U9c : bv_unsigned (ew (sch_E4 (ms_regs MS4) Bw) 9) = sp1)
  by (rewrite (sch_ew4_reg (ms_regs MS4) Bw 9 9%bv eq_refl), V9; apply unsigned_lit_small; lia).
assert (U25c : bv_unsigned (ew (sch_E4 (ms_regs MS4) Bw) 25) = F)
  by (rewrite (sch_ew4_reg (ms_regs MS4) Bw 25 25%bv eq_refl), V25; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SCH_C3)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan SENDCTL_FB.
{ sch_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ SENDCTL_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25c in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SENDCTL_CID) with 256.
  change (frame_addr lyc SENDCTL_CID pos) with F. lia. }
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
rename HF into HF2c, HFr into HFr2c, HG into HG2c.
pose proof HG2c as G2c.
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 128 <= a < F + 144) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) (ms_mem MS4) a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => F + 128 <= x < F + 144) HFr2c);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?U25c in Hx; lia |]).
  destruct Hin. }
clear HF2c HFr2c HG2c.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR5.
set (m5 := ms_mem ms) in *.
(* ---- what the walk left at m5 ---- *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/
     sp1 + 24 <= a < sp1 + 32 \/ F + 128 <= a < F + 144) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2c a Ha ltac:(intros X; apply Hn; tauto)).
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a G2c). apply (apresent_grows _ _ _ a G2b).
  exact (apresent_grows _ _ _ a G2a Ha). }
assert (Kg3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - SENDCTL_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - SENDCTL_STK) (spZ regs) SENDCTL_CID pos F (flag_addr lyc SENDCTL_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/
       sp1 + 24 <= a < sp1 + 32 \/ F + 128 <= a < F + 144)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | [X | X]]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes SENDCTL_CID) with 256. fold F. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes SENDCTL_CID / 8) with 32. fold F. lia.
    + left. lia.
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes SENDCTL_CID) with 256. fold F. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
assert (GK5 : gx_kept segs TG.G_HARNESS_B W memc W m5).
{ intros a Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd in Hl.
  rewrite (KF5 a ltac:(lia)); [exact (GK2 a Hg)|].
  intros [X | [X | [X | X]]];
  [ exact (NGF a ltac:(lia) Hg) | exact (NGH a ltac:(unfold SHADOW_OFF in *; lia) Hg)
  | exact (NGH a ltac:(unfold SHADOW_OFF; lia) Hg) | exact (NGF a ltac:(lia) Hg) ]. }
assert (Htw5 : tw_at TMAP_B (aview segs (w_H W) m5) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  apply GK5. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
assert (HROM5 : trans_rom_view_rd W m5).
{ intros a Hro. rewrite <- (HROM a Hro).
  destruct (trans_ro_rd_scoped B HROU HRNE a Hro) as [Hno He].
  pose proof Kg3 as (_ & _ & Ki & _).
  apply (Ki a (trans_ro_img a Hro)); [|exact Hno | exact He].
  intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Hro) as Rb.
  unfold TG.G_HARNESS_B_LO in Gh. lia. }
assert (HSV5 : forall (o : Z) (r0 : bv 5), In (o, r0) sch_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r0))).
{ intros o r0 Hin. pose proof (HSVo o r0 Hin) as Ho. rewrite <- (HSV2 o r0 Hin).
  apply rdword_ext. intros i Hi. apply KF5; [lia|].
  intros [X | [X | [X | X]]]; unfold SHADOW_OFF in *; lia. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SENDCTL_SAVED).
{ unfold SENDCTL_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r0))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r0)); unfold sch_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + 256 - 8) = Some (flag_addr lyc SENDCTL_CID pos)).
{ rewrite <- Hflag. apply rdword_ext. intros i Hi. apply KF5; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF in *.
  destruct HFapp as [HA0 [HA | [HA1 HA2]]]; destruct HFd as [HFd1 HFd2];
  intros [X | [X | [X | X]]]; lia. }
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
(* the frame's shadow bytes, at m5 *)
assert (SHk : forall j v, 0 <= j < 20 -> aview segs (w_H W) (ms_mem MS4) (SHADOW_OFF + F / 8 + j) = Some v ->
  aview segs (w_H W) m5 (SHADOW_OFF + F / 8 + j) = Some v).
{ intros j v Hj Hv. rewrite <- Hv. apply K2c; [unfold SHADOW_OFF in *; lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF in *.
  destruct HFapp as [HA0 [HA | [HA1 HA2]]]; destruct HFd as [HFd1 HFd2];
  intros X; lia. }
assert (SH4' := SHk 4 0 ltac:(lia) SH4). assert (SH5' := SHk 5 0 ltac:(lia) SH5).
assert (SH6' := SHk 6 0 ltac:(lia) SH6). assert (SH7' := SHk 7 0 ltac:(lia) SH7).
assert (SH8' := SHk 8 0 ltac:(lia) SH8). assert (SH9' := SHk 9 0 ltac:(lia) SH9).
assert (SH10' := SHk 10 0 ltac:(lia) SH10). assert (SH11' := SHk 11 4 ltac:(lia) SH11).
assert (SH16' := SHk 16 0 ltac:(lia) SH16). assert (SH17' := SHk 17 0 ltac:(lia) SH17).
assert (Hgr : forall c x, c mod 8 = 0 -> F + c <= x < F + c + 8 ->
  shadow_of_addr SHADOW_OFF x = SHADOW_OFF + F / 8 + c / 8).
{ intros c x Hc Hx. unfold shadow_of_addr.
  rewrite (sch_same_gran (F + c) x ltac:(rewrite Zplus_mod, HF8, Hc; reflexivity) ltac:(lia)).
  rewrite (sch_div8_add F c HF8 Hc). lia. }
assert (Hmod8 : forall c x, c mod 8 = 0 -> F + c <= x < F + c + 8 -> x mod 8 = x - (F + c)).
{ intros c x Hc Hx.
  assert (HFc8 : (F + c) mod 8 = 0) by (rewrite Zplus_mod, HF8, Hc; reflexivity).
  replace x with ((F + c) + (x - (F + c))) at 1 by lia.
  rewrite <- Zplus_mod_idemp_l, HFc8, Z.add_0_l. apply Z.mod_small. lia. }
(* f: the 60 bytes at F + 32 *)
assert (Hpf : forall a, F + 32 <= a < F + 32 + 60 -> apresent (w_H W) m5 a)
  by (intros a Ha; apply GF5; apply Hfpres; lia).
destruct (garr8_of_present segs (mrestrict (w_H W) m5) (F + 32) 60
  ltac:(intros a Ha; destruct (Hpf a ltac:(lia)) as (Hh & bb & Hbb); exists bb; unfold mrestrict; rewrite Hh;
        exact Hbb)) as (ojz & Hojl & Hojg).
assert (Hojok : bytes_ok ojz) by exact (garr8_bytes_ok segs _ _ _ Hojg).
assert (Hojz : TW.zs (TW.bs ojz) = ojz) by exact (sch_zs_bs ojz Hojok).
assert (HRAf : range_addressable (aview segs (w_H W) m5) SHADOW_OFF (F + 32) 60).
{ intros x Hx.
  destruct (Z_lt_le_dec x (F + 40)) as [h1|h1];
  [ exists 0; rewrite (Hgr 32 x eq_refl ltac:(lia)); split; [exact SH4' | left; reflexivity] |].
  destruct (Z_lt_le_dec x (F + 48)) as [h2|h2];
  [ exists 0; rewrite (Hgr 40 x eq_refl ltac:(lia)); split; [exact SH5' | left; reflexivity] |].
  destruct (Z_lt_le_dec x (F + 56)) as [h3|h3];
  [ exists 0; rewrite (Hgr 48 x eq_refl ltac:(lia)); split; [exact SH6' | left; reflexivity] |].
  destruct (Z_lt_le_dec x (F + 64)) as [h4|h4];
  [ exists 0; rewrite (Hgr 56 x eq_refl ltac:(lia)); split; [exact SH7' | left; reflexivity] |].
  destruct (Z_lt_le_dec x (F + 72)) as [h5|h5];
  [ exists 0; rewrite (Hgr 64 x eq_refl ltac:(lia)); split; [exact SH8' | left; reflexivity] |].
  destruct (Z_lt_le_dec x (F + 80)) as [h6|h6];
  [ exists 0; rewrite (Hgr 72 x eq_refl ltac:(lia)); split; [exact SH9' | left; reflexivity] |].
  destruct (Z_lt_le_dec x (F + 88)) as [h7|h7];
  [ exists 0; rewrite (Hgr 80 x eq_refl ltac:(lia)); split; [exact SH10' | left; reflexivity] |].
  exists 4. rewrite (Hgr 88 x eq_refl ltac:(lia)). split; [exact SH11'|].
  right. rewrite (Hmod8 88 x eq_refl ltac:(lia)). lia. }
assert (HPsh : forall i, 0 <= i < 32 -> apresent (w_H W) m5 (SHADOW_OFF + F / 8 + i)).
{ intros i Hi. apply GF5. replace (SHADOW_OFF + F / 8 + i) with (shadow_addr F + i) by (unfold shadow_addr; lia).
  exact (proj1 (HFsh i Hi)). }
assert (EH1 : shadow_addr (F + 32) / 8 * 8 = SHADOW_OFF + F / 8).
{ unfold shadow_addr. rewrite (sch_div8_add F 32 HF8 eq_refl). change (32 / 8) with 4.
  replace (SHADOW_OFF + (F / 8 + 4)) with (SHADOW_OFF + F / 8 + 4) by lia.
  apply sch_align8; [exact HS8 | lia]. }
assert (EH2 : shadow_addr (F + 32 + 60 - 1) / 8 * 8 + 8 = SHADOW_OFF + F / 8 + 16).
{ unfold shadow_addr. replace (F + 32 + 60 - 1) with (F + 88 + 3) by lia.
  rewrite (sch_same_gran (F + 88) (F + 88 + 3) ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)).
  rewrite (sch_div8_add F 88 HF8 eq_refl). change (88 / 8) with 11.
  replace (SHADOW_OFF + (F / 8 + 11)) with (SHADOW_OFF + F / 8 + 8 + 3) by lia.
  rewrite (sch_align8 (SHADOW_OFF + F / 8 + 8) 3 ltac:(rewrite Zplus_mod, HS8; reflexivity) ltac:(lia)). lia. }
assert (HHf : shadow_hull_vis (aview segs (w_H W) m5) (F + 32) 60).
{ intros s Hs. rewrite EH1, EH2 in Hs.
  replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
  apply aview_some_of_apresent. apply HPsh. lia. }
assert (HAMf : amem_range (F + 32) 60).
{ unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia. }
assert (HRDf : decode_rd_ok W m5 (F + 32) 60).
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply aview_some_of_apresent. apply Hpf. lia.
  - exact HRAf.
  - exact HHf.
  - exact HAMf.
  - lia.
  - lia. }
(* the twelve header bytes at F + 132 *)
sch_region HS 2%nat HRh.
assert (E33c : ew (sch_E4 (ms_regs MS4) Bw) 33 = Z_to_bv 64 (TW.u_at Bw TW.A_S_host_counter 4))
  by exact (sch_ew4_x (ms_regs MS4) Bw 1 ltac:(lia)).
assert (E34c : ew (sch_E4 (ms_regs MS4) Bw) 34 = Z_to_bv 64 (TW.u_at Bw TW.A_S_cfg_sum_mode 4))
  by exact (sch_ew4_x (ms_regs MS4) Bw 2 ltac:(lia)).
pose proof (TWL.u_at_range Bw TW.A_S_host_counter 4) as R33r.
pose proof (TWL.u_at_range Bw TW.A_S_cfg_sum_mode 4) as R34r.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R33r, R34r.
assert (E23c : ew (sch_E4 (ms_regs MS4) Bw) 23 = Z_to_bv 64 (bv_swrap 32 ack))
  by (rewrite (sch_ew4_reg (ms_regs MS4) Bw 23 23%bv eq_refl); exact V23).
assert (E21c : ew (sch_E4 (ms_regs MS4) Bw) 21 = Z_to_bv 64 cmd)
  by (rewrite (sch_ew4_reg (ms_regs MS4) Bw 21 21%bv eq_refl); exact V21).
pose proof (YC4b.field_of_region_any (sch_E4 (ms_regs MS4) Bw) (mrestrict (w_H W) m5) 25 F _ 128 144 128 144 132 4%N
  (SExt true 32 (SOff 33 0)) HRh U25c ltac:(sch_in) ltac:(cbn; lia)) as V132.
pose proof (YC4b.field_of_region_any (sch_E4 (ms_regs MS4) Bw) (mrestrict (w_H W) m5) 25 F _ 128 144 128 144 136 4%N
  (SOff 23 0) HRh U25c ltac:(sch_in) ltac:(cbn; lia)) as V136.
pose proof (YC4b.field_of_region_any (sch_E4 (ms_regs MS4) Bw) (mrestrict (w_H W) m5) 25 F _ 128 144 128 144 140 2%N
  (SLit 0) HRh U25c ltac:(sch_in) ltac:(cbn; lia)) as V140.
pose proof (YC4b.field_of_region_any (sch_E4 (ms_regs MS4) Bw) (mrestrict (w_H W) m5) 25 F _ 128 144 128 144 142 1%N
  (SOff 21 0) HRh U25c ltac:(sch_in) ltac:(cbn; lia)) as V142.
pose proof (YC4b.field_of_region_any (sch_E4 (ms_regs MS4) Bw) (mrestrict (w_H W) m5) 25 F _ 128 144 128 144 143 1%N
  (SLit 0) HRh U25c ltac:(sch_in) ltac:(cbn; lia)) as V143.
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V132, V136.
change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V140.
change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8) in V142, V143.
rewrite (sch_sext_mod (sch_E4 (ms_regs MS4) Bw) 33 (TW.u_at Bw TW.A_S_host_counter 4) E33c R33r) in V132.
rewrite (sch_off0_mod (sch_E4 (ms_regs MS4) Bw) 23 (bv_swrap 32 ack) 32 ltac:(lia) E23c) in V136.
rewrite (sch_swrap32 ack ltac:(lia)) in V136.
rewrite (sch_off0_mod (sch_E4 (ms_regs MS4) Bw) 21 cmd 8 ltac:(lia) E21c) in V142.
rewrite (Z.mod_small cmd (2 ^ 8)) in V142 by lia.
change (bv_unsigned (sv_denot (sch_E4 (ms_regs MS4) Bw) (SLit 0)) mod 2 ^ 16) with 0 in V140.
change (bv_unsigned (sv_denot (sch_E4 (ms_regs MS4) Bw) (SLit 0)) mod 2 ^ 8) with 0 in V143.
assert (HHDR : garr8 segs (mrestrict (w_H W) m5) (F + SENDCTL_HOFF + 4)
  (frame_fb_hdr_bytes (TW.S_host_counter Bw) ack 0 cmd 0)).
{ unfold SENDCTL_HOFF. replace (F + 128 + 4) with (F + 132) by lia.
  rewrite (sch_hdr_list (TW.S_host_counter Bw) ack cmd ltac:(exact R33r) ltac:(lia) ltac:(lia)).
  intros j Hj. cbn [length] in Hj.
  destruct j as [|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]; cbn [nth]; try (exfalso; lia).
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 132) 4 (TW.S_host_counter Bw) 0 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); exact R33r) ltac:(lia) V132 _ _);
    [reflexivity | change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 132) 4 (TW.S_host_counter Bw) 1 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); exact R33r) ltac:(lia) V132 _ _);
    [reflexivity | change (2 ^ (8 * Z.of_nat 1)) with 256; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 132) 4 (TW.S_host_counter Bw) 2 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); exact R33r) ltac:(lia) V132 _ _);
    [reflexivity | change (2 ^ (8 * Z.of_nat 2)) with 65536; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 132) 4 (TW.S_host_counter Bw) 3 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); exact R33r) ltac:(lia) V132 _ _);
    [reflexivity | change (2 ^ (8 * Z.of_nat 3)) with 16777216; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 136) 4 ack 0 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia) ltac:(lia) V136 _ _);
    [cbn [Z.of_nat]; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 136) 4 ack 1 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia) ltac:(lia) V136 _ _);
    [cbn [Z.of_nat]; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 136) 4 ack 2 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia) ltac:(lia) V136 _ _);
    [cbn [Z.of_nat]; lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 136) 4 ack 3 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia) ltac:(lia) V136 _ _);
    [cbn [Z.of_nat]; lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 140) 2 0 0 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 2)) with 65536; lia) ltac:(lia) V140 _ _);
    [cbn [Z.of_nat]; lia | reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 140) 2 0 1 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 2)) with 65536; lia) ltac:(lia) V140 _ _);
    [cbn [Z.of_nat]; lia | reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 142) 1 cmd 0 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 1)) with 256; lia) ltac:(lia) V142 _ _);
    [cbn [Z.of_nat]; lia | change (2 ^ (8 * Z.of_nat 0)) with 1; rewrite Z.div_1_r; reflexivity].
  - refine (sch_vm_byte' (mrestrict (w_H W) m5) (F + 143) 1 0 0 _ _
      ltac:(change (2 ^ (8 * Z.of_nat 1)) with 256; lia) ltac:(lia) V143 _ _);
    [cbn [Z.of_nat]; lia | reflexivity]. }
assert (HRDh : decode_rd_ok W m5 (F + SENDCTL_HOFF + 4) 12).
{ unfold SENDCTL_HOFF. replace (F + 128 + 4) with (F + 132) by lia.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. apply aview_some_of_apresent. apply GF5. apply Hfpres. lia.
  - intros x Hx. exists 0.
    destruct (Z_lt_le_dec x (F + 136)) as [h1|h1].
    + rewrite (Hgr 128 x eq_refl ltac:(lia)). change (128 / 8) with 16.
      split; [exact SH16' | left; reflexivity].
    + rewrite (Hgr 136 x eq_refl ltac:(lia)). change (136 / 8) with 17.
      split; [exact SH17' | left; reflexivity].
  - intros s Hs. unfold shadow_addr in Hs.
    rewrite (sch_same_gran (F + 128) (F + 132) ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)) in Hs.
    rewrite (sch_div8_add F 128 HF8 ltac:(reflexivity)) in Hs.
    replace (F + 132 + 12 - 1) with (F + 136 + 7) in Hs by lia.
    rewrite (sch_same_gran (F + 136) (F + 136 + 7) ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)) in Hs.
    rewrite (sch_div8_add F 136 HF8 ltac:(reflexivity)) in Hs.
    assert (EB1 : (SHADOW_OFF + (F / 8 + 128 / 8)) / 8 * 8 = SHADOW_OFF + F / 8 + 16).
    { change (128 / 8) with 16. replace (SHADOW_OFF + (F / 8 + 16)) with (SHADOW_OFF + F / 8 + 16 + 0) by lia.
      apply sch_align8; [rewrite Zplus_mod, HS8; reflexivity | lia]. }
    assert (EB2 : (SHADOW_OFF + (F / 8 + 136 / 8)) / 8 * 8 + 8 = SHADOW_OFF + F / 8 + 24).
    { change (136 / 8) with 17. replace (SHADOW_OFF + (F / 8 + 17)) with (SHADOW_OFF + F / 8 + 16 + 1) by lia.
      rewrite (sch_align8 (SHADOW_OFF + F / 8 + 16) 1 ltac:(rewrite Zplus_mod, HS8; reflexivity) ltac:(lia)). lia. }
    rewrite EB1, EB2 in Hs.
    replace s with (SHADOW_OFF + F / 8 + (s - (SHADOW_OFF + F / 8))) by lia.
    apply aview_some_of_apresent. apply HPsh. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
  - lia.
  - lia. }
(* the write right on f *)
assert (HTWRf : transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S lyc S2 ((SENDCTL_CID, pos) :: own) W m5
  (sp1 - FRAME_FB_FRAME) (F + SENDCTL_FOFF) SENDCTL_F).
{ apply (transport_twr_ok_g_intro segs B LAWS TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0
    ((SENDCTL_CID, pos) :: own) lyc S2 W m5 _ k (sp1 - FRAME_FB_FRAME) (F + SENDCTL_FOFF) SENDCTL_F HJ).
  intros a Ha. unfold SENDCTL_FOFF, SENDCTL_F in Ha. left. split.
  - unfold awr_byte. right; right; right. unfold in_frames. exists SENDCTL_CID, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes SENDCTL_CID) with 256. fold F. lia.
  - unfold FRAME_FB_FRAME. unfold ESTACK in *. lia. }
(* the cells at kp and klp *)
assert (HKF : forall cid pos0 s, In (cid, pos0) (frames Sc) ->
  in_zr s (shadow_addr (frame_addr lyc cid pos0), fs_frame_bytes cid / 8) ->
  aview segs (w_H W) m5 s = aview segs (w_H W) memc s).
{ intros cid pos0 s Hin Hs. pose proof Kg3 as (_ & _ & _ & Kf & _).
  exact (Kf cid pos0 s Hin (or_intror Hs) ltac:(intros [])). }
assert (HIN : sendctl_incells W m5 kp klp K KL).
{ destruct HKP as [Hk0 | (Hkp0 & HFake & HTWK & HRDK & HOFFK & HNGK & HLK & HGK & Hklp0 &
                         Hklp8 & HTWKL & HRDKL & HOFFKL & HNGKL & HLKL & HGKL & Hsep)];
  [left; exact Hk0|].
  unfold SENDCTL_F in *.
  assert (HKV : forall a, kp <= a < kp + 60 -> aview segs (w_H W) m5 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct HFake as (cid & pos0 & Hin & Hf1 & Hf2).
    pose proof Kg3 as (_ & _ & _ & Kf & _).
    assert (Hir : in_zr a (frame_rng lyc (cid, pos0)))
      by (unfold in_zr, frame_rng; cbn [fst snd]; lia).
    exact (Kf cid pos0 a Hin (or_introl Hir) ltac:(intros [])). }
  assert (HKLV : forall a, klp <= a < klp + 8 -> aview segs (w_H W) m5 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct (HTWKL a Ha) as [(Hw & Hp & Hno & Hs) | Hg]; [|exfalso; exact (HNGKL a Ha Hg)].
    pose proof Kg3 as (Kw & Kb & _ & Kf & _).
    destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
    - apply Kw; [lia|]. unfold decode_off_win in HOFFKL. lia.
    - replace a with (b + (a - b)) by lia. apply (Kb b m (a - b) Hb ltac:(lia)). intros [].
    - replace a with (b + (a - b)) by lia. apply (Kb b m (a - b) Hb ltac:(lia)). intros [].
    - apply (Kf c0 p0 a ltac:(rewrite HfrsC; apply in_or_app; left; exact Hc) Hr). intros []. }
  right. split; [|split; [|split]].
  - apply (sch_garr8_kept (w_H W) memc m5 kp (TW.zs K)); [|exact HGK].
    intros j Hj. apply HKV. unfold TW.zs in Hj. rewrite length_map, HLK in Hj. cbn in Hj. lia.
  - apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W memc m5 mdc kp 60 HAR HFake HRDK ltac:(lia) HKV HKF).
  - apply (sch_garr8_kept (w_H W) memc m5 klp (TW.zs KL)); [|exact HGKL].
    intros j Hj. apply HKLV. unfold TW.zs in Hj. rewrite length_map, HLKL in Hj. cbn in Hj. lia.
  - (* decode_rd_ok at klp: the three placements of its granule *)
    destruct (HTWKL klp ltac:(lia)) as [(Hw & Hp & Hno & Hs) | Hg]; [|exfalso; exact (HNGKL klp ltac:(lia) Hg)].
    assert (Eklp : forall x, klp <= x < klp + 8 -> shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF klp)
      by (intros x Hx; unfold shadow_of_addr; rewrite (sch_same_gran klp x Hklp8 Hx); reflexivity).
    pose proof HRDKL as HRDKLd. destruct HRDKLd as (HV0 & HRA0 & HHU0 & HAM0 & HQ0 & HQ1).
    assert (HVk : forall a, klp <= a < klp + 8 -> aview segs (w_H W) m5 a <> None)
      by (intros a Ha; rewrite (HKLV a Ha); exact (HV0 a Ha)).
    destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
    + (* the machine stack *)
      assert (Hk8 : klp + 8 <= sp0).
      { pose proof (Z.div_mod klp 8 ltac:(lia)) as D1. rewrite Hklp8, Z.add_0_r in D1.
        pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. rewrite Hsp0a, Z.add_0_r in D2. lia. }
      split; [exact HVk|]. split.
      { eapply can_stack_addressable; [exact HAR5 | lia | lia | lia]. }
      split; [eapply can_stack_hull; [exact HAR5 | lia | lia | lia]|].
      split; [exact HAM0 | split; [exact HQ0 | exact HQ1]].
    + (* a block of the call *)
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (Hb16 & Hb4096 & Hbce & _ & _ & _ & Hbn0).
      pose proof (req_size_pos m (proj1 Hbn0)) as [_ Hreq].
      destruct (al_shadow _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as [Hbs _].
      destruct (al_shadow _ _ LAWS lyc S2 W m5 _ b m HAR5 ltac:(rewrite Eab2; exact Hb)) as [Hbs5 _].
      assert (Hb8 : b mod 8 = 0)
        by (pose proof (Z.div_mod b 16 ltac:(lia)) as D; rewrite Hb16, Z.add_0_r in D; rewrite D;
            replace (16 * (b / 16)) with ((2 * (b / 16)) * 8) by lia; apply Z_mod_mult).
      assert (Hbd : (klp - b) mod 8 = 0) by (rewrite Zminus_mod, Hklp8, Hb8; reflexivity).
      assert (Hi : 0 <= (klp - b) / 8 < (req_size m + 7) / 8).
      { split; [apply Z.div_pos; lia|].
        apply Z.div_lt_upper_bound; [lia|].
        pose proof (Z.div_mod (klp - b) 8 ltac:(lia)) as D. rewrite Hbd, Z.add_0_r in D.
        pose proof (Z.div_mod (req_size m + 7) 8 ltac:(lia)) as D2.
        pose proof (Z.mod_pos_bound (req_size m + 7) 8 ltac:(lia)) as D3. lia. }
      assert (Esh : shadow_of_addr SHADOW_OFF klp = shadow_of_addr SHADOW_OFF b + (klp - b) / 8).
      { unfold shadow_of_addr. pose proof (sch_div8_add b (klp - b) Hb8 Hbd) as Edv.
        replace (b + (klp - b)) with klp in Edv by lia. lia. }
      split; [exact HVk|]. split.
      { intros x Hx. destruct (HRA0 x Hx) as (s0 & Hs0 & Hok0). exists s0. split; [|exact Hok0].
        rewrite (Eklp x Hx), Esh in Hs0 |- *.
        rewrite (proj2 (proj2 Hbs5) _ Hi). rewrite (proj2 (proj2 Hbs) _ Hi) in Hs0. exact Hs0. }
      split.
      { apply sch_hull8; [exact Hklp8|].
        exact (shadow_hull_vis_of_block segs B LAWS lyc S2 W m5 _ b m klp 1 HAR5
          ltac:(rewrite Eab2; exact Hb) ltac:(lia) ltac:(lia) ltac:(lia)). }
      split; [exact HAM0 | split; [exact HQ0 | exact HQ1]].
    + (* a temporary block of the call *)
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (Hb16 & Hb4096 & Hbce & _ & _ & _ & Hbn0).
      pose proof (req_size_pos m (proj1 Hbn0)) as [_ Hreq].
      destruct (al_shadow _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as [Hbs _].
      destruct (al_shadow _ _ LAWS lyc S2 W m5 _ b m HAR5 ltac:(rewrite Eab2; exact Hb)) as [Hbs5 _].
      assert (Hb8 : b mod 8 = 0)
        by (pose proof (Z.div_mod b 16 ltac:(lia)) as D; rewrite Hb16, Z.add_0_r in D; rewrite D;
            replace (16 * (b / 16)) with ((2 * (b / 16)) * 8) by lia; apply Z_mod_mult).
      assert (Hbd : (klp - b) mod 8 = 0) by (rewrite Zminus_mod, Hklp8, Hb8; reflexivity).
      assert (Hi : 0 <= (klp - b) / 8 < (req_size m + 7) / 8).
      { split; [apply Z.div_pos; lia|].
        apply Z.div_lt_upper_bound; [lia|].
        pose proof (Z.div_mod (klp - b) 8 ltac:(lia)) as D. rewrite Hbd, Z.add_0_r in D.
        pose proof (Z.div_mod (req_size m + 7) 8 ltac:(lia)) as D2.
        pose proof (Z.mod_pos_bound (req_size m + 7) 8 ltac:(lia)) as D3. lia. }
      assert (Esh : shadow_of_addr SHADOW_OFF klp = shadow_of_addr SHADOW_OFF b + (klp - b) / 8).
      { unfold shadow_of_addr. pose proof (sch_div8_add b (klp - b) Hb8 Hbd) as Edv.
        replace (b + (klp - b)) with klp in Edv by lia. lia. }
      split; [exact HVk|]. split.
      { intros x Hx. destruct (HRA0 x Hx) as (s0 & Hs0 & Hok0). exists s0. split; [|exact Hok0].
        rewrite (Eklp x Hx), Esh in Hs0 |- *.
        rewrite (proj2 (proj2 Hbs5) _ Hi). rewrite (proj2 (proj2 Hbs) _ Hi) in Hs0. exact Hs0. }
      split.
      { apply sch_hull8; [exact Hklp8|].
        exact (shadow_hull_vis_of_block segs B LAWS lyc S2 W m5 _ b m klp 1 HAR5
          ltac:(rewrite Eab2; exact Hb) ltac:(lia) ltac:(lia) ltac:(lia)). }
      split; [exact HAM0 | split; [exact HQ0 | exact HQ1]].
    + (* a frame of the caller *)
      assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
      destruct (dkg_frame_al64 segs B _ _ _ _ _ c0 p0 HAR Hc') as (HG64 & HGs64 & HGs).
      destruct Hr as [Hr | Hr].
      * unfold in_zr in Hr. cbn [fst snd] in Hr.
        apply (decode_rd_ok_fake_kept B LAWS lyc Sc W W memc m5 mdc klp 8 HAR
          ltac:(exists c0, p0; split; [exact Hc'|];
                pose proof (Z.div_mod klp 8 ltac:(lia)) as D1; rewrite Hklp8, Z.add_0_r in D1;
                pose proof (Z.div_mod (frame_addr lyc c0 p0) 8 ltac:(lia)) as D2;
                assert (HA8 : frame_addr lyc c0 p0 mod 8 = 0)
                  by (pose proof (Z.div_mod (frame_addr lyc c0 p0) 64 ltac:(lia)) as D3;
                      rewrite HG64, Z.add_0_r in D3; rewrite D3;
                      replace (64 * (frame_addr lyc c0 p0 / 64)) with
                        ((8 * (frame_addr lyc c0 p0 / 64)) * 8) by lia; apply Z_mod_mult);
                pose proof (Z.div_mod (fs_frame_bytes c0) 64 ltac:(lia)) as D4;
                rewrite HGs64, Z.add_0_r in D4; rewrite HA8, Z.add_0_r in D2; lia)
          HRDKL ltac:(lia) HKLV HKF).
      * exfalso. unfold in_zr in Hr. cbn [fst snd] in Hr.
        pose proof (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HAR Hc') as (G4096 & Gce & _).
        pose proof (Z.div_mod (frame_addr lyc c0 p0) 8 ltac:(lia)) as Dfa.
        pose proof (Z.mod_pos_bound (frame_addr lyc c0 p0) 8 ltac:(lia)) as Mfa.
        pose proof (Z.div_mod (fs_frame_bytes c0) 8 ltac:(lia)) as Dfs.
        pose proof (Z.mod_pos_bound (fs_frame_bytes c0) 8 ltac:(lia)) as Mfs.
        pose proof (fs_frame_bytes_nonneg c0) as Hfsn.
        unfold shadow_addr, SHADOW_OFF in Hr.
        unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM0.
        destruct HAM0 as [HA | [HA1 HA2]]; lia. }
(* ---- the kept fact, read with the out cell put back ---- *)
assert (HOUTP : forall a, inG (sendctl_outs kp klp) a ->
  0 <= a < 2 ^ 64 /\ ~ (spZ regs - SENDCTL_STK <= a < spZ regs) /\ apresent (w_H W) memc a /\
  apresent (w_H W) m5 a /\ apresent (w_H W) memc a).
{ intros a Hin. unfold sendctl_outs in Hin.
  destruct (Z.eqb_spec kp 0) as [Hk0 | Hk0].
  - exfalso. unfold inG in Hin. apply Exists_exists in Hin as (x & Hx & _). destruct Hx.
  - destruct HKP as [Hk0' | (Hkp0 & HFake & HTWK & HRDK & HOFFK & HNGK & HLK & HGK & Hklp0 &
                            Hklp8 & HTWKL & HRDKL & HOFFKL & HNGKL & HLKL & HGKL & Hsep)];
    [exfalso; exact (Hk0 Hk0')|].
    assert (Ha : klp <= a < klp + 8).
    { unfold inG in Hin. apply Exists_exists in Hin as ((b0, n0) & Hb0 & Hr0). cbn [In] in Hb0.
      destruct Hb0 as [Hb0 | []]. injection Hb0 as <- <-. unfold in_zr in Hr0. cbn [fst snd] in Hr0. lia. }
    destruct HRDKL as (HV0 & _ & _ & HAM0 & HQ0 & HQ1).
    destruct (HTWKL a Ha) as [(Hw & Hp & Hno & Hs) | Hg]; [|exfalso; exact (HNGKL a Ha Hg)].
    assert (Hni : ~ in_img segs a).
    { intros Hi.
      destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
      - pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
      - exact (blk_img segs B LAWS lyc Sc W memc mdc b m a HAR Hb ltac:(lia) Hi).
      - exact (blk_img segs B LAWS lyc Sc W memc mdc b m a HAR Hb ltac:(lia) Hi).
      - assert (Hc' : In (c0, p0) (frames Sc)) by (rewrite HfrsC; apply in_or_app; left; exact Hc).
        destruct Hr as [Hr | Hr].
        + unfold in_zr in Hr. cbn [fst snd] in Hr.
          exact (frm_img segs B LAWS lyc Sc W memc mdc c0 p0 a HAR Hc' ltac:(lia) Hi).
        + pose proof (transportb_segs_low a Hi) as Hl.
          pose proof (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HAR Hc') as (G4096 & Gce & _).
          pose proof (Z.div_pos (frame_addr lyc c0 p0) 8 ltac:(lia)) as Hdp.
          unfold in_zr, shadow_addr, SHADOW_OFF, kLowMemEnd in *. cbn [fst snd] in Hr. lia. }
    assert (HKLV : aview segs (w_H W) m5 a = aview segs (w_H W) memc a).
    { pose proof Kg3 as (Kw & Kb & _ & Kf & _).
      destruct Hw as [Hw | [(_ & b & m & Hb & Hr) | [(b & m & Hb & _ & Hr) | (c0 & p0 & Hc & Hr)]]].
      - apply Kw; [lia|]. unfold decode_off_win in HOFFKL. lia.
      - replace a with (b + (a - b)) by lia. apply (Kb b m (a - b) Hb ltac:(lia)). intros [].
      - replace a with (b + (a - b)) by lia. apply (Kb b m (a - b) Hb ltac:(lia)). intros [].
      - apply (Kf c0 p0 a ltac:(rewrite HfrsC; apply in_or_app; left; exact Hc) Hr). intros []. }
    split; [lia|]. split; [unfold decode_off_win in HOFFKL; lia|].
    split; [exact Hp|]. split; [|exact Hp].
    exact (apresent_transfer segs (w_H W) (w_H W) memc m5 a ltac:(lia) Hni HKLV Hp). }
assert (KGOV : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (gover (sendctl_outs kp klp) m5 memc)
  (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS_B lyc Sc W memc W (gover (sendctl_outs kp klp) m5 memc)
    (spZ regs - SENDCTL_STK) (spZ regs) (fun _ => False) (sendctl_wr kp klp)); [intros a []|].
  apply (sch_kept_mem1 TG.G_HARNESS_B lyc Sc W W (gover (sendctl_outs kp klp) memc memc) memc
    (gover (sendctl_outs kp klp) m5 memc) (spZ regs - SENDCTL_STK) (spZ regs) (fun _ => False));
  [exact (fun x => eq_sym (sch_gover_same (sendctl_outs kp klp) memc x))|].
  exact (acall_kept_g_gover B TG.G_HARNESS_B (sendctl_outs kp klp) lyc Sc W W memc m5 memc mdc
    (spZ regs - SENDCTL_STK) (spZ regs) (fun _ => False) LAWS HAR ltac:(lia) ltac:(lia) HOUTP Kg3). }
assert (HKLPR : kp = 0 \/ (forall i, 0 <= i < 8 -> apresent (w_H W) m5 (klp + i))).
{ destruct (Z.eqb_spec kp 0) as [Hk0 | Hk0]; [left; exact Hk0|].
  right. intros i Hi.
  assert (Hin : inG (sendctl_outs kp klp) (klp + i)).
  { unfold sendctl_outs. rewrite (proj2 (Z.eqb_neq kp 0) Hk0). unfold inG. apply Exists_exists.
    exists (klp, 8). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
  destruct (HOUTP (klp + i) Hin) as (_ & _ & _ & Hp & _). exact Hp. }
(* ---- the registers at the cut ---- *)
sch_kreg4 HS (ms_regs MS4) Bw (2%bv : bv 5) 2%nat V2 Y2.
sch_kreg4 HS (ms_regs MS4) Bw (3%bv : bv 5) 3%nat V3 Y3.
sch_kreg4 HS (ms_regs MS4) Bw (4%bv : bv 5) 4%nat V4 Y4.
sch_kreg4 HS (ms_regs MS4) Bw (8%bv : bv 5) 8%nat V8 Y8.
sch_kreg4 HS (ms_regs MS4) Bw (9%bv : bv 5) 9%nat V9 Y9.
sch_kreg4 HS (ms_regs MS4) Bw (18%bv : bv 5) 18%nat V18 Y18.
sch_kreg4 HS (ms_regs MS4) Bw (19%bv : bv 5) 19%nat V19 Y19.
sch_kreg4 HS (ms_regs MS4) Bw (20%bv : bv 5) 20%nat V20 Y20.
sch_kreg4 HS (ms_regs MS4) Bw (21%bv : bv 5) 21%nat V21 Y21.
sch_kreg4 HS (ms_regs MS4) Bw (22%bv : bv 5) 22%nat V22 Y22.
sch_kreg4 HS (ms_regs MS4) Bw (24%bv : bv 5) 24%nat V24 Y24.
sch_kreg4 HS (ms_regs MS4) Bw (25%bv : bv 5) 25%nat V25 Y25.
sch_kreg4 HS (ms_regs MS4) Bw (26%bv : bv 5) 26%nat V26 Y26.
sch_kreg4 HS (ms_regs MS4) Bw (27%bv : bv 5) 27%nat V27 Y27.
sch_reg HS (10%bv : bv 5) (w64 (F + 32)) Y10
  ltac:(cbn [sv_denot]; rewrite (sch_ew4_reg (ms_regs MS4) Bw 25 25%bv eq_refl), V25;
        change (bv_unsigned (w64 F)) with (F mod 2 ^ 64);
        rewrite (Z.mod_small F (2 ^ 64)) by lia; reflexivity).
sch_reg HS (11%bv : bv 5) (w64 SENDCTL_F) Y11 ltac:(reflexivity).
sch_reg HS (12%bv : bv 5) (w64 (SENDCTL_S + 120)) Y12
  ltac:(cbn [sv_denot]; rewrite (sch_ew4_reg (ms_regs MS4) Bw 19 19%bv eq_refl), V19;
        change (bv_unsigned (w64 SENDCTL_S)) with (SENDCTL_S mod 2 ^ 64);
        rewrite (Z.mod_small SENDCTL_S (2 ^ 64)) by (rewrite CS; lia); reflexivity).
sch_reg HS (13%bv : bv 5) (w64 SENDCTL_S) Y13
  ltac:(cbn [sv_denot]; rewrite (sch_ew4_reg (ms_regs MS4) Bw 19 19%bv eq_refl), V19;
        change (bv_unsigned (w64 SENDCTL_S)) with (SENDCTL_S mod 2 ^ 64);
        rewrite (Z.mod_small SENDCTL_S (2 ^ 64)) by (rewrite CS; lia); rewrite Z.add_0_r; reflexivity).
sch_reg HS (14%bv : bv 5) (w64 (F + SENDCTL_HOFF)) Y14
  ltac:(cbn [sv_denot]; rewrite (sch_ew4_reg (ms_regs MS4) Bw 25 25%bv eq_refl), V25;
        change (bv_unsigned (w64 F)) with (F mod 2 ^ 64);
        rewrite (Z.mod_small F (2 ^ 64)) by lia; reflexivity).
sch_reg HS (15%bv : bv 5) (w64 0) Y15 ltac:(reflexivity).
sch_reg HS (16%bv : bv 5) (w64 0) Y16 ltac:(reflexivity).
sch_reg HS (17%bv : bv 5) (w64 (TW.S_cfg_sum_mode Bw)) Y17
  ltac:(exact (sch_sext_g (sch_E4 (ms_regs MS4) Bw) 34 (TW.u_at Bw TW.A_S_cfg_sum_mode 4) E34c R34r)).
sch_reg HS (23%bv : bv 5) (w64 (F + SENDCTL_FOFF)) Y23
  ltac:(cbn [sv_denot]; rewrite (sch_ew4_reg (ms_regs MS4) Bw 25 25%bv eq_refl), V25;
        change (bv_unsigned (w64 F)) with (F mod 2 ^ 64);
        rewrite (Z.mod_small F (2 ^ 64)) by lia; reflexivity).
(* ---- the frame-build cut ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + SENDCTL_FB)) mm rom) mdx) Q) end.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  refine (FB _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
    pos sp1 F S2 mm mdx (TW.bs ojz) rg _ _ _) end.
- unfold sendctl_laws.
  split; [exact HPCS|]. split; [exact HCELLS|]. split; [exact HSC|]. split; [exact HROU|].
  split; [exact HRNE|]. split; [exact LAWS|]. split; [exact MTL|]. split; [exact MTF|].
  split; [exact SMP|]. split; [exact ASF|]. split; [exact FFL|]. split; [exact HGX | exact HGNE].
- unfold sendctl_callees.
  split; [exact ASM0|]. split; [exact FBC|]. split; [exact CPY | exact IOS].
- unfold sendctl_fix.
  split; [exact HJe|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|].
  split; [exact Htp|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  split; [exact H13|]. split; [exact H14|]. split; [exact Hsp16|]. split; [exact Hlo|].
  split; [exact Hhi|]. split; [exact Hcmd|]. split; [exact Hack|]. split; [exact HKP|].
  split; [exact Htw|]. split; [exact Hfn|]. split; [exact Hmodel|]. split; [exact HROM|].
  split; [exact HFLY|]. split; [exact HCMDL|]. split; [exact Hcnt|]. split; [exact Hev|].
  split;
  [ unfold sp1, SENDCTL_FRAME; replace (spZ regs - 128) with (spZ regs + -128) by lia; reflexivity |].
  split; [reflexivity|]. split; [exact HF0|]. split; [exact HF64|].
  split; [unfold SENDCTL_FBYTES; exact HFc | unfold SENDCTL_FBYTES; exact HFapp].
- unfold sendctl_fb_cur.
  split.
  { unfold sendctl_cur.
    split; [rewrite Z.add_0_r; exact HJ|].
    split; [unfold SENDCTL_EV, FRAME_FB_EV, IOSEND_EV; lia|].
    split; [exact Hfrs2|].
    split; [rewrite Eab2; apply Permutation_refl|].
    split; [reflexivity|]. split; [exact HMO|]. split; [exact KGOV|]. split; [exact HFW5|].
    split; [unfold SENDCTL_FBYTES; exact HFL5 | exact HKLPR]. }
  split; [exact Eab2|]. split; [exact Htw5|]. split; [exact HROM5|].
  split; [unfold TW.bs; rewrite length_map, Hojl; reflexivity|].
  split; [rewrite Hojz; exact Hojg|].
  split; [exact HRDf|]. split; [exact HTWRf|]. split; [exact HHDR|]. split; [exact HRDh | exact HIN].
- unfold sendctl_regs_fb.
  split; [exact Y2|]. split; [rewrite Y3; symmetry; exact Hgp|]. split; [rewrite Y4; symmetry; exact Htp|].
  split; [exact Y8|]. split; [exact Y9|]. split; [exact Y18|]. split; [exact Y19|]. split; [exact Y20|].
  split; [exact Y21|]. split; [exact Y22|]. split; [exact Y23|]. split; [exact Y24|]. split; [exact Y25|].
  split; [exact Y26|]. split; [exact Y27|]. split; [exact Y10|]. split; [exact Y11|]. split; [exact Y12|].
  split; [exact Y13|]. split; [exact Y14|]. split; [exact Y15|]. split; [exact Y16 | exact Y17].
Qed.

End head.
