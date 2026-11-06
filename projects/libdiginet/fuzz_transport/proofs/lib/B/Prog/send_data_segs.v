(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 397 of its 445 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SendctlBCut.v, with its module names changed; 138 of its 212 lines of code are new or changed and 371 lines of the source are left out. *)
(* send_data_segs: the cuts of image B's walk of send_data (fuzz_transport.asan-ubsan 0x89d78 = transportb_sigma
   TB_send_data, AF_send_data = 0x8ad8 of lib/B/Prog/DgnTransportBList.v), as STATEMENTS only, and the composition
   sd_holds_of: the statement transport_send_data_cg_holds_stmt of lib/B/Prog/send_data_cg.v from the three piece
   Props. Image B's twin of lib/A/Prog/send_data_segs.v: the same cut design, at image B's offsets. The walk holds the
   CALLER's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) from the entry to the return, with
   (SENDDATA_CID, pos) :: own while the class-0 frame is live. Image B's code is image A's with three more words: the
   UBSan alignment test of s (`andi a0, s3, 7` at +0x11c, `bnez a0` at +0x124 to the trap word at +0x35c), so every
   offset from +0x128 on is image A's + 8. It has three pieces:
     head  +0x000 .. +0x184  the frame (`addi sp,sp,-160`, `sd zero,0(sp)`, the 13 saves), s0 = the entry sp, the
                             32-byte realign into s1 = sp1, the two slots s1 + 16 (now) and s1 + 24 (body_len),
                             s7 = ncmds, s6 = bodyp, the two runtime cells (the flag word 1, so `beq a2, zero` at
                             +0x074 is not taken), s4 = the shadow base, s3 = s, `jal __asan_stack_malloc_0` (+0x07c;
                             lib/A/Prog/TransportGFrame.v gx_stack_malloc_at), s2 = s10 = the frame F (>= 4096, so
                             the real-stack arm at +0x094 is not entered), the slot s1 + 48, s8 = hp = F + 32, the
                             frame's 24-byte header, s11 = the frame's shadow address and its 8 shadow bytes
                             (4..5 := 0, 6..7 := 0xf3, 0..3 := 0xf1), `jal __asan_memset` (+0x118; hp, 0, 15), the
                             alignment test of s (not taken: s = 0x5df640 is a multiple of 8), the store of ncmds at
                             hp + 15, the checked load of S_host_counter (s9 = s + 160, s5 = its shadow address), the
                             two stores of the new counter at s + 160 and at hp + 4, the checked load of
                             S_cfg_sum_mode, s7 = out = s + 216, the seven argument registers and
                             `jal diginet_frame_build` (+0x184). Prop: sd_head_stmt.
     mid   +0x188 .. +0x2a8  a2 = n; n < 0 goes to the release cut; else the checked 8-byte store of n at s + 1736,
                             the four stores of inflight_start (s + 212, s + 1744, s + 1748, s + 1752), s5 = s + 18192,
                             the read-modify-write of stats.tx_data at s + 18200, the checked loads of S_io_send
                             (s + 72) and S_io_ctx (s + 64), `jalr a3` (+0x280: io_send at TI.ti_io_send timg_B),
                             a2 = r; r <> 0 goes to the release cut; else the read-modify-write of stats.tx_frames at
                             s + 18192 and a2 = 0, to the release cut. Prop: sd_mid_stmt.
     rel   +0x2ac .. +0x358  the frame's shadow bytes 4..5 := 0xf8, the header word 0x45e0360e at F, `beq s2, zero`
                             not taken, the frame's 8 shadow bytes := 0xf5, the flag pointer from the frame's last
                             word and the store of 0 at it (the release: lib/B/Prog/TransportGFrameB.v
                             gx_flag_store_pi), `j +0x318`, a0 = a2, sp = s0 - 160, the 13 reloads, sp = sp + 160,
                             `ret`. Prop: sd_rel_stmt.
   Each cut holds the caller's facts (sd_fix), the journal and the facts carried at the cut (sd_fb_cur, sd_rel_cur),
   and the registers the code after the cut reads (sd_regs_fb, sd_regs_rel), and concludes the statement's post
   (send_data_cg.v transport_senddata_post) at the cut's pc. The slot s1 + 48 the head stores (+0x0b0) is read by no
   later instruction, so no cut carries it. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TNeed TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TNd := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The cut points, the frame and the saved words                    *)
(* ------------------------------------------------------------------ *)

(* The two cut points, as offsets from the listing's base: the return address of the call of diginet_frame_build
   (`mv a2,a0` at +0x188) and the join the three paths reach (`li a0,-8` at +0x2ac, the target of `bltz a0` at
   +0x18c and of `bnez a0` at +0x288). *)
Definition SD_FB : Z := AF_send_data + 0x188.
Definition SD_REL : Z := AF_send_data + 0x2ac.
(* The `ret`. *)
Definition SD_RET : Z := AF_send_data + 0x358.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s11 (sd at sp + 152 ..
   sp + 56 after `addi sp, sp, -160`). *)
Definition SD_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22);
   (72, 23); (80, 24); (88, 25); (96, 26); (104, 27)].
(* The class-0 frame's size (a0 = 64 at +0x078). *)
Definition SENDDATA_FBYTES : Z := 64.
Lemma sd_fbytes : fs_frame_bytes SENDDATA_CID = SENDDATA_FBYTES.
Proof. reflexivity. Qed.

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma sd_some_w : forall (Bx By : list byte) (x y : Z), Some (Bx, x) = Some (By, y) -> Bx = By.
Proof. intros Bx By x y H. exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H). Qed.
Lemma sd_some_r : forall (Bx By : list byte) (x y : Z), Some (Bx, x) = Some (By, y) -> x = y.
Proof. intros Bx By x y H. exact (f_equal (fun o => match o with Some (_, v) => v | None => x end) H). Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model's worlds, step by step (lib/TModel/TSess.v send_data_m) *)
(* ------------------------------------------------------------------ *)

(* :391 the store of the new host counter. *)
Definition sd_M1 (Bw : list byte) (ncmds : Z) : list byte :=
  TW.set_S_host_counter Bw (DSpec.u32 (TW.S_host_counter Bw + ncmds)).
(* :393-394 diginet_frame_build's code, at the mode read from that world. *)
Definition sd_n (Bw : list byte) (ncmds : Z) (body : list byte) : Z :=
  TNd.diginet_frame_build_code body TS0.DIGINET_MAX_FRAME_LEN (TW.S_cfg_sum_mode (sd_M1 Bw ncmds)).
(* the frame diginet_frame_build builds into g_s.inflight_frame (send = the NEW host counter, ack = retry = 0,
   cmd = DIGINET_CMD_DATA, ncmds the uint8_t). *)
Definition sd_LF (Bw : list byte) (ncmds : Z) (body : list byte) : list byte :=
  DLib.lib_frame (TW.S_desk_mac (sd_M1 Bw ncmds)) (TW.S_cfg_host_mac (sd_M1 Bw ncmds))
    (TW.S_host_counter (sd_M1 Bw ncmds)) 0 0 TS0.DIGINET_CMD_DATA (DSpec.u8 ncmds) body
    (TW.S_cfg_sum_mode (sd_M1 Bw ncmds)).
Definition sd_B2 (Bw : list byte) (ncmds : Z) (body : list byte) : list byte :=
  TW.set_S_inflight_frame (sd_M1 Bw ncmds) (sd_LF Bw ncmds body).
(* :397 *)
Definition sd_B3 (Bw : list byte) (ncmds : Z) (body : list byte) : list byte :=
  TW.set_S_inflight_len (sd_B2 Bw ncmds body) (sd_n Bw ncmds body).
(* :398 inflight_start (:113-116), inlined *)
Definition sd_B7 (Bw : list byte) (ncmds : Z) (body : list byte) (now : Z) : list byte :=
  TW.set_S_inflight_sent_us
    (TW.set_S_inflight_retries
       (TW.set_S_inflight_counter (TW.set_S_inflight (sd_B3 Bw ncmds body) 1)
          (TW.S_host_counter (sd_B3 Bw ncmds body))) 0) now.
(* :399 *)
Definition sd_B8 (Bw : list byte) (ncmds : Z) (body : list byte) (now : Z) : list byte :=
  TW.set_S_stats_tx_data (sd_B7 Bw ncmds body now)
    (TS0.u64 (TW.S_stats_tx_data (sd_B7 Bw ncmds body now) + 1)).
(* the bytes send_raw hands io_send (:400) *)
Definition sd_fr (Bw : list byte) (ncmds : Z) (body : list byte) (now : Z) : list byte :=
  TW.sub (sd_B8 Bw ncmds body now) TW.A_S_inflight_frame (Z.to_nat (sd_n Bw ncmds body)).

(* The world at the cut SD_FB: the host-counter store, then diginet_frame_build's write of the 1514 bytes at
   out = s + 216 (unchanged when the build refused). *)
Definition sd_Bfb (Bw : list byte) (ncmds : Z) (body : list byte) : list byte :=
  if 0 <=? sd_n Bw ncmds body then sd_B2 Bw ncmds body else sd_M1 Bw ncmds.

(* ------------------------------------------------------------------ *)
(* 3. Shared facts about G and the written range                       *)
(* ------------------------------------------------------------------ *)

(* Every byte of g_s's payload is a byte of G (row 10 of TG.G_HARNESS_B). *)
Lemma sd_gs_row : In (TB_g_s, TW.SZ_g_s) TG.G_HARNESS_B.
Proof. unfold TG.G_HARNESS_B, TB_g_s, TW.SZ_g_s. do 9 right. left. reflexivity. Qed.

Lemma sd_inG_gs : forall a, TB_g_s <= a < TB_g_s + TW.SZ_g_s -> W_journalG.inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold W_journalG.inG. apply Exists_exists. exists (TB_g_s, TW.SZ_g_s).
split; [exact sd_gs_row | unfold in_zr; cbn [fst snd]; exact Ha].
Qed.

(* io_send's written range for a frame of at most 1514 bytes lies in send_data's. *)
Lemma sd_iosend_wr_sub : forall n a, iosend_wr n a -> senddata_wr a.
Proof.
intros n a H. unfold senddata_wr. do 9 right.
assert (Hm : Z.min n TC.SPEC_MAX_FRAME <= Z.min SENDDATA_CAP TC.SPEC_MAX_FRAME).
{ change (Z.min SENDDATA_CAP TC.SPEC_MAX_FRAME) with TC.SPEC_MAX_FRAME. apply Z.le_min_r. }
set (m1 := Z.min n TC.SPEC_MAX_FRAME) in H, Hm.
set (m2 := Z.min SENDDATA_CAP TC.SPEC_MAX_FRAME) in Hm |- *.
unfold iosend_wr in H |- *.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]];
  try tauto.
do 15 right. left. revert H. unfold twb_fld. intros H. split; [tauto | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The cuts                                                         *)
(* ------------------------------------------------------------------ *)

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma sd_cut_pcs :
  BASE + AF_send_data = transportb_sigma TB_send_data /\ BASE + SD_FB = 0x89f00 /\
  BASE + SD_REL = 0x8a024 /\ BASE + SD_RET = 0x8a0d0.
Proof. repeat split; reflexivity. Qed.

(* The facts of the record every piece may use: the premises of transport_send_data_cg_holds_stmt that are not
   callee contracts, with gx_ok / gx_noerrno already read off trans_g_unowned / trans_g_no_errno. *)
Definition sd_laws : Prop :=
  pc_stack_malloc (as_code B) SENDDATA_CID = transportb_sigma TB___asan_stack_malloc_0 /\
  transport_cells B /\ trans_senddata_cells B /\
  trans_g_unowned B /\ trans_g_no_errno B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS_B /\ gx_noerrno B TG.G_HARNESS_B.

(* The caller's facts (the premises of transport_send_data_cg at the entry registers regs), and what the head fixes
   before the first cut: sp1, the realigned stack pointer (`addi sp, sp, -160`, `andi sp, sp, -32`); pos, the slot of
   the class-0 frame the stack malloc gave; F, the frame's address. *)
Definition sd_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (bodyp ncmds now r : Z) (body : list byte) (TF : option TI.tframe)
    (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 SENDDATA_S /\ YK11.getr regs 11 = w64 bodyp /\
  YK11.getr regs 12 = w64 (Z.of_nat (length body)) /\ YK11.getr regs 13 = w64 (bv_swrap 32 ncmds) /\
  YK11.getr regs 14 = w64 now /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SENDDATA_STK /\ spZ regs <= sp0 /\
  0 <= ncmds < 2 ^ 32 /\ 0 <= now < 2 ^ 64 /\ 0 < bodyp /\
  garr8 segs (mrestrict (w_H W) memc) bodyp (TW.zs body) /\
  trans_src_ok B lyc Sc W memc bodyp (Z.of_nat (length body)) /\
  decode_off_win regs SENDDATA_STK bodyp (Z.of_nat (length body)) /\
  (forall x, bodyp <= x < bodyp + Z.of_nat (length body) -> ~ W_journalG.inG TG.G_HARNESS_B x) /\
  tw_at TMAP_B (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.send_data_m timg_B TF Bw body ncmds now = Some (Bw', r) /\
  trans_rom_view_rd W memc /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX) /\
  count_cid SENDDATA_CID (frames Sc) < fs_frames SENDDATA_CID /\
  count_cid TRANS_BC_CID (frames Sc) < fs_frames TRANS_BC_CID /\
  st_nev S + k + SENDDATA_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - SENDDATA_FRAME) / 32) /\
  F = frame_addr lyc SENDDATA_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + SENDDATA_FBYTES <= alloc_ceiling /\ in_app F SENDDATA_FBYTES.

(* What both cuts carry while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames
   where the call's layout puts them, the meter; what the call has kept so far (acall_kept_g over the statement's
   window and written range senddata_wr); the 13 saved words below the entry sp; the frame's last word, the address
   of its flag byte (astack_malloc_realizes' rdword). *)
Definition sd_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((SENDDATA_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= SENDDATA_EV /\
  frames S2 = (SENDDATA_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (spZ regs - SENDDATA_STK) (spZ regs) senddata_wr /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SD_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + SENDDATA_FBYTES - 8) = Some (flag_addr lyc SENDDATA_CID pos).

(* The state at the cut SD_FB (+0x188), reached from the head only: sd_cur, the world relation at sd_Bfb (the
   host-counter store and diginet_frame_build's write of out), the read-only image bytes io_send reads still the
   image's, and the slot s1 + 16 holding now (read at +0x220). *)
Definition sd_fb_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (ncmds now : Z) (body : list byte) (Bw : list byte) (pos sp1 F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  sd_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) (sd_Bfb Bw ncmds body) /\
  trans_rom_view_rd W2 mem2 /\
  rdword (aview segs (w_H W2) mem2) (sp1 + 16) = Some now.

(* The state at the release cut (+0x2ac), reached from the mid on any of its three paths: sd_cur, and the post's X
   already holds: the world relation at the model's world Bw' and g_fail_next Bw' <= 1. *)
Definition sd_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  sd_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_B (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1.

(* The callee-saved registers both cuts read or must hand back: gp, tp, s0 = the entry sp, s2 = s10 = the frame,
   s11 = the frame's shadow address. *)
Definition sd_regs_keep (regs regs2 : bvmap 5 word) (F : Z) : Prop :=
  YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\
  YK11.getr regs2 18 = w64 F /\ YK11.getr regs2 26 = w64 F /\
  YK11.getr regs2 27 = w64 (SHADOW_OFF + F / 8).
(* The release also reads a2, the result the three paths leave there. *)
Definition sd_regs_rel (regs regs2 : bvmap 5 word) (F res : Z) : Prop :=
  sd_regs_keep regs regs2 F /\ YK11.getr regs2 12 = w64 res.
(* The mid reads sp = s1 = sp1, a0 = n (diginet_frame_build's result, still in a0 at +0x188, where the pc of the
   cut is: `addi a2,a0,0` has NOT run yet, so a2 holds nothing the walk may use), s3 = s, s4 = the shadow base,
   s5 = the shadow address of s + 160, s7 = out = s + 216 and s9 = s + 160. *)
Definition sd_regs_fb (regs regs2 : bvmap 5 word) (sp1 F nn : Z) : Prop :=
  sd_regs_keep regs regs2 F /\
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 9 = w64 sp1 /\
  YK11.getr regs2 10 = w64 nn /\
  YK11.getr regs2 19 = w64 SENDDATA_S /\ YK11.getr regs2 20 = w64 SHADOW_OFF /\
  YK11.getr regs2 21 = w64 (SHADOW_OFF + (SENDDATA_S + 160) / 8) /\
  YK11.getr regs2 23 = w64 (SENDDATA_S + 216) /\ YK11.getr regs2 25 = w64 (SENDDATA_S + 160).

(* The release cut, +0x2ac: from the state sd_rel_cur, the post. *)
Definition sd_rel_at : Prop :=
  sd_laws ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bodyp ncmds now r : Z) (body : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
         (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
         (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    sd_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body TF Bw Bw' pos sp1 F ->
    sd_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' pos F ly2 S2 W2 mem2 md2 e ->
    sd_regs_rel regs regs2 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SD_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_senddata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The cut SD_FB, +0x188: from the state sd_fb_cur, the post; io_send's contract is its callee's. *)
Definition sd_fb_at : Prop :=
  sd_laws ->
  (forall fx' : YK11.FPState, @transport_io_send_cg fx' rc B MT (TI.ti_io_send timg_B)) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (bodyp ncmds now r : Z) (body : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
         (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
         (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    sd_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bodyp ncmds now r body TF Bw Bw' pos sp1 F ->
    sd_fb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs ncmds now body Bw pos sp1 F
      ly2 S2 W2 mem2 md2 e ->
    sd_regs_fb regs regs2 sp1 F (sd_n Bw ncmds body) ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SD_FB)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_senddata_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw' r).

(* The three pieces. rel: +0x2ac .. the return. mid: +0x188 .. +0x2a8, then the release cut. head: the entry ..
   +0x184, then the cut SD_FB. *)
Definition sd_rel_stmt : Prop := sd_rel_at.
Definition sd_mid_stmt : Prop := sd_rel_at -> sd_fb_at.
Definition sd_head_stmt : Prop := sd_fb_at -> @transport_send_data_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma sd_holds_of : sd_head_stmt -> sd_mid_stmt -> sd_rel_stmt ->
  @transport_send_data_cg_holds_stmt fx rc B MT.
Proof. intros HEAD MID REL. exact (HEAD (MID REL)). Qed.
End cut.
