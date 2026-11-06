(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 395 of its 443 lines of code are new or changed and 878 lines of the source are left out. *)
(* SendctlCut: the cuts of the walk of send_control (fuzz_transport.asan 0x86d5c = transport_sigma TS_send_control,
   AF_send_control = 0x5af8 of lib/A/Prog/DgnTransportList.v), as STATEMENTS only, the lemmas every piece shares, and
   the composition sendctl_holds_of: the statement transport_send_control_cg_holds_stmt of
   lib/A/Prog/send_control_cg.v from the five piece Props. The walk holds the CALLER's G journal (lib/A/W_journalG.v
   ajournal_gx TG.G_HARNESS 0 []) from the entry to the return, with (SENDCTL_CID, pos) :: own while the class-2
   frame is live. It has five pieces:
     head  +0x000 .. +0x1a0  the frame (`addi sp, sp, -128`), the zero word at sp, the 12 saves, s0 = the entry sp,
                             the realign into s1, s4 = klp, s6 = kp, s7 = ack, s5 = cmd, the two runtime cells (the
                             flag word is 1, so `beqz a2` at +0x070 is not taken), s10 = the shadow base, s3 = s,
                             `jal __asan_stack_malloc_2` (+0x078; lib/A/Prog/TransportGFrame.v gx_stack_malloc_at),
                             s2 = s9 = the frame, `bnez s2` taken, the frame's header and its 20 shadow bytes
                             (s8 = their address), the 4-byte store of 0 at frame + 128, the frame word at s1 + 24,
                             the checked load of s + 160, the five stores into h, the checked load of s + 20,
                             a7 = the sum mode, s7 = f = frame + 32 and the eight argument registers: the
                             frame-build cut. Prop: sendctl_head_stmt.
     fb    +0x1a4 .. +0x1b0  `jal diginet_frame_build` (+0x1a4), s5 = n, `bltz a0` (n < 0 goes to the release cut),
                             `beqz s6` (kp = 0 goes to the send cut, else the keep cut). Prop: sendctl_fb_stmt.
     keep  +0x1b4 .. +0x1d4  a0 = kp, a1 = f, a2 = n, `jal __asan_memcpy` (+0x1c0), the checked 8-byte store of n at
                             klp, to the send cut. Prop: sendctl_keep_stmt.
     send  +0x1d8 .. +0x248  the checked 8-byte loads of s + 72 and s + 64, `jalr a3` (+0x214: io_send at
                             TI.ti_io_send timg_A), s5 = r, `bnez a0` (r <> 0 goes to the release cut), the checked
                             8-byte load of s + 18192, s5 = 0, the increment and the store back, to the release cut.
                             Prop: sendctl_send_stmt.
     rel   +0x24c .. +0x3a4  the frame's shadow bytes 4..11 and 16..17 := 0xf8, the header word 0x45e0360e at the
                             frame, `beqz s2` not taken, the frame's 32 shadow bytes := 0xf5, the flag pointer from
                             the frame's last word, the store of 0 at it (the release: TransportGFrame.v
                             gx_flag_store_pi), `j +0x368`, a0 = s5, sp = s0 - 128, the 12 reloads, sp = sp + 128,
                             `ret`. Prop: sendctl_rel_stmt.
   Each cut holds the caller's facts (sendctl_fix), the journal and the facts carried at the cut (sendctl_cur and the
   cut's own), the registers the code after the cut reads (sendctl_regs_rel / _send / _keep / _fb), and concludes the
   statement's post (send_control_cg.v transport_sendctl_post) at the cut's pc.

   THE OUT CELL. The statement's post is transport_cg_post_out with the out cells sendctl_outs kp klp: its
   acall_kept_g is read at the memory with klp's 8 bytes put back (W_journalG.v gover), because the 8-byte store at
   +0x1d4 changes a byte of the CALLER's machine frame, which lies above alloc_ceiling and outside this call's stack
   window, where acall_kept_g's first clause keeps every byte whatever the written range is. So every cut carries the
   kept fact in that form, and acall_kept_g_gover below carries it over a step of the walk and over a callee call
   (both read the walk's entry memory at an out byte, and the byte is unhidden at both worlds). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o YM05 YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YG0a YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_frame_build_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_build_w_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TImg TSess0 TSess.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module PBuildW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_build_w_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The four cut points, as offsets from the listing's base: the `jal diginet_frame_build`, the first instruction of
   the keep path (`mv a0, s6`, the fall-through of `beqz s6`), the first instruction of the send path
   (`addi a0, s3, 72`) and the join of the three paths (`li a0, -8`). *)
Definition SENDCTL_FB : Z := AF_send_control + 0x1a4.
Definition SENDCTL_KEEP : Z := AF_send_control + 0x1b4.
Definition SENDCTL_SEND : Z := AF_send_control + 0x1d8.
Definition SENDCTL_REL : Z := AF_send_control + 0x24c.
(* The words the prologue saves, as (distance below the entry sp, register): ra, s0, s1, s2 .. s10 (sd at sp + 120 ..
   sp + 32 after `addi sp, sp, -128`). s11 is never written, so it is not saved. *)
Definition SENDCTL_SAVED : list (Z * Z) :=
  [(8, 1); (16, 8); (24, 9); (32, 18); (40, 19); (48, 20); (56, 21); (64, 22); (72, 23); (80, 24);
   (88, 25); (96, 26)].
(* The class-2 frame's size, and the two locals in it: f (60 bytes at frame + 32) and h (16 bytes at frame + 128),
   from the frame's description string "2 32 60 4 f:99 128 16 5 h:100". *)
Definition SENDCTL_FBYTES : Z := 256.
Definition SENDCTL_FOFF : Z := 32.
Definition SENDCTL_HOFF : Z := 128.
Lemma sendctl_fbytes : fs_frame_bytes SENDCTL_CID = SENDCTL_FBYTES.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The model (lib/TModel/TSess.v send_control_m)                        *)
(* ------------------------------------------------------------------ *)

(* The build's code: -1 when the sum mode is neither 0 nor 1, else 60. *)
Definition sendctl_code (Bw : list byte) : Z :=
  diginet_frame_build_code [] TS0.DIGINET_MIN_FRAME_LEN (TW.S_cfg_sum_mode Bw).
(* The 60 bytes the model builds. *)
Definition sendctl_fr (Bw : list byte) (cmd ack : Z) : list byte :=
  lib_frame (TW.S_desk_mac Bw) (TW.S_cfg_host_mac Bw) (TW.S_host_counter Bw) ack 0 cmd 0 [] (TW.S_cfg_sum_mode Bw).

Lemma sendctl_code_cases : forall Bw,
  sendctl_code Bw = -1 \/ (sendctl_code Bw = 60 /\ (TW.S_cfg_sum_mode Bw = 0 \/ TW.S_cfg_sum_mode Bw = 1)).
Proof.
intros Bw. unfold sendctl_code.
destruct ((TW.S_cfg_sum_mode Bw =? 0) || (TW.S_cfg_sum_mode Bw =? 1))%bool eqn:EM.
- right. split; [unfold diginet_frame_build_code; rewrite EM; reflexivity|].
  apply orb_true_iff in EM. destruct EM as [E|E]; apply Z.eqb_eq in E; [left | right]; exact E.
- left. unfold diginet_frame_build_code. rewrite EM. reflexivity.
Qed.

(* The wide contract's code at the 60 bytes of f is the model's (lib/Prog/T/send_data.v bcw_eq). *)
Lemma sendctl_bcw : forall Bw (oj : list byte), length oj = 60%nat ->
  PBuildW.build_code_w [] (Z.of_nat (length oj)) (TW.S_cfg_sum_mode Bw) = sendctl_code Bw.
Proof.
intros Bw oj Hoj. rewrite Hoj. unfold PBuildW.build_code_w, sendctl_code, diginet_frame_build_code.
rewrite lib_build_code_eq.
destruct ((TW.S_cfg_sum_mode Bw =? 0) || (TW.S_cfg_sum_mode Bw =? 1))%bool; reflexivity.
Qed.

(* The 60 bytes the build leaves at f are the model's frame (lib/Prog/T/send_control.v sc_build_out). *)
Lemma sendctl_build_out : forall Bw cmd ack (oj : list byte),
  (TW.S_cfg_sum_mode Bw = 0 \/ TW.S_cfg_sum_mode Bw = 1) -> length oj = 60%nat ->
  PBuildW.build_out_w (TW.S_desk_mac Bw) (TW.S_cfg_host_mac Bw) (TW.S_host_counter Bw) ack 0 cmd 0 []
    (TW.S_cfg_sum_mode Bw) oj = sendctl_fr Bw cmd ack.
Proof.
intros Bw cmd ack oj Hm Hoj. unfold PBuildW.build_out_w, sendctl_fr. rewrite Hoj. cbv zeta.
assert (E : PBuildW.build_code_w [] (Z.of_nat 60) (TW.S_cfg_sum_mode Bw) = 60)
  by (unfold PBuildW.build_code_w; destruct Hm as [-> | ->]; reflexivity).
rewrite E. destruct (Z.leb_spec 0 60) as [_|L]; [|lia].
rewrite skipn_all2 by (rewrite Hoj; cbn; lia). rewrite app_nil_r.
symmetry. apply frame_build_bytes. exact Hm.
Qed.

Lemma sendctl_len_fr : forall Bw cmd ack, length Bw = Z.to_nat TW.W_LEN ->
  length (sendctl_fr Bw cmd ack) = 60%nat.
Proof.
intros Bw cmd ack HL. unfold sendctl_fr, lib_frame.
assert (LD : length (TW.S_desk_mac Bw) = 6%nat).
{ unfold TW.S_desk_mac. apply TWL.length_sub; [unfold TW.A_S_desk_mac, TW.OFF_g_s; lia|].
  rewrite HL. unfold TW.A_S_desk_mac, TW.OFF_g_s, TW.W_LEN. lia. }
assert (LH : length (TW.S_cfg_host_mac Bw) = 6%nat).
{ unfold TW.S_cfg_host_mac. apply TWL.length_sub; [unfold TW.A_S_cfg_host_mac, TW.OFF_g_s; lia|].
  rewrite HL. unfold TW.A_S_cfg_host_mac, TW.OFF_g_s, TW.W_LEN. lia. }
rewrite !length_app, repeat_length, LD, LH. reflexivity.
Qed.

(* The model's result read off an equation between two results (no injection on a world-carrying option). *)
Lemma sendctl_some_inv : forall (Bx By : list byte) (px py : Z * list byte),
  Some (Bx, px) = Some (By, py) -> Bx = By /\ px = py.
Proof.
intros Bx By px py H. split.
- exact (f_equal (fun o => match o with Some (b, _) => b | None => Bx end) H).
- exact (f_equal (fun o => match o with Some (_, p) => p | None => px end) H).
Qed.

(* The two branches of send_control_m. *)
Lemma sendctl_model : forall I TF Bw cmd ack Bw' r f,
  TSS.send_control_m I TF Bw cmd ack = Some (Bw', (r, f)) ->
  (sendctl_code Bw = -1 /\ Bw' = Bw /\ r = -1 /\ f = []) \/
  (sendctl_code Bw = 60 /\ (TW.S_cfg_sum_mode Bw = 0 \/ TW.S_cfg_sum_mode Bw = 1) /\
   f = sendctl_fr Bw cmd ack /\ TW.S_io_send Bw = TI.ti_io_send I /\
   exists B1, TC.io_send_m I Bw f = Some (B1, r) /\
     ((r = 0 /\ Bw' = TW.set_S_stats_tx_frames B1 (TS0.u64 (TW.S_stats_tx_frames B1 + 1))) \/
      (r <> 0 /\ Bw' = B1))).
Proof.
intros I TF Bw cmd ack Bw' r f HM.
unfold TSS.send_control_m in HM. cbv zeta in HM.
fold (sendctl_code Bw) in HM.
destruct (sendctl_code_cases Bw) as [E | [E Hm]].
- rewrite E in HM. replace (-1 <? 0) with true in HM by reflexivity. cbv beta iota in HM.
  destruct (sendctl_some_inv _ _ _ _ HM) as [HB HP]. injection HP as HR HF.
  left. split; [exact E|]. split; [symmetry; exact HB|]. split; [symmetry; exact HR | symmetry; exact HF].
- rewrite E in HM. replace (60 <? 0) with false in HM by reflexivity. cbv beta iota in HM.
  unfold TSS.send_raw_m, TSS.call_send in HM.
  fold (sendctl_fr Bw cmd ack) in HM.
  destruct (TW.S_io_send Bw =? TI.ti_io_send I) eqn:ES; [|discriminate HM].
  destruct (TC.io_send_m I Bw (sendctl_fr Bw cmd ack)) as [[B1 r1]|] eqn:HIO; [|discriminate HM].
  cbv beta iota in HM.
  right. split; [exact E|]. split; [exact Hm|].
  destruct (r1 =? 0) eqn:ER0.
  + destruct (sendctl_some_inv _ _ _ _ HM) as [HB HP]. injection HP as HR HF.
    subst r f.
    split; [reflexivity|]. split; [apply Z.eqb_eq; exact ES|].
    exists B1. split; [exact HIO|].
    left. split; [apply Z.eqb_eq; exact ER0 | symmetry; exact HB].
  + destruct (sendctl_some_inv _ _ _ _ HM) as [HB HP]. injection HP as HR HF.
    subst r f.
    split; [reflexivity|]. split; [apply Z.eqb_eq; exact ES|].
    exists B1. split; [exact HIO|].
    right. split; [apply Z.eqb_neq; exact ER0 | symmetry; exact HB].
Qed.

Section cut. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The cut points and the entry in the image's addresses. *)
Lemma sendctl_cut_pcs :
  BASE + AF_send_control = transport_sigma TS_send_control /\ BASE + SENDCTL_FB = 0x86f00 /\
  BASE + SENDCTL_KEEP = 0x86f10 /\ BASE + SENDCTL_SEND = 0x86f34 /\ BASE + SENDCTL_REL = 0x86fa8.
Proof. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Reading acall_kept_g at the memory with the out cells put back       *)
(* ------------------------------------------------------------------ *)

Lemma gover_in_aview : forall (outs : list (Z * Z)) (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> inG outs a -> aview segs H (gover outs ma mb) a = aview segs H mb a.
Proof.
intros outs H ma mb a Ha Hin. apply (aview_eq_of segs). unfold mrestrict, gover.
rewrite unsigned_lit_small by lia.
destruct (inGb outs a) eqn:Eb; [reflexivity|].
exfalso. exact (proj1 (inGb_false outs a) Eb Hin).
Qed.

Lemma gover_nin_aview : forall (outs : list (Z * Z)) (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ inG outs a -> aview segs H (gover outs ma mb) a = aview segs H ma a.
Proof.
intros outs H ma mb a Ha Hn. apply (aview_eq_of segs). unfold mrestrict, gover.
rewrite unsigned_lit_small by lia.
destruct (inGb outs a) eqn:Eb; [exfalso; exact (Hn (proj1 (inGb_spec outs a) Eb)) | reflexivity].
Qed.

(* A byte unhidden at both worlds is read the same there, whatever the memory. *)
Lemma aview_pres_eq : forall (W1 W2 : world segs) (mA mB m : word -> option byte) a,
  apresent (w_H W1) mA a -> apresent (w_H W2) mB a ->
  aview segs (w_H W2) m a = aview segs (w_H W1) m a.
Proof.
intros W1 W2 mA mB m a (H1 & _) (H2 & _). unfold aview, mbyte, mrestrict. rewrite H1, H2. reflexivity.
Qed.

(* A kept fact read with the out cells put back on both sides: at an out byte both sides read the walk's entry
   memory memc, and the byte is unhidden at both worlds, so the views agree; every other byte reduces. The
   addresses the four keep clauses range over are bounded by the record's laws, as dk_kept_step_g bounds them. *)
Lemma acall_kept_g_gover : forall (G outs : list (Z * Z)) lyc Sc (W1 W2 : world segs) memA memB memc mdA slo shi
    (Eo : Z -> Prop),
  AR_laws segs B ->
  @AR rc segs B lyc Sc W1 memA mdA ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, inG outs a -> 0 <= a < 2 ^ 64 /\ ~ (slo <= a < shi) /\
     apresent (w_H W1) memA a /\ apresent (w_H W2) memB a /\ apresent (w_H W1) memc a) ->
  acall_kept_g segs B G lyc Sc W1 memA W2 memB slo shi Eo ->
  acall_kept_g segs B G lyc Sc W1 (gover outs memA memc) W2 (gover outs memB memc) slo shi Eo.
Proof.
intros G outs lyc Sc W1 W2 memA memB memc mdA slo shi Eo LAWS HAR Hce Hshi Hout (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstep : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W2) memB a = aview segs (w_H W1) memA a ->
  aview segs (w_H W2) (gover outs memB memc) a = aview segs (w_H W1) (gover outs memA memc) a).
{ intros a Ha Hk. destruct (inGb outs a) eqn:Eb.
  - assert (Hin : inG outs a) by (apply inGb_spec; exact Eb).
    destruct (Hout a Hin) as (_ & _ & HA & HB & _).
    rewrite (gover_in_aview outs (w_H W2) memB memc a Ha Hin).
    rewrite (gover_in_aview outs (w_H W1) memA memc a Ha Hin).
    exact (aview_pres_eq W1 W2 memA memB memc a HA HB).
  - assert (Hn : ~ inG outs a) by (apply inGb_false; exact Eb).
    rewrite (gover_nin_aview outs (w_H W2) memB memc a Ha Hn).
    rewrite (gover_nin_aview outs (w_H W1) memA memc a Ha Hn). exact Hk. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. apply Hstep; [lia | exact (K1 a Ha Hw)].
- intros b n i Hb Hi Hn.
  destruct (al_blocks _ _ LAWS lyc Sc W1 memA mdA b n HAR Hb) as (_ & H4096 & Hbce & _).
  apply Hstep; [lia | exact (K2 b n i Hb Hi Hn)].
- intros a Hi HnG Hno He.
  pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  apply Hstep; [lia | exact (K3 a Hi HnG Hno He)].
- intros cid pos a Hpin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W1 memA mdA cid pos HAR Hpin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  apply Hstep; [exact Ha | exact (K4 cid pos a Hpin Hr Hn)].
- intros a Ha Hw Hp. destruct (inGb outs a) eqn:Eb.
  + assert (Hin : inG outs a) by (apply inGb_spec; exact Eb).
    destruct (Hout a Hin) as (Hr & _ & _ & HB & Hc).
    destruct HB as (Hh2 & _). destruct Hc as (_ & bb & Hbb).
    split; [exact Hh2|]. exists bb. unfold gover. rewrite unsigned_lit_small by lia. rewrite Eb. exact Hbb.
  + assert (Hn : ~ inG outs a) by (apply inGb_false; exact Eb).
    destruct Hp as (Hh & bb & Hbb). unfold gover in Hbb.
    rewrite unsigned_lit_small in Hbb by lia. rewrite Eb in Hbb.
    destruct (K5 a Ha Hw (conj Hh (ex_intro _ bb Hbb))) as (Hh2 & bb2 & Hbb2).
    split; [exact Hh2|]. exists bb2. unfold gover. rewrite unsigned_lit_small by lia. rewrite Eb. exact Hbb2.
- intros a Ha.
  assert (Har : 0 <= a < 2 ^ 64) by lia.
  assert (Hn : ~ inG outs a) by (intros Hin; destruct (Hout a Hin) as (_ & Hw & _); exact (Hw Ha)).
  destruct (K6 a Ha) as (Hh & bb & Hbb).
  split; [exact Hh|]. exists bb. unfold gover. rewrite unsigned_lit_small by lia.
  destruct (inGb outs a) eqn:Eb; [exfalso; exact (Hn (proj1 (inGb_spec outs a) Eb)) | exact Hbb].
Qed.

(* ------------------------------------------------------------------ *)
(* The cuts                                                             *)
(* ------------------------------------------------------------------ *)

(* The facts of the record every piece may use: the premises of transport_send_control_cg_holds_stmt that are not
   callee contracts. *)
Definition sendctl_laws : Prop :=
  pc_stack_malloc (as_code B) SENDCTL_CID = transport_sigma TS___asan_stack_malloc_2 /\
  transport_cells B /\ trans_sendctl_cells B /\
  trans_ro_rd_unowned B /\ trans_rom_no_errno B /\
  AR_laws segs B /\ ameter_laws MT /\ ameter_fs_laws MT /\
  stack_malloc_progressP B /\ astack_free_law segs B /\ frame_flag_lawP segs B /\
  gx_ok segs B TG.G_HARNESS /\ gx_noerrno B TG.G_HARNESS.

(* The caller's facts (the premises of transport_send_control_cg at the entry registers regs), and what the head
   fixes before the first cut: sp1, the realigned stack pointer; pos, the slot of the class-2 frame the stack malloc
   gave; F, the frame's address. *)
Definition sendctl_fix (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z)
    (regs : bvmap 5 word) (cmd ack kp klp r : Z) (K KL f : list byte) (TF : option TI.tframe)
    (Bw Bw' : list byte) (pos sp1 F : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  YK11.getr regs 10 = w64 SENDCTL_S /\ YK11.getr regs 11 = w64 cmd /\
  YK11.getr regs 12 = w64 (bv_swrap 32 ack) /\ YK11.getr regs 13 = w64 kp /\ YK11.getr regs 14 = w64 klp /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - SENDCTL_STK /\ spZ regs <= sp0 /\
  0 <= cmd < 2 ^ 8 /\ 0 <= ack < 2 ^ 32 /\
  (kp = 0 \/
   (0 < kp /\
    decode_in_fake lyc Sc kp SENDCTL_F /\
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs) kp SENDCTL_F /\
    decode_rd_ok W memc kp SENDCTL_F /\
    decode_off_win regs SENDCTL_STK kp SENDCTL_F /\
    (forall x, kp <= x < kp + SENDCTL_F -> ~ inG TG.G_HARNESS x) /\
    length K = Z.to_nat SENDCTL_F /\ garr8 segs (mrestrict (w_H W) memc) kp (TW.zs K) /\
    klp mod 8 = 0 /\
    transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc Sc own W memc (spZ regs) klp 8 /\
    decode_rd_ok W memc klp 8 /\
    decode_off_win regs SENDCTL_STK klp 8 /\
    (forall x, klp <= x < klp + 8 -> ~ inG TG.G_HARNESS x) /\
    length KL = 8%nat /\ garr8 segs (mrestrict (w_H W) memc) klp (TW.zs KL) /\
    (kp + SENDCTL_F <= klp \/ klp + 8 <= kp))) /\
  tw_at TMAP_A (aview segs (w_H W) memc) Bw /\ TW.g_fail_next Bw <= 1 /\
  TSS.send_control_m timg_A TF Bw cmd ack = Some (Bw', (r, f)) /\
  trans_rom_view_rd W memc /\
  (TW.M_fly_on Bw <> 0 -> TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME) /\
  (forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING -> TW.Cmd_len Bw s <= DgnSpec.SPEC_CMD_MAX) /\
  count_cid SENDCTL_CID (frames Sc) + 1 < fs_frames SENDCTL_CID /\
  st_nev S + k + SENDCTL_EV <= EV_MAX /\
  sp1 = 32 * ((spZ regs - SENDCTL_FRAME) / 32) /\
  F = frame_addr lyc SENDCTL_CID pos /\
  4096 <= F /\ F mod 64 = 0 /\ F + SENDCTL_FBYTES <= alloc_ceiling /\ in_app F SENDCTL_FBYTES.

(* What every cut carries while the frame is live, at the current state (ly2, S2, W2, mem2, md2) after e events: the
   caller's G journal with the frame owned; the frame on top of the call's frames, the call's blocks, the frames
   where the call's layout puts them, the meter; what the call has kept so far, read at the memory with the out cell
   put back; the 12 saved words below the entry sp; the frame's last word, the address of its flag byte
   (astack_malloc_realizes' rdword); and, when kp <> 0, the out cell's 8 bytes present. *)
Definition sendctl_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (kp klp : Z) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((SENDCTL_CID, pos) :: own) ly2 S2 W2 mem2 md2 (k + e) /\
  0 <= e <= SENDCTL_EV /\
  frames S2 = (SENDCTL_CID, pos) :: frames Sc /\
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  ly_F ly2 = ly_F lyc /\
  mo_le MT Sc S2 0 /\
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (gover (sendctl_outs kp klp) mem2 memc)
    (spZ regs - SENDCTL_STK) (spZ regs) (sendctl_wr kp klp) /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem2) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SENDCTL_SAVED /\
  rdword (aview segs (w_H W2) mem2) (F + SENDCTL_FBYTES - 8) = Some (flag_addr lyc SENDCTL_CID pos) /\
  (kp = 0 \/ (forall i, 0 <= i < 8 -> apresent (w_H W2) mem2 (klp + i))).

(* The 60 bytes at kp and the 8 bytes at klp BEFORE the copy and the store: the caller's K and KL, and both ranges
   readable (the stack malloc and diginet_frame_build keep them: they lie in a frame of the CALL's frames). *)
Definition sendctl_incells (W2 : world segs) (mem2 : word -> option byte) (kp klp : Z) (K KL : list byte) : Prop :=
  kp = 0 \/
  (garr8 segs (mrestrict (w_H W2) mem2) kp (TW.zs K) /\ decode_rd_ok W2 mem2 kp SENDCTL_F /\
   garr8 segs (mrestrict (w_H W2) mem2) klp (TW.zs KL) /\ decode_rd_ok W2 mem2 klp 8).

(* The same cells at the return: f and its length when the build succeeded, the caller's K and KL when it failed
   (the post's X). *)
Definition sendctl_outcells (W2 : world segs) (mem2 : word -> option byte) (kp klp : Z) (K KL f : list byte) : Prop :=
  kp = 0 \/
  (garr8 segs (mrestrict (w_H W2) mem2) kp (TW.zs (match f with [] => K | _ => f end)) /\
   garr8 segs (mrestrict (w_H W2) mem2) klp
     (TW.zs (match f with [] => KL | _ => TW.put 8 (Z.of_nat (length f)) end))).

(* The registers the release reads or must hand back: sp = sp1, gp, tp, s0 = the entry sp, s1 = sp1, s2 = s9 = the
   frame, s5 = the result, s8 = the frame's shadow address, s11 (never written). *)
Definition sendctl_regs_rel (regs regs2 : bvmap 5 word) (sp1 F r : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 21 = w64 r /\ YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) /\
  YK11.getr regs2 25 = w64 F /\ YK11.getr regs2 27 = YK11.getr regs 27.
(* The send path also reads s3 = s, s7 = f and s10 = the shadow base. *)
Definition sendctl_regs_send (regs regs2 : bvmap 5 word) (sp1 F n : Z) : Prop :=
  sendctl_regs_rel regs regs2 sp1 F n /\
  YK11.getr regs2 19 = w64 SENDCTL_S /\ YK11.getr regs2 23 = w64 (F + SENDCTL_FOFF) /\
  YK11.getr regs2 26 = w64 SHADOW_OFF.
(* The keep path also reads s4 = klp and s6 = kp. *)
Definition sendctl_regs_keep (regs regs2 : bvmap 5 word) (sp1 F n kp klp : Z) : Prop :=
  sendctl_regs_send regs regs2 sp1 F n /\
  YK11.getr regs2 20 = w64 klp /\ YK11.getr regs2 22 = w64 kp.
(* At the frame-build call sp = sp1, the callee-saved registers the later cuts read are set, and the eight
   argument registers hold out, 60, dst, src, hp, body = 0, length [] = 0 and the sum mode. ra is not yet set: the
   `jal` at the cut sets it. *)
Definition sendctl_regs_fb (regs regs2 : bvmap 5 word) (sp1 F cmd kp klp mode : Z) : Prop :=
  YK11.getr regs2 2 = w64 sp1 /\ YK11.getr regs2 3 = YK11.getr regs 3 /\ YK11.getr regs2 4 = YK11.getr regs 4 /\
  YK11.getr regs2 8 = w64 (spZ regs) /\ YK11.getr regs2 9 = w64 sp1 /\ YK11.getr regs2 18 = w64 F /\
  YK11.getr regs2 19 = w64 SENDCTL_S /\ YK11.getr regs2 20 = w64 klp /\ YK11.getr regs2 21 = w64 cmd /\
  YK11.getr regs2 22 = w64 kp /\ YK11.getr regs2 23 = w64 (F + SENDCTL_FOFF) /\
  YK11.getr regs2 24 = w64 (SHADOW_OFF + F / 8) /\ YK11.getr regs2 25 = w64 F /\
  YK11.getr regs2 26 = w64 SHADOW_OFF /\ YK11.getr regs2 27 = YK11.getr regs 27 /\
  YK11.getr regs2 10 = w64 (F + SENDCTL_FOFF) /\ YK11.getr regs2 11 = w64 SENDCTL_F /\
  YK11.getr regs2 12 = w64 (SENDCTL_S + 120) /\ YK11.getr regs2 13 = w64 SENDCTL_S /\
  YK11.getr regs2 14 = w64 (F + SENDCTL_HOFF) /\ YK11.getr regs2 15 = w64 0 /\
  YK11.getr regs2 16 = w64 0 /\ YK11.getr regs2 17 = w64 mode.

(* The release cut, +0x24c: the walk's state, the post's X already established. *)
Definition sendctl_rel_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (kp klp : Z) (K KL f Bw' : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  sendctl_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\ TW.g_fail_next Bw' <= 1 /\
  sendctl_outcells W2 mem2 kp klp K KL f.

(* The send cut, +0x1d8: the world is still the entry's (nothing has written a byte of G), the 60 built bytes are at
   f and readable, the read-only bytes are the image's (io_send's premise), and the cells at kp and klp hold what
   the post says. *)
Definition sendctl_send_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (kp klp : Z) (K KL f : list byte) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  sendctl_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw /\
  trans_rom_view_rd W2 mem2 /\
  length f = Z.to_nat SENDCTL_F /\
  garr8 segs (mrestrict (w_H W2) mem2) (F + SENDCTL_FOFF) (TW.zs f) /\
  decode_rd_ok W2 mem2 (F + SENDCTL_FOFF) SENDCTL_F /\
  sendctl_outcells W2 mem2 kp klp K KL f.

(* The keep cut, +0x1b4: as the send cut, but the cells at kp and klp still hold the caller's K and KL, and the
   copy's destination and the store's cell are readable. *)
Definition sendctl_keep_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (kp klp : Z) (K KL f : list byte) (Bw : list byte) (pos F : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model) (e : Z) : Prop :=
  sendctl_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp pos F ly2 S2 W2 mem2 md2 e /\
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw /\
  trans_rom_view_rd W2 mem2 /\
  length f = Z.to_nat SENDCTL_F /\
  garr8 segs (mrestrict (w_H W2) mem2) (F + SENDCTL_FOFF) (TW.zs f) /\
  decode_rd_ok W2 mem2 (F + SENDCTL_FOFF) SENDCTL_F /\
  sendctl_incells W2 mem2 kp klp K KL.

(* The frame-build cut, +0x1a4: the stack malloc has run (the layout, the world and the event count are the call's,
   the blocks are the call's exactly), the frame's shadow bytes let f and h be read and written, oj are the bytes
   the frame holds at f, and the 12 bytes at h + 4 are the header the code stored. *)
Definition sendctl_fb_cur (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (cmd ack kp klp : Z) (K KL : list byte) (Bw : list byte) (pos sp1 F : Z)
    (S2 : astate) (mem2 : word -> option byte) (md2 : Model) (oj : list byte) : Prop :=
  sendctl_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp pos F lyc S2 W mem2 md2 0 /\
  ablocks B lyc S2 = ablocks B lyc Sc /\
  tw_at TMAP_A (aview segs (w_H W) mem2) Bw /\
  trans_rom_view_rd W mem2 /\
  length oj = Z.to_nat SENDCTL_F /\
  garr8 segs (mrestrict (w_H W) mem2) (F + SENDCTL_FOFF) (TW.zs oj) /\
  decode_rd_ok W mem2 (F + SENDCTL_FOFF) SENDCTL_F /\
  transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly S lyc S2 ((SENDCTL_CID, pos) :: own) W mem2
    (sp1 - FRAME_FB_FRAME) (F + SENDCTL_FOFF) SENDCTL_F /\
  garr8 segs (mrestrict (w_H W) mem2) (F + SENDCTL_HOFF + 4)
    (frame_fb_hdr_bytes (TW.S_host_counter Bw) ack 0 cmd 0) /\
  decode_rd_ok W mem2 (F + SENDCTL_HOFF + 4) 12 /\
  sendctl_incells W mem2 kp klp K KL.

(* ------------------------------------------------------------------ *)
(* The five pieces                                                      *)
(* ------------------------------------------------------------------ *)

(* The four callee contracts, as the holds statement gives them. Every piece takes the whole bundle, because a
   piece that falls into a later cut must supply that cut's callees too. *)
Definition sendctl_callees : Prop :=
  (forall fx' : YK11.FPState, @astack_malloc_realizes fx' rc segs B SENDCTL_CID) /\
  (forall fx' : YK11.FPState,
     @transport_diginet_frame_build_cg fx' rc B MT (transport_sigma TS_diginet_frame_build)) /\
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (transport_sigma TS___asan_memcpy)) /\
  (forall fx' : YK11.FPState, @transport_io_send_cg fx' rc B MT (TI.ti_io_send timg_A)).

Definition sendctl_rel_at : Prop :=
  sendctl_laws -> sendctl_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (cmd ack kp klp r : Z) (K KL f : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
         (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
         (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    sendctl_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
      pos sp1 F ->
    sendctl_rel_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw' pos F
      ly2 S2 W2 mem2 md2 e ->
    sendctl_regs_rel regs regs2 sp1 F r ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_REL)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_sendctl_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw' r).

Definition sendctl_send_at : Prop :=
  sendctl_laws -> sendctl_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (cmd ack kp klp r : Z) (K KL f : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
         (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
         (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    sendctl_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
      pos sp1 F ->
    sendctl_send_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw pos F
      ly2 S2 W2 mem2 md2 e ->
    sendctl_regs_send regs regs2 sp1 F SENDCTL_F ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_SEND)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_sendctl_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw' r).

Definition sendctl_keep_at : Prop :=
  sendctl_laws -> sendctl_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (cmd ack kp klp r : Z) (K KL f : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
         (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte)
         (md2 : Model) (e : Z) (regs2 : bvmap 5 word),
    sendctl_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
      pos sp1 F ->
    sendctl_keep_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw pos F
      ly2 S2 W2 mem2 md2 e ->
    sendctl_regs_keep regs regs2 sp1 F SENDCTL_F kp klp ->
    kp <> 0 ->
    SRr segs W2 (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_KEEP)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_sendctl_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw' r).

Definition sendctl_fb_at : Prop :=
  sendctl_laws -> sendctl_callees ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (cmd ack kp klp r : Z) (K KL f : list byte) (TF : option TI.tframe) (Bw Bw' : list byte)
         (pos sp1 F : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model) (oj : list byte)
         (regs2 : bvmap 5 word),
    sendctl_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cmd ack kp klp r K KL f TF Bw Bw'
      pos sp1 F ->
    sendctl_fb_cur STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs cmd ack kp klp K KL Bw pos sp1 F
      S2 mem2 md2 oj ->
    sendctl_regs_fb regs regs2 sp1 F cmd kp klp (TW.S_cfg_sum_mode Bw) ->
    SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + SENDCTL_FB)) mem2 (YK11.seg_rom segs)) md2)
      (@transport_sendctl_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs kp klp K KL f Bw' r).

(* The five piece Props; each later cut is a premise of the piece that falls into it. *)
Definition sendctl_rel_stmt : Prop := sendctl_rel_at.
Definition sendctl_send_stmt : Prop := sendctl_rel_at -> sendctl_send_at.
Definition sendctl_keep_stmt : Prop := sendctl_send_at -> sendctl_keep_at.
Definition sendctl_fb_stmt : Prop := sendctl_keep_at -> sendctl_send_at -> sendctl_rel_at -> sendctl_fb_at.
Definition sendctl_head_stmt : Prop := sendctl_fb_at -> @transport_send_control_cg_holds_stmt fx rc B MT.

(* The walk from its pieces. *)
Lemma sendctl_holds_of : sendctl_head_stmt -> sendctl_fb_stmt -> sendctl_keep_stmt -> sendctl_send_stmt ->
  sendctl_rel_stmt -> @transport_send_control_cg_holds_stmt fx rc B MT.
Proof.
intros HEAD FB KEEP SEND REL.
exact (HEAD (FB (KEEP (SEND REL)) (SEND REL) REL)).
Qed.
End cut.
