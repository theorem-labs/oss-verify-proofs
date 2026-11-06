(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc; file sha256 7a8df68f254a; donor not released), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the donors are proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (sm_effect_journal, sm_call) and .../LLVMFuzzerTestOneInput_seg_exit_tail.v (t_flag_store_pi) at origin/ossv/recipes 88154566652a: module paths, listing symbol type and this image's own numbers changed, the fake-frame class is 1 (128 bytes) instead of 0, the hypotheses model_laws and api_env are dropped and the two frame-list facts they gave are computed from lib/Reusable/YG00.v's own stack_malloc and stack_free_state, and the four-byte shadow-check lemma, the region helpers and the stack-shadow helpers are new. *)
(* Modified by Theorem Labs, 2026-10: ported to libdiginet/fuzz_frame image A: module paths, listing symbol type dfsym and this unit's own names; the side-stack-frame class stays a parameter. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's twin of this unit's lib/A/Prog/CanKit.v: module paths changed (lib/B/YB1v.v; the per-image lib/B/YCbq.v, YC5d.v, YImgTop.v and lib/B/Prog/PaJournal.v; lib/B/Prog/FrameBSyms.v, FrameBList.v, FrameBAddr.v, FrameBPa.v, FrameBImg.v and FrameBPaLib.v for the DgnFrame* listing files); the listing names are image B's (fbsym, frameb_listing, frameb_tpi, PI_frameb, PL_frameb for dfsym, dgnframe_listing, dgnframe_tpi, PI_dgnframe, PL_dgnframe). No statement changes otherwise. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/CanKit.v, with its module paths and module names changed; 219 of its 298 lines of code are new or changed and 450 lines of the source are left out. *)
(* on_ack_seg_kit: the side-stack frame kit this walk needs, for the G-form caller-journal walk of on_ack on
   fuzz_transport.asan-ubsan (lib/A/W_journalG.v ajournal_gx with XO = 0 and OUT = [], over the call kit
   lib/A/Prog/TransportGCg.v), image B's twin of lib/A/Prog/on_ack_seg_kit.v. A walk that takes a side-stack frame
   of its own holds its caller's G journal with (cid, pos) :: own while the frame is live. Nothing here names a
   program function.
   - oak_gx_stack_malloc_at: lib/B/Prog/CanKit.v can_stack_malloc_at inside the G journal (TransportGCg.v gx_open
     gives the donor journal at a start memory that agrees with the G journal's outside G; gx_pack0 packs it again
     there).
   - oak_gx_flag_store_pi: lib/B/Prog/CanKit.v can_flag_store_pi inside the G journal: a plain position-abstract run
     over image B's listing that writes bytes the journal allows and the frame's flag byte, and leaves that byte 0,
     releases the frame; its continuation takes the G journal with the frame gone.
   - oak_awr_ok_x_cons_own: the write right (W_journalG.v awr_ok_x at XO = 0) of a run region whose writable bytes are
     bytes of a frame the journal owns, or that frame's shadow bytes.
   - oak_dk_kept_step_gw, oak_dk_kept_run_gw, oak_dkg_nf_sep_gw, oak_dk_kept_own_gw: TransportGCg.v dk_kept_step_g,
     dk_kept_run_g, dkg_nf_sep and dk_kept_own_g at a CURRENT world W1 and a current layout ly2 that may differ from
     the call's (a G-form callee's transport_cg_post returns a later world and layout): a step of the walk after such
     a call keeps the caller's memory when each byte it may change is in the call's stack window, in the written
     range, in the own frame (its bytes, its shadow bytes, its flag byte) or in G. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanKit DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI16.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ------------------------------------------------------------------ *)
(* 1. The class-cid stack malloc in the G journal                      *)
(* ------------------------------------------------------------------ *)

Section sm.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis stack_malloc_progress : stack_malloc_progressP B.

(* can_stack_malloc_at's post with the G journal in place of the donor journal; the call's acall_kept (whose image
   clause keeps G when G is outside the owned statics and errno: TransportGCg.v gx_kept_of_acall_kept) is unchanged. *)
Lemma oak_gx_stack_malloc_at : forall cid, astack_malloc_realizes segs B cid -> 0 <= cid <= 10 ->
forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\
st_nev S2 = st_nev Sc /\ (exists f, S2 = set_fs f Sc) /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False)).
Proof.
intros cid ASM Hcid G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
destruct (gx_open segs B G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (can_stack_malloc_at (SK := SK) segs B LAWS segs_low stack_malloc_progress cid ASM Hcid W regsT memT STK sp0
    FP ly S W0 memS md own lyc Sc mdc k o raw HJi Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & Hc & HJ2 & Hrest).
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos. split; [exact Hc|].
split; [|exact Hrest].
exact (gx_pack0 segs B G STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k memS HSTK HJ2 Hag).
Qed.
End sm.

(* ------------------------------------------------------------------ *)
(* 2. The frame-flag store in the G journal                            *)
(* ------------------------------------------------------------------ *)

Section fp.
Local Abbreviation SEGS := (@pa_segs _ transportb_listing PI_transportb).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

(* can_flag_store_pi with the G journal before the run and in its continuation. *)
Lemma oak_gx_flag_store_pi : forall G W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  sym_runN_pi transportb_tpi n ss = (ss', st) -> can_plain_stop st ->
  ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
  0 <= cid ->
  (forall a, in_wrange E (ss_mem ss) a ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
  (forall msr, st_ok_pi SEGS VAL E ss' msr -> mbyte SEGS (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
  (forall ms' mat',
     st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
     ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms')
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros G W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q HE HS Hrun Hst HJ Hcid Hwr Hflag0 Hk.
destruct (gx_open SEGS B G STK sp0 FP ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k HJ)
  as (memS & HJi & Hag & HSTK).
apply (can_flag_store_pi (SK := SK) B LAWS ASF FFL W n E ss ss' st ms STK sp0 FP ly S W0 memS md own' lyc Sc mdc k
  cid pos Q HE HS Hrun Hst HJi Hcid Hwr Hflag0).
intros ms' mat' HS' HJ' F1 F2 F3.
apply (Hk ms' mat' HS'); [|exact F1 | exact F2 | exact F3].
exact (gx_pack0 SEGS B G STK sp0 FP ly S W0 mem md own' lyc (stack_free_state cid pos Sc) W (ms_mem ms')
  (with_vm_backing (m_vm_lazy mdc) mat' mdc) k memS HSTK HJ' Hag).
Qed.
End fp.

(* ------------------------------------------------------------------ *)
(* 3. The write right of own-frame bytes                               *)
(* ------------------------------------------------------------------ *)

(* A region whose writable bytes are bytes of a frame the journal owns, or that frame's shadow bytes (YCbq.v awr_byte's
   in_frames case), in a G journal with no out window. *)
Lemma oak_awr_ok_x_cons_own : forall E r rs G OUT STK sp0 FP bl0 blc ly own cid pos,
  In (cid, pos) own ->
  (forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r ->
     in_zr a (frame_addr ly cid pos, fs_frame_bytes cid) \/
     in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  awr_ok_x E rs G 0 OUT STK sp0 FP bl0 blc ly own -> awr_ok_x E (r :: rs) G 0 OUT STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs G OUT STK sp0 FP bl0 blc ly own cid pos Hin Hr H.
apply awr_ok_x_cons; [|exact H].
intros a Ha. left. split; [|lia].
unfold awr_byte. right; right; right. unfold in_frames. exists cid, pos. split; [exact Hin | exact (Hr a Ha)].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. acall_kept_g carried at a later world and layout                 *)
(* ------------------------------------------------------------------ *)

Section kw.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* TransportGCg.v dk_kept_step_g with the current memory read at a world W1 (the call's world is W). *)
Lemma oak_dk_kept_step_gw : forall G lyc Sc W memc mdc W1 memX memY slo shi (Eo Zs : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
  (forall a, Zs a -> in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     Zs a -> Eo a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros G lyc Sc W memc mdc W1 memX memY slo shi Eo Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
  rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi HnG Hno He. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [apply K3; assumption | lia | intros HZ; exact (HZi a HZ Hi HnG Hno He)].
- intros cid pos a Hin Hr Hn. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* TransportGCg.v dk_kept_run_g with the current memory read at a world W1. *)
Lemma oak_dk_kept_run_gw : forall G lyc Sc W memc mdc W1 memX memY slo shi (Eo NF Zs : Z -> Prop),
  gx_ok segs B G ->
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  dkg_in_frames lyc Sc Eo ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
  (forall a, NF a -> in_img segs a -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     NF a -> False) ->
  (forall a, NF a -> a < alloc_ceiling) ->
  (forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ NF a \/ inG G a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros G lyc Sc W memc mdc W1 memX memY slo shi Eo NF Zs HG HAR Hce Hshi HEf HNb HNi HNf HNc HZ KP Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (oak_dk_kept_step_gw G lyc Sc W memc mdc W1 memX memY slo shi Eo Zs HAR KP Hkp Hgr).
- intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Ho | [Hn | Hg]]]; [exact Hw | | pose proof (HNc a Hn); lia |].
  + destruct (HEf a Ho) as (c0 & p0 & Hin0 & Hr0).
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HAR Hin0) as (_ & Fce & _). lia.
  + pose proof (inG_low segs B segs_low G a HG Hg). unfold kLowMemEnd in *. lia.
- intros b m i Hb Hi Ha. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  destruct (HZ _ Ha) as [Hw | [Ho | [Hn | Hg]]]; [lia | exact Ho | exfalso; exact (HNb b m i Hb Hi Hn) |].
  exfalso. destruct (HG _ Hg) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) Hi').
- intros a Ha Hi HnG _ _. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct (HZ a Ha) as [Hw | [Ho | [Hn | Hg]]]; [lia | | exact (HNi a Hn Hi) | exact (HnG Hg)].
  destruct (HEf a Ho) as (c0 & p0 & Hin0 & Hr0).
  exact (frm_img segs B LAWS lyc Sc W memc mdc c0 p0 a HAR Hin0 Hr0 Hi).
- intros cid pos a Hin Hr Ha. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4096 & Gce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct (HZ a Ha) as [Hw | [Ho | [Hn | Hg]]].
  + exfalso. destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
  + exact Ho.
  + exfalso. exact (HNf cid pos a Hin Hr Hn).
  + exfalso. destruct (HG _ Hg) as [Hi _]. pose proof (inG_low segs B segs_low G a HG Hg) as Hl.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    * exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr Hi).
    * pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* TransportGCg.v dkg_nf_sep at a current state (ly2, S2) whose layout puts the frames where the call's layout lyc
   puts them (the same ly_F) and whose blocks contain the call's: the own frame of class cid (its bytes, its shadow
   bytes, its flag byte) is apart from the call's blocks, the image, the call's frames and their shadow bytes, and
   lies below the allocation ceiling. *)
Lemma oak_dkg_nf_sep_gw : forall lyc Sc ly2 S2 W2 mem2 md2 cid fpos F FL,
  AR segs B ly2 S2 W2 mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos ->
  frame_flag_lawP segs B ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> dkg_nf cid F FL (b + i) -> False) /\
  (forall a, dkg_nf cid F FL a -> in_img segs a -> False) /\
  (forall c pos a, In (c, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (c, pos)) \/ in_zr a (shadow_addr (frame_addr lyc c pos), fs_frame_bytes c / 8)) ->
     dkg_nf cid F FL a -> False) /\
  (forall a, dkg_nf cid F FL a -> a < alloc_ceiling).
Proof.
intros lyc Sc ly2 S2 W2 mem2 md2 cid fpos F FL HAR2 Hfrs Hbl ELF EF EFL FFL. unfold dkg_nf.
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr lyc c p) by (intros c p; unfold frame_addr; rewrite ELF; reflexivity).
assert (Efl : forall c p, flag_addr ly2 c p = flag_addr lyc c p) by (intros c p; unfold flag_addr; rewrite ELF; reflexivity).
rewrite <- Efa in EF. rewrite <- Efl in EFL. subst F FL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds segs B LAWS _ _ _ _ _ cid fpos HAR2 Hfin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ cid fpos HAR2 Hfin) as (_ & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
destruct (dkg_frame_al64 segs B _ _ _ _ _ cid fpos HAR2 Hfin) as (HF64 & HFs64 & HFs).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ cid fpos a HAR2 Hfin Ha) as HFimg.
set (F := frame_addr ly2 cid fpos) in *. set (FL := flag_addr ly2 cid fpos) in *.
set (fs := fs_frame_bytes cid) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod fs 64 ltac:(lia)) as DS.
rewrite HF64, Z.add_0_r in DF. rewrite HFs64, Z.add_0_r in DS.
assert (EF8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (ES8 : fs / 8 = 8 * (fs / 64)) by (rewrite DS at 1; replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : 0 <= F / 64) by (apply Z.div_pos; lia).
assert (HFS : SHADOW_OFF + F / 8 + fs / 8 <= kHighShadowEnd /\ kLowShadowBeg < SHADOW_OFF + F / 8).
{ unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg. lia. }
unfold kHighShadowEnd, kLowShadowBeg, SHADOW_OFF in HFS.
split; [|split; [|split]].
- intros b m i Hb Hi Hn. apply Hbl in Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & Hb4096 & Hbce & Hbapp & Hbown & _).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ b m cid fpos HAR2 Hb Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F fs in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia |].
  exact (proj2 (Hbown (b + i) ltac:(lia)) ltac:(rewrite Hn; exact HFLown)).
- intros a Hn Hi. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct Hn as [Hn|[Hn|Hn]]; [exact (HFimg a Hn Hi) | unfold SHADOW_OFF in Hn; lia | subst a; exact (HFLimg Hi)].
- intros c pos a Hin Hr Hn. rewrite <- Efa in Hr. unfold frame_rng in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr.
  assert (Hin2 : In (c, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ c pos HAR2 Hin2) as (HGal & HGapp & HGpres & HGSpres).
  destruct (dkg_frame_al64 segs B _ _ _ _ _ c pos HAR2 Hin2) as (HG64 & HGs64 & HGs).
  pose proof (dkg_own_sep segs B LAWS _ _ _ _ _ cid fpos Sc c pos HAR2 Hfrs Hin) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F fs in Hd.
  set (G := frame_addr ly2 c pos) in *. set (gs := fs_frame_bytes c) in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
  destruct Hn as [Hn|[Hn|Hn]].
  + destruct Hr as [Hr|Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end G gs ltac:(lia)) as Hse. unfold shadow_addr in Hse, Hr. fold G in Hr.
    assert ((G + gs) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). assert (0 <= G / 8) by (apply Z.div_pos; lia).
    change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF in Hr, Hse. lia.
  + destruct Hr as [Hr|Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr; [unfold SHADOW_OFF in Hn; lia|].
    unfold shadow_addr in Hr. fold G in Hr.
    pose proof (Z.div_mod G 64 ltac:(lia)) as DG. pose proof (Z.div_mod gs 64 ltac:(lia)) as DGS.
    rewrite HG64, Z.add_0_r in DG. rewrite HGs64, Z.add_0_r in DGS.
    assert (EG : G / 8 = 8 * (G / 64)) by (rewrite DG at 1; replace (64 * (G / 64)) with ((8 * (G / 64)) * 8) by lia; apply Z.div_mul; lia).
    assert (EGS : gs / 8 = 8 * (gs / 64)) by (rewrite DGS at 1; replace (64 * (gs / 64)) with ((8 * (gs / 64)) * 8) by lia; apply Z.div_mul; lia).
    unfold SHADOW_OFF in Hn, Hr. lia.
  + subst a. destruct Hr as [Hr|Hr]; unfold in_zr in Hr; cbn [fst snd] in Hr.
    * exact (proj2 (HGpres FL ltac:(fold G gs; lia)) HFLown).
    * unfold shadow_addr in Hr. fold G in Hr.
      exact (proj2 (HGSpres (FL - shadow_addr G) ltac:(unfold shadow_addr; fold G; lia))
        ltac:(replace (shadow_addr G + (FL - shadow_addr G)) with FL by lia; exact HFLown)).
- intros a [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | lia].
Qed.

(* TransportGCg.v dk_kept_own_g at a current world W1 and state (ly2, S2): one step of the walk keeps the caller's
   memory when each byte it may change is in the call's stack window, in the written range Eo, in the own frame of
   class cid, or in G. *)
Lemma oak_dk_kept_own_gw : forall G lyc Sc ly2 S2 W memc mdc W1 mem2 md2 memX memY slo shi cid fpos F FL (Eo Zs : Z -> Prop),
  gx_ok segs B G ->
  AR segs B lyc Sc W memc mdc -> AR segs B ly2 S2 W1 mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  ly_F ly2 = ly_F lyc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos -> frame_flag_lawP segs B ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  dkg_in_frames lyc Sc Eo ->
  (forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ dkg_nf cid F FL a \/ inG G a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W1) memY a = aview segs (w_H W1) memX a) ->
  (forall a, apresent (w_H W1) memX a -> apresent (w_H W1) memY a) ->
  acall_kept_g segs B G lyc Sc W memc W1 memY slo shi Eo.
Proof.
intros G lyc Sc ly2 S2 W memc mdc W1 mem2 md2 memX memY slo shi cid fpos F FL Eo Zs HG HAR HAR2 Hfrs Hbl ELF EF EFL FFL
  Hce Hshi HEf HZ KP Hkp Hgr.
destruct (oak_dkg_nf_sep_gw lyc Sc ly2 S2 W1 mem2 md2 cid fpos F FL HAR2 Hfrs Hbl ELF EF EFL FFL) as (N1 & N2 & N3 & N4).
exact (oak_dk_kept_run_gw G lyc Sc W memc mdc W1 memX memY slo shi Eo (dkg_nf cid F FL) Zs HG HAR Hce Hshi HEf N1 N2 N3 N4
  HZ KP Hkp Hgr).
Qed.
End kw.
End a.
