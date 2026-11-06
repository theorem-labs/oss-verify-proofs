(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths and module names changed; 669 of its 691 lines of code are new or changed and 308 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapSourceNextExit.v, with its module paths and module names changed; 518 of its 610 lines of code are new or changed and 599 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: what one segment
   of the header phase's run keeps. The phase itself is lib/B/Prog/PcapSourceNextHdrB.v; these lemmas are here,
   in a file with no Admitted and no walk, because the neighbouring phases (a Theorem Labs lane's lib/B/Prog/
   PcapSourceNextSkip.v) land their own runs with them.

   The run of a phase of this call writes at most three windows of the caller's memory: the spill slot NS_SEC
   of this call's machine frame, the struct's orig field [ps + 12, ps + 24), and the two shadow bytes 4 and 5
   of this call's own frame (the bytes that say whether `ph` is in scope). Everything else is kept, and that is
   what nx_body (hb_body_keep), nx_kept (hb_kept_step) and the caller-facing facts of nx_mid (hb_mid_keep) need.

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; capstone 5 disassembly of its unstripped twin). *)
(* Modified by Theorem Labs, 2026-10: the uses of PcapSourceNextFitB.v's vm_frame / asource_at_frame (deleted there) name
   lib/A/Prog/PcapSourceCloseSpec.v's vm_frame_segs / asource_at_frame_segs; PcapSourceNextFitB is no longer Required. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI01 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import RdU32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs PcapSourceNextHdrBDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextSkipDefs PcapSourceNextFitADefs.
(* The segs-generic frame lemmas vm_frame_segs / asource_at_frame_segs of lib/A/Prog/PcapSourceCloseSpec.v (a Theorem Labs lane,
   image-free), Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.

(* ---------------------------------------------------------------------------------------------- *)
(* The geometry of the frame, the struct and the stack                                              *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hb_geo : forall cx fp k2 ly3 S3 W3 mem3 md3,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) /\
  4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  in_app (nF cx fp) 64 /\ off_img (nF cx fp) 64 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8 /\
  (forall a, nF cx fp <= a < nF cx fp + 64 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  (forall o, 0 <= o < 8 -> apresent (w_H W3) mem3 (nSH cx fp + o) /\ ~ aowned B ly3 S3 (nSH cx fp + o)) /\
  4096 <= n_ps cx /\ n_ps cx + PS_LEN <= alloc_ceiling /\ in_app (n_ps cx) PS_LEN /\
  off_img (n_ps cx) PS_LEN /\ n_ps cx mod 8 = 0 /\
  (n_ps cx + PS_LEN <= nF cx fp \/ nF cx fp + 64 <= n_ps cx) /\
  alloc_ceiling + NX_STK_B <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47 /\
  spZ (n_regs cx) - 272 <= n_sp1 cx <= spZ (n_regs cx) - 256 /\ n_sp1 cx mod 32 = 0 /\
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK_B /\ spZ (n_regs cx) <= n_sp0 cx /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 HB HJ3 Hfr3.
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ &
  Hps8 & Hps0 & Hpshi & Hamr & Hown & Hfa1 & Hfa2 & _).
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr (n_lyc cx) c q).
{ intros c q. unfold frame_addr.
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _). pose proof Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  rewrite EF3, EF0. reflexivity. }
assert (Hfin3 : In (NX_CID, fp) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (_ & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (HF64 & _ & _).
pose proof (frm_off_imgP B _ _ _ _ _ NX_CID fp HAR3 Hfin3) as HFimg.
rewrite EFA in HFapp, HFpres, HFSpres, HF4096, HFceil, HF64, HFimg.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in *.
change (fs_frame_bytes NX_CID) with 64 in *.
change (64 / 8) with 8 in HFSpres.
(* the caller's frame that holds the struct *)
assert (HinC : In (n_cid cx, n_pos cx) (frames (n_Sc cx)))
  by (rewrite Hfrs0; apply in_or_app; left; exact Hown).
assert (HinC3 : In (n_cid cx, n_pos cx) (frames S3)) by (rewrite Hfr3; right; exact HinC).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ (n_cid cx) (n_pos cx) HAR3 HinC3) as (HC4096 & HCceil & HCapp).
pose proof (frm_off_imgP B _ _ _ _ _ (n_cid cx) (n_pos cx) HAR3 HinC3) as HCimg.
rewrite EFA in HC4096, HCceil, HCapp, HCimg.
(* the struct's frame and this call's frame are disjoint *)
assert (HdF : n_ps cx + PS_LEN <= nF cx fp \/ nF cx fp + 64 <= n_ps cx).
{ apply in_split in HinC as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (NX_CID, fp) (n_cid cx, n_pos cx) [] l1 l2 HAR3
    ltac:(rewrite Hfr3, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !EFA in Hd.
  change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Hd.
  change (fs_frame_bytes NX_CID) with 64 in Hd. unfold PS_LEN in *. lia. }
assert (HNS : NX_STK_B = 8464) by reflexivity.
pose proof (NX_STK_B_frame (spZ (n_regs cx)) Hal16) as (Hsp1b & Hsp1m).
change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1b, Hsp1m. unfold NX_MFRAME in Hsp1b.
unfold in_app in HCapp. unfold off_img in HCimg. unfold PS_LEN in *.
split; [exact EFA|]. split; [lia|]. split; [lia|]. split; [exact HF64|].
split; [exact HFapp|]. split; [exact HFimg|].
split; [reflexivity|].
split; [exact HFpres|].
split; [intros o Ho; exact (HFSpres o Ho)|].
split; [lia|]. split; [lia|]. split; [unfold in_app, PS_LEN; lia|].
split; [unfold off_img, PS_LEN; lia|]. split; [exact Hps8|].
split; [unfold PS_LEN; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hsp1m|].
split; [lia|]. split; [lia|]. exact C1.
Qed.

(* ---------------------------------------------------------------------------------------------- *)

(* The slot NS_SEC and the two shadow bytes of `ph` are none of the caller's bytes: the slot is inside this
   call's stack window, and the shadow bytes are in the shadow band, off the image, in no block of the
   caller and in no frame of the caller nor in one of their shadows (the own frame is disjoint from every
   caller frame, and the shadow map is injective on 64-byte granules). *)
Lemma hb_out : forall cx fp k2 ly3 S3 W3 mem3 md3 a,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (n_sp1 cx + 56 <= a < n_sp1 cx + 64 \/ nSH cx fp + 4 <= a < nSH cx fp + 6) ->
  ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> ~ (b <= a < b + req_size m)) /\
  (forall c p, In (c, p) (frames (n_Sc cx)) ->
     ~ in_zr a (frame_rng (n_lyc cx) (c, p)) /\
     ~ in_zr a (shadow_addr (frame_addr (n_lyc cx) c p), fs_frame_bytes c / 8)) /\
  (alloc_ceiling <= a -> spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx)).
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 a HB HJ3 Hfr3 Ha.
destruct (hb_geo cx fp k2 ly3 S3 W3 mem3 md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & _ & _ & _ & _ & _ & _ & _ & _ &
   Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
pose proof HB as (HJ0 & _). pose proof (proj1 HJ0) as HAR0.
pose proof HJ3 as (HAR3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HSHO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
assert (HdivF : 0 <= nF cx fp / 8 <= 17592184995840).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
(* the shadow window lies in the shadow band, below the heap ceiling and above the image *)
assert (HSHband : nSH cx fp + 4 <= a < nSH cx fp + 6 ->
                  2147450880 <= a < 17594333495296 /\ a < alloc_ceiling).
{ intros Hw. rewrite ESH in Hw. lia. }
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
assert (HIMG : forall x, in_img SEGS x -> 0x10000 <= x < (symaddr ImgPages.AsanUbsan.top))
  by (intros x Hx; rewrite <- HIE; exact (pa_img_range x Hx)).
assert (HSLOT : forall x, n_sp1 cx + 56 <= x < n_sp1 cx + 64 -> alloc_ceiling + 8248 <= x)
  by (intros x Hx; lia).
split.
{ intros Hi. pose proof (HIMG a Hi) as Hr. destruct Ha as [Hw|Hw].
  - pose proof (HSLOT a Hw). lia.
  - destruct (HSHband Hw) as (Hb & _). lia. }
split.
{ intros b m Hb Hr.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 ltac:(exact Hb)) as (_ & Hb4096 & Hbceil & Hbapp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Ha as [Hw|Hw]; [lia|]. destruct (HSHband Hw) as (Hband & Hlt). lia. }
split.
{ intros c p Hcq.
  assert (Hcq3 : In (c, p) (frames S3)) by (rewrite Hfr3; right; exact Hcq).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR3 Hcq3) as (HG4096 & HGceil & HGapp).
  destruct (frame_al64 SEGS B _ _ _ _ _ c p HAR3 Hcq3) as (HG64 & HGb64 & HGb).
  rewrite EFA in HG4096, HGceil, HGapp, HG64.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
  assert (EGd : frame_addr (n_lyc cx) c p = 64 * (frame_addr (n_lyc cx) c p / 64))
    by (pose proof (Z.div_mod (frame_addr (n_lyc cx) c p) 64 ltac:(lia)); lia).
  assert (EG8 : frame_addr (n_lyc cx) c p / 8 = 8 * (frame_addr (n_lyc cx) c p / 64))
    by (rewrite EGd at 1; replace (64 * (frame_addr (n_lyc cx) c p / 64))
          with (8 * (frame_addr (n_lyc cx) c p / 64) * 8) by lia; apply Z.div_mul; lia).
  assert (Enb : fs_frame_bytes c = 64 * (fs_frame_bytes c / 64))
    by (pose proof (Z.div_mod (fs_frame_bytes c) 64 ltac:(lia)); lia).
  assert (Enb8 : fs_frame_bytes c / 8 = 8 * (fs_frame_bytes c / 64))
    by (rewrite Enb at 1; replace (64 * (fs_frame_bytes c / 64))
          with (8 * (fs_frame_bytes c / 64) * 8) by lia; apply Z.div_mul; lia).
  assert (EFd : nF cx fp = 64 * (nF cx fp / 64))
    by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
  assert (EF8 : nF cx fp / 8 = 8 * (nF cx fp / 64))
    by (rewrite EFd at 1; replace (64 * (nF cx fp / 64)) with (8 * (nF cx fp / 64) * 8) by lia;
        apply Z.div_mul; lia).
  (* the two frames are disjoint *)
  assert (HdG : nF cx fp + 64 <= frame_addr (n_lyc cx) c p \/
                frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp).
  { apply in_split in Hcq as (l1 & l2 & El).
    pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (NX_CID, fp) (c, p) [] l1 l2 HAR3
      ltac:(rewrite Hfr3, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !EFA in Hd.
    change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Hd.
    change (fs_frame_bytes NX_CID) with 64 in Hd. lia. }
  unfold frame_rng, in_zr, shadow_addr. cbn [fst snd].
  rewrite ESH in Ha. rewrite EG8, Enb8, EF8 in *.
  split; intros Hr; destruct Ha as [Hw|Hw]; lia. }
intros Hceil. destruct Ha as [Hw|Hw]; [lia|]. rewrite ESH in Hw. lia.
Qed.

(* nx_kept across one segment of the run: the three windows are the slot NS_SEC (in the stack window),
   ps->orig (a byte of nx_E) and the shadow of `ph` (none of the caller's bytes, hb_out). The X form also
   leaves out [sp1 - 16, sp1), the frame of a callee (rd_u32) that ran inside the segment: that frame is in
   the stack window, so nx_kept never reads it. *)
Lemma hb_kept_stepX : forall cx fp k2 ly3 S3 W3 mem3 md3 (mem' : word -> option byte),
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
     aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W3) mem' a) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 mem3 (spZ (n_regs cx)) (nx_E cx) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 mem' (spZ (n_regs cx)) (nx_E cx).
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 mem' HB HJ3 Hfr3 UNCH HSTK (K1 & K2 & K3 & K4 & K5 & K6).
destruct (hb_geo cx fp k2 ly3 S3 W3 mem3 md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & _ & _ & HPS4096 & HPSceil & HPSapp & HPSimg &
   HPS8 & HdPF & Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
pose proof (hb_out cx fp k2 ly3 S3 W3 mem3 md3) as OUT.
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HPL : PS_LEN = 24) by reflexivity.
assert (HOLO : PS_OL_OFF = 12) by reflexivity.
(* the struct's orig bytes are bytes the call may write *)
assert (HPSE : forall a, n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN -> nx_E cx a)
  by (intros a Ha; unfold nx_E, nx_wrset; left; lia).
assert (HSLOTin : forall a, n_sp1 cx + 56 <= a < n_sp1 cx + 64 ->
                  spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx)) by (intros a Ha; lia).
split.
{ intros a Ha Hs HE. rewrite <- (K1 a Ha Hs HE). apply UNCH; [lia| | | |].
  - intros Hw. exact (Hs (HSLOTin a Hw)).
  - intros Hw. exact (HE (HPSE a Hw)).
  - intros Hw. destruct (OUT a HB HJ3 Hfr3 ltac:(right; exact Hw)) as (_ & _ & _ & Hc). lia.
  - intros Hw. apply Hs. clear - Hw Hsp1b HNSB. lia. }
split.
{ intros b m i Hb Hi HE. rewrite <- (K2 b m i Hb Hi HE).
  pose proof (proj1 (proj1 (conj HB I))) as HJ0.
  apply UNCH.
  - pose proof HB as (HJ0' & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m (proj1 HJ0') Hb) as (_ & Hb4096 & Hbceil & _).
    pose proof (req_size_pos m) as Hrq. lia.
  - intros Hw. destruct (OUT (b + i) HB HJ3 Hfr3 ltac:(left; exact Hw)) as (_ & Hnb & _).
    exact (Hnb b m Hb ltac:(lia)).
  - intros Hw. exact (HE (HPSE (b + i) Hw)).
  - intros Hw. destruct (OUT (b + i) HB HJ3 Hfr3 ltac:(right; exact Hw)) as (_ & Hnb & _).
    exact (Hnb b m Hb ltac:(lia)).
  - pose proof HB as (HJ0' & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m (proj1 HJ0') Hb) as (_ & Hb4096 & Hbceil & _).
    pose proof (req_size_pos m) as Hrq. intros Hw. lia. }
split.
{ intros a Hi Hno He. rewrite <- (K3 a Hi Hno He).
  pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  pose proof (pa_img_range a Hi) as Hr.
  assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
  apply UNCH; [lia| | | |].
  - intros Hw. destruct (OUT a HB HJ3 Hfr3 ltac:(left; exact Hw)) as (Hni & _). exact (Hni Hi).
  - intros Hw. unfold off_img, PS_LEN, PS_OL_OFF in HPSimg. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HPSimg.
    rewrite HIE in Hr. lia.
  - intros Hw. destruct (OUT a HB HJ3 Hfr3 ltac:(right; exact Hw)) as (Hni & _). exact (Hni Hi).
  - intros Hw. rewrite HIE in Hr. lia. }
split.
{ intros c p a Hcq Hr HE. rewrite <- (K4 c p a Hcq Hr HE).
  pose proof HB as (HJ0' & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p (proj1 HJ0') Hcq) as (HG4096 & HGceil & HGapp).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p)
    ltac:(pose proof asan_consts as (Q1 & Q2 & Q3 & Q4 & Q5); lia)) as Hs1.
  pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p + fs_frame_bytes c)
    ltac:(pose proof asan_consts as (Q1 & Q2 & Q3 & Q4 & Q5); lia)) as Hs2.
  pose proof (shadow_range_end (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) Hnn) as Hse.
  assert (Harange : 0 <= a < 2 ^ 64).
  { unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof asan_consts as (Q1 & Q2 & Q3 & Q4 & Q5). destruct Hr; lia. }
  apply UNCH; [exact Harange| | | |].
  - intros Hw. destruct (OUT a HB HJ3 Hfr3 ltac:(left; exact Hw)) as (_ & _ & Hnf & _).
    destruct (Hnf c p Hcq) as [H1 H2]. destruct Hr as [Hr|Hr]; [exact (H1 Hr) | exact (H2 Hr)].
  - intros Hw. exact (HE (HPSE a Hw)).
  - intros Hw. destruct (OUT a HB HJ3 Hfr3 ltac:(right; exact Hw)) as (_ & _ & Hnf & _).
    destruct (Hnf c p Hcq) as [H1 H2]. destruct Hr as [Hr|Hr]; [exact (H1 Hr) | exact (H2 Hr)].
  - intros Hw. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof asan_consts as (Q1 & Q2 & Q3 & Q4 & Q5). destruct Hr; lia. }
(* clause 5, presence above the heap ceiling: such a byte is no image byte (so equal views give presence,
   apresent_transfer) and lies in none of the four windows outside the stack window *)
split; [|intros a Ha; apply HSTK; exact Ha].
intros a Ha Hs Hp. pose proof (K5 a Ha Hs Hp) as Hp3.
assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
apply (apresent_transfer SEGS (w_H W3) (w_H W3) mem3 mem' a ltac:(lia)); [| |exact Hp3].
- intros Hi. pose proof (pa_img_range a Hi) as Hr. lia.
- apply UNCH; [lia | intros Hw; apply Hs; lia | lia | | intros Hw; apply Hs; lia].
  intros Hw. destruct (OUT a HB HJ3 Hfr3 ltac:(right; exact Hw)) as (_ & _ & _ & Hc).
  apply Hs. apply Hc. lia.
Qed.

(* The three-window form a Theorem Labs lane's walk applies. Its presence premise is no longer needed (hb_kept_stepX
   derives presence above the heap ceiling from the views); it stays so the existing callers apply
   unchanged. *)
Lemma hb_kept_step : forall cx fp k2 ly3 S3 W3 mem3 md3 (mem' : word -> option byte),
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
     aview SEGS (w_H W3) mem' a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem' a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W3) mem' a) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 mem3 (spZ (n_regs cx)) (nx_E cx) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 mem' (spZ (n_regs cx)) (nx_E cx).
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 mem' HB HJ3 Hfr3 UNCH _ HSTK HK.
exact (hb_kept_stepX cx fp k2 ly3 S3 W3 mem3 md3 mem' HB HJ3 Hfr3
         (fun a Ha N1 N2 N3 _ => UNCH a Ha N1 N2 N3) HSTK HK).
Qed.

(* nx_body across one segment: every word it names lies outside the three windows, except the two shadow
   bytes of `ph`, whose new values the caller gives. The X form also leaves out a callee's frame
   [sp1 - 16, sp1): no word of nx_body is there. *)
Lemma hb_body_keepX : forall cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 pc0 pc sh,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_body cx fp pc0 W ms NSH_ph ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_pc_val ms' = w64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some (nth 4 sh 0) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some (nth 5 sh 0) ->
  (forall i, (i < 8)%nat -> i <> 4%nat -> i <> 5%nat -> nth i sh 0 = nth i NSH_ph 0) ->
  length sh = NX_NSH ->
  nx_body cx fp pc W ms' sh.
Proof.
intros cx fp k2 ly3 S3 W ms ms' md3 pc0 pc sh HB HJ3 Hfr3 HBODY UNCH
  Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 Hsh4 Hsh5 Hshrest Hshlen.
destruct HBODY as ((_ & _ & _ & _ & _ & _ & _ & HSAVED & HHDR & HFLW & HSHADOW & Hphlen & _ & HFK) & HSLOTS).
destruct (hb_geo cx fp k2 ly3 S3 W (ms_mem ms) md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & _ & _ & HPS4096 & HPSceil & HPSapp & HPSimg &
   HPS8 & HdPF & Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HPL : PS_LEN = 24) by reflexivity.
assert (HOLO : PS_OL_OFF = 12) by reflexivity.
assert (HdivF : 0 <= nF cx fp / 8 <= 17592184995840).
{ split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
assert (HSHb : 2147450880 <= nSH cx fp /\ nSH cx fp + 8 <= 17594333495296).
{ rewrite ESH. unfold SHADOW_OFF. lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HPSapp, HFapp.
(* a word outside the three windows is kept *)
assert (TR : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 ->
     ~ (n_sp1 cx + 56 <= x < n_sp1 cx + 64) /\ ~ (n_ps cx + PS_OL_OFF <= x < n_ps cx + PS_LEN) /\
     ~ (nSH cx fp + 4 <= x < nSH cx fp + 6) /\ ~ (n_sp1 cx - 16 <= x < n_sp1 cx)) ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) a = Some v ->
  rdword (aview SEGS (w_H W) (ms_mem ms')) a = Some v).
{ intros a v Ha0 Ha1 Hap Hv.
  rewrite (rdword_ext (aview SEGS (w_H W) (ms_mem ms)) (aview SEGS (w_H W) (ms_mem ms')) a);
  [exact Hv|]. intros kk Hkk. destruct (Hap (a + kk) ltac:(lia)) as (X1 & X2 & X3 & X4).
  apply UNCH; [lia | exact X1 | exact X2 | exact X3 | exact X4]. }
assert (TRsp : forall o v, -104 <= o -> o + 8 <= 0 ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (spZ (n_regs cx) + o) = Some v ->
  rdword (aview SEGS (w_H W) (ms_mem ms')) (spZ (n_regs cx) + o) = Some v).
{ intros o v Ho0 Ho1 Hv. apply TR; [lia | lia | intros x Hx; split; [lia | split; [lia | split; lia]] | exact Hv]. }
assert (TRsl : forall o v, 0 <= o -> o + 8 <= 128 -> (o + 8 <= 56 \/ 64 <= o) ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (n_sp1 cx + o) = Some v ->
  rdword (aview SEGS (w_H W) (ms_mem ms')) (n_sp1 cx + o) = Some v).
{ intros o v Ho0 Ho1 Hod Hv.
  apply TR; [lia | lia | intros x Hx; split; [lia | split; [lia | split; lia]] | exact Hv]. }
assert (TRF : forall o v, 0 <= o -> o + 8 <= 64 ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (nF cx fp + o) = Some v ->
  rdword (aview SEGS (w_H W) (ms_mem ms')) (nF cx fp + o) = Some v).
{ intros o v Ho0 Ho1 Hv. apply TR; [lia | lia | intros x Hx; split; [lia | split; [lia | split; lia]] | exact Hv]. }
split.
- split; [exact Hpc|]. split; [exact Hresv|]. split; [exact Hsvc|]. split; [exact Hrom|].
  split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact HREGS|].
  split.
  { destruct HSAVED as (Hra & Hsv). split.
    - replace (spZ (n_regs cx) - 8) with (spZ (n_regs cx) + (-8)) by lia.
      apply TRsp; [lia | lia|]. replace (spZ (n_regs cx) + (-8)) with (spZ (n_regs cx) - 8) by lia.
      exact Hra.
    - intros j Hj. replace (spZ (n_regs cx) - 16 - 8 * j) with (spZ (n_regs cx) + (- 16 - 8 * j)) by lia.
      apply TRsp; [lia | lia|].
      replace (spZ (n_regs cx) + (- 16 - 8 * j)) with (spZ (n_regs cx) - 16 - 8 * j) by lia.
      exact (Hsv j Hj). }
  split.
  { destruct HHDR as (H0 & H8 & H16). split; [|split].
    - replace (nF cx fp) with (nF cx fp + 0) by lia. apply TRF; [lia | lia|].
      rewrite Z.add_0_r. exact H0.
    - apply TRF; [lia | lia | exact H8].
    - apply TRF; [lia | lia | exact H16]. }
  split.
  { unfold nflagw, NX_FLAGPTR in *. apply TRF; [lia | lia | exact HFLW]. }
  split.
  { intros i Hi. rewrite Hshlen in Hi. unfold NX_NSH in Hi.
    assert (Hi8 : (i < 8)%nat) by lia.
    destruct (Nat.eq_dec i 4%nat) as [->|N4]; [replace (Z.of_nat 4) with 4 by reflexivity; exact Hsh4|].
    destruct (Nat.eq_dec i 5%nat) as [->|N5]; [replace (Z.of_nat 5) with 5 by reflexivity; exact Hsh5|].
    rewrite (Hshrest i Hi8 N4 N5).
    rewrite <- (HSHADOW i ltac:(rewrite Hphlen; unfold NX_NSH; lia)).
    pose proof (Nat2Z.is_nonneg i) as Hi0.
    assert (Hilt : Z.of_nat i < 8) by lia.
    assert (Hi45 : Z.of_nat i <> 4 /\ Z.of_nat i <> 5).
    { split; intros Hq; [apply N4 | apply N5]; lia. }
    apply UNCH; [lia | lia | lia | lia | lia]. }
  split; [exact Hshlen|]. split; [exact R25|].
  unfold nslot, NS_FK in *. apply TRsl; [lia | lia | lia | exact HFK].
- destruct HSLOTS as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
  unfold nslots, nslot, NS_FK, NS_F0, NS_BUF, NS_TS, NS_SB, NS_PS12, NS_SH12, NS_OFF8, NS_OFF12,
         NS_PH4, NS_PH8, NS_PH12 in *.
  split; [apply TRsl; [lia | lia | lia | exact S1]|].
  split; [apply TRsl; [lia | lia | lia | exact S2]|].
  split; [apply TRsl; [lia | lia | lia | exact S3']|].
  split; [apply TRsl; [lia | lia | lia | exact S4]|].
  split; [apply TRsl; [lia | lia | lia | exact S5]|].
  split; [apply TRsl; [lia | lia | lia | exact S6]|].
  split; [apply TRsl; [lia | lia | lia | exact S7]|].
  split; [apply TRsl; [lia | lia | lia | exact S8]|].
  split; [apply TRsl; [lia | lia | lia | exact S9]|].
  split; [apply TRsl; [lia | lia | lia | exact S10]|].
  split; [apply TRsl; [lia | lia | lia | exact S11]|].
  apply TRsl; [lia | lia | lia | exact S12].
Qed.

Lemma hb_body_keep : forall cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 pc0 pc sh,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_body cx fp pc0 W ms NSH_ph ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  ms_pc_val ms' = w64 (BASE + pc) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some (nth 4 sh 0) ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some (nth 5 sh 0) ->
  (forall i, (i < 8)%nat -> i <> 4%nat -> i <> 5%nat -> nth i sh 0 = nth i NSH_ph 0) ->
  length sh = NX_NSH ->
  nx_body cx fp pc W ms' sh.
Proof.
intros cx fp k2 ly3 S3 W ms ms' md3 pc0 pc sh HB HJ3 Hfr3 HBODY UNCH.
apply (hb_body_keepX cx fp k2 ly3 S3 W ms ms' md3 pc0 pc sh HB HJ3 Hfr3 HBODY).
intros a Ha N1 N2 N3 _. exact (UNCH a Ha N1 N2 N3).
Qed.

(* The caller-facing facts of nx_mid (the struct apart from its orig field, the stream, the buffer and
   the timestamp cell) across one segment: every byte they name lies in application memory under the
   heap ceiling, or in the image, and so outside the three windows (and outside a callee's frame, the X
   form). *)
Lemma hb_mid_keepX : forall cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 ol ol' q0,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  n_h cx <> 0 ->
  nx_ps_at SEGS (rdW W (ms_mem ms)) (n_ps cx) (n_h cx) (n_sw cx) ol (n_lvt cx) (n_lvid cx) (n_pad cx) ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 ol' ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (n_ps cx) PS_LEN ->
  asource_at SEGS KS (rdW W (ms_mem ms)) (n_h cx) (n_b cx) (n_C cx) q0 ->
  (exists bj', garr8 SEGS (rdW W (ms_mem ms)) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) ->
  (n_ts cx <> 0 -> val_mem SEGS (rdW W (ms_mem ms)) (n_ts cx) 8 (n_tsv cx) /\
     range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (n_ts cx) 8) ->
  nx_ps_at SEGS (rdW W (ms_mem ms')) (n_ps cx) (n_h cx) (n_sw cx) ol' (n_lvt cx) (n_lvid cx) (n_pad cx) /\
  range_addressable (aview SEGS (w_H W) (ms_mem ms')) SHADOW_OFF (n_ps cx) PS_LEN /\
  asource_at SEGS KS (rdW W (ms_mem ms')) (n_h cx) (n_b cx) (n_C cx) q0 /\
  (exists bj', garr8 SEGS (rdW W (ms_mem ms')) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) /\
  (n_ts cx <> 0 -> val_mem SEGS (rdW W (ms_mem ms')) (n_ts cx) 8 (n_tsv cx) /\
     range_addressable (aview SEGS (w_H W) (ms_mem ms')) SHADOW_OFF (n_ts cx) 8).
Proof.
intros cx fp k2 ly3 S3 W ms ms' md3 ol ol' q0 HB HJ3 Hfr3 UNCH Hh0 HPSAT Vol' HRADDR HSRC HBJ HTSV.
destruct (hb_geo cx fp k2 ly3 S3 W (ms_mem ms) md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & _ & _ & HPS4096 & HPSceil & HPSapp & HPSimg &
   HPS8 & HdPF & Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbufb & Htsb & Hstream & _).
pose proof HPSAT as (_ & _ & _ & _ & _ & _ & Hpadlen).
pose proof HPSAT as (_ & _ & _ & _ & _ & _ & Hpadlen2).
destruct (Hstream Hh0) as (Hinh & Hinb & _ & HlenC & Hp0C & _ & _ & Hdpsh & Hdpsb & Hdts & _).
destruct (Hbufb Hh0) as (Hinbuf & Hbuf4096 & Hbufhi & _ & HlenBJ & Hcap & _ & Hdpsbuf).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hinh) as (_ & Hh4096 & Hhceil & Hhapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hinbuf) as (_ & _ & Hbufceil & Hbufapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp, Hbapp, Hbufapp, HPSapp.
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Hhapp.
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HPL : PS_LEN = 24) by reflexivity.
assert (HOLO : PS_OL_OFF = 12) by reflexivity.
assert (HSWO : PS_SW_OFF = 8) by reflexivity.
assert (HFO : PS_F_OFF = 0) by reflexivity.
assert (HVT : PS_VT_OFF = 16) by reflexivity.
assert (HVID : PS_VID_OFF = 20) by reflexivity.
assert (HSFB : SRC_FILE_BLOCK = 1304) by reflexivity.
assert (HdivF : 0 <= nF cx fp / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HSHb : 2147450880 <= nSH cx fp /\ nSH cx fp + 8 <= 17594333495296)
  by (rewrite ESH; unfold SHADOW_OFF; lia).
pose proof (req_size_pos (Z.of_nat (length (n_C cx)))) as Hrqb.
pose proof (req_size_pos (nx_bufn (n_cap cx))) as Hrqbuf.
(* the criterion: application memory under the ceiling, outside the orig field *)
assert (KEEP : forall a, 0 <= a -> a + 1 <= alloc_ceiling ->
  (a + 1 <= 2147446784 \/ 17594333495296 <= a) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
  mbyte SEGS (rdW W (ms_mem ms')) a = mbyte SEGS (rdW W (ms_mem ms)) a).
{ intros a Ha0 Ha1 Hband Hps. apply (mbyte_of_aview SEGS). apply UNCH;
  [clear - Ha0 Ha1 Hac; lia | clear - Ha1 Hac Hsplo Hsp1b HNSB; lia | exact Hps
  | clear - Hband HSHb; lia | clear - Ha1 Hac Hsplo Hsp1b HNSB; lia]. }
(* the image is below the shadow band and the ceiling *)
assert (KEEPI : forall a, in_img SEGS a -> mbyte SEGS (rdW W (ms_mem ms')) a = mbyte SEGS (rdW W (ms_mem ms)) a).
{ intros a Hi. pose proof (pa_img_range a Hi) as Hr. assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
  apply KEEP; [clear - Hr HIE; lia | clear - Hr HIE Hac; lia | clear - Hr HIE; lia |].
  clear - Hr HIE HPSimg HOLO HPL. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HPSimg. lia. }
(* The shadow of a caller frame's bytes: it lies in that frame's shadow, which hb_out keeps apart from
   this call's own frame's shadow (the only shadow bytes the run writes). *)
assert (KEEPSH : forall x n c p, In (c, p) (frames (n_Sc cx)) ->
  frame_addr (n_lyc cx) c p <= x -> x + n <= frame_addr (n_lyc cx) c p + fs_frame_bytes c -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms')) SHADOW_OFF x n).
{ intros x n c p Hin Hfa1 Hfa2 Hn HR y Hy. destruct (HR y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs.
  assert (Hin3 : In (c, p) (frames S3)) by (rewrite Hfr3; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p (proj1 HJ3) Hin3) as (HG4096 & HGceil & HGapp).
  destruct (frame_al64 SEGS B _ _ _ _ _ c p (proj1 HJ3) Hin3) as (HG64 & HGb64 & HGb).
  rewrite EFA in HG4096, HGceil, HGapp, HG64.
  assert (Hy1 : frame_addr (n_lyc cx) c p <= y < frame_addr (n_lyc cx) c p + fs_frame_bytes c)
    by (clear - Hy Hfa1 Hfa2 Hn; lia).
  assert (HdivY : frame_addr (n_lyc cx) c p / 8 <= y / 8 < frame_addr (n_lyc cx) c p / 8 + fs_frame_bytes c / 8).
  { split.
    - apply Z.div_le_mono; [lia | lia].
    - assert (Hfd : frame_addr (n_lyc cx) c p = 64 * (frame_addr (n_lyc cx) c p / 64))
        by (pose proof (Z.div_mod (frame_addr (n_lyc cx) c p) 64 ltac:(lia)); lia).
      assert (Hnd : fs_frame_bytes c = 64 * (fs_frame_bytes c / 64))
        by (pose proof (Z.div_mod (fs_frame_bytes c) 64 ltac:(lia)); lia).
      assert (E1 : frame_addr (n_lyc cx) c p / 8 = 8 * (frame_addr (n_lyc cx) c p / 64))
        by (rewrite Hfd at 1; replace (64 * (frame_addr (n_lyc cx) c p / 64))
              with (8 * (frame_addr (n_lyc cx) c p / 64) * 8) by lia; apply Z.div_mul; lia).
      assert (E2 : fs_frame_bytes c / 8 = 8 * (fs_frame_bytes c / 64))
        by (rewrite Hnd at 1; replace (64 * (fs_frame_bytes c / 64))
              with (8 * (fs_frame_bytes c / 64) * 8) by lia; apply Z.div_mul; lia).
      rewrite E1, E2. apply Z.div_lt_upper_bound; [lia|]. clear - Hy1 Hfd Hnd. lia. }
  apply UNCH.
  - unfold shadow_of_addr. clear - HG4096 HGceil HdivY Hy1 Hac HGb HG64.
    pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound y 8 17592186044416 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
  - unfold shadow_of_addr. clear - HG4096 HGceil HdivY Hy1 Hac Hsplo Hsp1b HNSB HGb HG64.
    pose proof (Z.div_le_upper_bound y 8 17592186044416 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
  - unfold shadow_of_addr. clear - HG4096 HGceil HdivY Hy1 Hac HPSapp HPS4096 HPSceil HPL HOLO HGb HG64.
    pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound y 8 17592186044416 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia.
  - intros Hw.
    destruct (hb_out cx fp k2 ly3 S3 W (ms_mem ms) md3 (shadow_of_addr SHADOW_OFF y) HB HJ3 Hfr3
      ltac:(right; exact Hw)) as (_ & _ & Hnf & _).
    destruct (Hnf c p Hin) as (_ & H2). apply H2.
    unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. lia.
  - unfold shadow_of_addr. clear - HG4096 HGceil HdivY Hy1 Hac Hsplo Hsp1b HNSB HGb HG64.
    pose proof (Z.div_le_upper_bound y 8 17592186044416 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
split.
{ destruct HPSAT as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (HX : forall x, n_ps cx <= x < n_ps cx + PS_LEN -> ~ (n_ps cx + PS_OL_OFF <= x < n_ps cx + 16) ->
    mbyte SEGS (rdW W (ms_mem ms')) x = mbyte SEGS (rdW W (ms_mem ms)) x)
    by (intros x Hx Hnx; apply KEEP; [clear - Hx HPS4096 HPL; lia | clear - Hx HPSceil HPL; lia
                                     | clear - Hx HPSapp HPL; lia | exact Hnx]).
  split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P1]; intros x Hx; apply HX; clear - Hx HFO HPL HOLO; cbn in Hx; lia|].
  split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P2]; intros x Hx; apply HX; clear - Hx HSWO HPL HOLO; cbn in Hx; lia|].
  split; [exact Vol'|].
  split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P4]; intros x Hx; apply HX; clear - Hx HVT HPL HOLO; cbn in Hx; lia|].
  split; [eapply PcapSourceCloseSpec.vm_frame_segs; [|exact P5]; intros x Hx; apply HX; clear - Hx HVID HPL HOLO; cbn in Hx; lia|].
  split; [|exact P7].
  apply (garr8_frame SEGS _ _ _ _ P6). intros x Hx. rewrite P7 in Hx. apply HX;
    clear - Hx HPL HOLO; cbn in Hx; lia. }
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & Hown & Hfa1 & Hfa2 & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs0 & _).
assert (HinC : In (n_cid cx, n_pos cx) (frames (n_Sc cx)))
  by (rewrite Hfrs0; apply in_or_app; left; exact Hown).
split; [apply (KEEPSH (n_ps cx) PS_LEN (n_cid cx) (n_pos cx) HinC Hfa1 Hfa2 ltac:(clear - HPL; lia) HRADDR)|].
split.
{ apply (PcapSourceCloseSpec.asource_at_frame_segs _ KS (rdW W (ms_mem ms)) (rdW W (ms_mem ms'))); [|exact HSRC].
  intros a [Ha|[Ha|Ha]].
  - apply KEEP; [clear - Ha Hh4096 HSFB; lia | clear - Ha Hhceil HSFB; lia
                | clear - Ha Hhapp HSFB; lia | clear - Ha Hdpsh HPL HOLO HSFB; lia].
  - apply KEEP; [clear - Ha Hb4096; lia | clear - Ha Hbceil Hrqb; lia
                | clear - Ha Hbapp Hrqb; lia | clear - Ha Hdpsb HPL HOLO; lia].
  - apply KEEPI. exact (proj1 (asil_env _ _ _ _ ASIL a Ha)). }
split.
{ destruct HBJ as (bj' & Hgb & Hlen). exists bj'. split; [|exact Hlen].
  apply (garr8_frame SEGS _ _ _ _ Hgb). intros x Hx. rewrite Hlen, HlenBJ in Hx.
  apply KEEP; [clear - Hx Hbuf4096; lia | clear - Hx Hbufceil Hrqbuf; lia
              | clear - Hx Hbufapp Hrqbuf; lia | clear - Hx Hdpsbuf HPL HOLO; lia]. }
intros Hts0. destruct (HTSV Hts0) as (Vts & Rts).
destruct (Htsb Hh0 Hts0) as (_ & Hts8 & Hts4096 & Hts47 & Hamts & (tcid & tpos & Htown & Htfa1 & Htfa2) &
  _ & _ & Hdpsts & _).
assert (HinT : In (tcid, tpos) (frames (n_Sc cx)))
  by (rewrite Hfrs0; apply in_or_app; left; exact Htown).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamts.
assert (HinT3 : In (tcid, tpos) (frames S3)) by (rewrite Hfr3; right; exact HinT).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos (proj1 HJ3) HinT3) as (HT4096 & HTceil & HTapp).
rewrite EFA in HT4096, HTceil, HTapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp.
pose proof (fs_frame_bytes_nonneg tcid) as HTnn.
split.
- eapply PcapSourceCloseSpec.vm_frame_segs; [|exact Vts]. intros x Hx. cbn in Hx.
  apply KEEP; [clear - Hx Hts4096; lia | clear - Hx Htfa1 Htfa2 HTceil; lia
              | clear - Hx Htfa1 Htfa2 HTapp HT4096 HTnn; lia
              | clear - Hx Hdpsts HPL HOLO; lia].
- exact (KEEPSH (n_ts cx) 8 tcid tpos HinT Htfa1 Htfa2 ltac:(lia) Rts).
Qed.

Lemma hb_mid_keep : forall cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 ol ol' q0,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  n_h cx <> 0 ->
  nx_ps_at SEGS (rdW W (ms_mem ms)) (n_ps cx) (n_h cx) (n_sw cx) ol (n_lvt cx) (n_lvid cx) (n_pad cx) ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 ol' ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (n_ps cx) PS_LEN ->
  asource_at SEGS KS (rdW W (ms_mem ms)) (n_h cx) (n_b cx) (n_C cx) q0 ->
  (exists bj', garr8 SEGS (rdW W (ms_mem ms)) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) ->
  (n_ts cx <> 0 -> val_mem SEGS (rdW W (ms_mem ms)) (n_ts cx) 8 (n_tsv cx) /\
     range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (n_ts cx) 8) ->
  nx_ps_at SEGS (rdW W (ms_mem ms')) (n_ps cx) (n_h cx) (n_sw cx) ol' (n_lvt cx) (n_lvid cx) (n_pad cx) /\
  range_addressable (aview SEGS (w_H W) (ms_mem ms')) SHADOW_OFF (n_ps cx) PS_LEN /\
  asource_at SEGS KS (rdW W (ms_mem ms')) (n_h cx) (n_b cx) (n_C cx) q0 /\
  (exists bj', garr8 SEGS (rdW W (ms_mem ms')) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) /\
  (n_ts cx <> 0 -> val_mem SEGS (rdW W (ms_mem ms')) (n_ts cx) 8 (n_tsv cx) /\
     range_addressable (aview SEGS (w_H W) (ms_mem ms')) SHADOW_OFF (n_ts cx) 8).
Proof.
intros cx fp k2 ly3 S3 W ms ms' md3 ol ol' q0 HB HJ3 Hfr3 UNCH.
apply (hb_mid_keepX cx fp k2 ly3 S3 W ms ms' md3 ol ol' q0 HB HJ3 Hfr3).
intros a Ha N1 N2 N3 _. exact (UNCH a Ha N1 N2 N3).
Qed.

End c.
End b.
End a.
