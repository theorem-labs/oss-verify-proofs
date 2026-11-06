(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 101 of its 135 lines of code are new or changed and 546 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceNext.v, with its module names changed; 291 of its 330 lines of code are new or changed and 96 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8) on the ASan+UBSan build of libreac v1.9.0: two helpers of the
   skip phase (lib/B/Prog/PcapSourceNextSkip.v, a Theorem Labs lane) for the fread of a chunk into the caller's buffer,
   fread(buf, 1, n, h) (0x81848, returning to NP_sk_ra 0x8184c).

   - sk_fread_buf_post: the caller's memory part of the middle state, from the state at the call (W3, m) to the
     state after it (W2, m2), given what the fread wrapper's post keeps (rread_kept with the window AFREAD_STK below
     sp1, and the shadow band) and the bytes it read (R, j of them, at the head of the buffer).
     PORTED from lib/A's nx_fread_buf_post (lib/A/Prog/PcapSourceNextSkipDefs.v:323-483 on
     a working branch da0818b5f51, a Theorem Labs lane) with its helpers nxs_vm_frame, nxs_ps_at_frame,
     nxs_ra_frame, nxs_mbyte_present (:119-146, unchanged). lib/B's changes: rread_kept / rread_wrset
     (lib/A/Stdio/PFreadM.v:344 / :285, the post of PFreadISpec's afread_spec) for afread_kept / afread_wrset;
     NX_STK_B = 272 + AFREAD_STK = 8464 (lib/B Defs) for NX_STK; the sp facts of lib/B's Seat (nx_sp_facts:
     alloc_ceiling + 8464 <= sp, sp <= 2 ^ 47, sp - 272 <= sp1 <= sp - 256) for lib/A's nx_E_below and its
     sp1 range (sp - 256 < sp1 <= sp - 224).
   - sk_body_call: nx_body across that call. The saved registers (sp - 104 .. sp - 8) and the spill slots
     (sp1 .. sp1 + 152) lie above sp1, so outside the callee's window and above the allocator's ceiling, where the
     FILE block and the buffer end: rread_kept's first clause keeps them. The frame's header and flag word lie in
     this call's frame, which is apart from the FILE block and the buffer (sep_block_frame; both are blocks):
     rread_kept's frames clause keeps them. The frame's shadow lies in the shadow band, which the post keeps.
     NEW at lib/B; template a Theorem Labs lane's nxb_hdA_ph after its fread (lib/B/Prog/PcapSourceNextHdrA.v:931-1142 on
     a working branch: TR1, TRO, TROS, HSL, HSV, HFW, HSHN). There the destination F + 32 lies in the frame;
     here it is a heap block.

   Every number is lib/B's (lib/B/Prog/PcapSourceNextDefs.v, lib/B/Prog/PcapSourceNextSeat.v), read from the pinned
   fuzz_pcap.asan-ubsan image (sha256 9e66f771f22af67a...). *)
(* Modified by Theorem Labs, 2026-10: nxs_vm_frame (the copy of lib/A's helper, an instance of lib/A/Prog/PcapSourceClose.v's
   vm_frame) and nxs_ra_frame (a copy of ra_frame) deleted; their uses name lib/A/Prog/PcapSourceCloseSpec.v's
   vm_frame_segs and ra_frame. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
(* PFreadM: rread_kept / rread_wrset, which PFreadISpec Requires without exporting. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YI13 YI01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit PcapSourceNextSeat.
(* The image-free frame lemmas vm_frame_segs and ra_frame, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
(* lib/B's phase layer, LAST (it Require-Exports Spec; lib/B's names shadow the shared ones). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* Byte-level helpers, statements as in lib/A's PcapSourceNextSkipDefs.v:119-146 on da0818b5f51   *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nxs_ps_at_frame : forall (m m' : word -> option byte) ps h sw lol lvt lvid pad,
  (forall x, ps <= x < ps + PS_LEN -> mbyte SEGS m' x = mbyte SEGS m x) ->
  nx_ps_at SEGS m ps h sw lol lvt lvid pad -> nx_ps_at SEGS m' ps h sw lol lvt lvid pad.
Proof.
intros m m' ps h sw lol lvt lvid pad Hfr Hps. unfold nx_ps_at in *. destruct Hps as (V1 & V2 & V3 & V4 & V5 & G & Hl).
unfold PS_LEN, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V1]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V2]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V3]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V4]|].
split; [apply (PcapSourceCloseSpec.vm_frame_segs _ m); [intros x Hx; apply Hfr; clear - Hx; lia | exact V5]|].
split; [|exact Hl]. apply (garr8_frame SEGS m m' _ _ G). intros x Hx. apply Hfr. rewrite Hl in Hx. clear - Hx. cbn [length] in Hx. lia.
Qed.

Lemma nxs_mbyte_present : forall H (m : word -> option byte) a,
  apresent H m a -> exists b, mbyte SEGS (mrestrict H m) a = Some b.
Proof. intros H m a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The fread of a chunk into the caller's buffer, inside this call's journal                        *)
(* ---------------------------------------------------------------------------------------------- *)

Section f.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

(* After the call: the middle state's memory part from the state at the call (W3, m) to the state after it
   (W2, m2), given what afread_spec's post keeps (rread_kept, the shadow band) and the bytes it read (R, j of them,
   at the head of the buffer). *)
Lemma sk_fread_buf_post : forall cx fp k2 ly3 S3 W3 m md3 W2 m2 md2 n j ol vt vid tv R,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 m md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 < n <= n_cap cx ->
  rread_kept SEGS B AFREAD_STK ly3 S3 W3 m W2 m2 (n_sp1 cx) (rread_wrset (n_h cx) (n_buf cx) n) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W2) m2 s = aview SEGS (w_H W3) m s) ->
  AR SEGS B ly3 S3 W2 m2 md2 ->
  garr8 SEGS (rdW W2 m2) (n_buf cx) R -> Z.of_nat (length R) = j -> 0 <= j <= n ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m (spZ (n_regs cx)) (nx_E cx) ->
  nx_ps_at SEGS (rdW W3 m) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (n_ps cx) PS_LEN ->
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W3 m) (n_ts cx) 8 tv /\ range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (n_ts cx) 8) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 m2 (spZ (n_regs cx)) (nx_E cx) /\
  nx_ps_at SEGS (rdW W2 m2) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) /\
  range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF (n_ps cx) PS_LEN /\
  (forall bj0, garr8 SEGS (rdW W3 m) (n_buf cx) bj0 -> length bj0 = length (n_bj cx) ->
     exists bj', garr8 SEGS (rdW W2 m2) (n_buf cx) bj' /\ length bj' = length (n_bj cx) /\
       firstn (Z.to_nat j) bj' = R /\ skipn (Z.to_nat n) bj' = skipn (Z.to_nat n) bj0) /\
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W2 m2) (n_ts cx) 8 tv /\ range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF (n_ts cx) 8).
Proof.
intros cx fp k2 ly3 S3 W3 m md3 W2 m2 md2 n j ol vt vid tv R HB Hh HJ HFR Hab Hn HK HSB HAR2 HR HlR Hj
  (O1 & O2 & O3 & O4 & O5 & O6) Hps Hpsra Hts.
destruct HK as (A1 & A2 & A3 & A4 & A5 & A6).
(* lib/B's stack facts (Seat), for lib/A's nx_E_below and its sp1 range *)
pose proof (nx_sp_facts B KS cx HB) as (_ & Hspc & Hsp47 & Hsp1 & _).
pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ & Hps8 & Hps4 & Hps47 & Hpsam
  & Hown & Hfa1 & Hfa2 & _ & _ & _ & _ & _ & Hbuf & Htsb & Hstr & _).
destruct (Hbuf Hh) as (Hinb & Hb4096 & Hb63 & _ & Hlbj & Hcap & _ & Dbps).
destruct (Hstr Hh) as (Hinh & HinC & _ & HlC & _ & Dbh & Dbb & Dph & Dpb & Dts & _).
pose proof HJ as (HAR3 & Hly & _).
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
{ intros c p. rewrite (frame_addr_layout_le _ _ _ Hly c p). symmetry. exact (frame_addr_layout_le _ _ _ Hly0 c p). }
assert (HFc : forall c p, In (c, p) (frames (n_Sc cx)) -> In (c, p) (frames S3)) by (intros c p H; rewrite HFR; right; exact H).
assert (HOc : forall c p, In (c, p) (n_own cx) -> In (c, p) (frames (n_Sc cx)))
  by (intros c p H; rewrite Hfrs0; apply in_or_app; left; exact H).
assert (Hbn : n <= nx_bufn (n_cap cx)) by (unfold nx_bufn; revert Hn; clear; intros; lia).
assert (WE : forall a, rread_wrset (n_h cx) (n_buf cx) n a -> nx_E cx a).
{ intros a [Ha|Ha]; unfold nx_E, nx_wrset;
    [right; right; right; split; [exact Hh | exact Ha] | right; left; revert Ha Hbn; clear; intros; lia]. }
unfold NX_STK_B, AFREAD_STK in *.
(* the struct's and the timestamp cell's bytes: in the caller's frames, off the FILE and the buffer *)
assert (KF : forall c p x0 len, In (c, p) (n_own cx) -> frame_addr (n_lyc cx) c p <= x0 ->
  x0 + len <= frame_addr (n_lyc cx) c p + fs_frame_bytes c ->
  (x0 + len <= n_h cx \/ n_h cx + SRC_FILE_BLOCK <= x0) -> (n_buf cx + nx_bufn (n_cap cx) <= x0 \/ x0 + len <= n_buf cx) ->
  forall x, x0 <= x < x0 + len -> mbyte SEGS (rdW W2 m2) x = mbyte SEGS (rdW W3 m) x).
{ intros c p x0 len Hin H1 H2 D1 D2 x Hx. apply (mbyte_of_aview SEGS).
  assert (HRng : in_zr x (frame_rng (n_lyc cx) (c, p)) \/
               in_zr x (shadow_addr (frame_addr (n_lyc cx) c p), fs_frame_bytes c / 8)).
  { left. unfold in_zr, frame_rng. cbn [fst snd]. revert H1 H2 Hx. clear. intros. lia. }
  assert (HnW : ~ rread_wrset (n_h cx) (n_buf cx) n x).
  { unfold rread_wrset. intros [X|X].
    - revert X Hx D1. unfold SRC_FILE_BLOCK. clear. intros. lia.
    - revert X Hx D2 Hbn. clear. intros. lia. }
  apply (A4 c p x (HFc c p (HOc c p Hin))); [|exact HnW].
  unfold in_zr, frame_rng in HRng |- *. cbn [fst snd] in HRng |- *. rewrite !EFA. exact HRng. }
assert (KS0 : forall x, kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd ->
  aview SEGS (w_H W2) m2 (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W3) m (shadow_of_addr SHADOW_OFF x))
  by (intros x Hx; apply HSB; exact Hx).
split.
{ (* nx_kept *)
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw HnE. transitivity (aview SEGS (w_H W3) m a).
    + apply A1; [exact Ha | revert Hw Hsp1; clear; intros; lia | intros X; apply HnE; apply WE; exact X].
    + apply O1; [exact Ha | exact Hw | exact HnE].
  - intros b mm i Hin Hi HnE. transitivity (aview SEGS (w_H W3) m (b + i)).
    + apply (A2 b mm i); [rewrite Hab; exact Hin | exact Hi | intros X; apply HnE; apply WE; exact X].
    + apply (O2 b mm i Hin Hi HnE).
  - intros a Hi Hno He. transitivity (aview SEGS (w_H W3) m a); [apply A3; assumption | apply O3; assumption].
  - intros c p a Hin Hr HnE. transitivity (aview SEGS (w_H W3) m a).
    + apply (A4 c p a (HFc c p Hin)); [|intros X; apply HnE; apply WE; exact X].
      unfold in_zr, frame_rng in *. cbn [fst snd] in *. rewrite !EFA. exact Hr.
    + apply (O4 c p a Hin Hr HnE).
  - intros a Ha Hw Hp. apply A5; [exact Ha | revert Hw Hsp1; clear; intros; lia | exact (O5 a Ha Hw Hp)].
  - intros a Ha. destruct (Z_lt_le_dec a (n_sp1 cx - 8192)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (n_sp1 cx)) as [Hhi|Hhi]].
    + apply A5; [revert Ha Hspc Hsp1 Hsp47; clear; intros; lia | revert Hlo; clear; intros; lia | exact (O6 a Ha)].
    + apply A6. revert Hlo Hhi; clear; intros; lia.
    + apply A5; [revert Ha Hspc Hsp1 Hsp47; clear; intros; lia | revert Hhi; clear; intros; lia | exact (O6 a Ha)]. }
split.
{ apply (nxs_ps_at_frame (rdW W3 m)); [|exact Hps].
  intros x Hx. apply (KF (n_cid cx) (n_pos cx) (n_ps cx) PS_LEN Hown Hfa1 Hfa2 Dph Dbps x Hx). }
split.
{ apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) m)); [exact Hpsra|].
  intros x Hx. apply KS0. unfold shadow_of_addr, SHADOW_OFF, PS_LEN in *.
  assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
    by (revert Hx Hps4 Hps47; unfold PS_LEN; clear; intros; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  revert Hx8; clear; unfold kLowMemEnd, kHighShadowEnd; intros; lia. }
split.
{ intros bj0 Hbj0 Hl0.
  pose (L := length (n_bj cx)).
  assert (HL : Z.of_nat L = nx_bufn (n_cap cx)) by exact Hlbj.
  assert (Hl0' : length bj0 = L) by exact Hl0.
  assert (Hnl : (Z.to_nat n <= L)%nat) by (revert HL Hbn Hn; clear; intros; lia).
  set (tail := skipn (Z.to_nat n) bj0).
  assert (Hlt : length tail = (L - Z.to_nat n)%nat) by (unfold tail; rewrite length_skipn, Hl0'; reflexivity).
  assert (Gt0 : garr8 SEGS (rdW W3 m) (n_buf cx + n) tail).
  { pose proof (YI01.garr8_sub SEGS (rdW W3 m) (n_buf cx) bj0 (Z.to_nat n) (L - Z.to_nat n) Hbj0) as G.
    rewrite firstn_all2 in G by (rewrite length_skipn, Hl0'; clear; lia).
    rewrite Z2Nat.id in G by (revert Hn; clear; intros; lia). exact G. }
  assert (HinbS : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Hab; exact Hinb).
  assert (Hrb2 : req_size (nx_bufn (n_cap cx)) = nx_bufn (n_cap cx))
    by (unfold req_size, nx_bufn; destruct (Z.max (n_cap cx) 1 =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; revert Hz; clear; lia | reflexivity]).
  assert (Htl : forall x, n_buf cx + n <= x < n_buf cx + Z.of_nat L ->
    mbyte SEGS (rdW W2 m2) x = mbyte SEGS (rdW W3 m) x).
  { intros x Hx. apply (mbyte_of_aview SEGS).
    replace x with (n_buf cx + (x - n_buf cx)) by (revert Hx; clear; intros; lia).
    apply (A2 (n_buf cx) (nx_bufn (n_cap cx)) (x - n_buf cx) HinbS);
      [rewrite Hrb2; revert Hx HL Hn; clear; intros; lia|].
    unfold rread_wrset. intros [X|X].
    - revert X Hx Dbh HL Hbn Hn. unfold SRC_FILE_BLOCK. clear. intros. lia.
    - revert X Hx Hn. clear. intros. lia. }
  assert (Gt : garr8 SEGS (rdW W2 m2) (n_buf cx + n) tail).
  { apply (garr8_frame SEGS (rdW W3 m) (rdW W2 m2) _ _ Gt0). intros x Hx. rewrite Hlt in Hx.
    apply Htl. revert Hx Hnl Hn; clear; intros.
    rewrite Nat2Z.inj_sub in Hx by exact Hnl. rewrite Z2Nat.id in Hx by lia. lia. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 HinbS) as (_ & _ & _ & _ & Hbpres & _).
  destruct (YI13.garr8_of_readable SEGS (rdW W2 m2) (n_buf cx + j) (Z.to_nat (n - j))) as (M & HlM & GM).
  { intros a Ha. rewrite Z2Nat.id in Ha by (revert Hj; clear; intros; lia).
    apply nxs_mbyte_present.
    assert (Hin2 : n_buf cx <= a < n_buf cx + req_size (nx_bufn (n_cap cx)))
      by (rewrite Hrb2; revert Ha Hj Hn HL Hbn; clear; intros; lia).
    exact (proj1 (Hbpres a Hin2)). }
  exists (R ++ M ++ tail).
  assert (HlR' : length R = Z.to_nat j) by (revert HlR Hj; clear; intros; lia).
  split.
  { apply garr8_app. split; [exact HR|]. apply garr8_app. split.
    - rewrite HlR'. rewrite Z2Nat.id by (revert Hj; clear; intros; lia). exact GM.
    - rewrite HlR', HlM.
      replace (n_buf cx + Z.of_nat (Z.to_nat j) + Z.of_nat (Z.to_nat (n - j))) with (n_buf cx + n)
        by (revert Hj; clear; intros; lia).
      exact Gt. }
  split; [rewrite !length_app, HlR', HlM, Hlt; revert Hnl Hj Hn; clear; intros; lia|].
  split; [rewrite firstn_app, HlR', Nat.sub_diag, firstn_O, app_nil_r; apply firstn_all2; rewrite HlR'; clear; lia|].
  rewrite skipn_app, HlR'. rewrite skipn_all2 by (rewrite HlR'; revert Hj Hn; clear; intros; lia). cbn [app].
  rewrite skipn_app, HlM. rewrite skipn_all2 by (rewrite HlM; revert Hj Hn; clear; intros; lia). cbn [app].
  replace (Z.to_nat n - Z.to_nat j - Z.to_nat (n - j))%nat with 0%nat by (revert Hj Hn; clear; intros; lia).
  reflexivity. }
intros Hts0. destruct (Hts Hts0) as (Hv & Hra).
destruct (Htsb Hh Hts0) as (_ & Hts8 & Hts4 & Hts47 & _ & (tc & tp & Htin & Ht1 & Ht2) & _ & _ & _ & Dbt).
destruct (Dts Hts0) as (Dth & _).
split.
- apply (PcapSourceCloseSpec.vm_frame_segs _ (rdW W3 m)); [|exact Hv].
  intros x Hx. apply (KF tc tp (n_ts cx) 8 Htin Ht1 Ht2 Dth Dbt x). revert Hx; clear; intros; lia.
- apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) m)); [exact Hra|].
  intros x Hx. apply KS0. unfold shadow_of_addr, SHADOW_OFF in *.
  assert (Hx8 : 0 <= x / 8 < 2 ^ 44)
    by (revert Hx Hts4 Hts47; clear; intros; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  revert Hx8; clear; unfold kLowMemEnd, kHighShadowEnd; intros; lia.
Qed.

(* nx_body across the call: everything nx_body names lies above sp1 (the saved registers and the spill slots), in
   this call's frame (the header and the flag word) or in the shadow band (the frame's shadow), and the call writes
   only the FILE block, the buffer and its own window below sp1. The registers are the ones the caller names. *)
Lemma sk_body_call : forall cx fp k2 ly3 S3 W3 ms3 md3 W2 regs2 m2 n pc pc' sh,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 < n <= n_cap cx ->
  nx_body cx fp pc W3 ms3 sh ->
  rread_kept SEGS B AFREAD_STK ly3 S3 W3 (ms_mem ms3) W2 m2 (n_sp1 cx) (rread_wrset (n_h cx) (n_buf cx) n) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W2) m2 s = aview SEGS (w_H W3) (ms_mem ms3) s) ->
  (forall r, In r [2; 3; 4; 8; 9; 25]%bv -> getr regs2 r = getr (ms_regs ms3) r) ->
  nx_body cx fp pc' W2 (mkst regs2 (w64 (BASE + pc')) m2 (seg_rom SEGS)) sh.
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 W2 regs2 m2 n pc pc' sh HB Hh HJ HFR Hab Hn HBD HK HSB HRG.
destruct HBD as (HB0 & HSLOTS).
destruct HB0 as (_ & _ & _ & _ & _ & _ & HREGS & HSAVED & HHDR & HFLW & HSHA & HSHLEN & R25 & HFK).
destruct HREGS as (RG2 & RG8 & RG9 & RG3 & RG4).
destruct HK as (K1 & _ & _ & K4 & _ & _).
(* the numbers of this state (lib/B's Seat) *)
pose proof (nx_sp_facts B KS cx HB) as (_ & Hspc & Hsp47 & Hsp1 & _).
pose proof (nx_SH_range B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR) as (HSH0 & HSH1 & _).
pose proof (nx_frame_addr_eq B KS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ) as EFA.
pose proof NX_FRAME_slot as (EFB & _ & _). unfold NX_FRAME in EFB.
assert (HFIN : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
pose proof HJ as (HAR3 & _).
(* the FILE block and the buffer: blocks, under the allocator's ceiling, apart from this call's frame *)
pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hstr & _).
destruct (Hbuf Hh) as (Hinb & _).
destruct (Hstr Hh) as (Hinh & _).
assert (Hinb3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Hab; exact Hinb).
assert (Hinh3 : In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Hab; exact Hinh).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb3) as (_ & _ & Hbceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinh3) as (_ & _ & Hhceil & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; clear; lia)) as (_ & Hrb).
assert (Hbn : n <= nx_bufn (n_cap cx)) by (unfold nx_bufn; revert Hn; clear; intros; lia).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ NX_CID fp HAR3 Hinh3 HFIN) as Dh.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ NX_CID fp HAR3 Hinb3 HFIN) as Db.
unfold zdisjoint in Dh, Db. cbn [fst snd] in Dh, Db. rewrite EFA, EFB in Dh, Db.
change (req_size SRC_FILE_BLOCK) with 1304 in Dh.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Dh, Db.
assert (HNE : forall a, alloc_ceiling <= a -> ~ rread_wrset (n_h cx) (n_buf cx) n a).
{ intros a Ha [X | X].
  - unfold SRC_FILE_BLOCK in X. revert Ha X Hhceil; clear; intros; lia.
  - revert Ha X Hbceil Hrb Hbn; clear; intros; lia. }
(* what the call kept (the template's TR1, TRO, TROS) *)
assert (TR1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (n_sp1 cx - 8192 <= a < n_sp1 cx) ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw. exact (K1 a Ha Hw (HNE a (proj1 Ha))). }
assert (TRO : forall a, nF cx fp <= a < nF cx fp + 64 ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (K4 NX_CID fp a HFIN).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, EFB. exact Ha.
  - intros [X | X].
    + unfold SRC_FILE_BLOCK in X. destruct Dh as [D | D]; revert Ha X D; clear; intros; lia.
    + destruct Db as [D | D]; revert Ha X D Hrb Hbn; clear; intros; lia. }
assert (TROS : forall i, 0 <= i < 8 ->
  aview SEGS (w_H W2) m2 (nSH cx fp + i) = aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + i)).
{ intros i Hi. apply HSB. unfold kLowMemEnd, kHighShadowEnd. unfold SHADOW_OFF in HSH0, HSH1.
  revert Hi HSH0 HSH1; clear; intros; lia. }
(* the state after the call *)
set (ms2 := mkst regs2 (w64 (BASE + pc')) m2 (seg_rom SEGS)).
assert (MR : ms_regs ms2 = regs2) by reflexivity.
assert (MM : ms_mem ms2 = m2) by reflexivity.
assert (G2 : getr regs2 2 = getr (ms_regs ms3) 2) by (apply HRG; cbn [In]; left; reflexivity).
assert (G3 : getr regs2 3 = getr (ms_regs ms3) 3) by (apply HRG; cbn [In]; right; left; reflexivity).
assert (G4 : getr regs2 4 = getr (ms_regs ms3) 4) by (apply HRG; cbn [In]; right; right; left; reflexivity).
assert (G8 : getr regs2 8 = getr (ms_regs ms3) 8)
  by (apply HRG; cbn [In]; right; right; right; left; reflexivity).
assert (G9 : getr regs2 9 = getr (ms_regs ms3) 9)
  by (apply HRG; cbn [In]; right; right; right; right; left; reflexivity).
assert (G25 : getr regs2 25 = getr (ms_regs ms3) 25)
  by (apply HRG; cbn [In]; right; right; right; right; right; left; reflexivity).
(* the memory after the call (the template's HSL, HSV, HFW) *)
assert (HSL : forall off v, 0 <= off < 152 -> nslot cx W3 ms3 off v -> nslot cx W2 ms2 off v).
{ intros off v Hoff Hs. unfold nslot in Hs |- *. rewrite MM, <- Hs. apply rdword_ext. intros k Hk.
  apply TR1; revert Hoff Hk Hspc Hsp47 Hsp1; clear; intros; lia. }
assert (HSV : forall a v, spZ (n_regs cx) - 104 <= a <= spZ (n_regs cx) - 8 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W2) (ms_mem ms2)) a = Some v).
{ intros a v Ha Hv. rewrite MM, <- Hv. apply rdword_ext. intros k Hk.
  apply TR1; revert Ha Hk Hspc Hsp47 Hsp1; clear; intros; lia. }
assert (HFW : forall a v, nF cx fp <= a /\ a + 8 <= nF cx fp + 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v -> rdword (aview SEGS (w_H W2) (ms_mem ms2)) a = Some v).
{ intros a v Ha Hv. rewrite MM, <- Hv. apply rdword_ext. intros k Hk.
  apply TRO. revert Ha Hk; clear; intros; lia. }
split.
{ (* nx_body0 *)
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { unfold nregs. rewrite MR, G2, G8, G9, G3, G4. exact (conj RG2 (conj RG8 (conj RG9 (conj RG3 RG4)))). }
  split.
  { destruct HSAVED as (S1 & S2). split.
    - apply HSV; [clear; lia | exact S1].
    - intros jj Hjj. apply HSV; [revert Hjj; clear; intros; lia | exact (S2 jj Hjj)]. }
  split.
  { destruct HHDR as (H1 & H2 & H3).
    split; [apply HFW; [clear; lia | exact H1]|].
    split; [apply HFW; [clear; lia | exact H2] | apply HFW; [clear; lia | exact H3]]. }
  split; [apply HFW; [unfold NX_FLAGPTR; clear; lia | exact HFLW]|].
  split.
  { intros i Hi. pose proof (HSHA i Hi) as Hv. rewrite MM.
    rewrite HSHLEN in Hi. unfold NX_NSH in Hi.
    rewrite (TROS (Z.of_nat i) ltac:(revert Hi; clear; intros; lia)). exact Hv. }
  split; [exact HSHLEN|].
  split; [rewrite MR, G25; exact R25|].
  apply HSL; [unfold NS_FK; clear; lia | exact HFK]. }
destruct HSLOTS as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12).
split; [apply HSL; [unfold NS_FK; clear; lia | exact L1]|].
split; [apply HSL; [unfold NS_F0; clear; lia | exact L2]|].
split; [apply HSL; [unfold NS_BUF; clear; lia | exact L3]|].
split; [apply HSL; [unfold NS_TS; clear; lia | exact L4]|].
split; [apply HSL; [unfold NS_SB; clear; lia | exact L5]|].
split; [apply HSL; [unfold NS_PS12; clear; lia | exact L6]|].
split; [apply HSL; [unfold NS_SH12; clear; lia | exact L7]|].
split; [apply HSL; [unfold NS_OFF8; clear; lia | exact L8]|].
split; [apply HSL; [unfold NS_OFF12; clear; lia | exact L9]|].
split; [apply HSL; [unfold NS_PH4; clear; lia | exact L10]|].
split; [apply HSL; [unfold NS_PH8; clear; lia | exact L11]|].
apply HSL; [unfold NS_PH12; clear; lia | exact L12].
Qed.

End f.

End b.
End a.
