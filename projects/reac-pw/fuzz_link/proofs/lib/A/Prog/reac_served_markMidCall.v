(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 346 of its 396 lines of code are new or changed and 3507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v, with its numbers changed; 461 of its 510 lines of code are new or changed and 347 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A, the MID segment's call of reac_link_alias_read (0x8867c, the
   `jal` at +0x280): the cut base at the callee's entry (the run from +0x1d4 wrote only F's shadow bytes SH + 4 ..
   SH + 43, which `aside_rng` holds), the callee's Pre, its read set and its apre there (lib/A/Prog/
   reac_link_alias_read_c.v, `aleaf_rd`), and the RRET cut (+0x284, lib/A/Prog/reac_served_markDefs.v
   `srm_gi_rret`) from the callee's post.

   Proves no function (kind: segment lemma of reac_served_mark's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkPi LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c nl_talk_c reac_link_alias_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markDefs reac_served_markUniq reac_served_markKit reac_served_markKitAt reac_served_markXfer
reac_served_markMidRef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   Generic pieces
   ========================================================================== *)
Section g.
Variable segs : list Segment.

(* a byte outside the bytes a step changed has the view it had *)
Lemma srm_mid_view_frame : forall H (m m' : word -> option byte) (P : Z -> Prop) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a ->
  aview segs H m' a = aview segs H m a.
Proof.
  intros H m m' P a Hfr Ha HP. unfold aview, mbyte, mrestrict. cbv beta.
  rewrite (Hfr (Z_to_bv 64 a)); [reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by exact Ha. exact HP.
Qed.

Lemma srm_mid_apart_of : forall a n b k, 0 < n -> 0 < k ->
  (forall x, a <= x < a + n -> ~ (b <= x < b + k)) -> apart a n b k.
Proof.
  intros a n b k Hn Hk H. unfold apart.
  destruct (Z_le_gt_dec (a + n) b) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (b + k) a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.

Lemma srm_mid_mbyte_present : forall H (m : word -> option byte) a,
  apresent H m a -> exists b, mbyte segs (mrestrict H m) a = Some b.
Proof. intros H m a (Hh & b & Hb). exists b. unfold mbyte, mrestrict. cbv beta. rewrite Hh, Hb. reflexivity. Qed.

(* n bytes the memory holds and may write: a buffer *)
Lemma srm_mid_abuf : forall H (m : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall x, a <= x < a + n -> apresent H m x) -> abuf segs (mrestrict H m) a n.
Proof.
  intros H m a n H0 H1 Hn Hp. exists (abytes_of segs (mrestrict H m) a (Z.to_nat n)).
  rewrite abytes_of_length. split; [lia|]. split.
  - apply abytes_of_abytes; [exact H0 | lia |]. intros i Hi.
    apply (srm_mid_mbyte_present H m). apply Hp. lia.
  - rewrite abytes_of_length. intros i Hi. apply (apresent_writable segs). apply Hp. lia.
Qed.
End g.

(* ==========================================================================
   The cut at the callee's entry, and the call
   ========================================================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.

(* a frame's slot is one the side stack has *)
Lemma srm_mid_fpos : forall ly S (W : world SEGS) mem md cid pos,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> 0 <= pos < fs_frames cid.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros ly S W mem md cid pos (M & _) Hin.
  pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B ly S _ M))) (cid, pos) Hin)
    as [_ X].
  cbn [fst snd] in X. exact X.
Qed.

(* the base at a later state whose memory differs only at F's shadow bytes SH + 4 .. SH + 43 *)
Lemma srm_mid_base_side : forall cx fpos ly3 S3 W3 (ms ms' : machine_state) md md',
  srm_pre SK B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  srm_mid_regs_same (ms_regs ms) (ms_regs ms') ->
  (forall x : word, ~ (srm_SH cx fpos + 4 <= bv_unsigned x < srm_SH cx fpos + 44) -> ms_mem ms' x = ms_mem ms x) ->
  mem_grows (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms')) ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms' md'.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms ms' md md' HPRE HB H1 H2 H3 H4 H5
    (Q2 & Q9 & Q8 & Q18 & Q19 & Q25 & Q26 & Q20 & Q22 & Q3 & Q4 & Q27 & _) Hfr Hgr HJ Hfds Hfs.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (Hsp16 & Hspc & Hsp47 & Hsp1 & Hsp132).
  destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md HPRE HB)
    as (HF4096 & HFc & HF64 & HFapp & HFimg & _).
  pose proof HPRE as ((HJc & _) & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as HARc.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HSHv : srm_SH cx fpos = SHADOW_OFF + srm_F cx fpos / 8) by reflexivity.
  unfold SRM_FB in HFc, HFapp.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  assert (HK : REAC_SERVED_MARK_AK = 9504) by reflexivity.
  pose proof srm_pow as (P47 & P64).
  unfold SHADOW_OFF in HSHv.
  set (P := fun a => srm_SH cx fpos + 4 <= a < srm_SH cx fpos + 44) in *.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ P a ->
            aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha HP; exact (srm_mid_view_frame SEGS (w_H W3) (ms_mem ms) (ms_mem ms') P a Hfr Ha HP)).
  destruct HB as (_ & _ & _ & _ & _ & _ & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18
    & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).
  unfold srm_base; cbv zeta.
  rewrite Q2, Q9, Q8, Q18, Q19, Q25, Q26, Q20, Q22, Q3, Q4, Q27.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact HJ|].
  do 17 (split; [assumption|]).
  (* the saved words, above sp1 on the real stack *)
  split.
  { rewrite <- B24. apply srm_rdword_ext. intros x Hx. apply UN; unfold P; lia. }
  split.
  { intros j Hj. rewrite <- (B25 j Hj). apply srm_rdword_ext. intros x Hx. apply UN; unfold P; lia. }
  (* the flag address in F, F and its shadow present *)
  split.
  { rewrite <- B26. apply srm_rdword_ext. intros x Hx. unfold SRM_FLAGPTR in Hx. apply UN; unfold P; lia. }
  split.
  { intros a Ha. exact (apresent_grows (w_H W3) (ms_mem ms) (ms_mem ms') a Hgr (B27 a Ha)). }
  split.
  { intros a Ha. exact (apresent_grows (w_H W3) (ms_mem ms) (ms_mem ms') a Hgr (B28 a Ha)). }
  split.
  { apply (akept_step SK SEGS B LAWS pa_segs_low (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx)
      W3 (ms_mem ms) W3 (ms_mem ms') (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx)
      (fun a => srm_X0 a \/ aside_rng (sm_lyc cx) SRM_CID fpos a) (fun a => srm_X0 a \/ aside_rng (sm_lyc cx) SRM_CID fpos a)
      P HARc); [lia | lia | exact B29 | exact UN | | intros a Ha; exact Ha |].
    - intros a _ Hp. exact (apresent_grows (w_H W3) (ms_mem ms) (ms_mem ms') a Hgr Hp).
    - intros a Ha. left. right. right. left. unfold in_zr. cbn [fst snd].
      change (fs_frame_bytes SRM_CID / 8) with 64. fold (srm_F cx fpos). fold (srm_SH cx fpos). unfold P in Ha. lia. }
  split; [rewrite Hfds; exact B30|]. split; [rewrite Hfs; exact B31|].
  split; [|exact B33].
  intros a Hro Hno Herr. rewrite <- (B32 a Hro Hno Herr).
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (RELRO_IMG a Hr)]. }
  pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow. apply UN; [lia|]. unfold P. lia.
Qed.

(* the four arguments as aarg reads them *)
Lemma srm_mid_aarg : forall (R : bvmap 5 word) i v,
  getr R (Z_to_bv 5 (10 + i)) = w64 v -> 0 <= v < 2 ^ 64 -> aarg R i = v.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros R i v H Hv. unfold aarg, argZ. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv.
Qed.

(* the callee's write set: g_nl's prefix (a byte of srm_E) and F's two buffers *)
Lemma srm_mid_call_wr : forall cx fpos (R : bvmap 5 word) m a,
  getr R 11 = w64 (srm_kind cx fpos) -> getr R 12 = w64 KIND_CAP ->
  getr R 13 = w64 (srm_alias cx fpos) -> getr R 14 = w64 ALIAS_MAX ->
  4096 <= srm_F cx fpos -> srm_F cx fpos + 512 <= 2 ^ 64 ->
  inFP (reac_link_alias_read_awr R m) a -> srm_E cx a \/ srm_bufb cx fpos a.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos R m a R11 R12 R13 R14 HF0 HF1 (r & Hin & Hr).
  assert (A1 : aarg R 1 = srm_F cx fpos + 32) by (apply srm_mid_aarg; [exact R11 | lia]).
  assert (A2 : aarg R 2 = 32) by (apply srm_mid_aarg; [exact R12 | lia]).
  assert (A3 : aarg R 3 = srm_F cx fpos + 96) by (apply srm_mid_aarg; [exact R13 | lia]).
  assert (A4 : aarg R 4 = 256) by (apply srm_mid_aarg; [exact R14 | lia]).
  unfold reac_link_alias_read_awr in Hin. cbn [In] in Hin. rewrite A1, A2, A3, A4 in Hin. unfold aivl in Hin.
  replace (srm_F cx fpos + 32 =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; lia).
  replace (srm_F cx fpos + 96 =? 0) with false in Hin by (symmetry; apply Z.eqb_neq; lia).
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
  - left. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact Hr].
  - right. left. unfold srm_kind, SRM_KIND, KIND_CAP. lia.
  - right. right. unfold srm_alias, SRM_ALIAS, ALIAS_MAX. lia.
Qed.

(* ==========================================================================
   The callee's apre, read set and Pre at its entry
   ========================================================================== *)
Lemma srm_mid_call_pre : forall cx fpos ly3 S3 W3 (ms : machine_state) md s kbs tab,
  srm_pre SK B cx -> srm_gspan_ok B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms md ->
  amk_nlk_ok SEGS (srm_m0 cx) kbs tab 2 -> astr_arg SEGS (srm_m0 cx) (srm_name cx) (Some s) ->
  getr (ms_regs ms) 10 = w64 (srm_name cx) -> getr (ms_regs ms) 11 = w64 (srm_kind cx fpos) ->
  getr (ms_regs ms) 12 = w64 KIND_CAP -> getr (ms_regs ms) 13 = w64 (srm_alias cx fpos) ->
  getr (ms_regs ms) 14 = w64 ALIAS_MAX -> getr (ms_regs ms) 1 = w64 (BASE + SRM_CUT_RRET) ->
  (forall i, srm_bufsh_off i -> aview SEGS (w_H W3) (ms_mem ms) (srm_SH cx fpos + i) = Some 0) ->
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_LINK_ALIAS_READ_AK 0 REAC_LINK_ALIAS_READ_ASIDE
    (reac_link_alias_read_awr (ms_regs ms) (rdW W3 (ms_mem ms)))
    (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms) md (sm_k cx) (ms_regs ms) /\
  (forall a, reac_link_alias_read_ard SEGS (ms_regs ms) (rdW W3 (ms_mem ms)) a ->
     akb SEGS B ly3 S3 (spZ (ms_regs ms) - REAC_LINK_ALIAS_READ_AK) (spZ (ms_regs ms)) a) /\
  reac_link_alias_read_apre SEGS B (ms_regs ms) (rdW W3 (ms_mem ms)).
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms md s kbs tab HPRE HGS HB HNLK Hnm R10 R11 R12 R13 R14 R1 HZ.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (Hsp16 & Hspc & Hsp47 & Hsp1 & Hsp132).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md HPRE HB) as Hsp.
  destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md HPRE HB)
    as (HF4096 & HFc & HF64 & HFapp & HFimg & HinF & HFaddr & HFL & HFly & Hrow1 & Hrow2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  pose proof HPRE as ((HJc & _) & _ & HP).
  destruct HP as (kbs0 & tab0 & nm0 & k0 & Hsink & Hledg & HNLK0 & Herr0 & _).
  pose proof HNLK as (Hnlk0 & Hwf & Hopen & Hop2 & Hcl2 & Hift0 & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & HJ3 & _ & Hnin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & HFpres & HSHpres & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof (srm_mid_fpos ly3 S3 W3 (ms_mem ms) md SRM_CID fpos HAR3 HinF) as Hfpos.
  assert (HKr : REAC_LINK_ALIAS_READ_AK = 8592) by reflexivity.
  assert (HKe : REAC_CODE_EMIT_AK = 9360) by reflexivity.
  assert (HKm : REAC_SERVED_MARK_AK = 9504) by reflexivity.
  assert (HKc : 0 <= REAC_LINK_ALIAS_READ_AK <= REAC_CODE_EMIT_AK) by lia.
  assert (HX : forall a, srm_X0 a -> srm_E cx a) by (intros a []).
  assert (HFB : SRM_FB = 512) by reflexivity.
  assert (Hnamer : 0 <= srm_name cx < 2 ^ 64).
  { unfold srm_name, aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr (sm_regs cx) (Z_to_bv 5 (10 + 1)))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
  assert (A0 : aarg (ms_regs ms) 0 = srm_name cx) by (apply srm_mid_aarg; [exact R10 | exact Hnamer]).
  assert (A1 : aarg (ms_regs ms) 1 = srm_F cx fpos + 32) by (apply srm_mid_aarg; [exact R11 | lia]).
  assert (A2 : aarg (ms_regs ms) 2 = 32) by (apply srm_mid_aarg; [exact R12 | lia]).
  assert (A3 : aarg (ms_regs ms) 3 = srm_F cx fpos + 96) by (apply srm_mid_aarg; [exact R13 | lia]).
  assert (A4 : aarg (ms_regs ms) 4 = 256) by (apply srm_mid_aarg; [exact R14 | lia]).
  set (F := srm_F cx fpos) in *.
  assert (HFdef : F = srm_F cx fpos) by reflexivity.
  assert (Hkind : srm_kind cx fpos = F + 32) by reflexivity.
  assert (Halias : srm_alias cx fpos = F + 96) by reflexivity.
  assert (HSH : srm_SH cx fpos = SHADOW_OFF + F / 8) by reflexivity.
  clearbody F.
  (* the image's place, against F *)
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms) md SRM_CID fpos HAR3 HinF) as Hoff.
  rewrite HFaddr in Hoff. change (fs_frame_bytes SRM_CID) with 512 in Hoff.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
  pose proof (ts_errno B TB) as Herrv. unfold TFIB_ERRNO in Herrv.
  (* a byte the entry's read set holds is not a byte of F *)
  assert (HnotF : forall x, akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) x ->
                   ~ (F <= x < F + 512)).
  { intros x Hx Hr.
    assert (Hns : ~ aside_rng (sm_lyc cx) SRM_CID fpos x).
    { eapply akb_not_side; try eassumption; first [exact pa_img_range | unfold SRM_CID; lia]. }
    apply Hns. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes SRM_CID) with 512.
    rewrite HFdef in Hr. unfold srm_F in Hr. exact Hr. }
  (* the name at the cut *)
  assert (Hspan1 : forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
            akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
    by (intros a Ha; exact (proj1 HGS s a Hnm Ha)).
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md REAC_LINK_ALIAS_READ_AK s
              HPRE HB HX HKc Hnm Hspan1) as (Hnc & Hnrt & Hnlen & Hngnl & Hnsink & Hnerr & Hnmk).
  pose proof Hnrt as (Hn0 & Hn31 & Hnam & Hnra & Hnhull & Hntl & Hnfr).
  assert (HnF : forall x, srm_name cx <= x < srm_name cx + (Z.of_nat (length s) + 1) -> ~ (F <= x < F + 512)).
  { intros x Hx. apply HnotF. apply Hspan1. unfold srm_gspan.
    pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)). lia. }
  (* the kernel and the table at the cut *)
  destruct (srm_mid_kern_at SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 ms md kbs tab HPRE HB HNLK)
    as (Hnlk3 & Hift3).
  assert (HGT : forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_SIZE ->
            aview SEGS (w_H W3) (ms_mem ms) x = aview SEGS (w_H (sm_W cx)) (sm_memc cx) x)
    by (intros x Hx; exact (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md x
          HPRE HB HX Hx)).
  (* a table entry at the cut is the entry's: its slot, the in-range pointer, its string *)
  assert (HTE : forall i n2 ix, nth_error tab i = Some (n2, ix) ->
     exists p0, au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 /\
       au64_at SEGS (rdW W3 (ms_mem ms)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 /\
       acstr_at SEGS (srm_m0 cx) p0 n2 /\ p0 <> 0 /\ 0 <= p0 /\ p0 + Z.of_nat (length n2) + 1 <= 2 ^ 64).
  { intros i n2 ix Hi. pose proof Hift0 as (_ & Hl & Ht).
    destruct (Ht i n2 ix Hi) as (_ & p0 & Hp0 & Hp00 & Hc0 & _).
    assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    exists p0. split; [exact Hp0|]. split.
    - apply (srm_mid_val_mem SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms)); [|exact Hp0].
      intros y Hy. apply HGT. unfold NK_IF_NAME, NK_SIZE in *. lia.
    - split; [exact Hc0|]. split; [exact Hp00|].
      pose proof (srm_acstr_range SEGS _ _ _ Hc0). lia. }
  (* the facts of an in-range table entry at the cut *)
  assert (HTF : forall i n2 ix p0, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 ->
     au64_at SEGS (rdW W3 (ms_mem ms)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 ->
     acstr_at SEGS (srm_m0 cx) p0 n2 -> 0 <= p0 < 2 ^ 64 ->
     acstr_at SEGS (rdW W3 (ms_mem ms)) p0 n2 /\
     astr_rt_ok SEGS (ms_regs ms) REAC_LINK_ALIAS_READ_AK (rdW W3 (ms_mem ms)) p0 n2 /\
     achk SEGS (rdW W3 (ms_mem ms)) p0 (Z.of_nat (length n2) + 1) /\
     apart_gnl LA_G_NL p0 (Z.of_nat (length n2) + 1) /\ apart (as_errno B) 4 p0 (Z.of_nat (length n2) + 1) /\
     (forall x, p0 <= x < p0 + (Z.of_nat (length n2) + 1) -> ~ (F <= x < F + 512))).
  { intros i n2 ix p0 Hi Hp0 Hp3 Hc0 Hpr.
    assert (Hspan2 : forall a, p0 <= a <= p0 + Z.of_nat (length n2) ->
              akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
      by (intros a Ha; exact (proj2 HGS kbs tab i n2 ix p0 a Hnlk0 Hift0 Hi Hp0 Hc0 Ha)).
    destruct (srm_table_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md REAC_LINK_ALIAS_READ_AK
                kbs tab i n2 ix p0 HPRE HB HX HKc HNLK Hi Hp3 Hpr Hspan2)
      as (Htc & Htrt & Htchk & _ & Htgnl & Hterr & _ & _).
    split; [exact Htc|]. split; [exact Htrt|]. split; [exact Htchk|]. split; [exact Htgnl|].
    split; [exact Hterr|].
    intros x Hx. apply HnotF. apply Hspan2. unfold srm_gspan.
    pose proof (Z.mod_pos_bound (p0 + Z.of_nat (length n2)) 8 ltac:(lia)). lia. }
  split; [|split].
  (* ---- apre ---- *)
  - apply (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md
             REAC_LINK_ALIAS_READ_AK REAC_LINK_ALIAS_READ_ASIDE _ HPRE HB HX HKc).
    + rewrite R1. apply ret_ok_codeptr_v; [unfold SRM_CUT_RRET, AF_reac_served_mark; lia | reflexivity].
    + unfold raZ. rewrite R1. pose proof pa_B_ok as (HB0 & HB1 & _).
      pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
      unfold w64. rewrite unsigned_lit_small by (unfold SRM_CUT_RRET, AF_reac_served_mark; lia).
      unfold SRM_CUT_RRET, AF_reac_served_mark. lia.
    + intros cd Hcd. unfold REAC_LINK_ALIAS_READ_ASIDE in Hcd. cbn [In] in Hcd.
      destruct Hcd as [<- | [<- | []]]; exists 1; cbn [fst snd]; unfold REAC_SERVED_MARK_ASIDE; cbn [In];
        split; [tauto | reflexivity | tauto | reflexivity].
    + intros a Ha. exact (srm_mid_call_wr cx fpos (ms_regs ms) _ a R11 R12 R13 R14 ltac:(rewrite <- HFdef; lia) ltac:(rewrite <- HFdef; lia) Ha).
  (* ---- the read set ---- *)
  - intros a [(Hn0' & s' & Hc' & Ha) | (bs & tab' & i & n2 & ix & p & Hbs & Ht' & Hi & Hp & Hc & Ha)].
    + rewrite A0 in Hc', Ha.
      pose proof (acstr_at_unique SEGS _ _ _ _ Hc' Hnc) as Es. subst s'.
      apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md
               REAC_LINK_ALIAS_READ_AK a HPRE HB HKc).
      apply Hspan1. unfold srm_gspan.
      pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)). lia.
    + pose proof (anlk_at_unique SEGS _ _ _ _ Hbs Hnlk3) as Eb. subst bs.
      pose proof (aiftab_at_unique SEGS _ _ _ _ Ht' Hift3) as Et. subst tab'.
      destruct (HTE i n2 ix Hi) as (p0 & Hp0 & Hp03 & Hc0 & Hp00 & Hp0lo & Hp0hi).
      assert (Hpr : 0 <= p < 2 ^ 64)
        by (pose proof (srm_acstr_range SEGS _ _ _ Hc); lia).
      pose proof (srm_au64_unique SEGS _ _ _ _ Hp Hp03) as Hmod.
      rewrite (Z.mod_small p) in Hmod by exact Hpr. rewrite (Z.mod_small p0) in Hmod by lia. subst p0.
      apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md
               REAC_LINK_ALIAS_READ_AK a HPRE HB HKc).
      apply (proj2 HGS kbs tab i n2 ix p a Hnlk0 Hift0 Hi Hp0 Hc0). unfold srm_gspan.
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length n2)) 8 ltac:(lia)). lia.
  (* ---- the Pre ---- *)
  - exists kbs, tab, (Some s).
    rewrite A0, A1, A2, A3, A4.
    destruct (srm_errno_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md REAC_LINK_ALIAS_READ_AK
                HPRE HB HKc) as (He1 & He2 & He3 & He4 & He5 & He6 & _).
    destruct (srm_gnl_sh_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md HB) as (Hg1 & Hg2).
    assert (HK3 : F + 32 <> 0) by lia. assert (HA3 : F + 96 <> 0) by lia.
    assert (Hwin : spZ (ms_regs ms) - REAC_LINK_ALIAS_READ_AK >= F + 512) by (rewrite Hsp; lia).
    assert (Hgnl : forall q n, F <= q -> q + n <= F + 512 -> 0 <= n -> apart_gnl LA_G_NL q n).
    { intros q n H1 H2 H3. unfold apart_gnl, LA_G_NL, NK_SIZE. lia. }
    assert (Herrf : forall q n, F <= q -> q + n <= F + 512 -> apart (as_errno B) 4 q n).
    { intros q n H1 H2. unfold apart. rewrite Herrv. lia. }
    (* shadow facts of a buffer of F whose shadow is 0 *)
    assert (HRA : forall q n, F + 32 <= q -> q + n <= F + 64 \/ (F + 96 <= q /\ q + n <= F + 352) ->
              range_addressable (ard SEGS (rdW W3 (ms_mem ms))) SHADOW_OFF q n).
    { intros q n Hq Hn x Hx. exists 0. split; [|left; reflexivity].
      assert (HFx : x / 8 = F / 8 + (x - F) / 8).
      { assert (EF : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 64 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia));
          lia).
        replace x with (8 * (F / 8) + (x - F)) at 1 by lia. rewrite Z.mul_comm, Z.div_add_l by lia. lia. }
      assert (Hoff8 : srm_bufsh_off ((x - F) / 8)).
      { unfold srm_bufsh_off.
        destruct Hn as [Hn | Hn]; [left | right]; split;
          first [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
      pose proof (HZ _ Hoff8) as Hz. rewrite HSH in Hz. unfold shadow_of_addr.
      replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + (x - F) / 8) by lia. exact Hz. }
    assert (HHV : forall q n, F <= q -> q + n <= F + 512 -> 0 < n ->
              shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms))) q n).
    { intros q n H1 H2 H3.
      apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md SRM_CID fpos q n HAR3 HinF);
        rewrite ?HFaddr; [lia | change (fs_frame_bytes SRM_CID) with 512; lia | lia]. }
    assert (HAM : forall q n, F <= q -> q + n <= F + 512 -> amem_range q n).
    { intros q n H1 H2. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia. }
    split; [exact Hnlk3|]. split; [exact Hwf|]. split; [exact Hopen|]. split; [lia|]. split; [lia|].
    split; [exact Hift3|]. split; [exact Hg1|]. split; [exact Hg2|].
    split; [split; [exact He1|]; split; [exact He2|]; split; [exact He3|]; split; [exact He5 | exact He6]|].
    split; [split; [exact (proj1 Hnm) | exact Hnc]|].
    split; [intros _ _; apply (srm_mid_abuf SEGS); [lia | lia | lia | intros x Hx; apply HFpres; lia]|].
    split; [intros _ _; apply (srm_mid_abuf SEGS); [lia | lia | lia | intros x Hx; apply HFpres; lia]|].
    (* the table strings *)
    split.
    { intros i n2 ix p Hi Hp.
      destruct (HTE i n2 ix Hi) as (p0 & Hp0 & Hp03 & Hc0 & Hp00 & Hp0lo & Hp0hi).
      pose proof (srm_au64_unique SEGS _ _ _ _ Hp Hp03) as Hmod.
      rewrite (Z.mod_small p0) in Hmod by lia.
      pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as Hdm. rewrite Hmod in Hdm.
      destruct (Z.eq_dec (p / 2 ^ 64) 0) as [Hq0 | Hq0].
      - assert (Ep : p = p0) by lia. subst p.
        destruct (HTF i n2 ix p0 Hi Hp0 Hp03 Hc0 ltac:(lia)) as (_ & Htrt & Htchk & Htgnl & Hterr & HtF).
        pose proof Htrt as (Ht0 & Ht31 & _ & _ & _ & Httl & Htfr).
        split; [exact Htfr|]. split; [exact Htgnl|]. split; [exact Hterr|].
        split; [intros _ _; apply srm_mid_apart_of; [lia | lia |]; intros x Hx Hk; apply (HtF x Hx); lia|].
        split; [intros _ _; apply srm_mid_apart_of; [lia | lia |]; intros x Hx Hk; apply (HtF x Hx); lia|].
        intros _. split; [lia|]. split; [lia | split; [exact Htchk | exact Httl]].
      - assert (Hfar : p + (Z.of_nat (length n2) + 1) <= 0 \/ 2 ^ 64 <= p) by lia.
        assert (Hsp64 : spZ (ms_regs ms) < 2 ^ 64) by (rewrite Hsp; lia).
        split; [unfold apart_frame; lia|]. split; [unfold apart_gnl, LA_G_NL, NK_SIZE; lia|].
        split; [unfold apart; rewrite Herrv; lia|].
        split; [intros _ _; unfold apart; lia|]. split; [intros _ _; unfold apart; lia|].
        intros Hr. exfalso. lia. }
    (* the name against the buffers *)
    split.
    { intros s0 Es0. injection Es0 as <-.
      split; intros _ _; apply srm_mid_apart_of; try lia; intros x Hx Hk; apply (HnF x Hx); lia. }
    split; [intros _ _ _ _; unfold apart; lia|].
    split; [intros _; apply Herrf; lia|]. split; [intros _; apply Herrf; lia|].
    (* the name's own facts *)
    split.
    { intros s0 Es0. injection Es0 as <-.
      split; [exact Hnfr|]. split; [unfold apart_gnl in *; lia|]. split; [lia|].
      split; [split; [unfold amem_range in *; lia | split; [exact Hnra | exact Hnhull]] | exact Hntl]. }
    split; [intros _; split; [unfold apart_frame; lia | apply Hgnl; lia]|].
    split; [intros _; split; [unfold apart_frame; lia | apply Hgnl; lia]|].
    split.
    { intros _ _. split; [apply HAM; lia|]. split; [apply HRA; lia | apply HHV; lia]. }
    { intros _ _. split; [apply HAM; lia|]. split; [apply HRA; lia | apply HHV; lia]. }
Qed.

(* ==========================================================================
   The RRET cut, from the callee's post
   ========================================================================== *)
Lemma srm_mid_rret : forall cx fpos ly3 S3 W3 (ms : machine_state) md s kbs tab gbs k0 ly4 S4 W4 regs4 mem4 md4,
  srm_pre SK B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms md -> srm_ent cx s kbs tab gbs k0 ->
  getr (ms_regs ms) 10 = w64 (srm_name cx) -> getr (ms_regs ms) 11 = w64 (srm_kind cx fpos) ->
  getr (ms_regs ms) 12 = w64 KIND_CAP -> getr (ms_regs ms) 13 = w64 (srm_alias cx fpos) ->
  getr (ms_regs ms) 14 = w64 ALIAS_MAX -> getr (ms_regs ms) 1 = w64 (BASE + SRM_CUT_RRET) ->
  getr (ms_regs ms) 21 = w64 (-22) ->
  getr (ms_regs ms) 23 = w64 (srm_alias cx fpos) -> getr (ms_regs ms) 24 = w64 (srm_kind cx fpos) ->
  (forall i, srm_bufsh_off i -> aview SEGS (w_H W3) (ms_mem ms) (srm_SH cx fpos + i) = Some 0) ->
  srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4 ->
  aregs_preserved (ms_regs ms) regs4 ->
  akept SEGS B ly3 S3 W3 (ms_mem ms) W4 mem4 (spZ (ms_regs ms) - REAC_LINK_ALIAS_READ_AK) (spZ (ms_regs ms))
    (fun a => inFP (reac_link_alias_read_awr (ms_regs ms) (rdW W3 (ms_mem ms))) a) ->
  reac_link_alias_read_apost SEGS (ms_regs ms) (rdW W3 (ms_mem ms)) regs4 (rdW W4 mem4) ->
  exists s0 kbs0 tab0 gbs0 k00 kbs1,
    let R := srm_R s0 kbs0 tab0 in
    ms_pc_val (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) = w64 (BASE + SRM_CUT_RRET) /\
    srm_ent cx s0 kbs0 tab0 gbs0 k00 /\
    getr regs4 10 = w64 (r_rc R) /\ getr regs4 21 = w64 (-22) /\
    getr regs4 23 = w64 (srm_alias cx fpos) /\ getr regs4 24 = w64 (srm_kind cx fpos) /\
    srm_kern (rdW W4 mem4) kbs0 kbs1 tab0 (r_state R) (r_reqs R) 1 /\
    srm_bufs cx fpos W4 mem4 R /\
    amarks_at SEGS (rdW W4 mem4) (srm_mk cx) gbs0 /\
    amemfile_k SEGS (rdW W4 mem4) (sm_sink cx) k00 /\
    srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms md s kbs tab gbs k0 ly4 S4 W4 regs4 mem4 md4 HPRE HB HENT R10 R11 R12 R13 R14 R1 R21
    R23 R24 HZ HB4 HAP HK HPOST.
  pose proof HENT as (Hmk & Hnm & Hs0 & HNLK & Hg0 & Hgw & HMF & Hk0).
  destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md HPRE HB)
    as (HF4096 & HFc & HF64 & HFapp & HFimg & HinF & HFaddr & HFL & HFly & Hrow1 & Hrow2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HX : forall a, srm_X0 a -> srm_E cx a) by (intros a []).
  unfold SRM_FB in HFc, HFapp, HFimg.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  assert (Hnamer : 0 <= srm_name cx < 2 ^ 64).
  { unfold srm_name, aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr (sm_regs cx) (Z_to_bv 5 (10 + 1)))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
  assert (A0 : aarg (ms_regs ms) 0 = srm_name cx) by (apply srm_mid_aarg; [exact R10 | exact Hnamer]).
  assert (A1 : aarg (ms_regs ms) 1 = srm_F cx fpos + 32) by (apply srm_mid_aarg; [exact R11 | lia]).
  assert (A2 : aarg (ms_regs ms) 2 = 32) by (apply srm_mid_aarg; [exact R12 | lia]).
  assert (A3 : aarg (ms_regs ms) 3 = srm_F cx fpos + 96) by (apply srm_mid_aarg; [exact R13 | lia]).
  assert (A4 : aarg (ms_regs ms) 4 = 256) by (apply srm_mid_aarg; [exact R14 | lia]).
  set (F := srm_F cx fpos) in *.
  assert (HFdef : F = srm_F cx fpos) by reflexivity.
  assert (HSH : srm_SH cx fpos = SHADOW_OFF + F / 8) by reflexivity.
  clearbody F.
  (* the call's memory: the entry's kernel, name, marks and FILE *)
  destruct (srm_mid_kern_at SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 ms md kbs tab HPRE HB HNLK)
    as (Hnlk3 & Hift3).
  destruct (srm_mid_blocks_at SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 ms md HPRE HB) as (HMF3 & HMK3).
  assert (Hnm3 : astr_arg SEGS (rdW W3 (ms_mem ms)) (aarg (ms_regs ms) 0) (Some s)).
  { rewrite A0. destruct Hnm as (Hn0 & Hc). split; [exact Hn0|].
    apply (srm_mid_acstr SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms)); [|exact Hc].
    intros x Hx. exact (srm_name_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md s x
                          HPRE HB HX (conj Hn0 Hc) Hx). }
  destruct (HPOST kbs tab (Some s) Hnlk3 Hift3 Hnm3) as (Hrc & (kbs1 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9
    & K10 & K11 & K12 & K13 & K14 & K15 & _) & Hck & Hca & Hbk & Hba).
  rewrite A1, A2, A3, A4 in *.
  change (read_lib tab (Some s) 32 256 (nk_sent kbs) (nk_kstate kbs)) with (srm_R s kbs tab) in *.
  (* the blocks of the call's state and of the return state *)
  pose proof HB as (_ & _ & _ & _ & _ & HJ3 & _ & _ & _ & Hperm3 & _).
  pose proof HB4 as (_ & _ & _ & _ & _ & HJ4 & _ & _ & _ & Hperm4 & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof HPRE as (_ & _ & HP).
  destruct HP as (kbs0 & tab0 & nm0 & k1 & Hsink & Hledg & _).
  assert (Hin3 : forall x, In x (ablocks B (sm_lyc cx) (sm_Sc cx)) -> In x (ablocks B ly3 S3))
    by (intros x Hx; exact (Permutation_in x (Permutation_sym Hperm3) Hx)).
  assert (Hin4 : forall x, In x (ablocks B (sm_lyc cx) (sm_Sc cx)) -> In x (ablocks B ly4 S4))
    by (intros x Hx; exact (Permutation_in x (Permutation_sym Hperm4) Hx)).
  (* a heap block byte of the entry is outside the callee's write set *)
  assert (HNE : forall b m a, In (b, m) (ablocks B (sm_lyc cx) (sm_Sc cx)) -> b <= a < b + req_size m ->
            ~ inFP (reac_link_alias_read_awr (ms_regs ms) (rdW W3 (ms_mem ms))) a).
  { intros b m a Hbm Ha (r & Hr & Hra).
    pose proof (srm_blk_noside SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms md b m a HB Hbm Ha)
      as Hns.
    pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms) md b m HAR3 (Hin3 _ Hbm)) as Hoff.
    unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
    unfold reac_link_alias_read_awr in Hr. rewrite A1, A2, A3, A4 in Hr. unfold aivl in Hr.
    replace (F + 32 =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia).
    replace (F + 96 =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia).
    cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra.
    - unfold LA_G_NL, NK_N_SENT in Hra. lia.
    - apply Hns. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes SRM_CID) with 512.
      rewrite HFdef in Hra. unfold srm_F in Hra. lia.
    - apply Hns. left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes SRM_CID) with 512.
      rewrite HFdef in Hra. unfold srm_F in Hra. lia. }
  exists s, kbs, tab, gbs, k0, kbs1. cbv zeta.
  split; [cbn [ms_pc_val mkst]; exact R1|].
  split; [exact HENT|].
  split; [exact Hrc|].
  assert (Hcs : forall r, 18 <= r <= 27 -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
    by (intros r Hr; apply HAP; unfold acallee_saved; lia).
  split; [rewrite <- R21; exact (Hcs 21 ltac:(lia))|].
  split; [rewrite <- R23; exact (Hcs 23 ltac:(lia))|].
  split; [rewrite <- R24; exact (Hcs 24 ltac:(lia))|].
  split.
  { split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|].
    split; [exact K6|]. split; [exact K7|]. split; [exact K8|]. split; [exact K9|]. split; [exact K10|].
    split; [exact K11|]. split; [exact K12|]. split; [exact K13|]. split; [exact K14 | exact K15]. }
  split.
  { assert (Hkd : srm_kind cx fpos = F + 32) by (rewrite HFdef; reflexivity).
    assert (Had : srm_alias cx fpos = F + 96) by (rewrite HFdef; reflexivity).
    unfold srm_bufs. rewrite Hkd, Had.
    split; [exact (Hck ltac:(lia) ltac:(lia))|]. split; [exact (Hca ltac:(lia) ltac:(lia))|].
    split; [exact (Hbk ltac:(lia) ltac:(lia))|]. split; [exact (Hba ltac:(lia) ltac:(lia))|].
    intros i Hi. rewrite <- (HZ i Hi). pose proof HK as (_ & _ & _ & KF & _).
    apply (KF SRM_CID fpos); [exact HinF | |].
    - right. rewrite HFaddr. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes SRM_CID / 8) with 64.
      rewrite HSH. unfold shadow_addr, srm_bufsh_off in *. lia.
    - intros (r & Hr & Hra). unfold reac_link_alias_read_awr in Hr. rewrite A1, A2, A3, A4 in Hr. unfold aivl in Hr.
      replace (F + 32 =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia).
      replace (F + 96 =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia).
      assert (HF8 : F / 8 < 17592186044352)
        by (apply Z.div_lt_upper_bound; [lia | change (8 * 17592186044352) with 140737488354816; lia]).
      assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
      cbn [In] in Hr. rewrite HSH in Hra. unfold srm_bufsh_off in Hi.
      destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra;
        unfold SHADOW_OFF, LA_G_NL, NK_N_SENT in *; lia. }
  split.
  { destruct (Hledg Hmk) as (Hmk1 & _). pose proof (HMK3 Hmk gbs Hg0) as Hg3.
    eapply xfer_amarks; try eassumption; [apply Hin3; exact Hmk1 | apply Hin4; exact Hmk1 |].
    intros a Ha. apply (HNE (srm_mk cx) MK_SIZE a Hmk1). change (req_size MK_SIZE) with MK_SIZE. exact Ha. }
  split.
  { pose proof (HMF3 k0 HMF) as Hf3.
    eapply xfer_amemfile_k; try eassumption; [apply Hin3; exact Hsink | apply Hin4; exact Hsink |].
    intros a Ha. apply (HNE (sm_sink cx) AMF_BLOCK a Hsink). change (req_size AMF_BLOCK) with AMF_BLOCK. exact Ha. }
  exact HB4.
Qed.

End b.
End a.
