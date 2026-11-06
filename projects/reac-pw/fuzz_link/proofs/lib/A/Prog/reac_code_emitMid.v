(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 695 of its 778 lines of code are new or changed and 1468 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_code_emitEntry.v; 397 of its 516 lines of code are new or changed and 659 lines of the source are left out. *)
(* reac_code_emit (fuzz_link.asan 0x89be4) on image A: the MIDDLE phase of its walk, `em_mid` of
   lib/A/Prog/reac_code_emitDefs.v. From the cut EM_f1_ra (+0x120, wrapper_fprintf returned) the code
     +0x120          sb zero, 4(s5): F's shadow byte 4 := 0 (the va_list slot F + 0x20 addressable)
     +0x124..+0x12c  a0 := s0 (the va_list: the four vararg words the prologue stored at sp0 - 0x20); sd a0, 0x20(s6);
                     ld a2, 0x20(s6)
     +0x130..+0x134  a0 := s4 (the stream), a1 := s2 (the caller's format)
     +0x138          jal wrapper_vfprintf (V1)
   up to the cut EM_v1_ra (+0x13c). The run is the PLAIN run of lib/A/Prog/LinkWalkSide.v (`paj_run_call_plain_x`),
   whose state has two writable windows: F's eight shadow bytes and F's va_list slot. The call is
   lib/A/Prog/LinkWalkMkPrintf.v `aj_gx_printf_mf_at` over the vfprintf contract (Section hypothesis VFPR, the form of
   lib/A/Rt/LinkVfTop.v link_vfprintf_mf_rel); its family premise is lib/A/Prog/LinkWalkMkFmt.v link_vf_FF_of_c over
   the caller's format and %s strings, moved from the call's memory by lib/A/Prog/reac_code_emitMove.v.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkVfInst LinkPfPiece.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkPrintf LinkWalkMkFmt LinkWalkMkFile LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c reac_code_emitDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_code_emitMove.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require RT_pf_sh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at the cut: atoms 0..31 are the registers at the cut (s5 = F's shadow, atom 21; s6 = F,
   atom 22); two regions: F's shadow (writable) and F's va_list slot F + 0x20 (writable) ---- *)
Definition md_SH : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 8 [].
Definition md_FR : YP09.region := YP09.mkRegion (Some 22%nat) 32 40 32 40 [].
Definition md_ss0 : sstate := mkSS EM_f1_ra sr_atoms [md_SH; md_FR] None (mkFacts [] [] []).

Lemma md_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma md_side_unfold : forall ly fpos a,
  aside_rng ly 0 fpos a <->
  (frame_addr ly 0 fpos <= a < frame_addr ly 0 fpos + 64) \/
  (SHADOW_OFF + frame_addr ly 0 fpos / 8 <= a < SHADOW_OFF + frame_addr ly 0 fpos / 8 + 8) \/
  a = flag_addr ly 0 fpos.
Proof.
intros ly fpos a. unfold aside_rng, in_zr, frame_rng, shadow_addr. cbn [fst snd].
change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. tauto.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
(* the certificate of link's image: lib/A/AF0m.v PcapSyms, discharged at link's B by AD2l.PcapB_syms *)
Hypothesis TB : AF0m.PcapSyms B.
(* the segments the listing is certified against (LinkImgInst.v pi_link_segs) *)
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.
(* the read-only window is image bytes (PcapRelroA.v pcap_relro_in_image at tfibsegs) *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
(* wrapper_vfprintf (0x4307c): lib/A/Rt/LinkVfTop.v link_vfprintf_mf_rel at the walk's pa_segs / B *)
Hypothesis VFPR : forall fx' : YK11.FPState,
  @avfprintf_mf_realizes fx' rc pa_segs B link_amf PCAP_RLO PCAP_RHI link_vf_FF LVF_STK LinkMfDefs.LA_GOT_GUARD
    LinkMfDefs.LA_GUARD LA_W_VFPRINTF.

Lemma md_hvfpr : pa_sigma LS___interceptor_trampoline_vfprintf = LA_W_VFPRINTF.
Proof. rewrite (lv_sigma HV). reflexivity. Qed.

Lemma md_cs : forall z : Z,
  ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%bool = true ->
  acallee_saved z.
Proof.
  intros z H. unfold acallee_saved.
  rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.

Lemma md_getr_lit : forall (regs : bvmap 5 word) (r : bv 5), getr regs (Z_to_bv 5 (bv_unsigned r)) = getr regs r.
Proof. intros regs r. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma md_sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply wvb_fds_fs. Qed.

Theorem em_mid : (forall fx' : YK11.FPState, em_from SK B fx' (em_v1_inv B)) -> em_from SK B fx (em_f1_inv B).
Proof.
intros NEXT fxe cx fpos k2 ly3 S3 W3 ms3 md3 Hfxr Hfrm HBASE HJ3 HGI.
pose proof HBASE as HBASE0.
pose proof (fxr_frm0 fxe fx Hfrm Hfxr) as Hfrm0.
(* the post at the entry's FP state from the post at the current one; then fxe leaves the context, so the
   FPState instances below resolve to fx (the next phase is applied at fxe := fx) *)
unfold em_post.
eapply SRr_mono; [| intros W' c' _ HQ;
  exact (apostF_lift SK pa_segs B fxe fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfxr HQ)].
clear Hfxr Hfrm. clear fxe.
unfold em_f1_inv in HGI.
destruct HGI as ((Hpc & Zrsv & Zsvc & Zrom & Zfrg & Zfcsr) & (R2 & R8 & R9 & R18 & R20 & R3 & R4 & R24 & R25 & R26 & R27) &
  (R19 & R22 & R21 & R23) & (Hra & Hsav) & Hva & Hflagw & HF4096 & HFceil &
  (Ek2 & Hperm & HfsS3 & Hfrs3 & Hnin & Hfa3 & Hfl3 & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1) & Hfds3 & Hfs3) &
  (HK3 & HROD3 & _) & Hfile).
unfold em_flagw, em_at in Hflagw. unfold em_at in Hra, Hsav. unfold em_va, em_at in Hva.
pose proof HBASE as (HPRE & HRD & Hf0 & Hfp0 & HFIN & HMF & HBLK & HFIT & HFMT & _).
pose proof HPRE as (HJ & HGX & HROD & Hraok & Hra4 & Hgp & Htp & Hsp16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as (ACv & _).
set (regs := e_regs cx) in *. set (R := ms_regs ms3) in *. set (m3 := ms_mem ms3) in *.
set (lyc := e_lyc cx) in *. set (Sc := e_Sc cx) in *. set (Wc := e_W cx) in *. set (memc := e_memc cx) in *.
change (e_spe cx) with (spZ regs) in *.
set (sp := spZ regs) in *.
set (F := eF cx fpos) in *. set (FL := eFL cx fpos) in *. set (SH := eSH cx fpos) in *.
change EM_CID with 0 in *.
assert (EF0 : frame_addr lyc 0 fpos = F) by reflexivity.
assert (EFL0 : flag_addr lyc 0 fpos = FL) by reflexivity.
assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
change (fs_frame_bytes 0) with 64 in HFceil.
subst k2.
(* ---- the journal's window and the stack ---- *)
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & _) & _).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hspr : 0 <= sp < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu).
assert (HKv : REAC_CODE_EMIT_AK = 9360) by reflexivity.
rewrite HKv in Hwlo.
assert (HspK : alloc_ceiling <= sp - REAC_CODE_EMIT_AK) by (rewrite HKv; lia).
assert (Hsp47 : sp <= 2 ^ 47) by lia.
(* ---- the frame and its shadow ---- *)
pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (HinF : In (0, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (HinF3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF : frame_addr ly3 0 fpos = F) by (rewrite Hfa3; reflexivity).
assert (EFL : flag_addr ly3 0 fpos = FL) by (rewrite Hfl3; reflexivity).
destruct (frames_bounds pa_segs B LAWS _ _ _ _ _ 0 fpos HAR1 HinF) as (_ & _ & HFapp).
rewrite EF0 in HFapp. change (fs_frame_bytes 0) with 64 in HFapp.
pose proof (frame_al64 pa_segs B _ _ _ _ _ 0 fpos HAR1 HinF) as (HFal & _ & _). rewrite EF0 in HFal.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 HinF3) as (_ & _ & HFpres & HFSpres).
rewrite EF in HFpres, HFSpres. change (fs_frame_bytes 0) with 64 in HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct HFapp as (_ & HFapp').
assert (HF8 : 0 <= F / 8 /\ F / 8 + 8 <= (F + 64) / 8).
{ split; [apply Z.div_pos; lia|]. replace (F + 64) with (F + 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8c : (F + 64) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in HF8c.
assert (HSHb : SHADOW_OFF <= SH /\ SH + 8 <= SHADOW_OFF + 2 ^ 44) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (HSHr : 0 <= SH < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (UF : bv_unsigned (w64 F) = F) by (unfold w64; apply unsigned_lit_small; lia).
assert (USH : bv_unsigned (w64 SH) = SH) by (unfold w64; apply unsigned_lit_small; lia).
set (s0 := sp + EM_VA) in *.
assert (Us0 : bv_unsigned (w64 s0) = s0) by (unfold w64, s0, EM_VA; apply unsigned_lit_small; lia).
destruct (sp1_facts (sp - REAC_CODE_EMIT_AFRAME) ltac:(unfold REAC_CODE_EMIT_AFRAME; lia)
  ltac:(unfold REAC_CODE_EMIT_AFRAME; rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
change (32 * ((sp - REAC_CODE_EMIT_AFRAME) / 32)) with (e_sp1 cx) in Hsp1r, Hsp1al32, Hsp1al16.
unfold REAC_CODE_EMIT_AFRAME in Hsp1r.
set (sp1 := e_sp1 cx) in *.
assert (Usp1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; apply unsigned_lit_small; lia).
(* ---- the environment: the registers at the cut ---- *)
set (E := Eimg (Ereg R [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg R []) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr R r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (E21 : ew E 21 = w64 SH) by (rewrite (EREG 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 F) by (rewrite (EREG 22%nat 22%bv eq_refl); exact R22).
assert (U21 : bv_unsigned (ew E 21) = SH) by (rewrite E21; exact USH).
assert (U22 : bv_unsigned (ew E 22) = F) by (rewrite E22; exact UF).
(* ---- the symbolic state at the cut ---- *)
assert (HS : st_ok_pi pa_segs VAL E md_ss0 (restrict (w_H W3) ms3)).
{ rewrite (md_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold md_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold region_ok, md_SH, md_FR;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U21. pose proof HSHb as HSHb'. unfold SHADOW_OFF in HSHb'. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable pa_segs).
      replace (SH + o) with (shadow_addr F + o) by (rewrite HSHeq; unfold shadow_addr; lia).
      exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U22. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable pa_segs). exact (proj1 (HFpres (F + o) ltac:(lia))).
  - apply pairwise_disjoint_of_extents.
    unfold md_SH, md_FR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U21, U22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HSHeq in *. unfold SHADOW_OFF in *. unfold kLowMemEnd in *.
    repeat split; first [ (left; lia) | (right; lia) | lia
                        | (destruct HFapp' as [? | (? & ?)]; [left | left]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [left | right]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [right | left]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [right | right]; lia)
                        | (lazymatch goal with |- ?g => idtac "DISJ" g end; fail) ].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. first [exact I | constructor]. }
clearbody E.
(* ---- +0x120 .. +0x138: F's shadow byte 4, the va_list into F + 0x20 and back, the three arguments (plain run) ---- *)
pose (RUNP := paj_run_call_plain_x SK B LAWS (e_G cx) HGX (e_XO cx) (e_OUT cx)).
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNP with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, PRS_call ?sf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
      eapply (RUNP Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ3);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem md_ss0].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val md_SH] in Ha. rewrite U21 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 fpos a HJ3
      (or_introl eq_refl)).
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8.
    rewrite HSHeq in Ha. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val md_FR] in Ha. rewrite U22 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 fpos a HJ3
      (or_introl eq_refl)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia. }
  apply awr_ok_x_nil. }
cbv beta. intros ms4 mat4 HS4 HJ4 HF4 HFr4 HG4.
cbn [ms_mem mkst] in HF4, HFr4, HG4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
(* the registers at the call *)
sreg HS4 (1%bv : bv 5) Q1. sreg HS4 (2%bv : bv 5) Q2. sreg HS4 (3%bv : bv 5) Q3. sreg HS4 (4%bv : bv 5) Q4.
sreg HS4 (8%bv : bv 5) Q8. sreg HS4 (9%bv : bv 5) Q9. sreg HS4 (10%bv : bv 5) Q10. sreg HS4 (11%bv : bv 5) Q11.
sreg HS4 (12%bv : bv 5) Q12. sreg HS4 (18%bv : bv 5) Q18. sreg HS4 (19%bv : bv 5) Q19. sreg HS4 (20%bv : bv 5) Q20.
sreg HS4 (21%bv : bv 5) Q21. sreg HS4 (22%bv : bv 5) Q22. sreg HS4 (23%bv : bv 5) Q23.
sreg HS4 (24%bv : bv 5) Q24. sreg HS4 (25%bv : bv 5) Q25. sreg HS4 (26%bv : bv 5) Q26. sreg HS4 (27%bv : bv 5) Q27.
cbn [sv_denot] in Q1, Q2, Q3, Q4, Q8, Q9, Q10, Q11, Q12, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
rewrite ?Z.add_0_r in Q2, Q3, Q4, Q8, Q9, Q10, Q11, Q12, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
rewrite ?Z_to_bv_bv_unsigned in Q2, Q3, Q4, Q8, Q9, Q10, Q11, Q12, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
rewrite (EREG 2%nat 2%bv eq_refl), R2 in Q2. rewrite (EREG 3%nat 3%bv eq_refl), R3 in Q3.
rewrite (EREG 4%nat 4%bv eq_refl), R4 in Q4. rewrite (EREG 8%nat 8%bv eq_refl), R8 in Q8, Q12.
rewrite (EREG 9%nat 9%bv eq_refl), R9 in Q9. rewrite (EREG 20%nat 20%bv eq_refl), R20 in Q10, Q20.
rewrite (EREG 18%nat 18%bv eq_refl), R18 in Q11, Q18. rewrite (EREG 19%nat 19%bv eq_refl), R19 in Q19.
rewrite (EREG 21%nat 21%bv eq_refl), R21 in Q21. rewrite (EREG 22%nat 22%bv eq_refl), R22 in Q22.
rewrite (EREG 23%nat 23%bv eq_refl), R23 in Q23. rewrite (EREG 24%nat 24%bv eq_refl), R24 in Q24.
rewrite (EREG 25%nat 25%bv eq_refl), R25 in Q25. rewrite (EREG 26%nat 26%bv eq_refl), R26 in Q26.
rewrite (EREG 27%nat 27%bv eq_refl), R27 in Q27.
assert (IMG : forall nn, (A_TEXT <= nn < A_LIM)%nat -> bv_unsigned (ew E nn) = pa_val nn) by exact HEI.
rewrite (IMG 240%nat ltac:(cbv; lia)) in Q1. change (pa_val 240) with BASE in Q1.
assert (Hsp4 : spZ (ms_regs ms4) = sp1) by (unfold spZ; rewrite Q2; exact Usp1).
(* ---- what the walk kept: the cut's akept, then the run's frame (F's shadow and its va_list slot) ---- *)
set (Ea := aside_rng lyc 0 fpos) in *.
set (slo := sp - REAC_CODE_EMIT_AK) in *.
assert (Hslo_c : alloc_ceiling <= slo) by (unfold slo; lia).
set (X4 := fun a : Z => (SH <= a < SH + 8) \/ (F + 32 <= a < F + 40)).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ X4 HFr4
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U21, ?U22 in HrrW; unfold X4; lia|]); destruct HinW)) as UN4.
assert (X4side : forall a, X4 a -> Ea a).
{ intros a Ha. unfold Ea. apply (proj2 (md_side_unfold lyc fpos a)). rewrite EF0. rewrite <- HSHeq.
  unfold X4 in Ha. lia. }
assert (K4 : akept pa_segs B lyc Sc Wc memc W3 (ms_mem ms4) slo sp (fun a => e_E cx a \/ Ea a)).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc Wc memc (e_mdc cx) W3 m3 W3 (ms_mem ms4) slo sp
    (fun a => e_E cx a \/ Ea a) (fun a => e_E cx a \/ Ea a) X4 HAR Hslo_c ltac:(lia) HK3 UN4).
  - intros a _ Hp. eapply apresent_grows; [exact HG4 | exact Hp].
  - intros a H; exact H.
  - intros a Ha. left. right. exact (X4side a Ha). }
pose proof K4 as (_ & K4blk & K4img & _).
assert (NSIDE : forall a, in_img pa_segs a -> ~ Ea a).
{ intros a Hi HEa.
  destruct (aside_rng_low SK pa_segs B LAWS pa_segs_low lyc S1 W1 mem1 md1 0 fpos a HAR1 HinF HEa) as (_ & Hn).
  exact (Hn Hi). }
assert (HROD4 : arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W3) (ms_mem ms4))).
{ intros a Hro Ho He.
  assert (Hia : in_img pa_segs a)
    by (destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | lia] | exact (RELRO_IMG a Hr)]).
  rewrite (K4img a Hia Ho He ltac:(intros [HE | HE]; [exact (Hnro a HE Hro) | exact (NSIDE a Hia HE)])).
  exact (HROD a Hro Ho He). }
(* ---- the FILE at the call ---- *)
pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
assert (HFIN3 : In (e_f cx, AMF_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact HFIN).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_f cx) AMF_BLOCK HAR4 HFIN3) as (_ & Hf4096 & Hfceil & Hfapp & Hfpres & _ & _).
change (req_size AMF_BLOCK) with AMF_BLOCK in Hfceil, Hfapp, Hfpres.
pose proof (sep_block_frame pa_segs B LAWS ly3 S3 W3 m3 md3 (e_f cx) AMF_BLOCK 0 fpos HAR3 HFIN3 HinF3) as HsepF.
unfold zdisjoint in HsepF. cbn [fst snd] in HsepF. change (req_size AMF_BLOCK) with AMF_BLOCK in HsepF.
change (fs_frame_bytes 0) with 64 in HsepF. rewrite EF in HsepF.
assert (FNX : forall a, e_f cx <= a < e_f cx + AMF_BLOCK -> ~ X4 a).
{ intros a Ha Hx. unfold X4 in Hx. destruct Hx as [Hx | Hx].
  - pose proof (in_app_addr _ _ a Hfapp ltac:(lia)) as Hap. unfold app_addr in Hap.
    pose proof HSHb as HSHb'. rewrite HSHeq in Hx, HSHb'.
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, SHADOW_OFF in *. lia.
  - unfold AMF_BLOCK in *. lia. }
assert (FB4 : forall a, e_f cx <= a < e_f cx + AMF_BLOCK ->
  mbyte pa_segs (rdW W3 (ms_mem ms4)) a = mbyte pa_segs (rdW W3 m3) a).
{ intros a Ha. apply (mbyte_of_aview pa_segs). apply UN4; [unfold AMF_BLOCK in *; lia | exact (FNX a Ha)]. }
unfold em_file in Hfile.
pose proof (amf_k_ext pa_segs link_amf (rdW W3 m3) (rdW W3 (ms_mem ms4)) (e_f cx) _ FB4 Hfile) as HMF4.
assert (VIS : forall i, 0 <= i < e_kf cx + EMIT_HEAD ->
  ard pa_segs (rdW W3 (ms_mem ms4)) (e_f cx + AMF_BUF + i) <> None).
{ intros i Hi. destruct (Hfpres (e_f cx + AMF_BUF + i) ltac:(unfold AMF_BUF, AMF_BLOCK, EMIT_HEAD, AMF_BUFSIZ in *; lia))
    as (Hp & _).
  destruct Hp as (Hh & b0 & Hb0). unfold ard, mbyte, mrestrict. rewrite Hh, Hb0. discriminate. }
destruct (amf_k_facts pa_segs link_amf _ (e_f cx) _ HMF4 VIS)
  as (fl & om & wend & wpos & wbase & pos & len & pb & Hdyn & Hpend & Hplen).
(* ---- the caller's format and its %s strings at the call ---- *)
pose proof HFMT as (C1 & RT1 & Hflo & Hfhi & P1 & Hne & K1 & T1 & A1).
assert (HL : em_later B lyc Sc ly3 S3).
{ pose proof HJ as J1. eapply aj_stk_row_eq in J1. pose proof HJ3 as J3. eapply aj_stk_row_eq in J3.
  destruct J1 as (J1a & J1b). destruct J3 as (J3a & J3b).
  split; [congruence|]. split; [congruence|].
  split; [intros q m Hqm; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hqm|].
  split; [intros c q Hcq; rewrite Hfrs3; right; exact Hcq|].
  intros c q. exact (Hfa3 c q). }
pose proof HAR1 as [M1 _].
destruct (frame_facts B lyc S1 _ 0 fpos M1 HinF) as (Hc0 & Hpos0 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_f cx) AMF_BLOCK HAR HFIN) as (_ & _ & _ & Hfapp0 & _ & _ & _).
change (req_size AMF_BLOCK) with AMF_BLOCK in Hfapp0.
assert (HfE : fmiss lyc Sc (fun a => e_E cx a \/ Ea a)).
{ apply fmiss_or.
  - apply (fmiss_app pa_segs B LAWS lyc Sc Wc memc (e_mdc cx) (e_E cx) HAR).
    intros a Ha. apply (proj1 (e_E_file cx a Hf0)) in Ha.
    pose proof (in_app_addr _ _ a Hfapp0 Ha) as Hap. unfold app_addr in Hap.
    unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
  - exact (fmiss_side pa_segs B lyc Sc Wc memc (e_mdc cx) 0 fpos HAR Hc0 Hpos0 Hnin). }
assert (NSa : forall a, akb pa_segs B lyc Sc slo sp a -> ~ Ea a).
{ intros a Ha. exact (akb_not_side SK pa_segs B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ slo sp 0 fpos a HJ
    Hc0 Hpos0 Hnin Ha). }
pose proof (blk_off_imgP B lyc Sc Wc memc (e_mdc cx) (e_f cx) AMF_BLOCK HAR HFIN) as HfOff.
change (req_size AMF_BLOCK) with AMF_BLOCK in HfOff. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HfOff.
assert (HFakb : forall a, e_fp cx <= a <= e_fp cx + Z.of_nat (length (map (Z_to_bv 8) (e_fmt cx))) ->
  akb pa_segs B lyc Sc slo sp a).
{ intros a Ha. apply HRD. left. split; [exact Hfp0|]. exists (map (Z_to_bv 8) (e_fmt cx)). split; [exact C1 | exact Ha]. }
destruct (em_cstr_keep SK B LAWS TB HSEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem ms4) md4 slo sp _
  regs REAC_CODE_EMIT_AK (e_fp cx) (map (Z_to_bv 8) (e_fmt cx)) HJ HAR4 HL
  ltac:(unfold slo; rewrite HKv; lia)
  ltac:(lia) K4 HfE HFakb
  ltac:(intros a Ha [HE | HE];
        [ apply (proj1 (e_E_file cx a Hf0)) in HE; rewrite length_map in Ha; unfold LA_GOT_GUARD, LA_RO_LO in *; lia
        | exact (NSa a (HFakb a Ha) HE) ])
  C1 RT1) as (C1' & RT1').
assert (HAakb : forall a, apf_rd [getr regs 14; getr regs 15; getr regs 16; getr regs 17] (e_args cx) a ->
  akb pa_segs B lyc Sc slo sp a).
{ intros a Ha. apply HRD. right. exists (e_fmt cx), (e_ps cx), (e_args cx), (e_T cx). split; [exact HFMT | exact Ha]. }
pose proof (em_args_keep SK B LAWS TB HSEGS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ly3 S3 W3 (ms_mem ms4) md4 slo sp _
  regs REAC_CODE_EMIT_AK (e_f cx) _ (e_args cx) HJ HAR4 HL
  ltac:(unfold slo; rewrite HKv; lia)
  ltac:(lia) K4 HfE HAakb
  ltac:(intros a Ha Hnf [HE | HE];
        [ apply (proj1 (e_E_file cx a Hf0)) in HE; exact (Hnf HE) | exact (NSa a (HAakb a Ha) HE) ])
  A1) as A1'.
(* ---- +0x138: wrapper_vfprintf (f, fmt, ap) ---- *)
pmkst HS4. rewrite md_hvfpr.
set (WS := map (fun r : word => bv_unsigned r) [getr regs 14; getr regs 15; getr regs 16; getr regs 17]).
assert (HWIN : win_in sp REAC_CODE_EMIT_AK sp1 LVF_STK).
{ unfold win_in, LVF_STK, LVF_MUSL_STK. rewrite HKv. repeat split; lia. }
destruct (link_guard_val HSEGS W3 (ms_mem ms4)) as (cval & Hcval).
destruct (link_guard_apart B LAWS HSEGS ly3 S3 W3 (ms_mem ms4) md4 LVF_STK sp1 (e_f cx) HAR4 HFIN3
  ltac:(unfold LVF_STK, LVF_MUSL_STK; lia) ltac:(unfold LVF_STK, LVF_MUSL_STK; lia)) as (HGA1 & HGA2).
assert (HES : ESTACK = 4096) by reflexivity.
destruct (aj_gx_printf_pre SK pa_segs B LVF_STK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms4) HJ4
  ltac:(unfold LVF_STK, LVF_MUSL_STK; rewrite HES; lia) ltac:(rewrite Hsp4; exact Hsp1al16)
  ltac:(rewrite Hsp4; unfold LVF_STK, LVF_MUSL_STK; lia) ltac:(rewrite Hsp4; lia)
  ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp))
  as (Hecall & Hstklo & Hwinp).
(* the four vararg words at ap = s0, at the call *)
assert (KW4 : forall a, 0 <= a -> a + 8 <= 2 ^ 64 -> (forall j, a <= j < a + 8 -> ~ X4 j) ->
  rdword (aview pa_segs (w_H W3) (ms_mem ms4)) a = rdword (aview pa_segs (w_H W3) m3) a).
{ intros a H0 H1 H2. apply rdword_ext. intros j Hj. apply UN4; [lia|]. apply H2. lia. }
assert (HSF : forall j, sp1 <= j < sp -> ~ X4 j).
{ intros j Hj Hx. unfold X4 in Hx. pose proof HSHb as HSHb'. rewrite HSHeq in Hx, HSHb'.
  unfold SHADOW_OFF in *. destruct HFapp' as [? | (? & ?)]; lia. }
assert (HWS : words_at (aview pa_segs (w_H W3) (ms_mem ms4)) s0 WS).
{ intros i Hi. unfold WS in Hi. cbn [length map] in Hi.
  rewrite KW4 by (unfold s0, EM_VA in *; first [lia | intros j Hj; apply HSF; unfold s0, EM_VA in *; lia]).
  assert (Hi4 : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat) by lia.
  destruct Hi4 as [-> | [-> | [-> | ->]]]; cbn [nth WS map];
  lazymatch goal with |- rdword _ (?b + 8 * Z.of_nat ?i) = Some (bv_unsigned (getr _ ?r)) =>
    rewrite <- (md_getr_lit regs r);
    pose proof (Hva (Z.of_nat i) ltac:(lia)) as Hv; unfold s0;
    replace (bv_unsigned r) with (14 + Z.of_nat i) by reflexivity; exact Hv
  end. }
pose proof HFIT as HFIT'. cbv [AMF_BUFSIZ EMIT_HEAD] in HFIT'.
pose proof (Nat2Z.is_nonneg (length pb)) as Hpb0.
assert (HTlen : Z.of_nat (length (e_T cx)) <= 1024).
{ clear - HFIT' Hpb0 Hplen. cbv [EMIT_HEAD] in Hplen. lia. }
assert (HEf : getr (ms_regs ms4) 10 = w64 (e_f cx)).
{ rewrite Q10. unfold w64.
  change (e_f cx) with (bv_unsigned (getr regs (Z_to_bv 5 (bv_unsigned (10%bv : bv 5))))).
  rewrite md_getr_lit, Z_to_bv_bv_unsigned. reflexivity. }
assert (HEfp : getr (ms_regs ms4) 11 = w64 (e_fp cx)).
{ rewrite Q11. unfold w64.
  change (e_fp cx) with (bv_unsigned (getr regs (Z_to_bv 5 (bv_unsigned (13%bv : bv 5))))).
  rewrite md_getr_lit, Z_to_bv_bv_unsigned. reflexivity. }
eapply SRr_bind.
{ eapply (aj_gx_printf_mf_at SK pa_segs B LAWS pa_segs_low LVF_STK LA_W_VFPRINTF _ _ _ W3 (ms_regs ms4) (ms_mem ms4)
    _ _ _ _ _ _ _ _ _ ly3 S3 md4 _ (getr (ms_regs ms4) 1) (e_f cx) (e_kf cx + EMIT_HEAD) pb (e_T cx) fl om wend
    pos len HGX HJ4 ltac:(unfold LVF_STK, LVF_MUSL_STK; lia) ltac:(rewrite Hsp4; unfold LVF_STK, LVF_MUSL_STK; lia)
    ltac:(rewrite Hsp4; lia) eq_refl).
  - intros a Ha.
    eapply ajw_mono.
    + apply Hajw. apply (proj2 (e_E_file cx a Hf0)). exact Ha.
    + intros bb mm Hbm. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hbm.
    + intros x Hx. right. exact Hx.
    + intros c q. exact (Hfa3 c q).
  - rewrite <- Hsp4 in HGA1, HGA2.
    refine (VFPR fx ly3 S3 W3 (ms_regs ms4) (ms_mem ms4) md4 (e_f cx) (e_fp cx) s0 (e_kf cx + EMIT_HEAD) fl om wend wpos
      wbase pos len pb WS (e_T cx) cval Hecall Hstklo Hwinp HEf HEfp _ HFIN3 _ HMF4 Hdyn Hpend Hplen _ HROD4 _ Hcval
      _ _ _ _ HGA1 HGA2 HWS _ _ _ _ _ Hfrm0).
    + rewrite Q12. reflexivity.
    + rewrite Hsp4. cbn [vmf_out pairwise]. split; [|split; [constructor | exact I]].
      constructor; [|constructor]. unfold zdisjoint. cbn [fst snd]. unfold LVF_STK, LVF_MUSL_STK, AMF_BLOCK in *. lia.
    + exact HFIT.
    + exact (link_guard_got B TB HSEGS ly3 S3 W3 (ms_mem ms4) md4 HAR4).
    + unfold LinkMfDefs.LA_GOT_GUARD. lia.
    + unfold LinkMfDefs.LA_GOT_GUARD. lia.
    + unfold LinkMfDefs.LA_GUARD. lia.
    + unfold LinkMfDefs.LA_GUARD. lia.
    + rewrite Hsp4. unfold s0, EM_VA. lia.
    + unfold WS. cbn [length map]. unfold s0, EM_VA. lia.
    + rewrite Hsp4. unfold WS. cbn [vmf_out length map]. constructor; [|constructor; [|constructor]];
        unfold zdisjoint; cbn [fst snd]; unfold s0, EM_VA, LVF_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia.
    + rewrite Hsp4.
      destruct (apf_args_slack pa_segs regs REAC_CODE_EMIT_AK _ (e_f cx) _ (e_args cx) A1) as (Hsl & Ham).
      apply (link_vf_FF_of_c _ _ (e_fp cx) (e_fmt cx) (e_ps cx) (e_args cx) (e_T cx) WS).
      * exact (afmt_at pa_segs regs REAC_CODE_EMIT_AK (rdW W3 (ms_mem ms4)) (e_fp cx) (e_fmt cx) LVF_STK sp1 (e_f cx)
          HWIN (pf_parse_bytes _ _ P1) C1' RT1'
          ltac:(unfold apart; unfold LA_GOT_GUARD, LA_RO_LO in *; lia)).
      * exact P1.
      * exact K1.
      * exact (apf_args_asan pa_segs regs REAC_CODE_EMIT_AK (rdW W3 (ms_mem ms4)) (e_f cx) _ (e_args cx) LVF_STK sp1 HWIN A1').
      * exact T1.
      * unfold LA_RO_LO in Hflo. lia.
      * unfold LA_GOT_GUARD in Hfhi. lia.
      * exact Hsl.
      * exact Hne.
      * exact Ham.
    + lia. }
cbv beta. intros W5 c5 _ (-> & fx' & regs5 & mem5 & md5 & -> & Hfxr5 & HJ5 & HP5 & Hsm5 & H10 & Hfp5 & Hkept5 & Hpres5).
(* ---- +0x13c: wrapper_vfprintf returned at fx'; the cut EM_v1_ra ---- *)
set (X5 := fun a : Z => (e_f cx <= a < e_f cx + AMF_BLOCK) \/ (sp1 - LVF_STK <= a < sp1)).
assert (UN5 : forall a, 0 <= a < 2 ^ 64 -> ~ X5 a ->
  aview pa_segs (w_H W3) mem5 a = aview pa_segs (w_H W3) (ms_mem ms4) a).
{ intros a Ha HX. apply Hkept5; [exact Ha | intro H; apply HX; left; exact H |].
  rewrite Hsp4. intro H; apply HX; right; exact H. }
assert (K5 : akept pa_segs B lyc Sc Wc memc W3 mem5 slo sp (fun a => e_E cx a \/ Ea a)).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc Wc memc (e_mdc cx) W3 (ms_mem ms4) W3 mem5 slo sp
    (fun a => e_E cx a \/ Ea a) (fun a => e_E cx a \/ Ea a) X5 HAR Hslo_c ltac:(lia) K4 UN5).
  - intros a _ Hp. exact (Hpres5 a Hp).
  - intros a H; exact H.
  - intros a Ha. unfold X5 in Ha. destruct Ha as [Ha | Ha].
    + left. left. exact (proj2 (e_E_file cx a Hf0) Ha).
    + right. unfold slo, LVF_STK, LVF_MUSL_STK in *. rewrite HKv. lia. }
pose proof K5 as (_ & _ & K5img & _).
assert (HROD5 : arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W3) mem5)).
{ intros a Hro Ho He.
  assert (Hia : in_img pa_segs a)
    by (destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | lia] | exact (RELRO_IMG a Hr)]).
  rewrite (K5img a Hia Ho He ltac:(intros [HE | HE]; [exact (Hnro a HE Hro) | exact (NSIDE a Hia HE)])).
  exact (HROD a Hro Ho He). }
set (md5' := md5) in *.
assert (Hfd : m_fds md5' = m_fds (e_mdc cx) /\ m_fs md5' = m_fs (e_mdc cx)).
{ destruct (md_sbm_fds _ _ Hsm5) as [A1f A2f]. unfold md4 in A1f, A2f.
  destruct (wvb_fds_fs (m_vm_lazy md3) mat4 md3) as [B1f B2f]. split; congruence. }
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs5 r = getr (ms_regs ms4) r).
{ intros r Hr. rewrite <- (md_getr_lit regs5 r), <- (md_getr_lit (ms_regs ms4) r). exact (HP5 _ Hr). }
assert (KW : forall a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall j, a <= j < a + 8 -> ~ X4 j /\ ~ X5 j) ->
  rdword (aview pa_segs (w_H W3) mem5) a = rdword (aview pa_segs (w_H W3) m3) a).
{ intros a H0 H1 H2. apply rdword_ext. intros j Hj.
  rewrite UN5 by (try lia; exact (proj2 (H2 (a + j) ltac:(lia)))).
  apply UN4; [lia | exact (proj1 (H2 (a + j) ltac:(lia)))]. }
assert (STK_OUT : forall j, alloc_ceiling <= j -> ~ X4 j).
{ intros j Hj Hx. unfold X4 in Hx. pose proof HSHb as HSHb'. rewrite HSHeq in Hx, HSHb'.
  unfold SHADOW_OFF in *. lia. }
apply (NEXT fx' fx cx fpos (e_k cx) ly3 S3 W3 (@mkst fx' regs5 (getr (ms_regs ms4) 1) mem5 (seg_rom pa_segs)) md5'
  Hfxr5 Hfrm0 HBASE0 HJ5).
unfold em_v1_inv.
destruct (ms_shape_mkst (fx := fx') pa_segs (mkst regs5 (getr (ms_regs ms4) 1) mem5 (seg_rom pa_segs)) regs5 _ mem5
  eq_refl) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
split.
{ unfold em_shape. rewrite Z6, Q1. split; [reflexivity|]. split; [exact Z1|]. split; [exact Z2|].
  split; [exact Z3|]. split; [exact Z4 | exact Z5]. }
split.
{ unfold em_regs. cbn [ms_regs mkst].
  rewrite (PR 2%bv ltac:(apply md_cs; reflexivity)), (PR 8%bv ltac:(apply md_cs; reflexivity)),
    (PR 9%bv ltac:(apply md_cs; reflexivity)), (PR 18%bv ltac:(apply md_cs; reflexivity)),
    (PR 20%bv ltac:(apply md_cs; reflexivity)), (PR 3%bv ltac:(apply md_cs; reflexivity)),
    (PR 4%bv ltac:(apply md_cs; reflexivity)), (PR 24%bv ltac:(apply md_cs; reflexivity)),
    (PR 25%bv ltac:(apply md_cs; reflexivity)), (PR 26%bv ltac:(apply md_cs; reflexivity)),
    (PR 27%bv ltac:(apply md_cs; reflexivity)).
  rewrite Q2, Q8, Q9, Q18, Q20, Q3, Q4, Q24, Q25, Q26, Q27. repeat split; reflexivity. }
split.
{ unfold em_fregs. cbn [ms_regs mkst].
  rewrite (PR 19%bv ltac:(apply md_cs; reflexivity)), (PR 22%bv ltac:(apply md_cs; reflexivity)),
    (PR 21%bv ltac:(apply md_cs; reflexivity)), (PR 23%bv ltac:(apply md_cs; reflexivity)).
  rewrite Q19, Q22, Q21, Q23. repeat split; reflexivity. }
split.
{ unfold em_saved, em_at. cbn [ms_mem mkst]. change (e_spe cx) with sp. split.
  - rewrite KW by (unfold EM_RA; first [lia | intros j Hj; split;
      [apply STK_OUT; lia | unfold X5, LVF_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia]]).
    exact Hra.
  - intros j Hj. rewrite KW by (unfold EM_S0; first [lia | intros j' Hj'; split;
      [apply STK_OUT; lia | unfold X5, LVF_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia]]).
    exact (Hsav j Hj). }
split.
{ unfold em_flagw, em_at. cbn [ms_mem mkst]. change (eF cx fpos) with F. change (eFL cx fpos) with FL.
  change EM_CID with 0. change (fs_frame_bytes 0) with 64.
  rewrite KW by (first [lia | intros j Hj; split;
      [ unfold X4; pose proof HSHb as HSHb'; rewrite HSHeq in HSHb' |- *; unfold SHADOW_OFF in *;
        destruct HFapp' as [? | (? & ?)]; lia
      | unfold X5, LVF_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia ]]).
  exact Hflagw. }
split; [exact HF4096|].
split; [exact HFceil|].
split.
{ unfold em_jbk. split; [reflexivity|]. split; [exact Hperm|]. split; [exact HfsS3|].
  split; [exact Hfrs3|]. split; [exact Hnin|]. split; [exact Hfa3|]. split; [exact Hfl3|].
  split; [exists S1, W1, mem1, md1; split; [exact HAR1 | split; [exact Hfrs1 | exact Hbl1]]|].
  exact Hfd. }
split.
{ unfold em_kept. cbn [ms_mem mkst]. split; [exact K5|]. split; [exact HROD5 | intros a H; exact H]. }
{ unfold em_file. cbn [ms_mem mkst].
  destruct (apf_file_post_parts _ _ _ _ _ _ _ _ _ _ _ _ Hfp5) as (HF5 & _ & _).
  exact HF5. }
Qed.

About em_mid.
Print Assumptions em_mid.

End b.
End a.
