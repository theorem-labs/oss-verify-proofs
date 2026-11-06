(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module paths and module names changed; 771 of its 824 lines of code are new or changed and 538 lines of the source are left out. *)
(* reac_link_alias_write on image A: THE ARMS PIECE, the stretch +0x1a8 .. +0x1f0 from the MID cut, i.e.

     aw_arms : aw_exit_obl SK B -> aw_send_obl SK B -> aw_mid_obl SK B

   of lib/A/Prog/reac_link_alias_writeDefs.v. The code (listing
   (internal path) (internal record, sha256 0b8d5e317aa8)):
     +0x1a8  `beqz s6`                        name = NULL               -> +0x3a4, s5 = -22   (ArmsB.v)
     +0x1ac..+0x1b8                            the instrumented check of name[0]
     +0x1bc  `beqz s4`                        alias = NULL              -> +0x3a4, s5 = -22   (ArmsB.v)
     +0x1c0..+0x1c4 `lbu; beqz`               the name is empty         -> +0x3a4, s5 = -22   (ArmsB.v)
     +0x1c8..+0x1cc `mv a0,s4; jal`           wrapper_strlen(alias): RtString.astrlen_realizes through
                                              lib/A/Prog/LinkWalkStrS.v aj_gx_strlen_atS
     +0x1d0..+0x1dc `bgeu 255,a0`             |alias| >= 256            -> s5 = -36, +0x3a4   (ARM 6)
     +0x1e0..+0x1e8 `mv s5,a0; mv a0,s6; jal` fuzz_if_nametoindex(name): its contract under SRr_bind
     +0x1ec  `beqz a0`                        index 0                   -> +0x3a0 (s5 = -19), +0x3a4 (ARM 8)
     +0x1f0                                   otherwise: THE SEND CUT.
   Each stage starts a fresh symbolic state whose atoms are the stage's registers; the memory facts it carries
   are aw_base (reac_link_alias_writeDefs.v) and, across the two calls, ArmsC.v's awc_inv.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YI01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import fuzz_if_nametoindex_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeArmsA reac_link_alias_writeArmsB.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeSendA reac_link_alias_writeArmsC.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkStrS LinkWalkCall LinkWalkZsh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the index fuzz_if_nametoindex answers is one of the table's indices, or 0 *)
Lemma awd_index_range : forall (tab : list (list byte * Z)) s,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab s < 2 ^ 31.
Proof.
  induction tab as [|[n i] t IH]; intros s H; cbn [index_of]; [lia|].
  destruct (bl_eqb n s).
  - exact (H 0%nat n i eq_refl).
  - apply IH. intros j n' ix' Hj. exact (H (S j) n' ix' Hj).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
(* the image's symbols (lib/A/AF0m.v PcapSyms); the instance is AD2l.PcapB_syms *)
Hypothesis TB : PcapSyms B.
(* the segments the listing is certified against; the link PAImg instance has it by reflexivity *)
Hypothesis HSEGS : SEGS = tfibsegs.
(* the read-only window is image bytes: discharged in lib/A/Prog/reac_link_alias_write.v (aw_relro_img_tfib) *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
(* wrapper_strlen (0x43044): lib/A/Rt/RtClosed.v cmd_strlen_closed at link's B (PcapSyms) *)
Hypothesis ASTRLEN : RtString.astrlen_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strlen).
(* fuzz_if_nametoindex (0x826cc): the proof of its contract *)
Hypothesis NIX : fuzz_if_nametoindex_acontract SK SEGS PCAP_RLO PCAP_RHI B.
(* the strcmp tail facts of the name and of each table string at the call's memory (reac_link_alias_writeDefs.v
   aw_tails), read off reac_link_alias_write_c.v's Pre (its tail clauses, commit e2b13a9a8f08) *)
Lemma aw_tails_of_pre : forall cx : awcx, aw_pre SK B cx -> aw_tails cx.
Proof.
  intros cx (_ & _ & HP).
  destruct HP as (kbs0 & tab0 & nm0 & al0 & HN0 & _ & _ & _ & _ & HT0 & _ & _ & _ & HNM0 & _ & HTS0 & HNS0 & _ & _).
  split.
  - intros s Hs.
    assert (Enm : nm0 = Some s) by exact (aw_astr_arg_unique SEGS _ _ _ _ HNM0 Hs).
    destruct (HNS0 s Enm) as (_ & _ & _ & _ & Htl). exact Htl.
  - intros kbs tab i n2 ix p HN HT Hi Hp Hp64.
    assert (kbs0 = kbs) by exact (aw_anlk_unique SEGS _ _ _ _ HN0 HN). subst kbs0.
    assert (tab0 = tab) by exact (aw_aiftab_unique SEGS _ _ _ _ _ HT0 HT). subst tab0.
    destruct (HTS0 i n2 ix p Hi Hp) as (_ & _ & _ & H4).
    destruct (H4 Hp64) as (_ & _ & _ & Htl). exact Htl.
Qed.

(* the environment of a stage: atom r is the value of register r at the stage's start *)
Definition awdR (R : bvmap 5 word) : env := Eimg (Ereg R []).

Lemma awdR_img : forall R, img_env VAL A_LIM (awdR R).
Proof. intros R. apply Eimg_env. Qed.

Lemma awdR_reg : forall R n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (awdR R) n = getr R r.
Proof. intros R n r Hn. unfold awdR. exact (ew_Eimg_Ereg_nat R [] n r Hn). Qed.

(* the two extra atoms of the MID cut's environment: atom 32 unused, atom 33 the name's first byte *)
Definition awd_X (v : Z) : list word := [Z_to_bv 64 0; Z_to_bv 64 v].

Lemma awd_ext : forall ms3 extra n j, n = (32 + j)%nat -> (n < A_TEXT)%nat ->
  ew (awE ms3 extra) n = nth j extra (Z_to_bv 64 0).
Proof. intros ms3 extra n j -> Hj. unfold awE. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma awd_m19 : Z_to_bv 64 18446744073709551597 = w64 (-19).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma awd_m36 : Z_to_bv 64 18446744073709551580 = w64 (-36).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* the shape fields of a machine state that is an mkst *)
Ltac awd_shape := cbn [ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem ms_pc_val mkst]; reflexivity.

(* ==========================================================================
   1. From +0x1ec (fuzz_if_nametoindex returned): ARM 8 (index 0) or the SEND cut
   ========================================================================== *)
Lemma aw_d_tail : aw_exit_obl SK B -> aw_send_obl SK B ->
  forall (cx : awcx) fpos ly S W ms md sn sa tab kbs,
  aw_pre SK B cx -> aw_base SK B cx fpos ly S W ms md -> aw_gnl_kept cx W (ms_mem ms) ->
  ms_pc_val ms = w64 (BASE + (AF_reac_link_alias_write + 0x1ec)) ->
  anlk_at SEGS (aw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab ->
  acstr_at SEGS (aw_m0 cx) (aw_name cx) sn -> aw_name cx <> 0 -> sn <> [] ->
  acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa -> aw_alias cx <> 0 -> Z.of_nat (length sa) < ALIAS_MAX ->
  getr (ms_regs ms) 10 = w64 (index_of tab sn) ->
  getr (ms_regs ms) 20 = w64 (aw_alias cx) -> getr (ms_regs ms) 21 = w64 (Z.of_nat (length sa)) ->
  getr (ms_regs ms) 22 = w64 (aw_name cx) -> getr (ms_regs ms) 23 = w64 SHADOW_OFF ->
  SRr SEGS W (mkCfg ms md) (aw_post SK B cx).
Proof.
  intros EXIT SEND cx fpos ly S W ms md sn sa tab kbs HPRE HB HG Hpc HNK HIT HSN HN0 HSNE HSA HA0 HAL
    R10 R20 R21 R22 R23.
  pose proof (aw_base_shape SK B cx fpos ly S W ms md HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (aw_base_jx SK B cx fpos ly S W ms md HB) as HJ.
  pose proof HPRE as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (aw_G cx)) by (unfold apre in HAPRE; tauto).
  assert (Hms : ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + (AF_reac_link_alias_write + 0x1ec))) (ms_mem ms)
                  (seg_rom SEGS))
    by (apply (aw_mkst_at W ms (AF_reac_link_alias_write + 0x1ec)); assumption).
  assert (Hrms : restrict (w_H W) ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + (AF_reac_link_alias_write + 0x1ec)))
                   (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HEIa : img_env VAL A_LIM (awdR (ms_regs ms))) by apply awdR_img.
  pose proof HIT as (_ & _ & HITe).
  assert (Hidx : 0 <= index_of tab sn < 2 ^ 31)
    by (apply awd_index_range; intros i n ix Hi; exact (proj1 (HITe i n ix Hi))).
  (* the strings and the table the refusal / the SEND cut name are the Pre's *)
  assert (HRC : forall kbs' tab' nm al,
     anlk_at SEGS (aw_m0 cx) LA_G_NL kbs' -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs' tab' ->
     astr_arg SEGS (aw_m0 cx) (aw_name cx) nm -> astr_arg SEGS (aw_m0 cx) (aw_alias cx) al ->
     kbs' = kbs /\ tab' = tab /\ nm = Some sn /\ al = Some sa).
  { intros kbs' tab' nm al HN HT HA HBl.
    assert (E1 : kbs' = kbs) by exact (aw_anlk_unique SEGS _ _ _ _ HN HNK). subst kbs'.
    split; [reflexivity|]. split; [exact (aw_aiftab_unique SEGS _ _ _ _ _ HT HIT)|].
    split; [apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HA | split; assumption]|].
    apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_alias cx)); [exact HBl | split; assumption]. }
  pose (RUNTO := paj_run_to_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
  destruct (Z.eq_dec (index_of tab sn) 0) as [Hz | Hnz].
  - (* ARM 8: `beqz a0` taken, +0x3a0 s5 := -19, +0x3a4 *)
    assert (HS : st_ok_pi SEGS VAL (awdR (ms_regs ms))
       (mkSS (AF_reac_link_alias_write + 0x1ec) (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []))
       (restrict (w_H W) ms)).
    { apply (ast_ok_pi_set_reg_fp (awdR (ms_regs ms))
               (mkSS (AF_reac_link_alias_write + 0x1ec) sr_atoms [] None (mkFacts [] [] []))
               (restrict (w_H W) ms) 10%bv (SLit 0)).
      - rewrite Hrms. apply pa_entry_st_ok_full.
        + unfold awdR. apply regs_ok_Eimg_Ereg.
        + vm_compute; reflexivity.
        + constructor.
        + exact I.
        + split; [exact I | split; exact I].
      - reflexivity.
      - cbn [ms_regs restrict mkst sv_denot]. rewrite R10, Hz. reflexivity. }
    assert (SHOK : sh_ok SEGS AwBx [] (awdR (ms_regs ms)) (mrestrict (w_H W) (ms_mem ms))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK AwBspan AW_CUT_EXIT; [apply awr_ok_x_nil |].
    assert (Hmem : ms_mem ms0 = ms_mem ms).
    { apply functional_extensionality. intros x. apply HF.
      cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
    prreg HS (2%bv : bv 5) Q2. rewrite (awdR_reg (ms_regs ms) 2%nat 2%bv eq_refl) in Q2.
    prreg HS (9%bv : bv 5) Q9. rewrite (awdR_reg (ms_regs ms) 9%nat 9%bv eq_refl) in Q9.
    prreg HS (8%bv : bv 5) Q8. rewrite (awdR_reg (ms_regs ms) 8%nat 8%bv eq_refl) in Q8.
    prreg HS (18%bv : bv 5) Q18. rewrite (awdR_reg (ms_regs ms) 18%nat 18%bv eq_refl) in Q18.
    prreg HS (19%bv : bv 5) Q19. rewrite (awdR_reg (ms_regs ms) 19%nat 19%bv eq_refl) in Q19.
    prreg HS (24%bv : bv 5) Q24. rewrite (awdR_reg (ms_regs ms) 24%nat 24%bv eq_refl) in Q24.
    prreg HS (3%bv : bv 5) Q3. rewrite (awdR_reg (ms_regs ms) 3%nat 3%bv eq_refl) in Q3.
    prreg HS (4%bv : bv 5) Q4. rewrite (awdR_reg (ms_regs ms) 4%nat 4%bv eq_refl) in Q4.
    prreg HS (25%bv : bv 5) Q25. rewrite (awdR_reg (ms_regs ms) 25%nat 25%bv eq_refl) in Q25.
    prreg HS (26%bv : bv 5) Q26. rewrite (awdR_reg (ms_regs ms) 26%nat 26%bv eq_refl) in Q26.
    prreg HS (27%bv : bv 5) Q27. rewrite (awdR_reg (ms_regs ms) 27%nat 27%bv eq_refl) in Q27.
    prreg HS (21%bv : bv 5) Q21.
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Hms4.
    set (md4 := with_vm_backing (m_vm_lazy md) mat md).
    apply (EXIT cx fpos ly S W ms0 md4 HPRE).
    exists (-19).
    split; [rewrite Hms4 at 1; cbn [ms_pc_val mkst]; reflexivity|].
    split; [rewrite Q21; exact awd_m19|].
    split.
    { apply (aw_base_step_nomem SK B cx fpos ly S W ms md ms0 md4 HB Hmem);
        try (rewrite Hms4 at 1; awd_shape).
      - exact (proj1 (wvb_fds_fs (m_vm_lazy md) mat md)).
      - exact (proj2 (wvb_fds_fs (m_vm_lazy md) mat md)).
      - exact HJ.
      - exact Q2.
      - exact Q9.
      - exact Q8.
      - exact Q18.
      - exact Q19.
      - exact Q24.
      - exact Q3.
      - exact Q4.
      - exact Q25.
      - exact Q26.
      - exact Q27. }
    apply (aw_pf_at B HSEGS cx W (ms_mem ms0) (-19) HP).
    + rewrite Hmem. exact HG.
    + rewrite Hmem. intros a Ha. exact (aw_rd_kept SK B cx fpos ly S W ms md a HPRE HB Ha).
    + intros kbs' tab' nm al HN HT HA HBl.
      destruct (HRC kbs' tab' nm al HN HT HA HBl) as (-> & -> & -> & ->).
      rewrite (aw_wl_no_dev tab sn sa (nk_sent kbs) (nk_kstate kbs) HSNE HAL Hz). cbn [w_rc w_reqs w_state].
      split; [reflexivity | split; reflexivity].
  - (* the SEND cut: `beqz a0` not taken *)
    assert (HS : st_ok_pi SEGS VAL (awdR (ms_regs ms))
       (mkSS (AF_reac_link_alias_write + 0x1ec) sr_atoms [] None (mkFacts [(10%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] []))
       (restrict (w_H W) ms)).
    { rewrite Hrms. apply pa_entry_st_ok_full.
      - unfold awdR. apply regs_ok_Eimg_Ereg.
      - vm_compute; reflexivity.
      - constructor.
      - exact I.
      - split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. split; [|exact I].
        unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awdR_reg (ms_regs ms) 10%nat 10%bv eq_refl), R10, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]]. }
    assert (SHOK : sh_ok SEGS AwBx [] (awdR (ms_regs ms)) (mrestrict (w_H W) (ms_mem ms))) by constructor.
    paj_run_to_tok RUNTO HS HJ SHOK AwBspan AW_CUT_SEND; [apply awr_ok_x_nil |].
    assert (Hmem : ms_mem ms0 = ms_mem ms).
    { apply functional_extensionality. intros x. apply HF.
      cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
    prreg HS (2%bv : bv 5) Q2. rewrite (awdR_reg (ms_regs ms) 2%nat 2%bv eq_refl) in Q2.
    prreg HS (9%bv : bv 5) Q9. rewrite (awdR_reg (ms_regs ms) 9%nat 9%bv eq_refl) in Q9.
    prreg HS (8%bv : bv 5) Q8. rewrite (awdR_reg (ms_regs ms) 8%nat 8%bv eq_refl) in Q8.
    prreg HS (18%bv : bv 5) Q18. rewrite (awdR_reg (ms_regs ms) 18%nat 18%bv eq_refl) in Q18.
    prreg HS (19%bv : bv 5) Q19. rewrite (awdR_reg (ms_regs ms) 19%nat 19%bv eq_refl) in Q19.
    prreg HS (24%bv : bv 5) Q24. rewrite (awdR_reg (ms_regs ms) 24%nat 24%bv eq_refl) in Q24.
    prreg HS (3%bv : bv 5) Q3. rewrite (awdR_reg (ms_regs ms) 3%nat 3%bv eq_refl) in Q3.
    prreg HS (4%bv : bv 5) Q4. rewrite (awdR_reg (ms_regs ms) 4%nat 4%bv eq_refl) in Q4.
    prreg HS (25%bv : bv 5) Q25. rewrite (awdR_reg (ms_regs ms) 25%nat 25%bv eq_refl) in Q25.
    prreg HS (26%bv : bv 5) Q26. rewrite (awdR_reg (ms_regs ms) 26%nat 26%bv eq_refl) in Q26.
    prreg HS (27%bv : bv 5) Q27. rewrite (awdR_reg (ms_regs ms) 27%nat 27%bv eq_refl) in Q27.
    prreg HS (10%bv : bv 5) Q10. rewrite (awdR_reg (ms_regs ms) 10%nat 10%bv eq_refl) in Q10.
    prreg HS (20%bv : bv 5) Q20. rewrite (awdR_reg (ms_regs ms) 20%nat 20%bv eq_refl) in Q20.
    prreg HS (21%bv : bv 5) Q21. rewrite (awdR_reg (ms_regs ms) 21%nat 21%bv eq_refl) in Q21.
    prreg HS (22%bv : bv 5) Q22. rewrite (awdR_reg (ms_regs ms) 22%nat 22%bv eq_refl) in Q22.
    prreg HS (23%bv : bv 5) Q23. rewrite (awdR_reg (ms_regs ms) 23%nat 23%bv eq_refl) in Q23.
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Hms4.
    set (md4 := with_vm_backing (m_vm_lazy md) mat md).
    apply (SEND cx fpos ly S W ms0 md4 HPRE).
    exists sn, sa, tab, kbs.
    split; [rewrite Hms4 at 1; cbn [ms_pc_val mkst]; reflexivity|].
    split; [exact HNK|]. split; [exact HIT|]. split; [exact HSN|]. split; [exact HN0|]. split; [exact HSNE|].
    split; [exact HSA|]. split; [exact HA0|]. split; [exact HAL|].
    split; [rewrite Q10; exact R10|]. split; [exact Hnz|].
    split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
    split; [rewrite Q22; exact R22|]. split; [rewrite Q23; exact R23|].
    split; [rewrite Hmem; exact HG|].
    apply (aw_base_step_nomem SK B cx fpos ly S W ms md ms0 md4 HB Hmem);
      try (rewrite Hms4 at 1; awd_shape).
    + exact (proj1 (wvb_fds_fs (m_vm_lazy md) mat md)).
    + exact (proj2 (wvb_fds_fs (m_vm_lazy md) mat md)).
    + exact HJ.
    + exact Q2.
    + exact Q9.
    + exact Q8.
    + exact Q18.
    + exact Q19.
    + exact Q24.
    + exact Q3.
    + exact Q4.
    + exact Q25.
    + exact Q26.
    + exact Q27.
Qed.

(* ==========================================================================
   2. From +0x1d0 (wrapper_strlen returned, a0 = |alias|): ARM 6, or fuzz_if_nametoindex(name) and section 1
   ========================================================================== *)
Lemma aw_d_len : aw_exit_obl SK B -> aw_send_obl SK B ->
  forall (cx : awcx) fpos ly S W ms md sn sa tab kbs,
  aw_pre SK B cx -> aw_base SK B cx fpos ly S W ms md -> aw_gnl_kept cx W (ms_mem ms) ->
  ms_pc_val ms = w64 (BASE + (AF_reac_link_alias_write + 0x1d0)) ->
  anlk_at SEGS (aw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab ->
  acstr_at SEGS (aw_m0 cx) (aw_name cx) sn -> aw_name cx <> 0 -> sn <> [] ->
  acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa -> aw_alias cx <> 0 -> Z.of_nat (length sa) + 1 < 2 ^ 32 ->
  getr (ms_regs ms) 10 = w64 (Z.of_nat (length sa)) ->
  getr (ms_regs ms) 20 = w64 (aw_alias cx) ->
  getr (ms_regs ms) 22 = w64 (aw_name cx) -> getr (ms_regs ms) 23 = w64 SHADOW_OFF ->
  SRr SEGS W (mkCfg ms md) (aw_post SK B cx).
Proof.
  intros EXIT SEND cx fpos ly S W ms md sn sa tab kbs HPRE HB HG Hpc HNK HIT HSN HN0 HSNE HSA HA0 Hl32
    R10 R20 R22 R23.
  pose proof (aw_base_shape SK B cx fpos ly S W ms md HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (aw_base_jx SK B cx fpos ly S W ms md HB) as HJ.
  pose proof HPRE as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (aw_G cx)) by (unfold apre in HAPRE; tauto).
  assert (Hms : ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + (AF_reac_link_alias_write + 0x1d0))) (ms_mem ms)
                  (seg_rom SEGS))
    by (apply (aw_mkst_at W ms (AF_reac_link_alias_write + 0x1d0)); assumption).
  assert (Hrms : restrict (w_H W) ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + (AF_reac_link_alias_write + 0x1d0)))
                   (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HEIa : img_env VAL A_LIM (awdR (ms_regs ms))) by apply awdR_img.
  assert (SHOK : sh_ok SEGS AwBx [] (awdR (ms_regs ms)) (mrestrict (w_H W) (ms_mem ms))) by constructor.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HNIN & _ & _ & HS1 & _ & B2 & B9 & B8 & B18 & B19 & B24 & B3 & B4
    & B25 & B26 & B27 & _).
  destruct (Z_lt_le_dec (Z.of_nat (length sa)) ALIAS_MAX) as [Hshort | Hlong].
  2:{ (* ARM 6: `bgeu a1,a0` not taken, s5 := -36, `j +0x3a4` *)
    assert (HS : st_ok_pi SEGS VAL (awdR (ms_regs ms))
       (mkSS (AF_reac_link_alias_write + 0x1d0) sr_atoms [] None (mkFacts [(10%nat, mkAF 256 (2 ^ 32 - 1) 0)] [] []))
       (restrict (w_H W) ms)).
    { rewrite Hrms. apply pa_entry_st_ok_full.
      - unfold awdR. apply regs_ok_Eimg_Ereg.
      - vm_compute; reflexivity.
      - constructor.
      - exact I.
      - split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. split; [|exact I].
        unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awdR_reg (ms_regs ms) 10%nat 10%bv eq_refl), R10, unsigned_lit_small by lia.
        unfold ALIAS_MAX in Hlong. split; [lia | split; [apply Zmod_1_r | lia]]. }
    pose (RUNTO := paj_run_to_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
    paj_run_to_tok RUNTO HS HJ SHOK AwBspan AW_CUT_EXIT; [apply awr_ok_x_nil |].
    assert (Hmem : ms_mem ms0 = ms_mem ms).
    { apply functional_extensionality. intros x. apply HF.
      cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
    prreg HS (2%bv : bv 5) Q2. rewrite (awdR_reg (ms_regs ms) 2%nat 2%bv eq_refl) in Q2.
    prreg HS (9%bv : bv 5) Q9. rewrite (awdR_reg (ms_regs ms) 9%nat 9%bv eq_refl) in Q9.
    prreg HS (8%bv : bv 5) Q8. rewrite (awdR_reg (ms_regs ms) 8%nat 8%bv eq_refl) in Q8.
    prreg HS (18%bv : bv 5) Q18. rewrite (awdR_reg (ms_regs ms) 18%nat 18%bv eq_refl) in Q18.
    prreg HS (19%bv : bv 5) Q19. rewrite (awdR_reg (ms_regs ms) 19%nat 19%bv eq_refl) in Q19.
    prreg HS (24%bv : bv 5) Q24. rewrite (awdR_reg (ms_regs ms) 24%nat 24%bv eq_refl) in Q24.
    prreg HS (3%bv : bv 5) Q3. rewrite (awdR_reg (ms_regs ms) 3%nat 3%bv eq_refl) in Q3.
    prreg HS (4%bv : bv 5) Q4. rewrite (awdR_reg (ms_regs ms) 4%nat 4%bv eq_refl) in Q4.
    prreg HS (25%bv : bv 5) Q25. rewrite (awdR_reg (ms_regs ms) 25%nat 25%bv eq_refl) in Q25.
    prreg HS (26%bv : bv 5) Q26. rewrite (awdR_reg (ms_regs ms) 26%nat 26%bv eq_refl) in Q26.
    prreg HS (27%bv : bv 5) Q27. rewrite (awdR_reg (ms_regs ms) 27%nat 27%bv eq_refl) in Q27.
    prreg HS (21%bv : bv 5) Q21.
    pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS eq_refl) as Hms4.
    set (md4 := with_vm_backing (m_vm_lazy md) mat md).
    apply (EXIT cx fpos ly S W ms0 md4 HPRE).
    exists (-36).
    split; [rewrite Hms4 at 1; cbn [ms_pc_val mkst]; reflexivity|].
    split; [rewrite Q21; exact awd_m36|].
    split.
    { apply (aw_base_step_nomem SK B cx fpos ly S W ms md ms0 md4 HB Hmem);
        try (rewrite Hms4 at 1; awd_shape).
      - exact (proj1 (wvb_fds_fs (m_vm_lazy md) mat md)).
      - exact (proj2 (wvb_fds_fs (m_vm_lazy md) mat md)).
      - exact HJ.
      - exact Q2.
      - exact Q9.
      - exact Q8.
      - exact Q18.
      - exact Q19.
      - exact Q24.
      - exact Q3.
      - exact Q4.
      - exact Q25.
      - exact Q26.
      - exact Q27. }
    apply (aw_pf_at B HSEGS cx W (ms_mem ms0) (-36) HP).
    + rewrite Hmem. exact HG.
    + rewrite Hmem. intros a Ha. exact (aw_rd_kept SK B cx fpos ly S W ms md a HPRE HB Ha).
    + intros kbs' tab' nm al HN HT HA HBl.
      assert (Enm : nm = Some sn)
        by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HA | split; assumption]).
      assert (Eal : al = Some sa)
        by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_alias cx)); [exact HBl | split; assumption]).
      rewrite Enm, Eal, (aw_wl_too_long tab' sn sa (nk_sent kbs') (nk_kstate kbs') HSNE Hlong).
      cbn [w_rc w_reqs w_state]. split; [reflexivity | split; reflexivity]. }
  (* |alias| < 256: `bgeu a1,a0` taken, s5 := a0, a0 := s6, the call of fuzz_if_nametoindex *)
  assert (HS : st_ok_pi SEGS VAL (awdR (ms_regs ms))
     (mkSS (AF_reac_link_alias_write + 0x1d0) sr_atoms [] None (mkFacts [(10%nat, mkAF 0 255 0)] [] []))
     (restrict (w_H W) ms)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - unfold awdR. apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (awdR_reg (ms_regs ms) 10%nat 10%bv eq_refl), R10, unsigned_lit_small by lia.
      unfold ALIAS_MAX in Hshort. split; [lia | split; [apply Zmod_1_r | lia]]. }
  pose (RUN := paj_run_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
  paj_run_tok RUN HS HJ SHOK AwBspan; [apply awr_ok_x_nil |].
  assert (Hmem : ms_mem ms0 = ms_mem ms).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms5. cbn [ss_pc setpc] in Hms5.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (2%bv : bv 5) Q2. rewrite (awdR_reg (ms_regs ms) 2%nat 2%bv eq_refl) in Q2.
  prreg HS (9%bv : bv 5) Q9. rewrite (awdR_reg (ms_regs ms) 9%nat 9%bv eq_refl) in Q9.
  prreg HS (8%bv : bv 5) Q8. rewrite (awdR_reg (ms_regs ms) 8%nat 8%bv eq_refl) in Q8.
  prreg HS (18%bv : bv 5) Q18. rewrite (awdR_reg (ms_regs ms) 18%nat 18%bv eq_refl) in Q18.
  prreg HS (19%bv : bv 5) Q19. rewrite (awdR_reg (ms_regs ms) 19%nat 19%bv eq_refl) in Q19.
  prreg HS (24%bv : bv 5) Q24. rewrite (awdR_reg (ms_regs ms) 24%nat 24%bv eq_refl) in Q24.
  prreg HS (3%bv : bv 5) Q3. rewrite (awdR_reg (ms_regs ms) 3%nat 3%bv eq_refl) in Q3.
  prreg HS (4%bv : bv 5) Q4. rewrite (awdR_reg (ms_regs ms) 4%nat 4%bv eq_refl) in Q4.
  prreg HS (25%bv : bv 5) Q25. rewrite (awdR_reg (ms_regs ms) 25%nat 25%bv eq_refl) in Q25.
  prreg HS (26%bv : bv 5) Q26. rewrite (awdR_reg (ms_regs ms) 26%nat 26%bv eq_refl) in Q26.
  prreg HS (27%bv : bv 5) Q27. rewrite (awdR_reg (ms_regs ms) 27%nat 27%bv eq_refl) in Q27.
  prreg HS (10%bv : bv 5) Q10. rewrite (awdR_reg (ms_regs ms) 22%nat 22%bv eq_refl) in Q10.
  prreg HS (20%bv : bv 5) Q20. rewrite (awdR_reg (ms_regs ms) 20%nat 20%bv eq_refl) in Q20.
  prreg HS (21%bv : bv 5) Q21. rewrite (awdR_reg (ms_regs ms) 10%nat 10%bv eq_refl) in Q21.
  prreg HS (22%bv : bv 5) Q22. rewrite (awdR_reg (ms_regs ms) 22%nat 22%bv eq_refl) in Q22.
  prreg HS (23%bv : bv 5) Q23. rewrite (awdR_reg (ms_regs ms) 23%nat 23%bv eq_refl) in Q23.
  rewrite Hms5 at 1.
  set (md5 := with_vm_backing (m_vm_lazy md) mat md) in *.
  (* the base at the call's state *)
  assert (HB5 : aw_base SK B cx fpos ly S W ms0 md5).
  { apply (aw_base_step_nomem SK B cx fpos ly S W ms md ms0 md5 HB Hmem);
      try (rewrite Hms5 at 1; awd_shape).
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md) mat md)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md) mat md)).
    - exact HJ.
    - exact Q2.
    - exact Q9.
    - exact Q8.
    - exact Q18.
    - exact Q19.
    - exact Q24.
    - exact Q3.
    - exact Q4.
    - exact Q25.
    - exact Q26.
    - exact Q27. }
  pose proof (awc_inv_of_base SK B cx fpos ly S W ms0 md5 HB5) as HI5.
  pose proof HI5 as (HJ5 & Hfr5 & Hfs5 & Hperm5 & Hfa5 & Hrav5 & Hsv5 & Hfl5 & HK5 & Hfds5 & Hfs5' & Hro5).
  pose proof (awc_aj_ar SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR5.
  destruct (awc_win SK B cx HPRE) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
  destruct (awc_F B LAWS cx fpos HS1) as (F1 & F2 & F3 & F4 & F5 & F6).
  destruct (awc_pre_misc SK B cx HPRE) as (Hgp & Htp & Hnev & Hside).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560. pose proof FUZZ_IF_NAMETOINDEX_AK_val as HK8272.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  assert (Hsp : spZ (ms_regs ms0) = aw_sp1 cx) by (apply (awc_spZ SK B cx HPRE); rewrite Q2; exact B2).
  assert (Hn1 : 0 < aw_name cx /\ aw_name cx + Z.of_nat (length sn) + 1 <= 2 ^ 64)
    by (destruct (aw_acstr_range SEGS _ _ _ HSN) as (H0 & H1); split; lia).
  assert (A0 : aarg (ms_regs ms0) 0 = aw_name cx)
    by (apply (awc_aarg (ms_regs ms0) 0 (aw_name cx) (eq_trans Q10 R22)); lia).
  assert (Hin : In (AW_CID, fpos) (frames S)) by (rewrite Hfr5; left; reflexivity).
  assert (Hfrm : frame_addr ly AW_CID fpos = aw_F cx fpos) by exact (Hfa5 AW_CID fpos).
  assert (HG5 : aw_gnl_kept cx W (ms_mem ms0)) by (rewrite Hmem; exact HG).
  (* the name and the table at the call's memory *)
  assert (HSN5 : acstr_at SEGS (rdW W (ms_mem ms0)) (aw_name cx) sn).
  { apply (aw_acstr_move SEGS (aw_m0 cx) _ (aw_name cx) sn HSN). intros x Hx.
    apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (aw_rd_kept SK B cx fpos ly S W ms0 md5 x HPRE HB5). left.
    split; [exact HN0|]. exists sn. split; [exact HSN | exact Hx]. }
  pose proof (awc_nk_now HSEGS cx kbs HNK W (ms_mem ms0) HG5) as HNK5.
  pose proof (awc_tab_kept SK B LAWS TB HSEGS cx fpos HPRE HNIN HS1 tab kbs HNK HIT W (ms_mem ms0) kbs HK5 eq_refl)
    as HIT5.
  pose proof HIT as (_ & L80 & HITe).
  destruct (zsh_gnl_ard B TB SEGS ly S W (ms_mem ms0) md5 HAR5) as [ZG1 _].
  pose proof HP as (kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNM0 & _ & _ & HNS0 & _ & _).
  assert (Enm : nm0 = Some sn)
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HNM0 | split; assumption]).
  destruct (HNS0 sn Enm) as (Hapf & Hapg & Hln32 & (Hmr & Hra & Hhv) & _).
  change (aarg (aw_regs cx) 0) with (aw_name cx) in Hapf, Hmr, Hra, Hhv.
  unfold apart_frame in Hapf. change (spZ (aw_regs cx)) with (aw_sp cx) in Hapf.
  destruct (aw_shadow_at SK B LAWS TB cx fpos ly S W ms0 md5 (aw_name cx) (Z.of_nat (length sn) + 1) HPRE HB5
              ltac:(lia)
              ltac:(intros a Ha; unfold aw_name in Ha; apply HRD; left; split; [exact HN0|]; exists sn;
                    split; [exact HSN | lia])
              Hra Hhv) as (Hra5 & Hhv5).
  assert (Rlo : ly_stk_lo ly = ly_stk_lo (aw_lyc cx) /\ ly_stk_hi ly = ly_stk_hi (aw_lyc cx)).
  { pose proof HJ5 as R5. apply (aj_stk_row_eq SK SEGS B) in R5.
    pose proof (awc_pre_j SK B cx HPRE) as Rc. apply (aj_stk_row_eq SK SEGS B) in Rc.
    split; [rewrite (proj1 R5), (proj1 Rc); reflexivity | rewrite (proj2 R5), (proj2 Rc); reflexivity]. }
  eapply SRr_bind.
  { rewrite (lv_sigma LV). change (link_sigma LS_fuzz_if_nametoindex) with FUZZ_IF_NAMETOINDEX_A.
    change (mkCfg (mkst (ms_regs ms0) (Z_to_bv 64 FUZZ_IF_NAMETOINDEX_A) (ms_mem ms0) (seg_rom SEGS)) md5)
      with (cfg_at SEGS FUZZ_IF_NAMETOINDEX_A (ms_regs ms0) (ms_mem ms0) md5).
    apply (NIX (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx)
      (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly S W (ms_mem ms0) md5 (aw_k cx)
      (ms_regs ms0)).
    - (* apre *)
      split; [exact HJ5|]. split; [exact HGx|]. split; [exact Hro5|].
      split; [rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
      split; [unfold raZ; rewrite Q1, unsigned_lit_small; lia|].
      split; [rewrite Q3, B3; exact Hgp|]. split; [rewrite Q4, B4; exact Htp|].
      split; [rewrite Hsp; exact S1al16|].
      split; [rewrite Hsp, HK8272; lia|]. split; [rewrite Hsp; lia|].
      split; [exact Hnev|].
      split; [apply Forall_nil|].
      split; [intros a (r & Hr & _); destruct Hr|].
      intros a (r & Hr & _); destruct Hr.
    - (* the read set: the name, read where the call's read set was *)
      intros a (s & Hcs & Ha). rewrite A0 in Hcs, Ha.
      assert (Es : s = sn) by exact (aw_acstr_unique SEGS _ _ _ _ Hcs HSN5). subst s.
      rewrite Hsp, HK8272.
      apply (akb_sub SEGS B (aw_lyc cx) (aw_Sc cx) ly S (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) _ _ a
               (HRD a (or_introl (conj HN0 (ex_intro _ sn (conj HSN Ha)))))).
      + lia.
      + lia.
      + exact (proj1 Rlo).
      + exact (proj2 Rlo).
      + intros bb mm Hbm. exact (Permutation_in _ (Permutation_sym Hperm5) Hbm).
      + intros c q Hcq. rewrite Hfr5. right. exact Hcq.
      + exact Hfa5.
    - (* the Pre *)
      unfold fuzz_if_nametoindex_apre. exists kbs, tab, sn. rewrite A0.
      split; [exact HNK5|]. split; [exact HIT5|].
      split; [intros x Hx; apply ZG1; unfold NK_IF_NAME, NK_SIZE in *; lia|].
      split; [intros x Hx; apply ZG1; unfold NK_IF_INDEX, NK_SIZE in *; lia|].
      split; [exact HN0|]. split; [exact HSN5|].
      split.
      { unfold astrcmp_arg_ni. split; [lia|]. split; [exact Hln32|]. split; [exact Hmr|].
        split; [exact Hra5|]. split; [exact Hhv5|].
        split; [unfold apart_frame; rewrite Hsp, HK8272; rewrite HK8560 in Hapf; lia|].
        (* the name's tail: visible at the call's memory (aw_tails), carried to this memory by awc_tail_cut *)
        pose proof (proj1 (aw_tails_of_pre cx HPRE) sn ltac:(split; assumption)) as Htl.
        change (aarg (aw_regs cx) 0) with (aw_name cx) in Hapg.
        unfold apart_gnl in Hapg. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr.
        intros a Ha. change (ard SEGS (rdW W (ms_mem ms0)) a) with (aview SEGS (w_H W) (ms_mem ms0) a).
        apply (awc_tail_cut SK B LAWS TB HSEGS cx fpos HPRE ly S W ms0 md5 (aw_name cx + Z.of_nat (length sn))
                 HB5); [| lia | lia | lia | | exact Ha].
        - apply HRD. left. split; [exact HN0|]. exists sn. split; [exact HSN | unfold aw_name; lia].
        - intros x Hx Hm. apply (Htl x Hx). unfold ard. cbv beta. rewrite Hm. reflexivity. }
      intros i n2 ix p Hi Hp Hp64.
      assert (Hilt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      assert (Hp0 : au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (aw_val_mem_move SEGS (rdW W (ms_mem ms0)) (aw_m0 cx) _ 8 p Hp). intros x Hx.
        apply (mbyte_of_aview_eq SEGS _ _ _ _ x x). symmetry. apply HG5.
        change (Z.of_nat 8) with 8 in Hx. unfold NK_IF_NAME, NK_SIZE in *. lia. }
      destruct (awc_tab_pre SK B cx HPRE tab kbs HNK HIT i n2 ix p Hi Hp0) as (A1 & A2 & A4).
      destruct (A4 Hp64) as (Hp1 & Hn32 & Hmrp & Hrap & Hhvp).
      destruct (HITe i n2 ix Hi) as (_ & p' & P' & _ & C' & _).
      pose proof (aws_au64_unique SEGS _ _ _ _ Hp0 P') as Ep. pose proof (aw_acstr_range SEGS _ _ _ C') as Rp.
      rewrite !Z.mod_small in Ep by lia. subst p'.
      destruct (aw_shadow_at SK B LAWS TB cx fpos ly S W ms0 md5 p (Z.of_nat (length n2) + 1) HPRE HB5 ltac:(lia)
                  ltac:(intros a Ha; apply (awc_rd_tab SK B cx HPRE tab kbs HNK HIT i n2 ix p a Hi Hp0 C'); lia)
                  Hrap Hhvp) as (Hrap5 & Hhvp5).
      unfold astrcmp_arg_ni. split; [lia|]. split; [exact Hn32|]. split; [exact Hmrp|].
      split; [exact Hrap5|]. split; [exact Hhvp5|].
      split; [unfold apart_frame in *; change (spZ (aw_regs cx)) with (aw_sp cx) in A1;
              rewrite Hsp, HK8272; rewrite HK8560 in A1; lia|].
      (* the table string's tail: visible at the call's memory (aw_tails), carried here by awc_tail_cut *)
      pose proof (proj2 (aw_tails_of_pre cx HPRE) kbs tab i n2 ix p HNK HIT Hi Hp0 Hp64) as Htl.
      unfold apart_gnl in A2. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmrp.
      intros a Ha. change (ard SEGS (rdW W (ms_mem ms0)) a) with (aview SEGS (w_H W) (ms_mem ms0) a).
      apply (awc_tail_cut SK B LAWS TB HSEGS cx fpos HPRE ly S W ms0 md5 (p + Z.of_nat (length n2))
               HB5); [| lia | lia | lia | | exact Ha].
      + apply (awc_rd_tab SK B cx HPRE tab kbs HNK HIT i n2 ix p _ Hi Hp0 C'). lia.
      + intros x Hx Hm. apply (Htl x Hx). unfold ard. cbv beta. rewrite Hm. reflexivity. }
  (* the return to +0x1ec: fuzz_if_nametoindex's Post, the invariant across the call, section 1 *)
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hfds2 & Hfs2 & HK2 & _ & HS2 & Hperm2 & HPOST).
  rewrite Z.add_0_r in HJ2. rewrite Hsp, HK8272 in HK2. rewrite Q1.
  pose proof (HPOST kbs tab sn HNK5 HIT5 ltac:(rewrite A0; exact HSN5)) as R10'.
  assert (Hfa2 : forall c q, frame_addr ly2 c q = frame_addr (aw_lyc cx) c q).
  { intros c q. transitivity (frame_addr (aw_ly cx) c q).
    - eapply LinkWalkCall.aj_frame_addr. exact HJ2.
    - symmetry. eapply LinkWalkCall.aj_frame_addr. exact (awc_pre_j SK B cx HPRE). }
  assert (KS : forall a, aw_sp cx - 80 <= a < aw_sp cx ->
             aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha. destruct HK2 as (K1 & _). apply K1; [lia | lia |]. intros (r & Hr & _). destruct Hr. }
  assert (KF : forall a, aw_F cx fpos + 504 <= a < aw_F cx fpos + 512 ->
             aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms0) a).
  { intros a Ha. destruct HK2 as (_ & _ & _ & K4 & _). apply (K4 AW_CID fpos a Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfrm. change (fs_frame_bytes AW_CID) with 512. lia.
    - intros (r & Hr & _). destruct Hr. }
  assert (HI6 : awc_inv SK B cx fpos ly2 S2 W2 mem2 md2).
  { split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr5|].
    split; [destruct Hfs5 as (fs & Hfs0); exists (st_fs S2); rewrite HS2 at 1; rewrite Hfs0; apply awc_set_fs_set_fs|].
    split; [exact (Permutation_trans Hperm2 Hperm5)|]. split; [exact Hfa2|].
    split; [rewrite <- Hrav5; apply aws_rdword_eq; intros i Hi; apply KS; lia|].
    split; [intros j Hj; rewrite <- (Hsv5 j Hj); apply aws_rdword_eq; intros i Hi; apply KS; lia|].
    split; [rewrite <- Hfl5; apply aws_rdword_eq; intros i Hi; apply KF; unfold AW_FLAGPTR; lia|].
    split.
    { eapply (akept_trans_ly SK SEGS B LAWS pa_segs_low (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) ly S W
        (ms_mem ms0) W2 mem2 (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) (aw_sp1 cx - 8272) (aw_sp1 cx));
        [rewrite HK8560; lia | lia | exact HK5 | exact HK2 | rewrite HK8560; lia | lia | | | exact Hfa5 | | ].
      - intros bb mm Hbm. exact (Permutation_in _ (Permutation_sym Hperm5) Hbm).
      - intros f Hf. rewrite Hfr5. right. exact Hf.
      - intros a H. exact H.
      - intros a (r & Hr & _). destruct Hr. }
    split; [rewrite Hfds2; exact Hfds5|]. split; [rewrite Hfs2; exact Hfs5'|].
    apply (awc_arodata_call B RELRO_IMG ly S W (ms_mem ms0) W2 mem2 _ _ _ HK2); [|exact Hro5].
    intros a (r & Hr & _). destruct Hr. }
  assert (HG6 : aw_gnl_kept cx W2 mem2).
  { apply (awc_gnl_call B TB HSEGS cx ly S W (ms_mem ms0) W2 mem2 _ _ _ HK2); [|exact HG5].
    intros a (r & Hr & _). destruct Hr. }
  assert (P : forall (r : Z) v, acallee_saved r -> getr (ms_regs ms0) (Z_to_bv 5 r) = v ->
                getr regs2 (Z_to_bv 5 r) = v)
    by (intros r v Hr H; exact (awc_pres (ms_regs ms0) regs2 r v HP2 Hr H)).
  apply (aw_d_tail EXIT SEND cx fpos ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + 28532)) mem2 (seg_rom SEGS)) md2
           sn sa tab kbs HPRE).
  - apply (awc_base_of_inv SK B LAWS cx fpos HNIN HS1); try awd_shape.
    + exact (P 2 _ ltac:(unfold acallee_saved; lia) (eq_trans Q2 B2)).
    + exact (P 9 _ ltac:(unfold acallee_saved; lia) (eq_trans Q9 B9)).
    + exact (P 8 _ ltac:(unfold acallee_saved; lia) (eq_trans Q8 B8)).
    + exact (P 18 _ ltac:(unfold acallee_saved; lia) (eq_trans Q18 B18)).
    + exact (P 19 _ ltac:(unfold acallee_saved; lia) (eq_trans Q19 B19)).
    + exact (P 24 _ ltac:(unfold acallee_saved; lia) (eq_trans Q24 B24)).
    + exact (P 3 _ ltac:(unfold acallee_saved; lia) (eq_trans Q3 B3)).
    + exact (P 4 _ ltac:(unfold acallee_saved; lia) (eq_trans Q4 B4)).
    + exact (P 25 _ ltac:(unfold acallee_saved; lia) (eq_trans Q25 B25)).
    + exact (P 26 _ ltac:(unfold acallee_saved; lia) (eq_trans Q26 B26)).
    + exact (P 27 _ ltac:(unfold acallee_saved; lia) (eq_trans Q27 B27)).
    + exact HI6.
  - exact HG6.
  - reflexivity.
  - exact HNK.
  - exact HIT.
  - exact HSN.
  - exact HN0.
  - exact HSNE.
  - exact HSA.
  - exact HA0.
  - exact Hshort.
  - exact R10'.
  - exact (P 20 _ ltac:(unfold acallee_saved; lia) (eq_trans Q20 R20)).
  - exact (P 21 _ ltac:(unfold acallee_saved; lia) (eq_trans Q21 R10)).
  - exact (P 22 _ ltac:(unfold acallee_saved; lia) (eq_trans Q22 R22)).
  - exact (P 23 _ ltac:(unfold acallee_saved; lia) (eq_trans Q23 R23)).
Qed.

(* ==========================================================================
   3. From the MID cut on a non-empty name and a non-NULL alias: the instrumented check of name[0], the two
      tests, wrapper_strlen(alias), then section 2
   ========================================================================== *)
Lemma aw_arm_call : aw_exit_obl SK B -> aw_send_obl SK B ->
  forall (cx : awcx) fpos ly3 S3 W3 ms3 md3 sn sa,
  aw_pre SK B cx -> aw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
  aw_name cx <> 0 -> acstr_at SEGS (aw_m0 cx) (aw_name cx) sn -> sn <> [] ->
  aw_alias cx <> 0 -> acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa ->
  SRr SEGS W3 (mkCfg ms3 md3) (aw_post SK B cx).
Proof.
  intros EXIT SEND cx fpos ly3 S3 W3 ms3 md3 sn sa HPRE HMID Hn0 Hcs Hsne Ha0 Hca.
  destruct HMID as (Hpc & Hs4 & Hs5 & Hs6 & Hs7 & HGNL & HB).
  pose proof (aw_base_shape SK B cx fpos ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (aw_base_jx SK B cx fpos ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPRE as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (aw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HNIN & _ & _ & HS1 & _ & B2 & B9 & B8 & B18 & B19 & B24 & B3 & B4
    & B25 & B26 & B27 & _).
  pose proof HP as (kbs & tab & nm0 & al0 & HNK & _ & _ & _ & _ & HIT & _ & _ & _ & HNM0 & HAL0 & _ & HNS0 & HAS0
    & _).
  assert (Enm : nm0 = Some sn)
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_name cx)); [exact HNM0 | split; assumption]).
  assert (Eal : al0 = Some sa)
    by (apply (aw_astr_arg_unique SEGS (aw_m0 cx) (aw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HNS0 sn Enm) as (_ & _ & _ & (Hmr & Hra & Hhv) & _).
  destruct (HAS0 sa Eal) as (_ & _ & _ & Hmra & _ & _).
  assert (Hakb : forall a, aw_name cx <= a < aw_name cx + (Z.of_nat (length sn) + 1) ->
     akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a).
  { intros a Ha. unfold aw_name in Ha. apply HRD. left. split; [exact Hn0|]. exists sn.
    split; [exact Hcs | lia]. }
  destruct (aw_shadow_at SK B LAWS TB cx fpos ly3 S3 W3 ms3 md3 (aw_name cx) (Z.of_nat (length sn) + 1)
              HPRE HB ltac:(lia) Hakb Hra Hhv) as (Hra3 & Hhv3).
  assert (Hn1 : 0 < aw_name cx) by (destruct Hcs as ((H0 & _ & _) & _); lia).
  assert (Hn2 : aw_name cx + 1 <= 2 ^ 47 - 1)
    by (unfold aw_name; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia).
  assert (Ha1 : 0 < aw_alias cx) by (destruct Hca as ((H0 & _ & _) & _); lia).
  assert (Ha2 : aw_alias cx + 1 <= 2 ^ 47 - 1)
    by (unfold aw_alias; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmra; lia).
  (* the name's first byte at the cut's memory, which is not 0 *)
  destruct sn as [|b0 sn']; [exfalso; exact (Hsne eq_refl)|].
  assert (Hcs3 : acstr_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (aw_name cx) (b0 :: sn')).
  { apply (aw_acstr_move SEGS (aw_m0 cx) (mrestrict (w_H W3) (ms_mem ms3)) (aw_name cx) (b0 :: sn') Hcs).
    intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (aw_rd_kept SK B cx fpos ly3 S3 W3 ms3 md3 x HPRE HB). left.
    split; [exact Hn0|]. exists (b0 :: sn'). split; [exact Hcs | unfold aw_name in *; lia]. }
  pose proof (aw_abytes_head SEGS (mrestrict (w_H W3) (ms_mem ms3)) (aw_name cx) b0 (sn' ++ [zb 0])
                ltac:(cbn [app] in Hcs3; exact (proj1 Hcs3))) as Hbyte.
  assert (Hb0 : 1 <= bv_unsigned b0 < 256).
  { pose proof (bv_unsigned_in_range 8 b0) as Hr. change (bv_modulus 8) with 256 in Hr.
    pose proof Hcs as (_ & Hnz). split; [|lia].
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [E0|E0]; [|lia].
    exfalso. apply Hnz. left. apply bv_eq. rewrite E0. reflexivity. }
  assert (HEI : img_env VAL A_LIM (awE ms3 (awd_X (bv_unsigned b0)))) by apply awE_img.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (aw_mkst_at W3 ms3 AW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (EBx : U (awE ms3 (awd_X (bv_unsigned b0))) AwBx = SHADOW_OFF).
  { unfold U, AwBx. rewrite (awE_sv ms3 _ 23%nat 23%bv eq_refl), Hs7.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (E22 : U (awE ms3 (awd_X (bv_unsigned b0))) (SOff 22 0) = aw_name cx).
  { unfold U. rewrite (awE_sv ms3 _ 22%nat 22%bv eq_refl), Hs6. apply unsigned_lit_small. lia. }
  assert (E33 : ew (awE ms3 (awd_X (bv_unsigned b0))) 33 = Z_to_bv 64 (bv_unsigned b0)).
  { rewrite (awd_ext ms3 _ 33 1 eq_refl ltac:(unfold A_TEXT; lia)). reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (awE ms3 (awd_X (bv_unsigned b0)))
     (mkSS AW_CUT_MID sr_atoms
        [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
        (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
                  (20%nat, mkAF 1 (2 ^ 47 - 1) 0); (33%nat, mkAF 1 255 0)] [] []))
     (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor; [|constructor].
      unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (awE_reg ms3 _ 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS (awE ms3 (awd_X (bv_unsigned b0))) _ (aw_name cx) 0 1 (SOff 33 0) (bv_unsigned b0)).
      + cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      + change (Z.of_N 1) with 1. lia.
      + rewrite Z.add_0_r. apply val_mem1_of_mbyte; [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hbyte.
    - cbn; tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. split; [|split; [|split; [|split; [|exact I]]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awE_reg ms3 _ 22%nat 22%bv eq_refl), Hs6, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awE_reg ms3 _ 23%nat 23%bv eq_refl), Hs7, unsigned_lit_small
          by (unfold SHADOW_OFF; lia).
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (awE_reg ms3 _ 20%nat 20%bv eq_refl), Hs4, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E33, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]]. }
  assert (SHOK : sh_ok SEGS AwBx [mkSHE 22 0 1] (awE ms3 (awd_X (bv_unsigned b0)))
                   (mrestrict (w_H W3) (ms_mem ms3))).
  { constructor; [|constructor].
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite EBx, E22. split.
    - intros x Hx. apply Hra3. cbn [length] in *. lia.
    - intros a Ha. cbn [Z.min Z.max] in Ha. unfold aw_name in Ha.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. cbn [length] in Hmr.
      unfold SHADOW_OFF. lia. }
  pose (RUN := paj_run_x SK B LAWS (aw_G cx) HGx (aw_XO cx) (aw_OUT cx)).
  paj_run_tok RUN HS HJ3 SHOK AwBspan;
    [ intros a (r0 & Hin & Hw); cbn [In] in Hin; destruct Hin as [<- | []];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; exfalso; lia |].
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & Hw). cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms5. cbn [ss_pc setpc] in Hms5.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (2%bv : bv 5) Q2. rewrite (awE_reg ms3 _ 2%nat 2%bv eq_refl) in Q2.
  prreg HS (9%bv : bv 5) Q9. rewrite (awE_reg ms3 _ 9%nat 9%bv eq_refl) in Q9.
  prreg HS (8%bv : bv 5) Q8. rewrite (awE_reg ms3 _ 8%nat 8%bv eq_refl) in Q8.
  prreg HS (18%bv : bv 5) Q18. rewrite (awE_reg ms3 _ 18%nat 18%bv eq_refl) in Q18.
  prreg HS (19%bv : bv 5) Q19. rewrite (awE_reg ms3 _ 19%nat 19%bv eq_refl) in Q19.
  prreg HS (24%bv : bv 5) Q24. rewrite (awE_reg ms3 _ 24%nat 24%bv eq_refl) in Q24.
  prreg HS (3%bv : bv 5) Q3. rewrite (awE_reg ms3 _ 3%nat 3%bv eq_refl) in Q3.
  prreg HS (4%bv : bv 5) Q4. rewrite (awE_reg ms3 _ 4%nat 4%bv eq_refl) in Q4.
  prreg HS (25%bv : bv 5) Q25. rewrite (awE_reg ms3 _ 25%nat 25%bv eq_refl) in Q25.
  prreg HS (26%bv : bv 5) Q26. rewrite (awE_reg ms3 _ 26%nat 26%bv eq_refl) in Q26.
  prreg HS (27%bv : bv 5) Q27. rewrite (awE_reg ms3 _ 27%nat 27%bv eq_refl) in Q27.
  prreg HS (10%bv : bv 5) Q10. rewrite (awE_reg ms3 _ 20%nat 20%bv eq_refl) in Q10.
  prreg HS (20%bv : bv 5) Q20. rewrite (awE_reg ms3 _ 20%nat 20%bv eq_refl) in Q20.
  prreg HS (22%bv : bv 5) Q22. rewrite (awE_reg ms3 _ 22%nat 22%bv eq_refl) in Q22.
  prreg HS (23%bv : bv 5) Q23. rewrite (awE_reg ms3 _ 23%nat 23%bv eq_refl) in Q23.
  rewrite Hms5 at 1.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  assert (HB4 : aw_base SK B cx fpos ly3 S3 W3 ms md4).
  { apply (aw_base_step_nomem SK B cx fpos ly3 S3 W3 ms3 md3 ms md4 HB Hmem);
      try (rewrite Hms5 at 1; awd_shape).
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HJ3.
    - exact Q2.
    - exact Q9.
    - exact Q8.
    - exact Q18.
    - exact Q19.
    - exact Q24.
    - exact Q3.
    - exact Q4.
    - exact Q25.
    - exact Q26.
    - exact Q27. }
  pose proof (awc_inv_of_base SK B cx fpos ly3 S3 W3 ms md4 HB4) as HI4.
  destruct (awc_win SK B cx HPRE) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
  destruct (awc_pre_misc SK B cx HPRE) as (Hgp & Htp & Hnev & Hside).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof REAC_LINK_ALIAS_WRITE_AK_val as HK8560.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp : spZ (ms_regs ms) = aw_sp1 cx) by (apply (awc_spZ SK B cx HPRE); rewrite Q2; exact B2).
  destruct (awc_strlen_pre SK B LAWS TB HSEGS cx fpos HPRE ly3 S3 W3 ms md4 sa (ms_regs ms) HB4 Ha0 Hca Hsp)
    as (Hca4 & Hstr & Hrd & Htail & Hrrom & Hl32).
  eapply SRr_bind.
  { eapply (aj_gx_strlen_atS SK SEGS B LAWS pa_segs_low (pa_sigma LS___interceptor_trampoline_strlen) ASTRLEN
      (aw_G cx) (aw_XO cx) (aw_OUT cx) W3 (ms_regs ms) (ms_mem ms) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
      (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx) ly3 S3 md4 (aw_k cx)
      (aw_alias cx) sa _ HGx HJ3);
    [ rewrite Hsp; exact S1al16 | rewrite Hsp; lia | rewrite Hsp; lia
    | rewrite Q3, B3; exact Hgp | rewrite Q4, B4; exact Htp | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite Q10; exact Hs4 | exact Ha1
    | exact Hstr | exact Hrd | exact Htail | exact Hrrom ]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10 & Hfr2 & Hpres2 & Hsm2).
  assert (Efd : m_fds md2 = m_fds md4 /\ m_fs md2 = m_fs md4).
  { unfold same_but_materialized in Hsm2. rewrite Hsm2. exact (wvb_fds_fs _ _ _). }
  assert (HI5 : awc_inv SK B cx fpos ly3 S3 W3 mem2 md2).
  { apply (awc_inv_step SK B LAWS RELRO_IMG cx fpos HPRE HS1 ly3 S3 W3 (ms_mem ms) md4 mem2 md2
             (fun a => aw_sp1 cx - ESTACK <= a < aw_sp1 cx) HI4 HJ2).
    - intros a Ha Hn. apply Hfr2; [exact Ha | rewrite Hsp; exact Hn].
    - intros a Ha. cbv beta in Ha. left. rewrite HK8560. lia.
    - exact Hpres2.
    - exact (proj1 Efd).
    - exact (proj2 Efd). }
  assert (HG5 : aw_gnl_kept cx W3 mem2).
  { apply (awc_gnl_step SK B cx HPRE W3 (ms_mem ms) mem2 (fun a => aw_sp1 cx - ESTACK <= a < aw_sp1 cx)).
    - intros a Ha Hn. apply Hfr2; [exact Ha | rewrite Hsp; exact Hn].
    - intros a Ha. cbv beta in Ha. rewrite HK8560. lia.
    - rewrite Hmem. exact HGNL. }
  assert (P : forall (r : Z) v, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = v ->
                getr regs2 (Z_to_bv 5 r) = v)
    by (intros r v Hr H; exact (awc_pres (ms_regs ms) regs2 r v HP2 Hr H)).
  apply (aw_d_len EXIT SEND cx fpos ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 28504)) mem2 (seg_rom SEGS)) md2
           (b0 :: sn') sa tab kbs HPRE).
  - apply (awc_base_of_inv SK B LAWS cx fpos HNIN HS1); try awd_shape.
    + exact (P 2 _ ltac:(unfold acallee_saved; lia) (eq_trans Q2 B2)).
    + exact (P 9 _ ltac:(unfold acallee_saved; lia) (eq_trans Q9 B9)).
    + exact (P 8 _ ltac:(unfold acallee_saved; lia) (eq_trans Q8 B8)).
    + exact (P 18 _ ltac:(unfold acallee_saved; lia) (eq_trans Q18 B18)).
    + exact (P 19 _ ltac:(unfold acallee_saved; lia) (eq_trans Q19 B19)).
    + exact (P 24 _ ltac:(unfold acallee_saved; lia) (eq_trans Q24 B24)).
    + exact (P 3 _ ltac:(unfold acallee_saved; lia) (eq_trans Q3 B3)).
    + exact (P 4 _ ltac:(unfold acallee_saved; lia) (eq_trans Q4 B4)).
    + exact (P 25 _ ltac:(unfold acallee_saved; lia) (eq_trans Q25 B25)).
    + exact (P 26 _ ltac:(unfold acallee_saved; lia) (eq_trans Q26 B26)).
    + exact (P 27 _ ltac:(unfold acallee_saved; lia) (eq_trans Q27 B27)).
    + exact HI5.
  - exact HG5.
  - reflexivity.
  - exact HNK.
  - exact HIT.
  - exact Hcs.
  - exact Hn0.
  - exact Hsne.
  - exact Hca.
  - exact Ha0.
  - exact Hl32.
  - exact H10.
  - exact (P 20 _ ltac:(unfold acallee_saved; lia) (eq_trans Q20 Hs4)).
  - exact (P 22 _ ltac:(unfold acallee_saved; lia) (eq_trans Q22 Hs6)).
  - exact (P 23 _ ltac:(unfold acallee_saved; lia) (eq_trans Q23 Hs7)).
Qed.

(* ==========================================================================
   4. THE ARMS PIECE: the Pre's strings decide the branch
   ========================================================================== *)
Theorem aw_arms : aw_exit_obl SK B -> aw_send_obl SK B -> aw_mid_obl SK B.
Proof.
  intros EXIT SEND cx fpos ly3 S3 W3 ms3 md3 HPRE HMID.
  pose proof HPRE as (_ & _ & HP).
  destruct HP as (kbs & tab & nm & al & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNM & HAL & _).
  destruct nm as [sn|].
  2:{ exact (aw_arm_name_null SK B LAWS HSEGS EXIT cx fpos ly3 S3 W3 ms3 md3 HPRE HMID HNM). }
  destruct HNM as (Hn0 & Hcs).
  destruct al as [sa|].
  2:{ exact (aw_arm_alias_null SK B LAWS HSEGS TB EXIT cx fpos ly3 S3 W3 ms3 md3 sn HPRE HMID Hn0 Hcs HAL). }
  destruct HAL as (Ha0 & Hca).
  destruct sn as [|b sn'].
  - exact (aw_arm_name_empty SK B LAWS HSEGS TB EXIT cx fpos ly3 S3 W3 ms3 md3 sa HPRE HMID Hn0 Hcs Ha0 Hca).
  - exact (aw_arm_call EXIT SEND cx fpos ly3 S3 W3 ms3 md3 (b :: sn') sa HPRE HMID Hn0 Hcs
             ltac:(discriminate) Ha0 Hca).
Qed.

End b.
End a.

About aw_arms.
Print Assumptions aw_arms.
