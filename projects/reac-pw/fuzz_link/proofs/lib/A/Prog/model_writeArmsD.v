(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 339 of its 386 lines of code are new or changed and 544 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: from the LEN cut (+0x14c, a0 = |alias|) of
   lib/A/Prog/model_writeArmsC.v to the EXIT cut or the SEND cut (cut interface lib/A/Prog/model_writeDefs.v; listing
   (internal path) (internal record, sha256 2152d78b142c)):
     +0x14c..+0x150  `li a1,255; bgeu a1,a0`: |alias| >= 256 -> s8 := -36, +0x210 (a token run to the EXIT cut)
     +0x15c..+0x160  s8 := |alias|, a0 := s6: a token run to the call of index_of
     +0x164          index_of(name): the own callee's contract (index_of_c.v) at the empty relro window, its Pre from
                     the entry Pre carried to the call (model_writeCut.v, model_writeCall.v)
     +0x168          `beqz a0`: index 0 -> s8 := -19, +0x210 (EXIT cut); otherwise +0x16c, the SEND cut
   The model side of the two refusals is model_writeArmsA.v (write_model on |alias| >= ALIAS_MAX and on index 0).

   Section hypotheses: LAWS, TB, HSEGS (as model_writeCut.v), LV (LinkVals: index_of's entry is the listing's call
   target), IDX (index_of's contract at every rlo rhi; discharge: index_of_aproof).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep model_writeArmsA model_writeCut
model_writeCall model_writeArmsB model_writeArmsC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition MW_IDX : Z := AF_model_write + 0x168.   (* the return address of index_of *)

(* the index index_of answers is one of the table's indices or 0 *)
Lemma mw_index_rng : forall tab s,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab s < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros s H; cbn [index_of]; [lia|].
  destruct (bl_eqb n s).
  - exact (H 0%nat n ix eq_refl).
  - apply IH. intros i n' ix' Hi. exact (H (S i) n' ix' Hi).
Qed.

Lemma mw_ra_sub : forall (rd : reader) p n q k,
  range_addressable rd SHADOW_OFF p n -> p <= q -> q + k <= p + n -> range_addressable rd SHADOW_OFF q k.
Proof. intros rd p n q k H H1 H2 x Hx. apply H. lia. Qed.

Lemma mw_hull_sub : forall (rd : reader) p n q k,
  shadow_hull_vis rd p n -> p <= q -> 0 < k -> q + k <= p + n -> 0 <= p -> shadow_hull_vis rd q k.
Proof.
  intros rd p n q k H H1 H2 H3 H4 s Hs. apply H. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (SHADOW_OFF + p / 8) (SHADOW_OFF + q / 8) 8 ltac:(lia)
    ltac:(pose proof (Z.div_le_mono p q 8 ltac:(lia) H1); lia)).
  pose proof (Z.div_le_mono (SHADOW_OFF + (q + k - 1) / 8) (SHADOW_OFF + (p + n - 1) / 8) 8 ltac:(lia)
    ltac:(pose proof (Z.div_le_mono (q + k - 1) (p + n - 1) 8 ltac:(lia) ltac:(lia)); lia)).
  lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Set Default Proof Using "All".

(* ---- a string of the entry's read set, at a callee's call on the realigned sp ---- *)
Lemma mw_strarg_at : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 (regs' : bvmap 5 word) Kc p s,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  spZ regs' = mw_sp1 cx -> 0 <= Kc <= INDEX_OF_AK ->
  acstr_at SEGS (mw_m0 cx) p s -> astrcmp_arg SEGS (mw_regs cx) MODEL_WRITE_AK (mw_m0 cx) p s ->
  (forall a, p <= a <= p + Z.of_nat (length s) ->
     akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a) ->
  acstr_at SEGS (rdW W3 (ms_mem ms3)) p s /\ astrcmp_arg SEGS regs' Kc (rdW W3 (ms_mem ms3)) p s.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 regs' Kc p s HPX HB Hsp HKc Hcs Harg Hakb.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
  destruct Harg as (Hp0 & Hl32 & Hmr & Hra & Hhv & Hfr & Htl).
  split.
  { apply (mw_acstr_move SEGS (mw_m0 cx) (rdW W3 (ms_mem ms3)) p s Hcs).
    intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    exact (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 x HPX HB (Hakb x Hx)). }
  destruct (mw_shadow_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 p (Z.of_nat (length s) + 1) HPX HB
              ltac:(lia) ltac:(intros a Ha; apply Hakb; lia) Hra Hhv) as (Hra3 & Hhv3).
  split; [exact Hp0|]. split; [exact Hl32|]. split; [exact Hmr|].
  split; [exact Hra3|]. split; [exact Hhv3|].
  split; [unfold apart_frame in *; rewrite Hsp; unfold mw_sp, mw_sp1 in *; lia|].
  intros a Ha.
  change (ard SEGS (rdW W3 (ms_mem ms3)) a) with (aview SEGS (w_H W3) (ms_mem ms3) a).
  apply (mw_tail_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 (p + Z.of_nat (length s)) a HPX HB
           (Hakb (p + Z.of_nat (length s)) ltac:(lia)) ltac:(lia) Ha).
  exact (Htl a Ha).
Qed.

(* ---- the fake kernel's views at a cut before talk ---- *)
Lemma mw_gnl_at : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 kbs tab,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  anlk_at SEGS (mw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs /\ aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs tab.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 kbs tab HPX HB HN HT.
  pose proof HPX as (_ & HRD & _).
  assert (Hmb : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE ->
            mbyte SEGS (rdW W3 (ms_mem ms3)) x = mbyte SEGS (mw_m0 cx) x).
  { intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    exact (mw_gnl_view SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 x HPX HB (fun a H => match H with end) Hx). }
  split.
  - apply (mw_anlk_move SEGS (mw_m0 cx) _ LA_G_NL kbs HN Hmb).
    assert (HWg : forall (mm : word -> option byte) a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS mm a).
    { intros mm a Ha. rewrite HSEGS. apply LA_G_NL_writable. unfold NK_SIZE in Ha. exact Ha. }
    intros x Hx. apply HWg. exact Hx.
  - apply (mw_aiftab_move SEGS (mw_m0 cx) _ LA_G_NL kbs tab HT Hmb).
    intros i n2 ix p Hi HU HC x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 x HPX HB). apply HRD.
    right; right. exists kbs, (Z.of_nat i), p, n2.
    destruct HT as (Hlen & _ & _).
    assert (Hil : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    split; [exact HN|]. split; [lia|]. split; [exact HU|]. split; [exact HC | exact Hx].
Qed.

Hypothesis LV : LinkVals.
(* index_of (0x86784): index_of_c.v, at every rlo rhi *)
Hypothesis IDX : forall rlo rhi, index_of_acontract SK SEGS rlo rhi B.

(* ==========================================================================
   The LEN cut
   ========================================================================== *)
Lemma mw_len : mw_exit_obl SK B -> mw_send_obl SK B ->
  forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3,
    mw_pre SK B cx -> mw_gi_len SK B cx fpos ly3 S3 W3 ms3 md3 ->
    SRr SEGS W3 (mkCfg ms3 md3) (mw_post SK B cx).
Proof.
  intros EXIT SEND cx fpos ly3 S3 W3 ms3 md3 HPX HLEN.
  destruct HLEN as (sn & sa & Hpc & Hcs & Hn0 & Hsn & Hca & Ha0 & Hs10 & Hs22 & Hs25 & HB).
  pose proof (mw_base_shape SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & HM0 & HWF0 & HN0 & HNW0 & HT0 & HNM0 & HAL0 & HRN0 & HRI0
                    & HNS0 & HTS0 & HAS0 & _).
  assert (Enm : nm0 = Some sn)
    by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_name cx)); [exact HNM0 | split; assumption]).
  assert (Eal : al0 = Some sa)
    by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HAS0 sa Eal) as (Hl32 & _).
  assert (Hlenr : 0 <= Z.of_nat (length sa) < 2 ^ 32) by lia.
  assert (HEI : img_env VAL A_LIM (mwE ms3 [])) by apply Eimg_env.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_LEN)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_LEN); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_LEN)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (U10 : bv_unsigned (ew (mwE ms3 []) 10) = Z.of_nat (length sa)).
  { rewrite (mwE_reg ms3 [] 10%nat 10%bv eq_refl), Hs10. unfold w64. apply unsigned_lit_small. lia. }
  assert (U25 : bv_unsigned (ew (mwE ms3 []) 25) = SHADOW_OFF).
  { rewrite (mwE_reg ms3 [] 25%nat 25%bv eq_refl), Hs25. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  assert (SHOK : sh_ok SEGS MwBx [] (mwE ms3 []) (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  pose (RUNTO := paj_run_to_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  pose (RUN := paj_run_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  destruct (Z_lt_ge_dec (Z.of_nat (length sa)) ALIAS_MAX) as [Hshort | Hlong].
  2: {
    (* |alias| >= 256: -36 *)
    assert (HS : st_ok_pi SEGS VAL (mwE ms3 [])
       (mkSS MW_LEN sr_atoms [] None
          (mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 256 (2 ^ 32 - 1) 0)] [] []))
       (restrict (w_H W3) ms3)).
    { rewrite Hrms. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute; reflexivity.
      - constructor.
      - exact I.
      - split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
        + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25. split; [lia | split; [apply Zmod_1_r | lia]].
        + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10. unfold ALIAS_MAX in Hlong.
          split; [lia | split; [apply Zmod_1_r | lia]]. }
    paj_run_to_tok RUNTO HS HJ3 SHOK MwBspan MW_CUT_EXIT; [apply awr_ok_x_nil |].
    assert (Hmem : ms_mem ms = ms_mem ms3).
    { apply functional_extensionality. intros x. apply HF. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ _ HS eq_refl) as Hms4.
    prreg HS (24%bv : bv 5) Q24.
    assert (HR : mw_rsame (ms_regs ms3) (ms_regs ms)) by (unfold mw_rsame; mwc_rsame HS ms3).
    apply (mw_exit_nomem SK B LAWS TB HSEGS EXIT cx fpos ly3 S3 W3 ms3 md3 ms _ (-36) HPX HB Hmem Hms4 HJ3).
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HR.
    - rewrite Q24. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    - intros mbs kbs tab nm al H1 H2 H3 H4 H5.
      assert (Hnm : nm = Some sn) by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_name cx)); [exact H4 | split; assumption]).
      assert (Hal : al = Some sa) by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_alias cx)); [exact H5 | split; assumption]).
      rewrite Hnm, Hal, (mw_wm_too_long tab sn sa _ _ Hsn ltac:(lia)). cbn [w_rc w_reqs w_state].
      split; [reflexivity | split; reflexivity]. }
  (* |alias| < 256: to the call of index_of *)
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 [])
     (mkSS MW_LEN sr_atoms [] None
        (mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 0 255 0)] [] []))
     (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25. split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10. unfold ALIAS_MAX in Hshort.
        split; [lia | split; [apply Zmod_1_r | lia]]. }
  paj_run_tok RUN HS HJ3 SHOK MwBspan.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms4. cbn [ss_pc setpc] in Hms4.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite (mwE_reg ms3 [] 22%nat 22%bv eq_refl) in Q10.
  prreg HS (24%bv : bv 5) Q24. rewrite (mwE_reg ms3 [] 10%nat 10%bv eq_refl) in Q24.
  prreg HS (25%bv : bv 5) Q25. rewrite (mwE_reg ms3 [] 25%nat 25%bv eq_refl) in Q25.
  assert (HR : mw_rsame (ms_regs ms3) (ms_regs ms)) by (unfold mw_rsame; mwc_rsame HS ms3).
  set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  assert (HBc : mw_base SK B cx fpos NoX ly3 S3 W3 ms mdc).
  { apply (mw_base_nomem SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 ms mdc HPX HB Hmem);
      try (rewrite Hms4; reflexivity).
    - exact HJ3.
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HR. }
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc HPX HBc) as Hspc.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARc.
  set (regs5 := ms_regs ms) in *.
  set (m5 := rdW W3 (ms_mem ms)).
  (* the name *)
  destruct (HNS0 sn Enm) as (Hnp0 & Hnl32 & Hnmr & _).
  assert (Hnb : 0 < mw_name cx /\ mw_name cx + Z.of_nat (length sn) + 1 <= 2 ^ 47 - 1)
    by (unfold mw_name; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hnmr; lia).
  assert (A0 : aarg regs5 0 = mw_name cx).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q10, Hs22. unfold w64. apply unsigned_lit_small. lia. }
  assert (Hakbn : forall a, mw_name cx <= a <= mw_name cx + Z.of_nat (length sn) ->
     akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a).
  { intros a Ha. apply HRD. left. split; [exact Hn0|]. exists sn. split; [exact Hcs | exact Ha]. }
  destruct (mw_strarg_at cx fpos ly3 S3 W3 ms mdc regs5 INDEX_OF_AK (mw_name cx) sn HPX HBc Hspc ltac:(lia) Hcs
              (HNS0 sn Enm) Hakbn) as (Hcs5 & Harg5).
  destruct (mw_gnl_at cx fpos ly3 S3 W3 ms mdc kbs0 tab0 HPX HBc HN0 HT0) as (HN5 & HT5).
  pose proof HT0 as (HTl & HT80 & HTe).
  (* index_of's Pre at the call *)
  assert (HPRE5 : index_of_apre SEGS regs5 m5).
  { exists kbs0, tab0, sn.
    assert (HZ : range_addressable (ard SEGS (rdW W3 (ms_mem ms))) SHADOW_OFF LA_G_NL NK_SIZE /\
                 shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms))) LA_G_NL NK_SIZE)
      by (eapply zsh_gnl_ard; eassumption).
    destruct HZ as (Hgra & _).
    split; [exact HN5|]. split; [exact HT5|].
    split; [apply (mw_ra_sub _ LA_G_NL NK_SIZE); [exact Hgra | unfold NK_IF_NAME; lia | unfold NK_IF_NAME, NK_SIZE; lia]|].
    split; [apply (mw_ra_sub _ LA_G_NL NK_SIZE); [exact Hgra | unfold NK_IF_INDEX; lia | unfold NK_IF_INDEX, NK_SIZE; lia]|].
    split; [rewrite A0; exact Hn0|].
    split; [rewrite A0; exact Hcs5|].
    split; [rewrite A0; exact Harg5|].
    intros i n2 ix p Hi Hp5 Hp64.
    assert (Hil : (i < length tab0)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    assert (Hp0 : au64_at SEGS (mw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
    { apply (mw_val_mem_move SEGS m5 (mw_m0 cx) _ 8 p Hp5). intros x Hx. symmetry.
      apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
      apply (mw_gnl_view SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc x HPX HBc (fun a H => match H with end)).
      change (Z.of_nat 8) with 8 in Hx. unfold NK_IF_NAME, NK_SIZE in *. lia. }
    destruct (HTe i n2 ix Hi) as (_ & p' & Hp' & _ & Hc' & _).
    pose proof (mw_acstr_range SEGS _ _ _ Hc') as Hr'.
    assert (p' = p) as -> by (apply (mw_au64_det SEGS (mw_m0 cx) _ p' p Hp' Hp0); lia).
    apply (mw_strarg_at cx fpos ly3 S3 W3 ms mdc regs5 INDEX_OF_AK p n2 HPX HBc Hspc ltac:(lia) Hc'
             (HTS0 i n2 ix p Hi Hp0 Hp64)).
    intros a Ha. apply HRD. right; right. exists kbs0, (Z.of_nat i), p, n2.
    split; [exact HN0|]. split; [lia|]. split; [exact Hp0|]. split; [exact Hc' | exact Ha]. }
  assert (HRD5 : forall a, index_of_ard SEGS regs5 m5 a ->
                   akb SEGS B ly3 S3 (spZ regs5 - INDEX_OF_AK) (spZ regs5) a).
  { intros a (s' & Hs' & Ha). rewrite A0 in Hs', Ha.
    rewrite (mw_acstr_unique SEGS m5 (mw_name cx) s' sn Hs' Hcs5) in Ha.
    apply (mw_akb_call SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc INDEX_OF_AK a HPX HBc ltac:(lia)).
    exact (Hakbn a Ha). }
  assert (Hret5 : YK0s.ret_ok (getr regs5 1))
    by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hra5 : 4096 <= raZ regs5).
  { unfold raZ. rewrite Q1. pose proof pa_B_ok as (HB0 & HB1 & HB2).
    rewrite unsigned_lit_small by lia. lia. }
  pose proof (mw_call_apre SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc INDEX_OF_AK (index_of_awr regs5 m5)
    HPX HBc (fun a H => match H with end) ltac:(lia) Hret5 Hra5
    (fun a H => match inFP_nil a H with end)) as HAPRE5.
  pmkst HS.
  assert (Hsig : pa_sigma LS_index_of = INDEX_OF_A) by (rewrite (lv_sigma LV); reflexivity).
  rewrite Hsig.
  eapply SRr_bind.
  { exact (IDX 0 0 (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (mw_ly cx) (mw_S cx)
      (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly3 S3 W3 (ms_mem ms) mdc (mw_k cx) regs5
      HAPRE5 HRD5 HPRE5). }
  intros W6 c6 _ Hpost.
  destruct (mw_call_back SK B LAWS TB HSEGS cx fpos NoX NoX ly3 S3 W3 ms mdc INDEX_OF_AK _
              (index_of_apost SEGS regs5 m5) W6 c6 HPX HBc ltac:(lia) (fun a H => H)
              (fun a H => match inFP_nil a H with end) (fun a H => match H with end) Hpost)
    as (ly6 & S6 & regs6 & mem6 & md6 & -> & HB6 & KEEP6 & HK6 & HIDX).
  assert (Hidx : getr regs6 10 = w64 (index_of tab0 sn)).
  { apply (HIDX kbs0 tab0 sn HN5 HT5). rewrite A0. exact Hcs5. }
  assert (Hir : 0 <= index_of tab0 sn < 2 ^ 31)
    by (apply mw_index_rng; intros i n ix Hi; exact (proj1 (HTe i n ix Hi))).
  set (ms6 := mkst regs6 (getr regs5 1) mem6 (seg_rom SEGS)) in *.
  pose proof (mw_base_jx SK B cx fpos NoX ly6 S6 W6 ms6 md6 HB6) as HJ6.
  assert (G25 : getr regs6 25 = w64 SHADOW_OFF).
  { etransitivity; [exact (KEEP6 25 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact Q25 | exact Hs25]. }
  assert (G24 : getr regs6 24 = w64 (Z.of_nat (length sa))).
  { etransitivity; [exact (KEEP6 24 ltac:(unfold acallee_saved; lia))|]. etransitivity; [exact Q24 | exact Hs10]. }
  assert (HEI6 : img_env VAL A_LIM (mwE ms6 [])) by apply Eimg_env.
  assert (Hrms6 : restrict (w_H W6) ms6 =
     mkst regs6 (Z_to_bv 64 (BASE + MW_IDX)) (mrestrict (w_H W6) mem6) (seg_rom SEGS)).
  { unfold ms6. rewrite restrict_mkst_fx. rewrite Q1. reflexivity. }
  assert (U25' : bv_unsigned (ew (mwE ms6 []) 25) = SHADOW_OFF).
  { rewrite (mwE_reg ms6 [] 25%nat 25%bv eq_refl). cbn [ms_regs mkst ms6]. rewrite G25. unfold w64.
    apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  assert (SHOK6 : sh_ok SEGS MwBx [] (mwE ms6 []) (mrestrict (w_H W6) (ms_mem ms6))) by constructor.
  pose (RUNTO6 := paj_run_to_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  destruct (Z.eq_dec (index_of tab0 sn) 0) as [Hi0 | Hi0].
  - (* index 0: -19 *)
    assert (HS6 : st_ok_pi SEGS VAL (mwE ms6 [])
       (mkSS MW_IDX (sr_set sr_atoms 10%bv (SLit 0)) [] None
          (mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
       (restrict (w_H W6) ms6)).
    { apply (ast_ok_pi_set_reg_fp (mwE ms6 [])
               (mkSS MW_IDX sr_atoms [] None (mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
               (restrict (w_H W6) ms6) 10%bv (SLit 0)).
      - rewrite Hrms6. apply pa_entry_st_ok_full.
        + apply regs_ok_Eimg_Ereg.
        + vm_compute; reflexivity.
        + constructor.
        + exact I.
        + split; [|split; [exact I | exact I]].
          cbn [f_atoms atoms_ok]. split; [|exact I].
          unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25'. split; [lia | split; [apply Zmod_1_r | lia]].
      - reflexivity.
      - cbn [ms_regs restrict mkst sv_denot ms6]. rewrite Hidx, Hi0. reflexivity. }
    paj_run_to_tok RUNTO6 HS6 HJ6 SHOK6 MwBspan MW_CUT_EXIT; [apply awr_ok_x_nil |].
    assert (Hmem7 : ms_mem ms0 = ms_mem ms6).
    { apply functional_extensionality. intros x. apply HF0. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W6) _ _ _ HS6 eq_refl) as Hms7.
    prreg HS6 (24%bv : bv 5) Q24'.
    assert (HR7 : mw_rsame (ms_regs ms6) (ms_regs ms0)) by (unfold mw_rsame; mwc_rsame HS6 ms6).
    apply (mw_exit_nomem SK B LAWS TB HSEGS EXIT cx fpos ly6 S6 W6 ms6 md6 ms0 _ (-19) HPX HB6 Hmem7 Hms7 HJ6).
    + exact (proj1 (wvb_fds_fs (m_vm_lazy md6) mat0 md6)).
    + exact (proj2 (wvb_fds_fs (m_vm_lazy md6) mat0 md6)).
    + exact HR7.
    + rewrite Q24'. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
    + intros mbs kbs tab nm al H1 H2 H3 H4 H5.
      assert (Hnm : nm = Some sn) by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_name cx)); [exact H4 | split; assumption]).
      assert (Hal : al = Some sa) by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_alias cx)); [exact H5 | split; assumption]).
      rewrite <- (mw_anlk_unique SEGS (mw_m0 cx) LA_G_NL kbs0 kbs HN0 H2) in H3.
      rewrite <- (mw_aiftab_unique SEGS (mw_m0 cx) LA_G_NL kbs0 tab0 tab HT0 H3).
      rewrite Hnm, Hal, (mw_wm_no_dev tab0 sn sa _ _ Hsn Hshort Hi0). cbn [w_rc w_reqs w_state].
      split; [reflexivity | split; reflexivity].
  - (* index not 0: the SEND cut *)
    assert (U10' : bv_unsigned (ew (mwE ms6 []) 10) = index_of tab0 sn).
    { rewrite (mwE_reg ms6 [] 10%nat 10%bv eq_refl). cbn [ms_regs mkst ms6]. rewrite Hidx. unfold w64.
      apply unsigned_lit_small. lia. }
    assert (HS6 : st_ok_pi SEGS VAL (mwE ms6 [])
       (mkSS MW_IDX sr_atoms [] None
          (mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 1 (2 ^ 31 - 1) 0)] [] []))
       (restrict (w_H W6) ms6)).
    { rewrite Hrms6. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute; reflexivity.
      - constructor.
      - exact I.
      - split; [|split; [exact I | exact I]].
        cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
        + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25'. split; [lia | split; [apply Zmod_1_r | lia]].
        + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10'. split; [lia | split; [apply Zmod_1_r | lia]]. }
    paj_run_to_tok RUNTO6 HS6 HJ6 SHOK6 MwBspan MW_CUT_SEND; [apply awr_ok_x_nil |].
    assert (Hmem7 : ms_mem ms0 = ms_mem ms6).
    { apply functional_extensionality. intros x. apply HF0. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
    pose proof (st_ok_pi_restrict_mkst (w_H W6) _ _ _ HS6 eq_refl) as Hms7.
    prreg HS6 (10%bv : bv 5) Q10'. rewrite (mwE_reg ms6 [] 10%nat 10%bv eq_refl) in Q10'.
    prreg HS6 (24%bv : bv 5) Q24'. rewrite (mwE_reg ms6 [] 24%nat 24%bv eq_refl) in Q24'.
    assert (HR7 : mw_rsame (ms_regs ms6) (ms_regs ms0)) by (unfold mw_rsame; mwc_rsame HS6 ms6).
    assert (HB7 : mw_base SK B cx fpos NoX ly6 S6 W6 ms0 (with_vm_backing (m_vm_lazy md6) mat0 md6)).
    { apply (mw_base_nomem SK B LAWS TB HSEGS cx fpos ly6 S6 W6 ms6 md6 ms0 _ HPX HB6 Hmem7);
        try (rewrite Hms7; reflexivity).
      - exact HJ6.
      - exact (proj1 (wvb_fds_fs (m_vm_lazy md6) mat0 md6)).
      - exact (proj2 (wvb_fds_fs (m_vm_lazy md6) mat0 md6)).
      - exact HR7. }
    apply (SEND cx fpos ly6 S6 W6 ms0 _ HPX).
    exists sn, sa, tab0, kbs0.
    split; [rewrite Hms7 at 1; reflexivity|].
    split; [exact HN0|]. split; [exact HT0|]. split; [exact Hcs|]. split; [exact Hn0|]. split; [exact Hsn|].
    split; [exact Hca|]. split; [exact Ha0|]. split; [exact Hshort|].
    split; [rewrite Q10'; cbn [ms_regs mkst ms6]; exact Hidx|].
    split; [exact Hi0|].
    split; [rewrite Q24'; cbn [ms_regs mkst ms6]; exact G24|].
    exact HB7.
Qed.

End b.
End a.
