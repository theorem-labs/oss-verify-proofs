(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module paths and module names changed; 274 of its 317 lines of code are new or changed and 548 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: from the MID cut (+0x124) of a call whose name is a non-empty C
   string and whose alias is a C string, through the strlen wrapper, to the LEN cut (+0x14c, a0 = |alias|) (cut interface
   lib/A/Prog/model_writeDefs.v; listing (internal path) (internal record, sha256 2152d78b142c)):
     +0x124..+0x144  `beqz s6` (not taken), the instrumented check of name[0] (shadow entry mkSHE 22 0 1),
                     `beqz s3` (not taken), `lbu name[0]` (atom 32, in [1, 255]), `beqz` (not taken), a0 := s3:
                     a token run that stops at the call of wrapper_strlen
     +0x148          wrapper_strlen(alias): LinkWalkStrS.v aj_gx_strlen_atS, its premises from the Pre carried to
                     the call (model_writeCut.v: the alias's bytes and shadow, the slack after its NUL, the
                     runtime's read-only image)
   The LEN cut `mw_gi_len` is this file's: the piece after it (the length test, index_of and the SEND cut) is
   lib/A/Prog/model_writeArmsD.v.

   Section hypotheses: LAWS, TB, HSEGS (as model_writeCut.v), STRLEN (the strlen wrapper's contract at its
   trampoline, lib/A/Rt/RtClosed.v cmd_strlen_closed).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall LinkWalkStrS.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep model_writeArmsA model_writeCut
model_writeCall model_writeArmsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition MW_LEN : Z := AF_model_write + 0x14c.   (* the return address of wrapper_strlen *)

Ltac mwc_rsame HS ms3 :=
  let Q2 := fresh "Q" in let Q9 := fresh "Q" in let Q8 := fresh "Q" in let Q18 := fresh "Q" in
  let Q27 := fresh "Q" in let Q21 := fresh "Q" in let Q23 := fresh "Q" in let Q19 := fresh "Q" in
  let Q20 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in
  prreg HS (2%bv : bv 5) Q2; rewrite (mwE_reg ms3 _ 2%nat 2%bv eq_refl) in Q2;
  prreg HS (9%bv : bv 5) Q9; rewrite (mwE_reg ms3 _ 9%nat 9%bv eq_refl) in Q9;
  prreg HS (8%bv : bv 5) Q8; rewrite (mwE_reg ms3 _ 8%nat 8%bv eq_refl) in Q8;
  prreg HS (18%bv : bv 5) Q18; rewrite (mwE_reg ms3 _ 18%nat 18%bv eq_refl) in Q18;
  prreg HS (27%bv : bv 5) Q27; rewrite (mwE_reg ms3 _ 27%nat 27%bv eq_refl) in Q27;
  prreg HS (21%bv : bv 5) Q21; rewrite (mwE_reg ms3 _ 21%nat 21%bv eq_refl) in Q21;
  prreg HS (23%bv : bv 5) Q23; rewrite (mwE_reg ms3 _ 23%nat 23%bv eq_refl) in Q23;
  prreg HS (19%bv : bv 5) Q19; rewrite (mwE_reg ms3 _ 19%nat 19%bv eq_refl) in Q19;
  prreg HS (20%bv : bv 5) Q20; rewrite (mwE_reg ms3 _ 20%nat 20%bv eq_refl) in Q20;
  prreg HS (3%bv : bv 5) Q3; rewrite (mwE_reg ms3 _ 3%nat 3%bv eq_refl) in Q3;
  prreg HS (4%bv : bv 5) Q4; rewrite (mwE_reg ms3 _ 4%nat 4%bv eq_refl) in Q4;
  exact (conj Q2 (conj Q9 (conj Q8 (conj Q18 (conj Q27 (conj Q21 (conj Q23 (conj Q19 (conj Q20 (conj Q3 Q4)))))))))).

Lemma mwc_nth_some : forall (l : list byte) n d, (n < length l)%nat -> nth_error l n = Some (nth n l d).
Proof. induction l as [|x l IH]; intros [|n] d H; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.

Lemma mw_sbm_fds2 : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. unfold same_but_materialized in H. rewrite H. apply wvb_fds_fs. Qed.

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

(* ---- the LEN cut: wrapper_strlen has returned |alias| in a0 ---- *)
Definition mw_gi_len (cx : mwcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists sn sa,
  ms_pc_val ms3 = w64 (BASE + MW_LEN) /\
  acstr_at SEGS (mw_m0 cx) (mw_name cx) sn /\ mw_name cx <> 0 /\ sn <> [] /\
  acstr_at SEGS (mw_m0 cx) (mw_alias cx) sa /\ mw_alias cx <> 0 /\
  getr (ms_regs ms3) 10 = w64 (Z.of_nat (length sa)) /\
  getr (ms_regs ms3) 22 = w64 (mw_name cx) /\ getr (ms_regs ms3) 25 = w64 SHADOW_OFF /\
  mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3.

(* ---- the base across a stretch that writes nothing ---- *)
Lemma mw_base_nomem : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 (ms : machine_state) md,
  mw_pre SK B cx -> mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3 ->
  ms_mem ms = ms_mem ms3 ->
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 (ms_mem ms) md (mw_k cx) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  mw_rsame (ms_regs ms3) (ms_regs ms) ->
  mw_base SK B cx fpos NoX ly3 S3 W3 ms md.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 ms md HPX HB Hmem H1 H2 H3 H4 H5 HJ Hfd Hfs HR.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  pose proof asan_consts as ((C1a & C1b) & _).
  apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 ly3 S3 W3 ms md (mw_sp1 cx) (mw_sp1 cx) NoX
           HPX HB H1 H2 H3 H4 H5 HJ eq_refl).
  - unfold mw_base in HB. cbv zeta in HB. tauto.
  - unfold mw_base in HB. cbv zeta in HB. tauto.
  - rewrite Hmem. apply (akept_refl SK SEGS B LAWS pa_segs_low). intros a Ha. lia.
  - lia.
  - lia.
  - intros a [].
  - intros a _ [].
  - intros a _ [].
  - exact HR.
  - exact Hfd.
  - exact Hfs.
Qed.

(* wrapper_strlen (0x43044): lib/A/Rt/RtClosed.v cmd_strlen_closed *)
Hypothesis STRLEN : RtString.astrlen_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strlen).

(* ---- the MID cut to the LEN cut ---- *)
Lemma mw_to_len :
  (forall cx' fpos' ly' S' W' (ms' : machine_state) md', mw_pre SK B cx' ->
     mw_gi_len cx' fpos' ly' S' W' ms' md' -> SRr SEGS W' (mkCfg ms' md') (mw_post SK B cx')) ->
  forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 sn sa,
    mw_pre SK B cx -> mw_gi_mid SK B cx fpos ly3 S3 W3 ms3 md3 ->
    mw_name cx <> 0 -> acstr_at SEGS (mw_m0 cx) (mw_name cx) sn -> sn <> [] ->
    mw_alias cx <> 0 -> acstr_at SEGS (mw_m0 cx) (mw_alias cx) sa ->
    SRr SEGS W3 (mkCfg ms3 md3) (mw_post SK B cx).
Proof.
  intros LEN cx fpos ly3 S3 W3 ms3 md3 sn sa HPX HMID Hn0 Hcs Hsn Ha0 Hca.
  destruct HMID as (Hpc & Hs6 & Hs8 & Hs9 & HB).
  pose proof (mw_base_shape SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof (mw_base_X SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HB) as R19.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  (* the alias's premises *)
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & _ & _ & _ & _ & _ & _ & HAL0 & _ & _ & _ & _ & HAS0 & _).
  assert (Eal : al0 = Some sa)
    by (apply (mw_astr_arg_unique SEGS (mw_m0 cx) (mw_alias cx)); [exact HAL0 | split; assumption]).
  destruct (HAS0 sa Eal) as (Hl32 & Hmra & Hraa & Hhva & Hafr & slack & Hslk & Hslkn).
  assert (Hakba : forall a, mw_alias cx <= a < mw_alias cx + (Z.of_nat (length sa) + 1) ->
     akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a).
  { intros a Ha. apply HRD. right; left. split; [exact Ha0|]. exists sa.
    split; [exact Hca | unfold mw_alias in Ha; lia]. }
  assert (Ha1 : 0 < mw_alias cx) by (destruct Hca as ((H0 & _ & _) & _); lia).
  assert (Ha2 : mw_alias cx + Z.of_nat (length sa) + 1 <= 2 ^ 47 - 1)
    by (unfold mw_alias; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmra; lia).
  (* the name's first byte *)
  destruct sn as [|b0 sn']; [exfalso; exact (Hsn eq_refl)|].
  destruct (mw_name_shok SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 (b0 :: sn') [Z_to_bv 64 (bv_unsigned b0)]
              HPX HB Hs6 Hs9 Hn0 Hcs) as (SHOK & Hn1 & Hn2).
  assert (Hcs3 : acstr_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) (mw_name cx) (b0 :: sn')).
  { apply (mw_acstr_move SEGS (mw_m0 cx) (mrestrict (w_H W3) (ms_mem ms3)) (mw_name cx) _ Hcs).
    intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x).
    apply (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 x HPX HB). apply HRD. left.
    split; [exact Hn0|]. exists (b0 :: sn'). split; [exact Hcs | unfold mw_name in *; lia]. }
  pose proof (mw_abytes_head SEGS (mrestrict (w_H W3) (ms_mem ms3)) (mw_name cx) b0 (sn' ++ [zb 0])
                ltac:(destruct Hcs3 as (Hb3 & _); cbn [app] in Hb3; exact Hb3)) as Hbyte.
  assert (Hb0r : 1 <= bv_unsigned b0 <= 255).
  { pose proof (bv_unsigned_in_range 8 b0) as Hr. change (bv_modulus 8) with 256 in Hr.
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [E0 | E0]; [|lia].
    exfalso. destruct Hcs as (_ & Hnz). apply Hnz. left. apply bv_eq. rewrite E0. reflexivity. }
  set (extra := [Z_to_bv 64 (bv_unsigned b0)]).
  assert (HEI : img_env VAL A_LIM (mwE ms3 extra)) by apply Eimg_env.
  assert (E32 : ew (mwE ms3 extra) 32 = Z_to_bv 64 (bv_unsigned b0))
    by exact (mwE_extra ms3 extra 0 ltac:(unfold A_TEXT; lia)).
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_CUT_MID); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_MID)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 extra)
     (mkSS MW_CUT_MID sr_atoms
        [YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
        (mkFacts [(22%nat, mkAF 1 (2 ^ 47 - 1) 0); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
                  (19%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF 1 255 0)] [] []))
     (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor; [|constructor].
      unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (mwE_reg ms3 extra 22%nat 22%bv eq_refl), Hs6. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS (mwE ms3 extra) _ (mw_name cx) 0 1%N (SOff 32 0) (bv_unsigned b0)).
      + cbn [sv_denot]. rewrite E32, Z.add_0_r. rewrite unsigned_lit_small by lia. reflexivity.
      + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      + cbn. lia.
      + intros k Hk. assert (k = 0%nat) as -> by (cbn in Hk; lia).
        assert (Hle : YO0f.le_byte (bv_unsigned b0) 1 0 = bv_unsigned b0).
        { unfold YO0f.le_byte. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
          replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. rewrite !Z.mod_small by lia.
          reflexivity. }
        change (N.to_nat 1) with 1%nat. replace (mw_name cx + 0 + Z.of_nat 0) with (mw_name cx) by lia.
        rewrite Hbyte, Hle. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    - cbn; tauto.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. split; [|split; [|split; [|split; [|exact I]]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (mwE_reg ms3 extra 22%nat 22%bv eq_refl), Hs6. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (mwE_reg ms3 extra 25%nat 25%bv eq_refl), Hs9. unfold w64.
        rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        split; [lia | split; [apply Zmod_1_r | lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (mwE_reg ms3 extra 19%nat 19%bv eq_refl), R19. unfold w64.
        rewrite unsigned_lit_small by (unfold mw_alias in *; lia).
        split; [unfold mw_alias in *; lia | split; [apply Zmod_1_r | unfold mw_alias in *; lia]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
        split; [lia | split; [apply Zmod_1_r | lia]]. }
  pose (RUN := paj_run_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  paj_run_tok RUN HS HJ3 SHOK MwBspan.
  { cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia|].
    apply awr_ok_x_nil. }
  assert (Hmem : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF.
    cbn [ss_mem]. intros (r0 & Hin & Hw). cbn [In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Hms4. cbn [ss_pc setpc] in Hms4.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite (mwE_reg ms3 extra 19%nat 19%bv eq_refl) in Q10.
  prreg HS (22%bv : bv 5) Q22. rewrite (mwE_reg ms3 extra 22%nat 22%bv eq_refl) in Q22.
  prreg HS (25%bv : bv 5) Q25. rewrite (mwE_reg ms3 extra 25%nat 25%bv eq_refl) in Q25.
  assert (HR : mw_rsame (ms_regs ms3) (ms_regs ms)) by (unfold mw_rsame; mwc_rsame HS ms3).
  set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  assert (HBc : mw_base SK B cx fpos NoX ly3 S3 W3 ms mdc).
  { apply (mw_base_nomem cx fpos ly3 S3 W3 ms3 md3 ms mdc HPX HB Hmem);
      try (rewrite Hms4; reflexivity).
    - exact HJ3.
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat md3)).
    - exact HR. }
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc HPX HBc) as Hspc.
  pose proof HBc as HBc0. unfold mw_base in HBc0. cbv zeta in HBc0.
  destruct HBc0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    Rc3 & Rc4 & _).
  (* the alias at the call *)
  assert (Hva : forall x, mw_alias cx <= x < mw_alias cx + (Z.of_nat (length sa) + 1) ->
            aview SEGS (w_H W3) (ms_mem ms) x = aview SEGS (w_H (mw_W cx)) (mw_memc cx) x).
  { intros x Hx. rewrite Hmem. exact (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 x HPX HB (Hakba x Hx)). }
  destruct (mw_shadow_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 (mw_alias cx) (Z.of_nat (length sa) + 1)
              HPX HB ltac:(lia) Hakba Hraa Hhva) as (Hra3 & Hhv3).
  rewrite <- Hmem in Hra3, Hhv3.
  assert (Hastr : astr_at SEGS W3 (ms_mem ms) (mw_alias cx) sa).
  { destruct Hca as ((_ & _ & Hb) & Hnz). unfold mw_m0 in Hb. split; [|exact Hnz].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite Hva by lia.
    unfold aview. rewrite (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite (mwc_nth_some _ _ (Z_to_bv 8 0)) by (rewrite length_app; cbn [length]; lia). reflexivity. }
  pmkst HS.
  eapply SRr_bind.
  { eapply (aj_gx_strlen_atS SK SEGS B LAWS pa_segs_low (pa_sigma LS___interceptor_trampoline_strlen) STRLEN
      (mw_G cx) (mw_XO cx) (mw_OUT cx) W3 (ms_regs ms) (ms_mem ms) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
      (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly3 S3 mdc (mw_k cx)
      (mw_alias cx) sa (getr (ms_regs ms) 1) HGx HJ3).
    - rewrite Hspc. lia.
    - rewrite Hspc, Hes. lia.
    - rewrite Hspc. lia.
    - rewrite Rc3. pose proof HAPRE as (_ & _ & _ & _ & _ & Hgp & _). exact Hgp.
    - rewrite Rc4. pose proof HAPRE as (_ & _ & _ & _ & _ & _ & Htp & _). exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [unfold MW_LEN, AF_model_write; lia | reflexivity].
    - rewrite Q10, R19. reflexivity.
    - exact Ha1.
    - exact Hastr.
    - unfold aread_ok. split; [lia|]. split; [unfold astr_len; lia|]. split; [unfold astr_len; lia|].
      split.
      + intros a Ha. unfold astr_len in Ha. split.
        * destruct Hastr as (Hab & _). unfold abytes_at in Hab.
          replace a with (mw_alias cx + Z.of_nat (Z.to_nat (a - mw_alias cx))) by lia.
          rewrite (Hab (Z.to_nat (a - mw_alias cx)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
        * unfold ascratch_stk. rewrite Hspc. unfold apart_frame, mw_alias, mw_sp, mw_sp1 in *. lia.
      + unfold astr_len. split; [unfold mw_alias in *; exact Hmra|]. split; [exact Hra3|]. intros _. exact Hhv3.
    - intros a Ha. unfold astr_len in Ha.
      set (e := mw_alias cx + Z.of_nat (length sa)) in *.
      pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as He8.
      pose proof (Z.mod_pos_bound (- (e + 1)) 8 ltac:(lia)) as He8'.
      assert (Hxakb : akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) e)
        by (apply Hakba; unfold e; lia).
      rewrite Hmem.
      apply (mw_tail_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms3 md3 e a HPX HB Hxakb ltac:(unfold e; lia) Ha).
      destruct Hslk as (_ & _ & Hsb).
      change (aarg (mw_regs cx) 2) with (mw_alias cx) in Hsb, Hslkn. fold e in Hsb, Hslkn.
      assert (Hidx : (Z.to_nat (a - (e + 1)) < length slack)%nat) by lia.
      replace a with (e + 1 + Z.of_nat (Z.to_nat (a - (e + 1)))) by lia.
      change (aview SEGS (w_H (mw_W cx)) (mw_memc cx)) with (ard SEGS (mw_m0 cx)).
      unfold ard. rewrite (Hsb _ Hidx).
      destruct (nth_error slack (Z.to_nat (a - (e + 1)))) eqn:En; [cbn; discriminate|].
      apply nth_error_None in En. lia.
    - exact (mw_rtrom SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc HPX HBc (fun a H => match H with end)). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hlen4 & Hfr4 & Hpres4 & Hsm4).
  (* the LEN cut *)
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARc.
  assert (HB4 : mw_base SK B cx fpos NoX ly3 S3 W3 (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4).
  { apply (mw_base_step SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms mdc ly3 S3 W3
             (mkst regs4 (getr (ms_regs ms) 1) mem4 (seg_rom SEGS)) md4 (mw_sp1 cx - ESTACK) (mw_sp1 cx) NoX
             HPX HBc); try reflexivity.
    - exact HJ4.
    - unfold mw_base in HBc. cbv zeta in HBc. tauto.
    - unfold mw_base in HBc. cbv zeta in HBc. tauto.
    - apply (mw_akept_un SK B LAWS TB HSEGS ly3 S3 W3 (ms_mem ms) mdc mem4 _ _ NoX HARc); [lia | lia | | | ].
      + intros a Ha. apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3).
        unfold mw_sp, mw_sp1 in *. rewrite HK, Hes in *. lia.
      + intros a Ha _ Hw. cbn [ms_mem mkst]. apply Hfr4; [exact Ha | rewrite Hspc; exact Hw].
      + intros a _ Hp. exact (Hpres4 a Hp).
    - rewrite Hes. unfold mw_sp, mw_sp1 in *. lia.
    - intros a [].
    - intros a _ [].
    - intros a _ [].
    - exact (mw_rsame_of_pres SK B LAWS TB HSEGS _ _ HP4).
    - exact (proj1 (mw_sbm_fds2 _ _ Hsm4)).
    - exact (proj2 (mw_sbm_fds2 _ _ Hsm4)). }
  apply (LEN cx fpos ly3 S3 W3 _ md4 HPX).
  exists (b0 :: sn'), sa.
  split; [cbn [ms_pc_val mkst]; rewrite Q1; reflexivity|].
  split; [exact Hcs|]. split; [exact Hn0|]. split; [exact Hsn|].
  split; [exact Hca|]. split; [exact Ha0|].
  split; [cbn [ms_regs mkst]; rewrite Hlen4; reflexivity|].
  split; [cbn [ms_regs mkst]; etransitivity; [exact (HP4 22 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact Q22 | exact Hs6]|].
  split; [cbn [ms_regs mkst]; etransitivity; [exact (HP4 25 ltac:(unfold acallee_saved; lia))|];
          etransitivity; [exact Q25 | exact Hs9]|].
  exact HB4.
Qed.

End b.
End a.
