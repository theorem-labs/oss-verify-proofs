(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 503 of its 550 lines of code are new or changed and 1285 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   from model_decide's return (+0x112c, Op2D.v o2_d_inv) through the verdict's test to the call that
   follows it (listing (internal path) (internal record, sha256 e84d6f0c6974)):

     +0x112c mv s7, a0; +0x1130 a0 := 1
     +0x1134 beq s7, a0 -> +0x1158      V_OURS: the bcmp wrapper (0x4305c, at 0x8393c) on the alias buffer F + 0x1a0
                                       against .str.11 ("reac-pw:served"), 15 bytes, to its return o2_b_inv (+0x116c)
     +0x1138 bnez s7 -> +0xc0c          V_LEAVE_*: the verdict is the answer (o2_u_inv)
     +0x113c .. +0x114c                 V_MARK: model_write(m, name, .str.11) (0x83920, model_write_c.v, the Section
                                       hypothesis MODEL_WRITE), to its return o2_w_inv (+0x1150)

   The bcmp wrapper is the kit's abcmp_realizes (LinkWalkBcmp.v aj_gx_bcmp_at, the Section hypothesis ABCMP),
   applied as Op3C.v does at op_unmark's 0x82ff0.

   o2_dv : forall POST i, FROM POST (o2_u_inv i) -> FROM POST (o2_w_inv i) -> FROM POST (o2_b_inv i) ->
           FROM POST (o2_d_inv i).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C LLVMFuzzerTestOneInputOp2R LLVMFuzzerTestOneInputDec
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp2D LLVMFuzzerTestOneInputOp2Nm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LO2_w : Z := AF_LLVMFuzzerTestOneInput + 0x1150.   (* 0x83924, model_write's return *)
Definition LO2_b : Z := AF_LLVMFuzzerTestOneInput + 0x116c.   (* 0x83940, the bcmp wrapper's return *)
Definition o2v_d_ss : sstate := mkSS LO2_d sr_atoms [] None (mkFacts [] [] []).

(* model_write's answer on model_read's requests and state *)
Definition o2_WW (t kbs : list byte) : wres :=
  write_model lf_tab (Some t) (Some S_SERVED) (r_reqs (o2_RR t kbs)) (r_state (o2_RR t kbs)).

(* the verdict is one of the four *)
Lemma o2_decide_range : forall k a, 0 <= decide k a <= 3.
Proof.
  intros k a. unfold decide, V_MARK, V_OURS, V_LEAVE_VLAN, V_LEAVE_HOST.
  destruct a as [a|]; [destruct (negb (Nat.eqb (length a) 0)); [destruct (has_prefix a); lia|]|];
    (destruct k as [k|]; [destruct (bl_eqb k S_VLAN); lia | lia]).
Qed.

(* the writer's code (srm_write_rc_range over Op3Lib.v u_talk_rc_range) *)
Lemma o2_write_rc_range : forall tab nm al reqs K,
  0 <= k_sock K < 2 ^ 31 -> 0 <= k_send K < 2 ^ 31 -> 0 <= k_end K < 2 ^ 31 ->
  - 2 ^ 32 < w_rc (write_core tab nm al reqs K) < 2 ^ 32.
Proof.
  intros tab nm al reqs K H1 H2 H3.
  assert (EI : E_INVAL = 22) by reflexivity. assert (ED : E_NODEV = 19) by reflexivity.
  assert (EN : E_NAMETOOLONG = 36) by reflexivity.
  unfold write_core. destruct nm as [s|]; [|cbn [w_rc]; lia]. destruct al as [a|]; [|cbn [w_rc]; lia].
  destruct (Nat.eqb (length s) 0); [cbn [w_rc]; lia|].
  destruct (ALIAS_MAX <=? Z.of_nat (length a)); [cbn [w_rc]; lia|]. cbv zeta.
  destruct (index_of tab s =? 0); [cbn [w_rc]; lia|].
  cbn [w_rc]. apply u_talk_rc_range; assumption.
Qed.

(* a beq of a register against a small literal *)
Lemma o2_beq_lit : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v =? c).
Proof.
  intros E n v c H Hv Hc. rewrite branch_eq_U, U_SOff, H, !U_lit by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, !Z.mod_small by lia. reflexivity.
Qed.

(* the model's answer on each path *)
Lemma o2_MM_open : forall t kbs gbs, (0 < length t)%nat -> r_rc (o2_RR t kbs) = 0 ->
  o2_MM (Some t) kbs gbs =
    (let v := decide (Some (r_kind (o2_RR t kbs))) (Some (r_alias (o2_RR t kbs))) in
     if v =? V_MARK
     then if negb (w_rc (o2_WW t kbs) =? 0)
          then Mres (w_rc (o2_WW t kbs)) (mk_names gbs) (w_reqs (o2_WW t kbs)) (w_state (o2_WW t kbs))
          else Mres v (remember (mk_names gbs) t) (w_reqs (o2_WW t kbs)) (w_state (o2_WW t kbs))
     else if (v =? V_OURS) && bl_eqb (r_alias (o2_RR t kbs)) S_SERVED
          then Mres v (remember (mk_names gbs) t) (r_reqs (o2_RR t kbs)) (r_state (o2_RR t kbs))
          else Mres v (mk_names gbs) (r_reqs (o2_RR t kbs)) (r_state (o2_RR t kbs))).
Proof.
  intros t kbs gbs Hl Hr. unfold o2_MM, o2_mm. destruct (Nat.eqb_spec (length t) 0) as [E|_]; [lia|].
  fold (o2_RR t kbs). rewrite Hr. cbn [Z.eqb negb]. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ABCMP : forall fy : YK11.FPState, @abcmp_realizes fy rc SEGS B (pa_sigma LS___interceptor_trampoline_bcmp).

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* +0x1150: model_write has answered (a0); s7 holds V_MARK *)
Definition o2_w_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_w ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\ r_rc (o2_RR t kbs) = 0 /\
  decide (Some (r_kind (o2_RR t kbs))) (Some (r_alias (o2_RR t kbs))) = V_MARK /\
  getr (ms_regs ms3) 23 = w64 V_MARK /\
  getr (ms_regs ms3) 10 = w64 (w_rc (o2_WW t kbs)) /\ - 2 ^ 32 < w_rc (o2_WW t kbs) < 2 ^ 32 /\
  md_reqs mbs = w_reqs (o2_WW t kbs).

(* +0x116c: the bcmp wrapper has answered (a0, 0 exactly when the alias is "reac-pw:served"); s7 holds V_OURS *)
Definition o2_b_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_b ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\ r_rc (o2_RR t kbs) = 0 /\
  decide (Some (r_kind (o2_RR t kbs))) (Some (r_alias (o2_RR t kbs))) = V_OURS /\
  getr (ms_regs ms3) 23 = w64 V_OURS /\ md_reqs mbs = r_reqs (o2_RR t kbs) /\
  (getr (ms_regs ms3) 10 = w64 0 <-> r_alias (o2_RR t kbs) = S_SERVED).

Lemma o2_dv : forall POST i,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_w_inv i) -> FROM POST (o2_b_inv i) ->
  FROM POST (o2_d_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HU HW HBC cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HD.
  destruct HD as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R18 & R21 & R22 & R26 & HM
    & Hare & Hr0 & Hrq & Hks & Hkd & Hal & R10).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  set (RR := o2_RR t kbs) in *.
  set (v := decide (Some (r_kind RR)) (Some (r_alias RR))) in *.
  pose proof (o2_decide_range (Some (r_kind RR)) (Some (r_alias RR))) as Hv. fold v in Hv.
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2v_d_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_d)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2v_d_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LO2_d ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_d)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E) by exact (lf_env_agree0 (ms_regs ms3)).
  paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x1134 taken: V_OURS, the bcmp wrapper on the alias *)
    rewrite (o2_beq_lit E 10 v 1 E10 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_frame_nil _ _ _ HFrA) as KA. pose proof (kagree_frame_nil _ _ _ HFrB) as KB0.
    assert (KAB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)))
      by (intros a0 Ha0; rewrite (KB0 a0 Ha0), (KA a0 Ha0); reflexivity).
    assert (GAB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
    pmkst HS.
    assert (Hpc : ss_pc ssA = pa_sigma LS___interceptor_trampoline_bcmp) by reflexivity.
    rewrite Hpc.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (12%bv : bv 5) Q12. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    try rewrite (img_env_codeptr E HEI) in Q1.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q10.
    rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19. rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20.
    rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl) in Q23.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (E251 : ew E 251 = Z_to_bv 64 0x21100).
    { unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 251%nat with (A_OBJ 10).
      rewrite (lv_obj LV 10 ltac:(unfold link_nobj; lia)). reflexivity. }
    rewrite E251 in Q11.
    assert (HMB : o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 msB md4)
      by exact (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs gbs
        T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msB md4 HM SH_M_len KAB (fun a _ H => H) GAB Fd Fs Q2 Q3 Q4 Q8 Q9 Q19 Q24
        Q25 Q27).
    pose proof HMB as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatnA & _).
    pose proof HjbkA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROA & _).
    destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly3 S3 W3 (ms_mem msB) md4 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
    destruct (o2r_buf_shadow cx fp W3 msB LO_B1A0 256 HfsA F32 F4 Fc ltac:(right; split; reflexivity)) as (BRA & BHV).
    destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
      (ms_mem msB) md4 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    pose proof alloc_ceiling_lt as CL.
    assert (Rsp : spZ (ms_regs msB) = lf_sp1 cx).
    { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
    pose proof (acstr_keep SEGS (fun _ => False) _ _ _ _ KAB (fun _ _ H => H) Hal) as HalA.
    (* .str.11, "reac-pw:served", texts[1] *)
    pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
    repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
    match goal with Hh : forallb _ (seq 0 11) = true |- _ => rename Hh into KTx end.
    pose proof (kp_forallb_seq _ _ KTx 1 ltac:(lia)) as KT1. cbv beta zeta in KT1.
    apply andb_prop in KT1 as [_ KS1].
    change (fst (nth 1 KP_TEXTS (0, []))) with 0x21100 in KS1.
    destruct (kp_kstr_acstr B (w_H W3) (ms_mem msB) _ _ HROA KS1) as (HSV & _ & _).
    change (map (Z_to_bv 8) (snd (nth 1 KP_TEXTS (0, [])))) with S_SERVED in HSV.
    unfold kp_kstr_b in KS1.
    repeat match type of KS1 with (_ && _)%bool = true => apply andb_prop in KS1 as [KS1 ?] end.
    match goal with Hh : kp_hull_b _ _ = true |- _ => rename Hh into KH1 end.
    match goal with Hh : kp_ra_b _ _ = true |- _ => rename Hh into KR1 end.
    pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _). pose proof HARA as (MA & _).
    assert (SVra : range_addressable (aview SEGS (w_H W3) (ms_mem msB)) SHADOW_OFF 0x21100 15)
      by exact (kp_ra B TB ly3 S3 _ _ _ MA KR1).
    assert (SVhv : shadow_hull_vis (aview SEGS (w_H W3) (ms_mem msB)) 0x21100 15)
      by exact (kp_hull B TB ly3 S3 _ _ _ MA KH1).
    set (F := lf_F cx fp) in *.
    assert (BUFP : forall a, F + LO_B1A0 <= a < F + LO_B1A0 + 15 -> aview SEGS (w_H W3) (ms_mem msB) a <> None)
      by (intros a Ha; apply aview_some_of_apresent; exact (proj1 (Fpres a ltac:(unfold LO_B1A0 in *; clia)))).
    assert (SVP : forall a, 0x21100 <= a < 0x21100 + 15 -> aview SEGS (w_H W3) (ms_mem msB) a <> None)
      by (intros a Ha; apply (u_cstr_some _ _ _ _ a HSV); rewrite u_served_len; clia).
    assert (BUFP' : forall i0, 0 <= i0 < 15 -> aview SEGS (w_H W3) (ms_mem msB) (F + LO_B1A0 + i0) <> None)
      by (intros i0 Hi0; apply BUFP; clia).
    change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_bcmp)) (ms_mem msB)
      (seg_rom SEGS)) md4) with (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_bcmp))
      (ms_mem msB) (seg_rom SEGS)) md4).
    eapply SRr_bind.
    { eapply (@aj_gx_bcmp_at fy rc SK SEGS B LAWS pa_segs_low _ (ABCMP fy)) with (x := F + LO_B1A0) (y := 0x21100) (n := 15).
      - exact HGX.
      - exact HJ.
      - rewrite Rsp. exact H16.
      - rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
      - rewrite Rsp. unfold LLVMF_STK in *. clia.
      - rewrite Q3, R3. exact (proj1 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
      - rewrite Q4, R4. exact (proj2 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)).
      - reflexivity.
      - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite Q10, R21. reflexivity.
      - rewrite Q11. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - unfold LO_B1A0. clia.
      - unfold LO_B1A0. clia.
      - lia.
      - lia.
      - intros a Ha. split; [exact (BUFP a Ha)|]. rewrite Rsp. unfold ESTACK, LO_B1A0, LLVMF_STK in *. clia.
      - intros a Ha. split; [exact (SVP a Ha)|]. rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
      - intros a Ha. rewrite Rsp. unfold ESTACK, LO_B1A0, LLVMF_STK in *. clia.
      - intros a Ha. rewrite Rsp. unfold ESTACK, LLVMF_STK in *. clia.
      - unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, LO_B1A0 in *. clia.
      - unfold amem_range. left. unfold kLowMemEnd. lia.
      - rewrite <- ard_aview. apply (md_ra_sub _ (F + LO_B1A0) 256); [exact BRA | lia | lia].
      - intros _. rewrite <- ard_aview. apply (md_hull_sub _ (F + LO_B1A0) 256); [exact BHV | lia | lia | lia].
      - exact SVra.
      - intros _. exact SVhv. }
    cbv beta. intros W2 c2 HWle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HRES & HKP2 & HPR2 & HSM2).
    set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
    change mem2 with (ms_mem ms2) in HJ2, HKP2, HPR2.
    assert (Fd2 : m_fds md2 = m_fds md4) by (unfold same_but_materialized in HSM2; rewrite HSM2; reflexivity).
    assert (Fs2 : m_fs md2 = m_fs md4) by (unfold same_but_materialized in HSM2; rewrite HSM2; reflexivity).
    set (X2 := fun a => ~ (0 <= a < 2 ^ 64) \/ (lf_sp1 cx - 2 * ESTACK <= a < lf_sp1 cx)).
    assert (KB2 : kagree SEGS X2 (rdW W3 (ms_mem msB)) (rdW W3 (ms_mem ms2))).
    { apply kagree_of_aview. intros a Ha. unfold X2 in Ha. apply HKP2; [tauto|]. rewrite Rsp. tauto. }
    assert (GB2 : mem_grows (rdW W3 (ms_mem msB)) (rdW W3 (ms_mem ms2))) by exact (ar_grows _ _ _ HPR2).
    assert (NX2 : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
       lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> ~ X2 a).
    { intros a Hf HXa. destruct (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
        cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 msB md4 a HB HJ Hfr HjbkA HblkA Hf) as (R0 & R1).
      unfold X2 in HXa. unfold ESTACK, LLVMF_STK in *. clia. }
    pose proof (ar_pres _ _ HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
    apply (HBC cx fy fp k2 ly3 S3 W3 ms2 md2 HB Hfx HJ2 Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split.
    { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
      rewrite Q1. unfold LO2_b, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
    cbn [ms_regs ms2 mkst].
    split; [rewrite P20, Q20; exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite P22, Q22; exact R22|]. split; [rewrite P26, Q26; exact R26|].
    split.
    { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP X2 i md mk P N kbs mbs gbs T3 SH_M cx fp k2
        ly3 S3 W3 msB md4 ms2 md2 HMB SH_M_len KB2 NX2 GB2 ltac:(rewrite Fd2; exact Fd) ltac:(rewrite Fs2; exact Fs));
        cbn [ms_regs ms2 mkst]; assumption. }
    split; [exact Hare|]. split; [exact Hr0|]. split; [exact Hc|].
    split; [rewrite P23, Q23, R10, Hc; reflexivity|]. split; [exact Hrq|].
    fold RR. rewrite HRES. rewrite <- (u_cmp15 W3 (ms_mem msB) (F + LO_B1A0) 0x21100 _ HalA BUFP' HSV).
    reflexivity.
  - (* +0x1134 not taken: v <> V_OURS *)
    rewrite (o2_beq_lit E 10 v 1 E10 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hc1.
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    rename ms into msA2, HF into HFA2, HFr into HFrA2, HG into HGA2.
    pose proof (kagree_frame_nil _ _ _ HFrA) as KA1. pose proof (kagree_frame_nil _ _ _ HFrA2) as KA2.
    assert (KA0 : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA2)))
      by (intros a0 Ha0; rewrite (KA2 a0 Ha0), (KA1 a0 Ha0); reflexivity).
    assert (GA0 : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA2))) by (intros x Hx; apply HGA2, HGA, Hx).
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    + (* +0x1138 taken: v is a V_LEAVE_*, the answer *)
      rewrite (u_bne0 E 10 v E10 ltac:(lia)) in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_u; [apply awr_ok_x_nil|].
      rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
      pose proof KA0 as KA. pose proof (kagree_frame_nil _ _ _ HFrC) as KC0.
      assert (KAC : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)))
        by (intros a0 Ha0; rewrite (KC0 a0 Ha0), (KA a0 Ha0); reflexivity).
      assert (GAC : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC))) by (intros x Hx; apply HGC, GA0, Hx).
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
      assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
      lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssC := ssx) in HS end.
      assert (KR : forall r : bv 5, sr_get (ss_regs ssC) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
        getr (ms_regs msC) r = getr (ms_regs ms3) r)
        by (intros r Hr; exact (lf_reg_atom fy W3 _ ssC msC _ r HS HA Hr)).
      prreg HS (23%bv : bv 5) Q23. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl) in Q23.
      apply (HU cx fy fp k2 ly3 S3 W3 msC md5 HB Hfx HJ Hfr).
      exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
      split; [exact (lf_shape_of_st_ok fy W3 _ ssC msC HS eq_refl)|].
      split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
      split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
      split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
      split.
      { apply (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs gbs
          T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msC md5 HM SH_M_len KAC (fun a _ H => H) GAC Fd5 Fs5);
          rewrite KR by (vm_compute; reflexivity); reflexivity. }
      rewrite (o2_MM_open t kbs gbs Hlt Hr0). cbv zeta. fold RR. fold v.
      replace (v =? V_MARK) with false by (symmetry; apply Z.eqb_neq; unfold V_MARK; exact Hc).
      replace (v =? V_OURS) with false by (symmetry; apply Z.eqb_neq; unfold V_OURS; exact Hc1).
      cbn [andb m_rc m_reqs m_marks].
      split; [rewrite Q23; exact R10|]. split; [exact Hrq|]. destruct Hare as (_ & Hm). symmetry; exact Hm.
    + (* +0x1138 not taken: V_MARK; model_write(m, name, .str.11) *)
      rewrite (u_bne0 E 10 v E10 ltac:(lia)) in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
      paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      pose proof KA0 as KA. pose proof (kagree_frame_nil _ _ _ HFrB) as KB0.
      assert (KAB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB)))
        by (intros a0 Ha0; rewrite (KB0 a0 Ha0), (KA a0 Ha0); reflexivity).
      assert (GAB : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, GA0, Hx).
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
      assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
      lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
      pmkst HS.
      assert (Hpc : ss_pc ssA = pa_sigma LS_model_write) by reflexivity.
      rewrite Hpc, (lv_sigma LV).
      replace (link_sigma LS_model_write) with MODEL_WRITE_A by reflexivity.
      prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
      prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
      prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
      prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
      prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      try rewrite (img_env_codeptr E HEI) in Q1.
      rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
      rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q10.
      rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q11.
      rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8. rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9.
      rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
      rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20.
      rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl) in Q23.
      rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
      rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
      assert (E251 : ew E 251 = Z_to_bv 64 0x21100).
      { unfold E. rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia). change 251%nat with (A_OBJ 10).
        rewrite (lv_obj LV 10 ltac:(unfold link_nobj; lia)). reflexivity. }
      rewrite E251 in Q12.
      assert (HMB : o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 msB md4)
        by exact (o2_mem2_carry B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP (fun _ => False) i md mk P N kbs mbs gbs
          T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msB md4 HM SH_M_len KAB (fun a _ H => H) GAB Fd Fs Q2 Q3 Q4 Q8 Q9 Q19 Q24
          Q25 Q27).
      pose proof HMB as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatnA & _).
      pose proof (lf_data_of_nm _ _ _ _ _ _ _ HdatnA Hare) as HdatA.
      pose proof (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
      pose proof (lv_text LV) as HBASE.
      pose proof HblkA as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
        & Bamm & Bamk).
      pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _). pose proof HARA as (MA & _).
      destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem msB) md4 md MD_SIZE HARA Bmd) as (_ & Bm4 & Bmceil & _).
      change (req_size MD_SIZE) with 8856 in Bmceil.
      pose proof HdatA as (Dk & Dwf & Dtab & _ & _ & _ & Dmd & Dmwf & _ & _ & _ & _ & Dgn & _).
      pose proof asan_consts as ((C1a & C1b) & _).
      pose proof alloc_ceiling_lt as CL.
      destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
        (ms_mem msB) md4 k2 HB HJ) as (Hs1 & H16 & Hlo & H47).
      assert (Rsp : spZ (ms_regs msB) = lf_sp1 cx).
      { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. clia. }
      pose proof HjbkA as (Jk & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
      assert (HK8 : 0 <= MODEL_WRITE_AK <= LLVMF_STK - 448) by (rewrite MODEL_WRITE_AK_val; unfold LLVMF_STK; lia).
      assert (HKc : alloc_ceiling <= spZ (ms_regs msB) - MODEL_WRITE_AK)
        by (rewrite Rsp, MODEL_WRITE_AK_val; clear - Hlo; unfold LLVMF_STK in *; lia).
      destruct (o2_name_rt B TB HSEGS ly3 S3 W3 (ms_mem msB) md4 (ms_regs msB) MODEL_WRITE_AK s t HARA HRO Dgn HKc Hw)
        as (Hac & Hrt & Hs16 & Hl11 & Hloc).
      assert (Hsb : 0x10000 <= s < 0x654000) by (clear - Hs16 Hloc; unfold LA_G_NL, LA_G_NAMES, G_NAMES_SIZE in *; lia).
      assert (Ra0 : aarg (ms_regs msB) 0 = md) by (rewrite ar_aarg0, Q10, R22; unfold w64; apply unsigned_lit_small; clia).
      assert (Ra1 : aarg (ms_regs msB) 1 = s) by (rewrite ar_aarg1, Q11, R20; unfold w64; apply unsigned_lit_small;
        clear - Hsb; lia).
      assert (Ra2 : aarg (ms_regs msB) 2 = 0x21100) by (rewrite ar_aarg2, Q12; reflexivity).
      destruct (lf_mdl_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB
        cx fp ly3 S3 W3 (ms_mem msB) md4 k2 md mk T3 (ms_regs msB) MODEL_WRITE_AK HB HJ HblkA Rsp HK8)
        as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
      (* .str.11, "reac-pw:served", texts[1] *)
      pose proof (kp_img_here B TB HSEGS) as KI. unfold kp_img_b in KI.
      repeat match type of KI with (_ && _)%bool = true => apply andb_prop in KI as [KI ?] end.
      match goal with Hh : forallb _ (seq 0 11) = true |- _ => rename Hh into KTx end.
      pose proof (kp_forallb_seq _ _ KTx 1 ltac:(lia)) as KT1. cbv beta zeta in KT1.
      apply andb_prop in KT1 as [_ KS1].
      change (fst (nth 1 KP_TEXTS (0, []))) with 0x21100 in KS1.
      destruct (kp_kstr_acstr B (w_H W3) (ms_mem msB) _ _ HRO KS1) as (HSV & _ & _).
      change (map (Z_to_bv 8) (snd (nth 1 KP_TEXTS (0, [])))) with S_SERVED in HSV.
      unfold kp_kstr_b in KS1.
      repeat match type of KS1 with (_ && _)%bool = true => apply andb_prop in KS1 as [KS1 ?] end.
      match goal with Hh : kp_hull_b _ _ = true |- _ => rename Hh into KH1 end.
      match goal with Hh : kp_ra_b _ _ = true |- _ => rename Hh into KR1 end.
      match goal with Hh : kp_somes_b _ (0x21100 + _ + 1) _ = true |- _ => rename Hh into KSo end.
      pose proof (kp_ard_here B TB HSEGS) as KA'. unfold kp_ard_b in KA'.
      repeat match type of KA' with (_ && _)%bool = true => apply andb_prop in KA' as [KA' ?] end.
      match goal with Hh : forallb _ (seq 0 11) = true |- _ => rename Hh into KAT end.
      pose proof (kp_forallb_seq _ _ KAT 1 ltac:(lia)) as KAs. cbv beta zeta in KAs.
      change (fst (nth 1 KP_TEXTS (0, []))) with 0x21100 in KAs.
      change (S (length (snd (nth 1 KP_TEXTS (0, []))))) with 15%nat in KAs.
      destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (HIMG & _).
      change (mkCfg (mkst (ms_regs msB) (Z_to_bv 64 MODEL_WRITE_A) (ms_mem msB) (seg_rom SEGS)) md4)
        with (@cfg_at fy SEGS MODEL_WRITE_A (ms_regs msB) (ms_mem msB) md4).
      eapply (@ar_leaf_call fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy).
      * exact (MODEL_WRITE fy).
      * exact HB.
      * exact HJ.
      * exact HRO.
      * rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
      * unfold raZ. rewrite Q1, HBASE. rewrite unsigned_lit_small by (unfold link_text; lia). unfold link_text. lia.
      * rewrite Q3, R3. exact Gp.
      * rewrite Q4, R4. exact Tp.
      * exact Rsp.
      * exact HK8.
      * lia.
      * clear - Jk Hi. pose proof lf_ev_bound as EB. unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *. lia.
      * apply (ar_side_room S3 fp _ Hfr). vm_compute. reflexivity.
      * intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
        destruct Hin as [<- | []]; cbn [fst snd] in Hr.
        apply (ar_ajw_blk B cx fp ly3 S3 md MD_SIZE a Bmd Bmc). unfold MD_SIZE in *. clia.
      * intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
        intros Hro. pose proof (lf_roP_bounds a Hro) as RB.
        destruct Hin as [<- | []]; cbn [fst snd] in Hr.
        unfold YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, MD_SIZE in *. clia.
      * (* the read set *)
        intros a [(Hz1 & s0 & Hs0 & Ha) | [(Hz1 & s0 & Hs0 & Ha) | (bs & i0 & p & s0 & Hbs & Hi0 & Hp & Hs0 & Ha)]].
        -- rewrite Ra1 in Hs0, Ha. pose proof (kp_acstr_unique _ _ _ _ _ Hs0 Hac) as Es. subst s0.
           right; right; left. exact (o2_name_img B TB HSEGS MS la_nul s t HMS HLN Hw a ltac:(clear - Ha; lia)).
        -- rewrite Ra2 in Hs0, Ha. pose proof (kp_acstr_unique _ _ _ _ _ Hs0 HSV) as Es. subst s0.
           rewrite u_served_len in Ha. eapply kp_akbs_of_b; [exact KAs | cbn; clear - Ha; lia].
        -- exact (lf_tab_akb SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
             cx fp ly3 S3 W3 (ms_mem msB) md4 k2 md mk kbs mbs gbs _ _ HB HJ HRO HdatA bs i0 p s0 a Hbs Hi0 Hp Hs0 Ha).
      * (* the Pre *)
        exists mbs, kbs, lf_tab, (Some t), (Some S_SERVED).
        rewrite Ra0, Ra1, Ra2.
        split; [exact Dmd|]. split; [exact Dmwf|]. split; [exact Dk|]. split; [exact Dwf|]. split; [exact Dtab|].
        split; [split; [clear - Hsb; lia | exact Hac]|].
        split; [split; [lia | exact HSV]|].
        split; [exact M1|]. split; [exact M2|].
        split; [intros s1 Hs1'; injection Hs1' as <-; exact (o2r_cmp_of_rt _ _ _ _ _ Hrt)|].
        split.
        { intros i0 n2 ix p Hn Hp Rp.
          exact (proj1 (lf_tab_strcmp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
            cx fp ly3 S3 W3 (ms_mem msB) md4 k2 md mk kbs mbs gbs (ms_regs msB) MODEL_WRITE_AK HB HJ HRO HdatA Rsp HK8
            i0 n2 ix p Hn Hp Rp)). }
        split.
        { intros s1 Hs1'. injection Hs1' as <-. rewrite u_served_len. cbn [Z.of_nat].
          split; [lia|]. split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
          split; [rewrite ard_aview; exact (kp_ra B TB ly3 S3 _ _ _ MA KR1)|].
          split; [rewrite ard_aview; exact (kp_hull B TB ly3 S3 _ _ _ MA KH1)|].
          split; [unfold apart_frame; left; pose proof alloc_ceiling_value as CV; clear - HKc CV; lia|].
          exists (abytes_of SEGS (rdW W3 (ms_mem msB)) (0x21100 + 14 + 1) (Z.to_nat ((- (0x21100 + 14 + 1)) mod 8))).
          rewrite abytes_of_length. split; [|change ((- (0x21100 + 14 + 1)) mod 8) with 1; cbn; lia].
          apply abytes_of_abytes; [lia | cbn; lia|]. intros k0 Hk0.
          exact (kp_somes_mbyte SEGS (rdW W3 (ms_mem msB)) _ _ KSo k0 Hk0). }
        split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7|].
        split; [exact M8|]. split; [exact M9|].
        rewrite (ts_errno B TB); unfold apart, YCbq.off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP, AF0m.TFIB_ERRNO,
          MD_SIZE in *; clia.
      * (* the return, +0x1150 *)
        intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
        rewrite Z.add_0_r in HJ2.
        set (ms2 := @mkst fy regs2 (getr (ms_regs msB) 1) mem2 (seg_rom SEGS)).
        change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
        set (Er := fun a => inFP (model_write_awr (ms_regs msB) (rdW W3 (ms_mem msB))) a) in *.
        assert (LC : lf_call B cx MODEL_WRITE_AK ly3 S3 ly2 S2 W3 (ms_mem msB) W2 (ms_mem ms2) Er).
        { split; [rewrite MODEL_WRITE_AK_val; lia|]. split; [rewrite <- Rsp; exact HKc|].
          split; [exact Hkp | exact Hsk]. }
        assert (HE : forall a, Er a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016)).
        { intros a (r & Hin & Hr). unfold model_write_awr in Hin. rewrite Ra0 in Hin.
          destruct Hin as [<- | []]; cbn in Hr. left. exact Hr. }
        pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
        assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
        assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
        pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msB)) md mk HAR2 Pmd Pmk)
          as WC.
        specialize (Hpost mbs kbs lf_tab (Some t) (Some S_SERVED)). rewrite Ra0, Ra1, Ra2 in Hpost.
        destruct (Hpost Dmd Dk Dtab ltac:(split; [clear - Hsb; lia | exact Hac]) ltac:(split; [lia | exact HSV]))
          as (Hrc & (mbs' & Hmd2 & Hmwf2 & Hnx2 & Hso2 & Hse2 & Hrq2 & Hnr2 & Hnm2 & Hmm2)).
        clear Hpost.
        destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
          cx fp MODEL_WRITE_AK ly3 S3 ly2 S2 W3 msB md4 W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs' T3 _ P N SH_M
          HB HJ Hfr LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(rewrite SH_M_len; lia) HsvA HhdA HfsA HslA HcurA HjbkA HblkA HdatA
          Hmd2 Hmwf2 Hnm2 Hmm2) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
        pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
          ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
        pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
        pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26
          & P27).
        pose proof Hdat2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hare2 & _).
        assert (HWW : write_model lf_tab (Some t) (Some S_SERVED) (md_reqs mbs) (md_kstate mbs kbs) = o2_WW t kbs)
          by (unfold o2_WW; rewrite Hrq, Hks; reflexivity).
        rewrite HWW in Hrc, Hrq2.
        assert (WRr : - 2 ^ 32 < w_rc (o2_WW t kbs) < 2 ^ 32).
        { pose proof Dmwf as (_ & _ & Wso & Wse & _). pose proof Dwf as (_ & _ & _ & _ & _ & _ & _ & _ & Wend & _).
          unfold o2_WW, write_model. cbv zeta. cbn [w_rc]. fold RR. apply u_norm_rc_range. apply o2_write_rc_range;
            rewrite <- Hks; unfold md_kstate; cbn [k_sock k_send k_end]; lia. }
        apply (HW cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
        exists md, mk, P, N, s, t, kbs, mbs', gbs, T3.
        split.
        { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
          rewrite Q1. unfold LO2_w, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
        cbn [ms_regs ms2 mkst].
        split; [rewrite P20, Q20; exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
        split; [rewrite P22, Q22; exact R22|]. split; [rewrite P26, Q26; exact R26|].
        split.
        { split; [exact Hi|]. split.
          { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
            rewrite R8, R9. repeat split; assumption. }
          split.
          { unfold o2_kregs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P24, P25, P27, Q19, Q24, Q25, Q27.
            repeat split; assumption. }
          split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|].
          split; [exact Hcur2|]. split; [exact Hjbk3|]. split; [exact Hblk3|].
          split; [exact (lf_data_nm_of _ _ _ _ _ _ _ Hdat2)|]. split; [exact Hop | exact Hns]. }
        split; [exact Hare2|]. split; [exact Hr0|]. split; [exact Hc|].
        split; [rewrite P23, Q23, R10, Hc; reflexivity|].
        split; [exact Hrc|]. split; [exact WRr | exact Hrq2].
Qed.

End a.
