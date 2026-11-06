(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v; 471 of its 508 lines of code are new or changed and 321 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases after the texts load (kernel_defs.v kin_txt, +0xa74):
   `kn_txt`, and the empty cursor's attribute (kin_acase KP_A0 ka_empty, +0xb10): `kn_a0e` (link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4). The state at +0xa74 and the case's branch conditions: kernel_a014_base.v.
   - a % 6 in {2, 3}: one run to +0xaa0 (kin_acase KP_A23 ka_23); a % 6 = 5: one run to +0xc24 (KP_A5 ka_5).
   - a % 6 = 0 and the empty cursor: one run to the `jal attr_text` at +0xb40 with a0 = w2, a2 = s11 = p, then
     kernel_atcall.v kn_atcall (katstr_img of p, a string of ki_strs by kac_tx_in) to kin_alat (+0xb44).
   - a % 6 = 4: the same with a2 = .str.8.
   - a % 6 = 1: checked_memset(long_alias, 0x61, 300) at +0xaf8, then the call with a2 = long_alias:
     kernel_a014_m.v.
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
   Section hypotheses: LAWS, LV, KI, TB, ATEXT (attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
attr_text_c LinkWalkCall kernel_entry kernel_next kernel_ocall kernel_msg0_kit kernel_atcall kernel_a014_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis ATEXT : attr_text_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* ---- a % 6 in {2, 3}: +0xa74 -> +0xaa0 ---- *)
Lemma tx_c23_ph : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_acase B Rc Rm Ra KP_A23 ka_23) ->
  kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 2 \/ x = 3)).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & Hc & Htx & HT & HAT0).
  destruct HAT0 as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc1 & Hci & Hj & Hm & Hk &
    Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (R23 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 23)) = w64 a) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (HCS : conds_ok E tx_c23).
  { pose proof (tx_conds E a ltac:(rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 23 (Z_to_bv 5 (Z.of_nat 23)) eq_refl), R23;
                                     reflexivity) Ha) as Q.
    destruct Hc as [Hc|Hc]; rewrite Hc in Q; exact Q. }
  assert (HS : st_ok_pi SEGS pa_val E (tx_ss tx_c23) (restrict (w_H W3) ms3)).
  { rewrite HEdef in HCS |- *.
    exact (tx_seat SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 _ a tx_c23 HB HJB HMS HR0 HSL
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) R23 Ha HCS). }
  assert (SHOK : sh_ok SEGS tx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK tx_span (kpc KP_A23).
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold tx_rg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin & Hw); cbn [ss_mem In] in Hin; destruct Hin as [<-|[]];
          unfold tx_rg in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia);
    assert (HMS' : kms KP_A23 msn)
      by (apply (kn_kms_of _ E ssx msn KP_A23 HS'); vm_compute; reflexivity);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word) nx_keep0 HS' HAG
                   ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r tx_keep ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) tx_keep) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r tx_keep Hr)));
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    apply (HN cx fpos k2 ly3 S3 W3 msn mdn HB ltac:(assumption) HFR)
  end.
  exists a, p. split; [exact Ha|]. split; [exact HT|]. split; [split; [exact Htx | exact Hc]|].
  exists c, ci, j, m, k, n, f, adv, hd, kd, left.
  do 11 (split; [assumption|]).
  split; [unfold kw_at in *; rewrite Hmem; exact HW|]. split; [exact I|].
  eapply kat_move; [ exact HAT | exact HMS' | exact HR0' | | exact Hmem | apply incl_refl | exact Hfds | exact Hfs ].
  unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    rewrite HKN by (unfold tx_keep; kn_in); apply (kn_reg_in ms3 _ _ _ HRL); kn_in.
Qed.

(* ---- a % 6 = 5: +0xa74 -> +0xc24 ---- *)
Lemma tx_c5_ph : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_acase B Rc Rm Ra KP_A5 ka_5) ->
  kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 5)).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & Hc & Htx & HT & HAT0).
  destruct HAT0 as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc1 & Hci & Hj & Hm & Hk &
    Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & _).
  pose proof HB as ((_ & HGok & _) & _).
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (R23 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 23)) = w64 a) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (HCS : conds_ok E tx_c5).
  { pose proof (tx_conds E a ltac:(rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 23 (Z_to_bv 5 (Z.of_nat 23)) eq_refl), R23;
                                     reflexivity) Ha) as Q.
    rewrite Hc in Q; exact Q. }
  assert (HS : st_ok_pi SEGS pa_val E (tx_ss tx_c5) (restrict (w_H W3) ms3)).
  { rewrite HEdef in HCS |- *.
    exact (tx_seat SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 _ a tx_c5 HB HJB HMS HR0 HSL
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) R23 Ha HCS). }
  assert (SHOK : sh_ok SEGS tx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK tx_span (kpc KP_A5).
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold tx_rg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin & Hw); cbn [ss_mem In] in Hin; destruct Hin as [<-|[]];
          unfold tx_rg in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia);
    assert (HMS' : kms KP_A5 msn)
      by (apply (kn_kms_of _ E ssx msn KP_A5 HS'); vm_compute; reflexivity);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word) nx_keep0 HS' HAG
                   ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r tx_keep ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) tx_keep) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r tx_keep Hr)));
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    apply (HN cx fpos k2 ly3 S3 W3 msn mdn HB ltac:(assumption) HFR)
  end.
  exists a, p. split; [exact Ha|]. split; [exact HT|]. split; [split; [exact Htx | exact Hc]|].
  exists c, ci, j, m, k, n, f, adv, hd, kd, left.
  do 11 (split; [assumption|]).
  split; [unfold kw_at in *; rewrite Hmem; exact HW|]. split; [exact I|].
  eapply kat_move; [ exact HAT | exact HMS' | exact HR0' | | exact Hmem | apply incl_refl | exact Hfds | exact Hfs ].
  unfold kregs_eq. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    rewrite HKN by (unfold tx_keep; kn_in); apply (kn_reg_in ms3 _ _ _ HRL); kn_in.
Qed.


(* ---- the attr_text call at +0xb40, from the state the run reached at attr_text's entry, to kin_alat (+0xb44) ---- *)
Definition tx_rl' (cx : kcx) (fpos left : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (22%nat, left)].

(* the registers of tx_rl' at a state the run reached, from the cut's *)
Lemma tx_rl'_keep : forall cx fpos left rl (ms3 msn : machine_state),
  kregs_eq ms3 (tx_rl' cx fpos left ++ rl) ->
  (forall r, In r tx_keep -> getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))) ->
  kregs_eq msn (tx_rl' cx fpos left).
Proof.
  intros cx fpos left rl ms3 msn HRL HKN.
  unfold kregs_eq, tx_rl'. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    rewrite HKN by (unfold tx_keep; kn_in); apply (kn_reg_in ms3 _ _ _ HRL); unfold tx_rl'; kn_in.
Qed.

Lemma tx_call : forall POST Rc Rm Ra cx fpos k2 ly3 S3 W3 (ms3 msn : machine_state) md3 mdn pc rl sl
    c ci j m k n f adv hd kd left p s,
  kfrom SK B POST (kin_alat B Rc Rm Ra) ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem msn) mdn k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  Rc cx (c - ci) -> Rm cx (m - k) -> Ra cx left -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci ->
  1 <= m <= 5 -> 0 <= k < m -> (kd = 0 \/ kd = 7) -> 1 <= left <= 4 -> 0 <= hd <= n ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  sl = kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)] ->
  kat B cx fpos pc rl sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3 ->
  kms KP_ATEXT msn -> kregs0 cx msn -> kregs_eq msn (tx_rl' cx fpos left) ->
  getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_ALAT) ->
  getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos) ->
  getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 p ->
  ms_mem msn = ms_mem ms3 -> m_fds mdn = m_fds md3 -> m_fs mdn = m_fs md3 ->
  katstr cx W3 ms3 p s ->
  SRr SEGS W3 (mkCfg msn mdn) (POST cx).
Proof.
  intros POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 msn md3 mdn pc rl sl c ci j m k n f adv hd kd left p s
    HN HB HJ HFR HRc HRm HRa Hc Hci Hj Hm Hk Hkd Hl Hhd HW Esl HAT HMS HR0 HRL' Rr1 Rr10 Rr12 Hmem Hfds Hfs HST.
  set (rlc := (1%nat, BASE + kpc KP_ALAT) :: (10%nat, kW2 cx fpos) :: (12%nat, p) :: tx_rl' cx fpos left).
  assert (HRLc : kregs_eq msn rlc).
  { unfold kregs_eq, rlc. apply Forall_cons; [exact Rr1|]. apply Forall_cons; [exact Rr10|].
    apply Forall_cons; [exact Rr12|]. exact HRL'. }
  assert (HATc : kat B cx fpos KP_ATEXT rlc sl (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 msn mdn)
    by (eapply kat_move; [exact HAT | exact HMS | exact HR0 | exact HRLc | exact Hmem | apply incl_refl
                         | exact Hfds | exact Hfs]).
  assert (HWn : kw_at W3 msn (kW2 cx fpos) n f) by (unfold kw_at in *; rewrite Hmem; exact HW).
  assert (HSTn : katstr cx W3 msn p s) by (unfold katstr in *; rewrite Hmem; exact HST).
  apply (kn_atcall SK B LAWS LV KI ATEXT POST cx fpos k2 ly3 S3 W3 msn mdn KP_ALAT rlc (tx_rl' cx fpos left) sl
           0xf8 0xf3 adv (Some j) n f p s HB HJ HFR HATc HWn
           (tx_getr msn rlc 1%nat 1%bv _ HRLc ltac:(unfold rlc; kn_in) eq_refl)
           ltac:(unfold kpc, AF_kernel, KP_ALAT; lia) ltac:(unfold kpc, AF_kernel, KP_ALAT; reflexivity)
           (tx_getr msn rlc 10%nat 10%bv _ HRLc ltac:(unfold rlc; kn_in) eq_refl)
           (tx_getr msn rlc 12%nat 12%bv _ HRLc ltac:(unfold rlc; kn_in) eq_refl) HSTn).
  - unfold rlc. intros x Hx. cbn [In] in Hx |- *. tauto.
  - unfold tx_rl'. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      unfold acallee_saved; do 5 right; lia.
  - rewrite Esl. reflexivity.
  - intros ly4 S4 W4 ms4 md4 n' f' HJ4 HF4 HK4 HW4 Hle.
    apply (HN cx fpos k2 ly4 S4 W4 ms4 md4 HB HJ4 HF4).
    exists c, ci, j, m, k, n', f', adv, hd, kd, left.
    do 10 (split; [assumption|]). split; [lia|]. split; [exact HW4|]. split; [exact I|].
    rewrite Esl in HK4. exact HK4.
Qed.

(* ---- a % 6 = 0: +0xa74 -> +0xad8 -> +0xb10 -> the attr_text call at +0xb40 with a2 = s11 = p ---- *)
Lemma tx_c0_ph : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_alat B Rc Rm Ra) ->
  kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 0)).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & Hc & Htx & HT & HAT0).
  destruct HAT0 as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc1 & Hci & Hj & Hm & Hk &
    Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & _).
  pose proof HB as ((_ & HGok & _) & _).
  (* the string p *)
  destruct (kac_tx_in SK B KI cx a p HB Ha Htx HT) as (bs & Hin).
  assert (HCOV : forall s, acstr_at SEGS (km0 cx) p s -> forall x, p <= x <= p + Z.of_nat (length s) ->
            kernel_ard SEGS (k_regs cx) (km0 cx) x).
  { intros s Hs x Hx. unfold kernel_ard. right; right; right; right; right; right; left.
    exists ((a / 8) mod 11), p, s. pose proof (Z.mod_pos_bound (a / 8) 11 ltac:(lia)).
    split; [unfold TEXTS_N; lia|]. split; [exact Htx|]. split; [exact Hs | lia]. }
  pose proof (katstr_img SK B LAWS KI TB cx fpos k2 ly3 S3 W3 ms3 md3 p bs HB HJ HJB HKK Hin HT HCOV) as HST.
  pose proof HST as (Hp0 & ((Hpa & Hpb & _) & _) & _). rewrite length_app in Hpb. cbn [length] in Hpb.
  (* the run *)
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (R23 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 23)) = w64 a) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (R21 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos))
    by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (R27 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 27)) = w64 p) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (B21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos).
  { rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl), R21.
    apply unsigned_lit_small. unfold kW2, KN_W2.
    destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    change (fs_frame_bytes KN_CID) with 16384 in F2. lia. }
  assert (B27 : bv_unsigned (ew E 27%nat) = p).
  { rewrite (ER 27%nat (Z_to_bv 5 (Z.of_nat 27)) eq_refl), R27. apply unsigned_lit_small. lia. }
  assert (HCS : conds_ok E tx_c0).
  { pose proof (tx_conds E a ltac:(rewrite (ER 23%nat (Z_to_bv 5 (Z.of_nat 23)) eq_refl), R23; reflexivity) Ha) as Q.
    rewrite Hc in Q. exact Q. }
  assert (HS : st_ok_pi SEGS pa_val E (tx_ss tx_c0) (restrict (w_H W3) ms3)).
  { rewrite HEdef in HCS |- *.
    exact (tx_seat SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 _ a tx_c0 HB HJB HMS HR0 HSL
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) R23 Ha HCS). }
  assert (SHOK : sh_ok SEGS tx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK tx_span.
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold tx_rg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with
  | HS' : st_ok _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin' & Hw); cbn [ss_mem In] in Hin'; destruct Hin' as [<-|[]];
          unfold tx_rg in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia);
    assert (HMS' : kms KP_ATEXT msn)
      by (apply (tx_kms_of _ E ssx msn KP_ATEXT HS');
          [vm_compute; reflexivity | cbn [ss_pc setpc]; exact tx_sigma_atext]);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word) nx_keep0 HS'
                   HAG ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r tx_keep ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) tx_keep) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r tx_keep Hr)));
    assert (Rr1 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_ALAT))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 1)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 1))) with (SOff 240 9896)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite (img_env_codeptr E HEI 9896); unfold w64; f_equal;
          unfold kpc, AF_kernel, KP_ALAT; lia);
    assert (Rr10 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 10)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 10))) with (SOff 21 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B21, Z.add_0_r; reflexivity);
    assert (Rr12 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 p)
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 12)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SOff 27 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B27, Z.add_0_r; reflexivity);
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    exact (tx_call POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 msn md3 mdn KP_TXT _ _
             c ci j m k n f adv hd kd left p _ HN HB ltac:(assumption) HFR HRc HRm HRa Hc1 Hci Hj Hm Hk Hkd Hl Hhd
             HW eq_refl HAT HMS' HR0' (tx_rl'_keep cx fpos left [(23%nat, a); (27%nat, p)] ms3 msn HRL HKN) Rr1 Rr10 Rr12 Hmem Hfds Hfs HST)
  end.
Qed.

(* ---- a % 6 = 4: +0xa74 -> +0xb24 -> the attr_text call at +0xb40 with a2 = .str.8 ---- *)
Lemma tx_c4_ph : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_alat B Rc Rm Ra) ->
  kfrom SK B POST (kin_txtc B Rc Rm Ra (fun x => x = 4)).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & Hc & Htx & HT & HAT0).
  destruct HAT0 as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc1 & Hci & Hj & Hm & Hk &
    Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & _).
  pose proof HB as ((_ & HGok & _) & _).
  (* the string .str.8 *)
  assert (Hin : In (LA_STR_X, [120; 0]) ki_strs)
    by (unfold ki_strs, LA_STR_X; cbn [In]; repeat (first [left; reflexivity | right])).
  assert (HTX : ktext cx LA_STR_X) by exact (proj1 (tx_apre_x SK B cx HB)).
  assert (HCOV : forall s, acstr_at SEGS (km0 cx) LA_STR_X s -> forall x, LA_STR_X <= x <= LA_STR_X + Z.of_nat (length s) ->
            kernel_ard SEGS (k_regs cx) (km0 cx) x).
  { intros s Hs x Hx. unfold kernel_ard. right; right; right; right; right; right; right; right; left.
    exists s. split; [exact Hs | lia]. }
  pose proof (katstr_img SK B LAWS KI TB cx fpos k2 ly3 S3 W3 ms3 md3 LA_STR_X _ HB HJ HJB HKK Hin HTX HCOV) as HST.
  assert (O21 : pa_val (A_OBJ 21) = LA_STR_X) by (rewrite (lv_obj LV) by (vm_compute; lia); reflexivity).
  (* the run *)
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (R23 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 23)) = w64 a) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (R21 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos))
    by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (B21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos).
  { rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl), R21.
    apply unsigned_lit_small. unfold kW2, KN_W2.
    destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    change (fs_frame_bytes KN_CID) with 16384 in F2. lia. }
  assert (HCS : conds_ok E tx_c4).
  { pose proof (tx_conds E a ltac:(rewrite (ER 23%nat (Z_to_bv 5 (Z.of_nat 23)) eq_refl), R23; reflexivity) Ha) as Q.
    rewrite Hc in Q. exact Q. }
  assert (HS : st_ok_pi SEGS pa_val E (tx_ss tx_c4) (restrict (w_H W3) ms3)).
  { rewrite HEdef in HCS |- *.
    exact (tx_seat SK B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 _ a tx_c4 HB HJB HMS HR0 HSL
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in)
             ltac:(apply in_or_app; left; unfold kslots_setup; kn_in) R23 Ha HCS). }
  assert (SHOK : sh_ok SEGS tx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK tx_span.
  { cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros x Hx. unfold tx_rg in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
  lazymatch goal with
  | HS' : st_ok _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin' & Hw); cbn [ss_mem In] in Hin'; destruct Hin' as [<-|[]];
          unfold tx_rg in Hw; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; lia);
    assert (HMS' : kms KP_ATEXT msn)
      by (apply (tx_kms_of _ E ssx msn KP_ATEXT HS');
          [vm_compute; reflexivity | cbn [ss_pc setpc]; exact tx_sigma_atext]);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word) nx_keep0 HS'
                   HAG ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r tx_keep ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) tx_keep) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r tx_keep Hr)));
    assert (Rr1 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_ALAT))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 1)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 1))) with (SOff 240 9896)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite (img_env_codeptr E HEI 9896); unfold w64; f_equal;
          unfold kpc, AF_kernel, KP_ALAT; lia);
    assert (Rr10 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 10)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 10))) with (SOff 21 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B21, Z.add_0_r; reflexivity);
    assert (Rr12 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 LA_STR_X)
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 12)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SOff (A_OBJ 21) 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite HEdef, Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
          rewrite O21, unsigned_lit_small by (unfold LA_STR_X; lia); rewrite Z.add_0_r; reflexivity);
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    exact (tx_call POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 msn md3 mdn KP_TXT _ _
             c ci j m k n f adv hd kd left LA_STR_X _ HN HB ltac:(assumption) HFR HRc HRm HRa Hc1 Hci Hj Hm Hk Hkd Hl Hhd
             HW eq_refl HAT HMS' HR0' (tx_rl'_keep cx fpos left [(23%nat, a); (27%nat, p)] ms3 msn HRL HKN) Rr1 Rr10 Rr12 Hmem Hfds Hfs HST)
  end.
Qed.

(* ---- the empty cursor's attribute: +0xb10 -> the attr_text call at +0xb40 with a2 = s11 = .str.1 ---- *)
Theorem kn_a0e : forall POST Rc Rm Ra,
  kfrom SK B POST (kin_alat B Rc Rm Ra) ->
  kfrom SK B POST (kin_acase B Rc Rm Ra KP_A0 ka_empty).
Proof.
  intros POST Rc Rm Ra HN cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (a & p & Ha & HT & (Ea & Ep) & HAT0). subst a p.
  destruct HAT0 as (c & ci & j & m & k & n & f & adv & hd & kd & left & HRc & HRm & HRa & Hc1 & Hci & Hj & Hm & Hk &
    Hkd & Hl & Hhd & HW & _ & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & _).
  pose proof HB as ((_ & HGok & _) & _).
  (* the string .str.1 *)
  assert (Hin : In (LA_STR_EMPTY, [0]) ki_strs) by (unfold ki_strs, LA_STR_EMPTY; cbn [In]; left; reflexivity).
  assert (HCOV : forall s, acstr_at SEGS (km0 cx) LA_STR_EMPTY s ->
            forall x, LA_STR_EMPTY <= x <= LA_STR_EMPTY + Z.of_nat (length s) ->
            kernel_ard SEGS (k_regs cx) (km0 cx) x).
  { intros s Hs x Hx. unfold kernel_ard. right; right; right; right; right; right; right; left.
    exists s. split; [exact Hs | lia]. }
  pose proof (katstr_img SK B LAWS KI TB cx fpos k2 ly3 S3 W3 ms3 md3 LA_STR_EMPTY _ HB HJ HJB HKK Hin HT HCOV) as HST.
  pose proof HST as (Hp0 & ((Hpa & Hpb & _) & _) & _). rewrite length_app in Hpb. cbn [length] in Hpb.
  (* the run *)
  remember (Eimg (Ereg (ms_regs ms3) (@nil word))) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) (@nil word)) E)
    by (rewrite HEdef; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (R21 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 21)) = w64 (kW2 cx fpos))
    by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (R27 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 27)) = w64 LA_STR_EMPTY) by (apply (kn_reg_in ms3 _ _ _ HRL); kn_in).
  assert (B21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos).
  { rewrite (ER 21%nat (Z_to_bv 5 (Z.of_nat 21)) eq_refl), R21.
    apply unsigned_lit_small. unfold kW2, KN_W2.
    destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    change (fs_frame_bytes KN_CID) with 16384 in F2. lia. }
  assert (B27 : bv_unsigned (ew E 27%nat) = LA_STR_EMPTY).
  { rewrite (ER 27%nat (Z_to_bv 5 (Z.of_nat 27)) eq_refl), R27. apply unsigned_lit_small. lia. }
  pose proof HAT as (HMSb & _).
  destruct HMSb as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  assert (B20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite (ER 20%nat 20%bv eq_refl), A20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (HS : st_ok_pi SEGS pa_val E tx_ss0 (restrict (w_H W3) ms3)).
  { rewrite (kn_ms_shape ms3 (BASE + kpc KP_A0) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
    rewrite restrict_mkst_fx. unfold tx_ss0. apply pa_entry_st_ok_full.
    - rewrite HEdef. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | exact I]].
      split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B20.
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
  assert (SHOK : sh_ok SEGS tx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK tx_span.
  { apply awr_ok_x_nil. }
  lazymatch goal with
  | HS' : st_ok _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
    |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
    assert (Hmem : ms_mem msn = ms_mem ms3)
      by (apply functional_extensionality; intros x; apply HF';
          intros (rr & Hin' & _); exact (False_ind _ Hin'));
    assert (HMS' : kms KP_ATEXT msn)
      by (apply (tx_kms_of _ E ssx msn KP_ATEXT HS');
          [vm_compute; reflexivity | cbn [ss_pc setpc]; exact tx_sigma_atext]);
    assert (HR0' : kregs0 cx msn)
      by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word) nx_keep0 HS'
                   HAG ltac:(vm_compute; reflexivity)));
    assert (HKN : forall r, In r tx_keep ->
              getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
      by (intros r Hr;
          exact (regs_kept_of_st_ok SEGS E ssx (restrict (w_H W3) msn) (ms_regs ms3) (@nil word)
                   (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) tx_keep) HS' HAG
                   ltac:(vm_compute; reflexivity) _ (kn_in_map5 r tx_keep Hr)));
    assert (Rr1 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 1)) = w64 (BASE + kpc KP_ALAT))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 1)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 1))) with (SOff 240 9896)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite (img_env_codeptr E HEI 9896); unfold w64; f_equal;
          unfold kpc, AF_kernel, KP_ALAT; lia);
    assert (Rr10 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 10)) = w64 (kW2 cx fpos))
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 10)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 10))) with (SOff 21 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B21, Z.add_0_r; reflexivity);
    assert (Rr12 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 12)) = w64 LA_STR_EMPTY)
      by (rewrite (st_ok_restrict_reg SEGS (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 12)) HS');
          replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 12))) with (SOff 27 0)
            by (vm_compute; reflexivity);
          cbn [sv_denot]; rewrite B27, Z.add_0_r; reflexivity);
    assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
    assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
    exact (tx_call POST Rc Rm Ra cx fpos k2 ly3 S3 W3 ms3 msn md3 mdn KP_A0 _ _
             c ci j m k n f adv hd kd left LA_STR_EMPTY _ HN HB ltac:(assumption) HFR HRc HRm HRa Hc1 Hci Hj Hm Hk Hkd Hl Hhd
             HW eq_refl HAT HMS' HR0' (tx_rl'_keep cx fpos left [(23%nat, 0); (27%nat, LA_STR_EMPTY)] ms3 msn HRL HKN) Rr1 Rr10 Rr12 Hmem Hfds Hfs HST)
  end.
Qed.

End b.
End a.

Print Assumptions kn_a0e.
