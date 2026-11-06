(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the walk through a
   runtime entry: cmp_tail and aj_memcmp_at) and lib/A/AC8b.v at c8557374ad2e: the walk of syntax_reply_matches on
   fuzz_command.asan, the comparison of an item with no '<' and the reply word: NOLT (0x886f0: length test, the bcmp
   wrapper's call) and RET2 (0x88704: its result). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa
  CmdPaLib PaSB PaDenot CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import syntax_reply_matches_c syntax_reply_matches_s1
  syntax_reply_matches_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Lemma U_neg_atom : forall E n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  U E (SMd M_MUL (SOff n 0) (SLit (-1))) = (- v) mod 2 ^ 64.
Proof.
intros E n v Hn Hv. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff, U_SLit, Hn. unfold zcanon, M64.
rewrite Z.add_0_r, (Z.mod_small v) by lia. rewrite Z.mul_mod_idemp_r by lia. f_equal. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation STK := SYNTAX_REPLY_MATCHES_STK.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIG CS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation INV := (srm_inv B).
#[local] Notation OK := (srm_ok B).
#[local] Notation AT := (srm_at B).

(* ---- RET2 (0x88704): the bcmp wrapper's result; 0 goes on to JOIN, any other value returns 0 ---- *)
Lemma srm_ret2 : forall x n regs m md k' L f'' j w, OK x -> INV x regs m md -> L0_stmt B x n ->
  w = word_len (skipn j (x_reply x)) -> w <> 0%nat -> (j + w <= length (x_reply x))%nat -> L = w ->
  (k' + L <= length (x_shape x))%nat -> (length (x_shape x) - (k' + L) < n)%nat ->
  (length (x_shape x) - (k' + L) <= f'')%nat ->
  reply_matches_items (firstn L (skipn k' (x_shape x)) :: items_f f'' (skipn (k' + L) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  has_lt (firstn L (skipn k' (x_shape x))) = false ->
  (getr regs 10 = w64 0 <-> firstn L (skipn k' (x_shape x)) = firstn L (skipn j (x_reply x))) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 21 = w64 (Z.of_nat w) -> getr regs 26 = w64 0x21120 ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + L)) ->
  AT x SRM_RET2 regs m md.
Proof.
intros x n regs m md k' L f'' j w HX HI IHL0 Hw Hw0 Hjw HLw Hk Hn Hf HV1 HLT HEQ H8 H21 H26 H18. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R23 & R22 & R24 & R25 & R9 & R27).
remember (bv_unsigned (getr regs 10)) as v eqn:Hv.
assert (Hv0 : getr regs 10 = w64 0 <-> v = 0).
{ subst v. split; intros H; [rewrite H; reflexivity|]. unfold w64. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. }
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V10 : bv_unsigned (ew E 10) = v)
  by (subst E v; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); reflexivity).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_RET2 (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_RET2)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
assert (Hvr : 0 <= v < 2 ^ 64) by (subst v; apply (bv_unsigned_in_range 64)).
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* the bytes differ: return 0 *)
  unorm Hc. bnorm Hc.
  assert (RM : reply_matches (x_shape x) (x_reply x) = false).
  { rewrite <- HV1. apply PSRM.rmi_mis. rewrite HLT. cbn [negb andb]. rewrite <- Hw.
    destruct (bytes_eqb (firstn L (skipn k' (x_shape x))) (firstn w (skipn j (x_reply x)))) eqn:EB; [|reflexivity].
    exfalso. apply PCT.bytes_eqb_iff in EB. rewrite <- HLw in EB. apply Hc. apply Hv0. apply HEQ. exact EB. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_EPI; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_epi B LAWS x (ms_regs msn) (ms_mem msn) _ HX HIn)
  end.
  rewrite RM. srm_rgoal HS. srm_ucalc. reflexivity.
- (* the bytes are equal: on to JOIN *)
  unorm Hc. bnorm Hc.
  assert (EQ : firstn L (skipn k' (x_shape x)) = firstn L (skipn j (x_reply x))) by (apply HEQ, Hv0; exact Hc).
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_JOIN; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 18; 21; 26]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_join B LAWS x n (ms_regs msn) (ms_mem msn) _ j w (k' + L) f'' HX HIn IHL0 Hw Hjw Hk Hn Hf);
  [ rewrite <- HV1, (PSRM.rmi_ok _ _ _ ltac:(rewrite <- Hw; exact Hw0));
      [ rewrite <- Hw, skipn_skipn, (Nat.add_comm w j); reflexivity
      | rewrite HLT, <- Hw, <- HLw, (proj2 (PCT.bytes_eqb_iff _ _) EQ); reflexivity ]
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 21%bv) by (cbn; tauto); exact H21
  | rewrite (HK2 26%bv) by (cbn; tauto); exact H26
  | rewrite (HK2 18%bv) by (cbn; tauto); exact H18 ]
  end.
Qed.

(* ---- NOLT (0x886f0): an item with no '<'; its length must be the word's, then the bcmp wrapper compares them ---- *)
Lemma srm_nolt : forall x n regs m md k' L f'' j w, OK x -> INV x regs m md -> L0_stmt B x n ->
  w = word_len (skipn j (x_reply x)) -> w <> 0%nat -> (j + w <= length (x_reply x))%nat ->
  (1 <= L)%nat -> (k' + L <= length (x_shape x))%nat -> (length (x_shape x) - (k' + L) < n)%nat ->
  (length (x_shape x) - (k' + L) <= f'')%nat ->
  reply_matches_items (firstn L (skipn k' (x_shape x)) :: items_f f'' (skipn (k' + L) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  has_lt (firstn L (skipn k' (x_shape x))) = false ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + L)) -> getr regs 21 = w64 (Z.of_nat w) ->
  getr regs 19 = w64 (x_P x + Z.of_nat k') -> getr regs 20 = w64 (x_P x + Z.of_nat k') ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 12 = w64 (Z.of_nat L) -> getr regs 26 = w64 0x21120 ->
  AT x SRM_NOLT regs m md.
Proof.
intros x n regs m md k' L f'' j w HX HI IHL0 Hw Hw0 Hjw HL1 Hk Hn Hf HV1 HLT H18 H21 H19 H20 H8 H12 H26. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R23 & R22 & R24 & R25 & R9 & R27).
pose proof HX as (HPRE & _ & _ & _ & _ & _ & HSM & HSA & HSH & _ & _ & _ & _ & HRM & HRA & HRH & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
assert (HSTK : STK = 8304) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V18 : bv_unsigned (ew E 18) = x_P x + Z.of_nat (k' + L)) by (subst E; apply (ew_EI_w64 regs _ 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (V21 : bv_unsigned (ew E 21) = Z.of_nat w) by (subst E; apply (ew_EI_w64 regs _ 21 21%bv); [lia | reflexivity | exact H21 | lia]).
assert (V19 : bv_unsigned (ew E 19) = x_P x + Z.of_nat k') by (subst E; apply (ew_EI_w64 regs _ 19 19%bv); [lia | reflexivity | exact H19 | lia]).
assert (E20 : ew E 20 = w64 (x_P x + Z.of_nat k')) by (subst E; rewrite ew_EI by lia; exact H20).
assert (E8 : ew E 8 = w64 (x_R x + Z.of_nat j)) by (subst E; rewrite ew_EI by lia; exact H8).
assert (E12 : ew E 12 = w64 (Z.of_nat L)) by (subst E; rewrite ew_EI by lia; exact H12).
assert (E2 : ew E 2 = w64 (srm_sp0 x - 112)) by (subst E; rewrite ew_EI by lia; exact R2).
assert (E3 : ew E 3 = getr (x_regs x) 3) by (subst E; rewrite ew_EI by lia; exact R3).
assert (E4 : ew E 4 = getr (x_regs x) 4) by (subst E; rewrite ew_EI by lia; exact R4).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_NOLT (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_NOLT)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* the item and the word differ in length: return 0 *)
  unorm Hc. bnorm Hc.
  rewrite (U_neg_atom E 21 (Z.of_nat w) V21), Z.add_mod_idemp_r in Hc by lia.
  assert (HLw : L <> w) by (intros EQL; apply Hc; rewrite Z.mod_small by lia; lia).
  assert (RM : reply_matches (x_shape x) (x_reply x) = false).
  { rewrite <- HV1. apply PSRM.rmi_mis. rewrite HLT. cbn [negb andb]. rewrite <- Hw, PSRM.bytes_eqb_len; [reflexivity|].
    rewrite !length_firstn, !length_skipn. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_EPI; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_epi B LAWS x (ms_regs msn) (ms_mem msn) _ HX HIn)
  end.
  rewrite RM. srm_rgoal HS. srm_ucalc. reflexivity.
- (* the same length: call the bcmp wrapper *)
  unorm Hc. bnorm Hc.
  rewrite (U_neg_atom E 21 (Z.of_nat w) V21), Z.add_mod_idemp_r in Hc by lia.
  assert (HLw : L = w).
  { destruct (Z_le_gt_dec 0 (x_P x + Z.of_nat (k' + L) + - Z.of_nat w)) as [D|D].
    - rewrite Z.mod_small in Hc by lia. lia.
    - exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in Hc by lia. rewrite Z.mod_small in Hc by lia. lia. }
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept_c HS HAE SRM_KEEP HK; srm_kept_c HS HAE ([8; 18; 21; 26]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  pmkst HS;
  eapply SRr_bind;
  [ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP (x_W x) (ms_regs msn) (ms_mem msn) STK (srm_sp0 x) []
      (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) [] (x_ly x) (x_S x) _ 0
      (x_P x + Z.of_nat k') (x_R x + Z.of_nat j) (Z.of_nat L) (-112) (Z_to_bv 64 (BASE + SRM_RET2)) HJ)
  | cbv beta; intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2);
    pose proof (srm_inv_call B x _ _ _ regs2 mem2 md2 HX HIn HJ2 (fun a Ha Hn => Hfr a Ha ltac:(lia)) HP2) as HI2;
    eapply (srm_ret2 x n regs2 mem2 md2 k' L f'' j w HX HI2 IHL0 Hw Hw0 Hjw HLw Hk Hn Hf HV1 HLT) ]
  end.
  (* the bcmp wrapper's premises *)
  + rewrite Q10, E20. reflexivity.
  + rewrite Q11, E8. reflexivity.
  + rewrite Q12, E12. reflexivity.
  + lia.
  + lia.
  + lia.
  + lia.
  + lia.
  + unfold spZ. rewrite Q2, E2, w64_unsigned by lia. lia.
  + reflexivity.
  + lia.
  + unfold SYNTAX_REPLY_MATCHES_STK, ESTACK. lia.
  + rewrite Q3, E3. exact Hgp.
  + rewrite Q4, E4. exact Htp.
  + exact Q1.
  + apply ret_ok_codeptr_v; [unfold SRM_RET2; lia | reflexivity].
  + intros a Ha. split; [|unfold spZ; rewrite Q2, E2, w64_unsigned by lia; lia].
    replace a with (x_P x + Z.of_nat (Z.to_nat (a - x_P x))) by lia.
    rewrite (srm_shape_byte B x _ _ _ _ HX HIn) by lia. discriminate.
  + intros a Ha. split; [|unfold spZ; rewrite Q2, E2, w64_unsigned by lia; lia].
    replace a with (x_R x + Z.of_nat (Z.to_nat (a - x_R x))) by lia.
    rewrite (srm_reply_byte B x _ _ _ _ HX HIn) by lia. discriminate.
  + intros a Ha. lia.
  + intros a Ha. lia.
  + eapply amem_range_sub; [exact HSM | lia | lia].
  + eapply amem_range_sub; [exact HRM | lia | lia].
  + eapply (range_addressable_sub _ _ (x_P x) (Z.of_nat (length (x_shape x)) + 1));
      [eapply (srm_ra_kept B x _ _ _ _ _ HX HIn); [lia | lia | exact HSA] | lia | lia].
  + intros _. eapply (shadow_hull_vis_sub _ (x_P x) (Z.of_nat (length (x_shape x)) + 1));
      [eapply (srm_hull_kept B x _ _ _ _ _ HX HIn); [lia | lia | lia | exact HSH] | lia | lia | lia].
  + eapply (range_addressable_sub _ _ (x_R x) (Z.of_nat (length (x_reply x)) + 1));
      [eapply (srm_ra_kept B x _ _ _ _ _ HX HIn); [lia | lia | exact HRA] | lia | lia].
  + intros _. eapply (shadow_hull_vis_sub _ (x_R x) (Z.of_nat (length (x_reply x)) + 1));
      [eapply (srm_hull_kept B x _ _ _ _ _ HX HIn); [lia | lia | lia | exact HRH] | lia | lia | lia].
  (* RET2's premises at the return *)
  + rewrite Hv, Hcmp. split.
    * intros H. apply firstn_nth_eq; [rewrite length_skipn; lia | rewrite length_skipn; lia |].
      intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)).
      replace (x_P x + Z.of_nat k' + Z.of_nat i) with (x_P x + Z.of_nat (k' + i)) in H by lia.
      replace (x_R x + Z.of_nat j + Z.of_nat i) with (x_R x + Z.of_nat (j + i)) in H by lia.
      rewrite (srm_shape_byte B x _ _ _ (k' + i) HX HIn) in H by lia.
      rewrite (srm_reply_byte B x _ _ _ (j + i) HX HIn) in H by lia.
      injection H as H. rewrite !srm_byte_app_lt in H by lia. unfold srm_byte in H.
      rewrite !nth_skipn_add. apply bv_eq. exact H.
    * intros H i Hi. assert (Hi' : (Z.to_nat i < L)%nat) by lia.
      pose proof (nth_firstn_eq _ _ L (Z.to_nat i) H Hi') as Hn'. rewrite !nth_skipn_add in Hn'.
      replace (x_P x + Z.of_nat k' + i) with (x_P x + Z.of_nat (k' + Z.to_nat i)) by lia.
      replace (x_R x + Z.of_nat j + i) with (x_R x + Z.of_nat (j + Z.to_nat i)) by lia.
      rewrite (srm_shape_byte B x _ _ _ _ HX HIn) by lia. rewrite (srm_reply_byte B x _ _ _ _ HX HIn) by lia.
      rewrite !srm_byte_app_lt by lia. unfold srm_byte. rewrite Hn'. reflexivity.
  + assert (P8 : getr regs2 8%bv = getr (ms_regs ms0) 8%bv) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
    rewrite P8, (HK2 8%bv) by (cbn; tauto). exact H8.
  + assert (P21 : getr regs2 21%bv = getr (ms_regs ms0) 21%bv) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
    rewrite P21, (HK2 21%bv) by (cbn; tauto). exact H21.
  + assert (P26 : getr regs2 26%bv = getr (ms_regs ms0) 26%bv) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
    rewrite P26, (HK2 26%bv) by (cbn; tauto). exact H26.
  + assert (P18 : getr regs2 18%bv = getr (ms_regs ms0) 18%bv) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
    rewrite P18, (HK2 18%bv) by (cbn; tauto). exact H18.
Qed.
End e.
End f.
End d.
