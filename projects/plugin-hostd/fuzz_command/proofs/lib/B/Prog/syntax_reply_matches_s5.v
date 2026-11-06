(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the walk through a
   runtime entry, cmp_tail) at c8557374ad2e, with the runtime step aj_art_at of lib/A/Prog/PaArt.v: the walk of
   syntax_reply_matches on fuzz_command.asan, the strcspn wrapper's call (CALL1, 0x88694) that measures the next word
   of the reply, and its result (RET1, 0x886a0). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/syntax_reply_matches_s5.v (a working branch
   db7d4effe38) for fuzz_command.asan-ubsan: CALL1 0x889c8 (the set kept in s11), RET1 0x889d4 (the empty-item test
   on s3, then a0 = 0 and a1 = ~s3 for L3's UBSan check), the set .str.5 at 0x21160, the stack-protector cells
   0xa6bf8 / 0x604158. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 713692f1e0c (statement pass 4b): ABCMP and ASTRCSPN hold at
   every FP state, as the statement has them; the strcspn call takes ASTRCSPN at fx. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa
  CmdPaLib PaSB PaDenot CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import syntax_reply_matches_c syntax_reply_matches_s1
  syntax_reply_matches_s2 syntax_reply_matches_s3 syntax_reply_matches_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaLibH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the set " " of the strcspn call: .str.5, among the read-only bytes the statement names *)
Lemma ro_str5 : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21160 RO_lit_21160.
Proof.
intros rd [HB _]. unfold cmd_ro_bytes in HB.
repeat (let H1 := fresh "H" in destruct HB as [H1 HB];
  try (lazymatch type of H1 with abytes_atR _ 0x21160 _ => exact H1 end)).
Qed.
(* `not a1, s3` (xori a1, s3, -1) over the walk's atoms *)
Lemma U_not_atom : forall E n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Hn. unfold zcanon, M64.
rewrite Z.add_0_r, (Z.mod_small v) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite lxor_allones by lia. apply Z.mod_small. lia.
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
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation INV := (srm_inv B).
#[local] Notation OK := (srm_ok B).
#[local] Notation AT := (srm_at B).

(* a range the walk's facts make readable, in the form the runtime entries ask (a Theorem Labs lane's aread_ok) *)
Lemma srm_aread : forall x regs m md regsT a n, OK x -> INV x regs m md -> spZ regsT = srm_sp0 x - 112 ->
  0 <= a -> a + n <= alloc_ceiling -> 0 <= n < 2 ^ 32 ->
  (forall y, a <= y < a + n -> rdW (x_W x) m y <> None) -> amem_range a n ->
  range_addressable (rdW (x_W x) (x_mem x)) SHADOW_OFF a n -> (0 < n -> shadow_hull_vis (rdW (x_W x) (x_mem x)) a n) ->
  aread_ok SEGS (2 * ESTACK) (x_W x) regsT m a n.
Proof.
intros x regs m md regsT a n HX HI Hsp Ha Han Hn Hv Hm Hra Hh.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (HSTK : STK = 8304) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros y Hy. split; [exact (Hv y Hy)|]. unfold ascratch_stk. lia. }
split; [exact Hm|]. split.
- exact (srm_ra_kept B x regs m md a n HX HI Ha Han Hra).
- intros Hn0. exact (srm_hull_kept B x regs m md a n HX HI Ha Han Hn0 (Hh Hn0)).
Qed.

(* ---- RET1 (0x889d4): the strcspn wrapper returned the word's length w; no word ends the match with 0, else on to
   the '<' search of the item with a0 = 0 and a1 = ~s3 ---- *)
Lemma srm_ret1 : forall x n regs m md k' L f'' j, OK x -> INV x regs m md -> L0_stmt B x n ->
  (j <= length (x_reply x))%nat -> (1 <= L)%nat -> (k' + L <= length (x_shape x))%nat ->
  (length (x_shape x) - (k' + L) < n)%nat -> (length (x_shape x) - (k' + L) <= f'')%nat ->
  reply_matches_items (firstn L (skipn k' (x_shape x)) :: items_f f'' (skipn (k' + L) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  getr regs 10 = w64 (Z.of_nat (word_len (skipn j (x_reply x)))) ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + L)) -> getr regs 19 = w64 (x_P x + Z.of_nat k') ->
  getr regs 20 = w64 (x_P x + Z.of_nat k') -> getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 27 = w64 0x21160 ->
  AT x SRM_RET1 regs m md.
Proof.
intros x n regs m md k' L f'' j HX HI IHL0 Hj HL1 Hk Hn Hf HV1 H10 H18 H19 H20 H8 H27. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
remember (word_len (skipn j (x_reply x))) as w eqn:Hw.
assert (Hwl : (w <= length (x_reply x) - j)%nat) by (rewrite Hw, <- length_skipn; apply PSRM.word_len_le).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V10 : bv_unsigned (ew E 10) = Z.of_nat w) by (subst E; apply (ew_EI_w64 regs _ 10 10%bv); [lia | reflexivity | exact H10 | lia]).
assert (V18 : bv_unsigned (ew E 18) = x_P x + Z.of_nat (k' + L)) by (subst E; apply (ew_EI_w64 regs _ 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (V19 : bv_unsigned (ew E 19) = x_P x + Z.of_nat k') by (subst E; apply (ew_EI_w64 regs _ 19 19%bv); [lia | reflexivity | exact H19 | lia]).
assert (V20 : bv_unsigned (ew E 20) = x_P x + Z.of_nat k') by (subst E; apply (ew_EI_w64 regs _ 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_RET1 (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_RET1)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* no word: return 0 *)
  unorm Hc. bnorm Hc.
  assert (RM : reply_matches (x_shape x) (x_reply x) = false) by (rewrite <- HV1; apply PSRM.rmi_w0; lia).
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_EPI; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_epi B LAWS x (ms_regs msn) (ms_mem msn) _ HX HIn)
  end.
  rewrite RM. srm_rgoal HS. srm_ucalc. rewrite Hc. reflexivity.
- unorm Hc. bnorm Hc.
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0))
  end.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
  + (* s3 = s2 would be an empty item; impossible *)
    exfalso. unorm Hc0. bnorm Hc0. lia.
  + unorm Hc0. bnorm Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L3; [awr_ok_tac|].
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 18; 19; 20; 27]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (srm_L3 B LAWS ABCMP (S L) x n (ms_regs msn) (ms_mem msn) _ k' L f'' j w 0 HX HIn IHL0 ltac:(lia) ltac:(lia)
      Hw ltac:(lia) ltac:(lia) Hk Hn Hf HV1 eq_refl);
    [ rewrite (HK2 19%bv) by (cbn; tauto); exact H19
    | rewrite (HK2 20%bv) by (cbn; tauto); rewrite Nat.add_0_r; exact H20
    | srm_rgoal HS; srm_ucalc; reflexivity
    | srm_rgoal HS; exact (U_not_atom _ 19 _ V19 ltac:(lia))
    | srm_rgoal HS; rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_neg_atom _ 19 _ V19) by lia; rewrite U_SOff, V18;
      unfold zcanon, M64; rewrite Z.add_0_r, (Z.mod_small (x_P x + Z.of_nat (k' + L))) by lia;
      rewrite Z.add_mod_idemp_r by lia; rewrite Z.mod_small by lia; lia
    | rewrite (HK2 18%bv) by (cbn; tauto); exact H18
    | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity
    | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
    | rewrite (HK2 27%bv) by (cbn; tauto); exact H27 ]
    end.
Qed.

(* ---- CALL1 (0x889c8): strcspn(reply + j, " ") through the wrapper, the set kept in s11 ---- *)
Lemma srm_call1 : forall x n regs m md k' L f'' j, OK x -> INV x regs m md -> L0_stmt B x n ->
  (j <= length (x_reply x))%nat -> (1 <= L)%nat -> (k' + L <= length (x_shape x))%nat ->
  (length (x_shape x) - (k' + L) < n)%nat -> (length (x_shape x) - (k' + L) <= f'')%nat ->
  reply_matches_items (firstn L (skipn k' (x_shape x)) :: items_f f'' (skipn (k' + L) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 11 = w64 0x21160 ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + L)) -> getr regs 19 = w64 (x_P x + Z.of_nat k') ->
  getr regs 20 = w64 (x_P x + Z.of_nat k') ->
  AT x SRM_CALL1 regs m md.
Proof.
intros x n regs m md k' L f'' j HX HI IHL0 Hj HL1 Hk Hn Hf HV1 H8 H11 H18 H19 H20. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _). pose proof ASAN_CEIL_range as (C2 & C3).
pose proof HI as (HJ & KEEP & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
pose proof HX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRs & _ & _ & HRM & HRA & HRH & _ & HRT & HRO & _ & HG
  & HA4 & HH4 & HT4 & HROM).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
assert (HSTK : STK = 8304) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E8 : ew E 8 = w64 (x_R x + Z.of_nat j)) by (subst E; rewrite ew_EI by lia; exact H8).
assert (E11 : ew E 11 = w64 0x21160) by (subst E; rewrite ew_EI by lia; exact H11).
assert (E2 : ew E 2 = w64 (srm_sp0 x - 112)) by (subst E; rewrite ew_EI by lia; exact R2).
assert (E3 : ew E 3 = getr (x_regs x) 3) by (subst E; rewrite ew_EI by lia; exact R3).
assert (E4 : ew E 4 = getr (x_regs x) 4) by (subst E; rewrite ew_EI by lia; exact R4).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_CALL1 (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_CALL1)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
lazymatch type of HS with context [restrict _ ?msn] =>
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
  by (intros a0 Ha0; exact (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0));
srm_kept_c HS HAE SRM_KEEP HK; srm_kept_c HS HAE ([8; 18; 19; 20]%bv : list (bv 5)) HK2;
pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (27%bv : bv 5) Q27;
prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
pose proof HIn as (_ & KEEPn & _);
assert (KO : kept_out (rdW (x_W x) (x_mem x)) (rdW (x_W x) (ms_mem msn)) (srm_sp0 x - STK) (srm_sp0 x))
  by (intros a Ha Hna; exact (KEEPn a Ha Hna));
assert (Hsp : spZ (ms_regs msn) = srm_sp0 x - 112) by (unfold spZ; rewrite Q2, E2, w64_unsigned by lia; reflexivity);
pmkst HS;
eapply SRr_bind;
[ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False) _ (x_W x) (ms_regs msn) (ms_mem msn)
    STK (srm_sp0 x) [] (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) [] (x_ly x) (x_S x) _ 0 (-112)
    (Z_to_bv 64 (BASE + SRM_RET1))
    (fun regs' _ => getr regs' 10 = w64 (Z.of_nat (PCspn.cspn_len [Z_to_bv 8 32] (skipn j (x_reply x))))) HJ)
| cbv beta; intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & Hfr);
  pose proof (srm_inv_call B x _ _ _ regs2 mem2 md2 HX HIn HJ2 (fun a Ha Hna => Hfr a Ha ltac:(lia) (fun F => F)) HP2) as HI2;
  eapply (srm_ret1 x n regs2 mem2 md2 k' L f'' j HX HI2 IHL0 Hj HL1 Hk Hn Hf HV1) ]
end.
(* aj_art_at's premises *)
- rewrite Hsp. lia.
- reflexivity.
- lia.
- lia.
- unfold SYNTAX_REPLY_MATCHES_STK. lia.
- exact Q1.
- intros a [].
- (* the strcspn wrapper's contract *)
  assert (Hlo : alloc_ceiling <= srm_sp0 x - STK) by lia.
  apply (ASTRCSPN fx (x_ly x) (x_S x) (x_W x) _ _ _ (x_R x + Z.of_nat j) 0x21160 (skipn j (x_reply x)) [Z_to_bv 8 32]).
  + apply (aguard_ok_kept SEGS _ _ _ _ _ _ _ KO HG); unfold A_SSP_GOT, A_SSP_GUARD; lia.
  + eapply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK (srm_sp0 x) [] (x_ly x) (x_S x) (x_W x) (x_mem x) (x_md x) []
      (x_ly x) (x_S x) (x_W x) _ _ 0 _ (-112) HJ Hsp); [reflexivity | lia | lia | lia | | rewrite Q3, E3; exact Hgp
      | rewrite Q4, E4; exact Htp].
    rewrite Q1. apply ret_ok_codeptr_v; [unfold SRM_RET1; lia | reflexivity].
  + rewrite Q10, E8. reflexivity.
  + rewrite Q11, E11. reflexivity.
  + lia.
  + lia.
  + apply astr_atR_view. apply (astr_atR_kept _ _ (srm_sp0 x - STK) (srm_sp0 x) _ _ KO); [| lia | rewrite length_skipn; lia | lia].
    exact (astr_atR_skipn _ _ _ j HRs Hj).
  + apply astr_atR_view. apply (astr_atR_kept _ _ (srm_sp0 x - STK) (srm_sp0 x) _ _ KO); [| lia | cbn; lia | lia].
    split; [exact (ro_str5 _ HRO) |]. intros [Hq|[]]. apply (f_equal bv_unsigned) in Hq. vm_compute in Hq. discriminate Hq.
  + apply (srm_aread x _ _ _ _ _ _ HX HIn Hsp); unfold astr_len; rewrite ?length_skipn; try lia.
    * intros y Hy. replace y with (x_R x + Z.of_nat (Z.to_nat (y - x_R x))) by lia.
      rewrite (srm_reply_byte B x _ _ _ _ HX HIn) by lia. discriminate.
    * eapply amem_range_sub; [exact HRM | lia | lia].
    * eapply range_addressable_sub; [exact HRA | lia | lia].
    * intros _. eapply shadow_hull_vis_sub; [exact HRH | lia | lia | lia].
  + (* the reply's band room 8 bytes past its suffix (RtString.v:166): srm_ok's amem_range R (nr + 8), which
       PaLibH.amem8_of_blockA gave from the statement's in_blockA (syntax_reply_matches.v, srm_ok_entry) *)
    eapply amem_range_sub; [exact HRM | lia | unfold astr_len; rewrite length_skipn; lia].
  + apply (srm_aread x _ _ _ _ _ _ HX HIn Hsp); unfold astr_len; cbn [length]; try lia.
    * intros y Hy. rewrite (KO y) by lia. replace y with (0x21160 + Z.of_nat (Z.to_nat (y - 0x21160))) by lia.
      rewrite (ro_str5 _ HRO (Z.to_nat (y - 0x21160)) ltac:(cbn; lia)). discriminate.
    * unfold amem_range, kLowMemEnd. lia.
    * exact HA4.
    * intros _. exact HH4.
  + (* the set's band room (RtString.v:169): .str.5 is a .rodata literal of the low band *)
    apply PaLibH.amem8_of_low; [lia | unfold astr_len, kLowMemEnd; cbn [length]; lia].
  + replace (x_R x + Z.of_nat j + astr_len (skipn j (x_reply x))) with (x_R x + Z.of_nat (length (x_reply x)))
      by (unfold astr_len; rewrite length_skipn; lia).
    apply (atail_vis_kept SEGS _ _ _ _ _ _ KO HRT); [lia | | lia].
    assert (Hlt : 0 <= x_R x + Z.of_nat (length (x_reply x)) < alloc_ceiling) by lia.
    pose proof (tail_below _ _ Hlt C3). lia.
  + change (0x21160 + astr_len [Z_to_bv 8 32]) with 0x21161.
    apply (atail_vis_kept SEGS _ _ _ _ _ _ KO HT4); [lia | | lia]. assert (0x21161 mod 8 = 1) by reflexivity. lia.
  + apply (rt_rom_view_keep SEGS B _ _ _ HROM). intros a (sg & Hsg & _ & Ha) _ _.
    assert (Hi : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Ha]).
    pose proof (pa_img_range a Hi). apply (KO a); lia.
(* RET1's premises at the return *)
- rewrite HQ, PSRM.cspn_word. reflexivity.
- assert (P18 : getr regs2 18%bv = getr (ms_regs ms) 18%bv) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
  rewrite P18, (HK2 18%bv) by (cbn; tauto). exact H18.
- assert (P19 : getr regs2 19%bv = getr (ms_regs ms) 19%bv) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
  rewrite P19, (HK2 19%bv) by (cbn; tauto). exact H19.
- assert (P20 : getr regs2 20%bv = getr (ms_regs ms) 20%bv) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
  rewrite P20, (HK2 20%bv) by (cbn; tauto). exact H20.
- assert (P8 : getr regs2 8%bv = getr (ms_regs ms) 8%bv) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
  rewrite P8, (HK2 8%bv) by (cbn; tauto). exact H8.
- assert (P27 : getr regs2 27%bv = getr (ms_regs ms) 27%bv) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
  rewrite P27, Q27, E11. reflexivity.
Qed.
End e.
End f.
End d.
