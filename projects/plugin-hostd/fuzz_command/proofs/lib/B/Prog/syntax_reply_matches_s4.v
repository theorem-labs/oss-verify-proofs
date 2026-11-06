(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and lib/A/AC8b.v (the
   loop by fuel induction, tcbb_loopX) at c8557374ad2e: the walk of syntax_reply_matches on fuzz_command.asan, the
   search of an item for '<' (L3, 0x886b4, check C3), the strcspn wrapper's call (CALL1, 0x88694) and its result
   (RET1, 0x886a0). *)
(* Modified by Theorem Labs, 2026-10: re-walked from lib/A/Prog/syntax_reply_matches_s4.v (a working branch
   db7d4effe38) for fuzz_command.asan-ubsan: L3 0x889ec, where a0 = i, a1 = ~s3, s4 = s3 + i is the checked byte and
   s3 + a0 the loaded one; the UBSan check 0x889ec (~s3 < i: s3 + i would wrap) is decided by the facts
   s3 <= CEIL_HI, i < 2^31. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 713692f1e0c (statement pass 4b): ABCMP holds at every FP
   state, as the statement has it. *)
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
  syntax_reply_matches_s2 syntax_reply_matches_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma nth_firstn_skipn : forall (l : list byte) k L i d, (i < L)%nat -> nth i (firstn L (skipn k l)) d = nth (k + i) l d.
Proof. intros l k L i d Hi. rewrite nth_firstn_lt by exact Hi. apply nth_skipn_add. Qed.

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
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation INV := (srm_inv B).
#[local] Notation OK := (srm_ok B).
#[local] Notation AT := (srm_at B).

(* ---- L3 (0x889ec): is there a '<' in the item?  The loop of the plain lt_loop
   (lib/Prog/syntax_reply_matches.v:391-420), by fuel induction as cgif's tcbb_loopX (A/AC8b.v:50-255).
   a0 = i, a1 = ~s3 (the UBSan bound), s3 = P + k', s4 = s3 + i (the byte check C3 reads), a2 = L. ---- *)
Definition l3_region : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition l3_facts : list (nat * afact) :=
  [(10%nat, mkAF 0 2147483648 0); (11%nat, mkAF (2 ^ 64 - 1 - CEIL_HI) (2 ^ 64 - 1) 0); (12%nat, mkAF 0 2147483648 0);
   (19%nat, mkAF 0 CEIL_HI 0); (20%nat, mkAF 0 CEIL_HI 0); (24%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)].
Definition l3_alias : list (sv * sv) := [(SAlu ALU_ADD (SOff 19 0) (SOff 10 0), SOff 20 0)].
Lemma srm_L3 : forall t x n regs m md k' L f'' j w i, OK x -> INV x regs m md -> L0_stmt B x n ->
  (L - i < t)%nat -> (i < L)%nat ->
  w = word_len (skipn j (x_reply x)) -> w <> 0%nat -> (j + w <= length (x_reply x))%nat ->
  (k' + L <= length (x_shape x))%nat -> (length (x_shape x) - (k' + L) < n)%nat ->
  (length (x_shape x) - (k' + L) <= f'')%nat ->
  reply_matches_items (firstn L (skipn k' (x_shape x)) :: items_f f'' (skipn (k' + L) (x_shape x))) (skipn j (x_reply x))
    = reply_matches (x_shape x) (x_reply x) ->
  has_lt (firstn L (skipn k' (x_shape x))) = has_lt (skipn i (firstn L (skipn k' (x_shape x)))) ->
  getr regs 19 = w64 (x_P x + Z.of_nat k') -> getr regs 20 = w64 (x_P x + Z.of_nat (k' + i)) ->
  getr regs 10 = w64 (Z.of_nat i) -> getr regs 11 = w64 (2 ^ 64 - 1 - (x_P x + Z.of_nat k')) ->
  getr regs 12 = w64 (Z.of_nat L) ->
  getr regs 18 = w64 (x_P x + Z.of_nat (k' + L)) -> getr regs 21 = w64 (Z.of_nat w) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 27 = w64 0x21160 ->
  AT x SRM_L3 regs m md.
Proof.
induction t as [|t IH]; intros x n regs m md k' L f'' j w i HX HI IHL0 Ht Hi Hw Hw0 Hjw Hk Hn Hf HV1 HLT
  H19 H20 H10 H11 H12 H18 H21 H8 H27; [lia|]. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R24 & R22 & R25 & R26 & R9 & R23).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & HSA & _).
set (a := x_P x + Z.of_nat (k' + i)) in *.
set (b := srm_byte (x_shape x ++ [Z_to_bv 8 0]) (k' + i)).
pose proof (srm_byte_range (x_shape x ++ [Z_to_bv 8 0]) (k' + i)) as Hb. fold b in Hb.
remember (Eimg (Ereg regs [w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 b]) E)
  by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V10 : bv_unsigned (ew E 10) = Z.of_nat i) by (subst E; apply (ew_EI_w64 regs _ 10 10%bv); [lia | reflexivity | exact H10 | lia]).
assert (V11 : bv_unsigned (ew E 11) = 2 ^ 64 - 1 - (x_P x + Z.of_nat k'))
  by (subst E; apply (ew_EI_w64 regs _ 11 11%bv); [lia | reflexivity | exact H11 | lia]).
assert (V12 : bv_unsigned (ew E 12) = Z.of_nat L) by (subst E; apply (ew_EI_w64 regs _ 12 12%bv); [lia | reflexivity | exact H12 | lia]).
assert (V19 : bv_unsigned (ew E 19) = x_P x + Z.of_nat k') by (subst E; apply (ew_EI_w64 regs _ 19 19%bv); [lia | reflexivity | exact H19 | lia]).
assert (V20 : bv_unsigned (ew E 20) = a) by (subst E; apply (ew_EI_w64 regs _ 20 20%bv); [lia | reflexivity | exact H20 | unfold a; lia]).
assert (V24 : bv_unsigned (ew E 24) = SB) by (subst E; apply (ew_EI_w64 regs _ 24 24%bv); [lia | reflexivity | exact R24 | unfold SB; lia]).
assert (V25 : bv_unsigned (ew E 25) = 60) by (subst E; apply (ew_EI_w64 regs _ 25 25%bv); [lia | reflexivity | exact R25 | lia]).
assert (V32 : bv_unsigned (ew E 32) = b) by (subst E; apply (ew_EX_w64 regs _ 0); [lia | reflexivity | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_L3 (srm_pins sr_atoms []) [l3_region] None (mkFacts l3_facts [] l3_alias))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_L3)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed.
  - constructor.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, l3_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite V20. unfold a. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 32 0) b).
    + apply sv_w64. rewrite U_SOff, V32. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
    + simpl. lia.
    + lia.
    + rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. apply val_mem1_of_aview.
      exact (srm_shape_byte B x regs m md (k' + i) HX HI ltac:(lia)).
  - cbn. tauto.
  - unfold facts_ok, l3_facts, l3_alias. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite V10, V11, V12, V19, V20, V24, V32. unfold a, CEIL_HI, SB. rewrite !Z.pow_0_r, !Z.mod_1_r.
    split; [repeat split; lia|]. split; [exact I|]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, V19, V10, V20. unfold zcanon, M64. rewrite !Z.add_0_r.
    rewrite (Z.mod_small (x_P x + Z.of_nat k')) by lia. rewrite (Z.mod_small (Z.of_nat i)) by lia.
    unfold a. f_equal. lia. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan.
all: first [ awr_ok_tac | idtac ].
{ (* C3: the item's byte i *)
  change (rd_of SEGS (mrestrict (w_H (x_W x)) m)) with (rdW (x_W x) m). unfold SRM_Bx.
  rewrite !U_SOff, V24, V20. unfold zcanon, M64. rewrite !Z.add_0_r, !Z.mod_small by (unfold a, SB; lia).
  unfold a.
  eapply (range_addressable_sub _ _ (x_P x) (Z.of_nat (length (x_shape x)) + 1));
    [ eapply (srm_ra_kept B x regs m md); [exact HX | exact HI | lia | lia | exact HSA] | lia | lia ]. }
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
assert (Hbyte : bz (hd NUL (skipn i (firstn L (skipn k' (x_shape x))))) = b).
{ unfold b, bz. rewrite hd_skipn_nth, nth_firstn_skipn by exact Hi. rewrite srm_byte_app_lt by lia. reflexivity. }
assert (Hlen : length (firstn L (skipn k' (x_shape x))) = L) by (rewrite length_firstn, length_skipn; lia).
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* '<': the item is a pattern, no comparison; on to JOIN *)
  unorm Hc. bnorm Hc.
  assert (HLT1 : has_lt (firstn L (skipn k' (x_shape x))) = true).
  { rewrite HLT, PSRM.has_lt_skipn by lia. rewrite Hbyte, Hc. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_JOIN; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 18; 21; 27]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_join B LAWS x n (ms_regs msn) (ms_mem msn) _ j w (k' + L) f'' HX HIn IHL0 Hw Hjw Hk Hn Hf);
  [ rewrite <- HV1, (PSRM.rmi_ok _ _ _ ltac:(rewrite <- Hw; exact Hw0));
      [ rewrite <- Hw, skipn_skipn, (Nat.add_comm w j); reflexivity
      | rewrite HLT1; reflexivity ]
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 21%bv) by (cbn; tauto); exact H21
  | rewrite (HK2 27%bv) by (cbn; tauto); exact H27
  | rewrite (HK2 18%bv) by (cbn; tauto); exact H18 ]
  end.
- unorm Hc. bnorm Hc.
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM2 : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0))
  end.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
  + (* i + 1 = L: no '<' in the item; compare it with the word *)
    unorm Hc0. bnorm Hc0.
    assert (HLT0 : has_lt (firstn L (skipn k' (x_shape x))) = false).
    { rewrite HLT, PSRM.has_lt_skipn by lia. rewrite Hbyte, (proj2 (Z.eqb_neq b 60) Hc), PSRM.has_lt_end by lia.
      reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_NOLT; [awr_ok_tac|].
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 12; 18; 19; 21; 27]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (srm_nolt B LAWS ABCMP x n (ms_regs msn) (ms_mem msn) _ k' L f'' j w HX HIn IHL0 Hw Hw0 Hjw ltac:(lia) Hk Hn Hf
      HV1 HLT0);
    [ rewrite (HK2 18%bv) by (cbn; tauto); exact H18
    | rewrite (HK2 21%bv) by (cbn; tauto); exact H21
    | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
    | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
    | rewrite (HK2 12%bv) by (cbn; tauto); exact H12
    | rewrite (HK2 27%bv) by (cbn; tauto); exact H27 ]
    end.
  + (* i + 2 <= L: the next byte *)
    unorm Hc0. bnorm Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L3; [awr_ok_tac|].
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 12; 18; 19; 21; 27]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (IH x n (ms_regs msn) (ms_mem msn) _ k' L f'' j w (S i) HX HIn IHL0 ltac:(lia) ltac:(lia) Hw Hw0 Hjw Hk Hn Hf HV1);
    [ rewrite HLT, PSRM.has_lt_skipn by lia; rewrite Hbyte, (proj2 (Z.eqb_neq b 60) Hc); reflexivity
    | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
    | srm_rgoal HS; srm_ucalc; unfold a; rewrite Z.mod_small by lia; lia
    | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
    | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
    | rewrite (HK2 12%bv) by (cbn; tauto); exact H12
    | rewrite (HK2 18%bv) by (cbn; tauto); exact H18
    | rewrite (HK2 21%bv) by (cbn; tauto); exact H21
    | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
    | rewrite (HK2 27%bv) by (cbn; tauto); exact H27 ]
    end.
Qed.
End e.
End f.
End d.
