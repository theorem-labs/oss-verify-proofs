(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop by fuel induction,
   tcbb_loopX) and lib/A/AChd.v at c8557374ad2e: the walk of syntax_reply_matches on fuzz_command.asan, the item loop
   (the plain main_loop and skip_loop, lib/Prog/syntax_reply_matches.v): L0 (0x885e8, the next item) and L1 (0x885f4,
   check C1 and the spaces before an item). *)
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
  syntax_reply_matches_s2 syntax_reply_matches_s3 syntax_reply_matches_s4 syntax_reply_matches_s5 syntax_reply_matches_s6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the items of the shape after the spaces in front of the next one (the plain main_loop, lib/Prog/
   syntax_reply_matches.v:453-459, with items_f_cons :119 and item_scan_fst / _snd :98-109) *)
Lemma items_next : forall (s : list byte) k0 k f, (k < length s)%nat ->
  bz (hd NUL (skipn k s)) <> 32 -> skip_sp (skipn k s) = skip_sp (skipn k0 s) ->
  items_f (S f) (skipn k0 s) =
  firstn (PSRM.ilen 0 (skipn k s)) (skipn k s) :: items_f f (skipn (k + PSRM.ilen 0 (skipn k s)) s).
Proof.
intros s k0 k f Hk Hb Hsk.
assert (E1 : skip_sp (skipn k s) = skipn k s).
{ rewrite (PSRM.skip_sp_at s k ltac:(lia)). rewrite (proj2 (Z.eqb_neq _ 32) Hb). reflexivity. }
assert (Hne : skipn k s <> []) by (intros H; apply (f_equal (@length _)) in H; rewrite length_skipn in H; cbn in H; lia).
rewrite (PSRM.items_f_cons f (skipn k0 s) (skipn k s)); [| rewrite <- Hsk; exact E1 | exact Hne].
rewrite PSRM.item_scan_fst, PSRM.item_scan_snd. f_equal. f_equal. rewrite PSRM.skipn_add. reflexivity.
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
Hypothesis ABCMP : abcmp_realizes SEGS B (SIG CS___interceptor_trampoline_bcmp).
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation INV := (srm_inv B).
#[local] Notation OK := (srm_ok B).
#[local] Notation AT := (srm_at B).

(* ---- L1 (0x885f4): check C1, skip a ' '; a NUL ends the shape (TAIL), any other byte starts an item (L2).
   s3 = s4 = P + k, a0 = s3 + 1; k0 is the position the item loop started from. ---- *)
Definition l1_region : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition l1_facts : list (nat * afact) :=
  [(19%nat, mkAF 0 CEIL_HI 0); (20%nat, mkAF 0 CEIL_HI 0); (23%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)].
Lemma srm_L1 : forall x n t regs m md k0 k j f, OK x -> INV x regs m md -> L0_stmt B x n ->
  (length (x_shape x) - k < t)%nat -> (k0 <= k <= length (x_shape x))%nat ->
  skip_sp (skipn k (x_shape x)) = skip_sp (skipn k0 (x_shape x)) ->
  (length (x_shape x) - k0 < S n)%nat -> (length (x_shape x) - k0 <= f)%nat -> (j <= length (x_reply x))%nat ->
  reply_matches_items (items_f f (skipn k0 (x_shape x))) (skipn j (x_reply x)) = reply_matches (x_shape x) (x_reply x) ->
  getr regs 19 = w64 (x_P x + Z.of_nat k) -> getr regs 20 = w64 (x_P x + Z.of_nat k) ->
  getr regs 10 = w64 (x_P x + Z.of_nat k + 1) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 11 = w64 0x21120 -> getr regs 15 = w64 62 ->
  AT x SRM_L1 regs m md.
Proof.
intros x n t. revert x n. induction t as [|t IH];
  intros x n regs m md k0 k j f HX HI IHL0 Ht Hk Hsk Hn Hf Hj HV H19 H20 H10 H8 H11 H15; [lia|].
unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R23 & R22 & R24 & R25 & R9 & R27).
pose proof HX as (_ & _ & _ & [_ HSn] & _ & _ & _ & HSA & _).
set (b := srm_byte (x_shape x ++ [Z_to_bv 8 0]) k).
pose proof (srm_byte_range (x_shape x ++ [Z_to_bv 8 0]) k) as Hb. fold b in Hb.
remember (Eimg (Ereg regs [w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 b]) E) by (subst E; split; [intros r Hr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V19 : bv_unsigned (ew E 19) = x_P x + Z.of_nat k) by (subst E; apply (ew_EI_w64 regs _ 19 19%bv); [lia | reflexivity | exact H19 | lia]).
assert (V20 : bv_unsigned (ew E 20) = x_P x + Z.of_nat k) by (subst E; apply (ew_EI_w64 regs _ 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (V10 : bv_unsigned (ew E 10) = x_P x + Z.of_nat k + 1) by (subst E; apply (ew_EI_w64 regs _ 10 10%bv); [lia | reflexivity | exact H10 | lia]).
assert (V22 : bv_unsigned (ew E 22) = 32) by (subst E; apply (ew_EI_w64 regs _ 22 22%bv); [lia | reflexivity | exact R22 | lia]).
assert (V23 : bv_unsigned (ew E 23) = SB) by (subst E; apply (ew_EI_w64 regs _ 23 23%bv); [lia | reflexivity | exact R23 | unfold SB; lia]).
assert (V32 : bv_unsigned (ew E 32) = b) by (subst E; apply (ew_EX_w64 regs _ 0); [lia | reflexivity | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_L1 (srm_pins sr_atoms []) [l1_region] None (mkFacts l1_facts [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_L1)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed.
  - constructor.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, l1_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite V20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 32 0) b).
    + apply sv_w64. rewrite U_SOff, V32. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
    + simpl. lia.
    + lia.
    + rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. apply val_mem1_of_aview.
      exact (srm_shape_byte B x regs m md k HX HI ltac:(lia)).
  - cbn. tauto.
  - unfold facts_ok, l1_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite V19, V20, V23, V32. unfold CEIL_HI, SB. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan.
all: first [ awr_ok_tac | idtac ].
{ (* C1: the shape's byte k *)
  change (rd_of SEGS (mrestrict (w_H (x_W x)) m)) with (rdW (x_W x) m). unfold SRM_Bx.
  rewrite !U_SOff, V23, V19. unfold zcanon, M64. rewrite !Z.add_0_r, !Z.mod_small by (unfold SB; lia).
  eapply (range_addressable_sub _ _ (x_P x) (Z.of_nat (length (x_shape x)) + 1));
    [ eapply (srm_ra_kept B x regs m md); [exact HX | exact HI | lia | lia | exact HSA] | lia | lia ]. }
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* not a ' ' *)
  unorm Hc. bnorm Hc.
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM2 : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0))
  end.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
  + (* NUL: no item is left; the tail compare *)
    unorm Hc0. bnorm Hc0.
    assert (Lk : k = length (x_shape x)).
    { destruct (Nat.lt_ge_cases k (length (x_shape x))) as [L|L]; [|lia]. exfalso.
      refine (srm_byte_le (x_shape x) k L HSn _). unfold b in Hc0. rewrite srm_byte_app_lt in Hc0 by exact L. exact Hc0. }
    assert (HV0 : reply_matches_items [] (skipn j (x_reply x)) = reply_matches (x_shape x) (x_reply x)).
    { rewrite <- HV, PSRM.items_f_nil; [reflexivity|]. rewrite <- Hsk, Lk, skipn_all. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_TAIL; [awr_ok_tac|].
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (srm_tail B LAWS x (ms_regs msn) (ms_mem msn) _ j HX HIn Hj HV0);
    rewrite (HK2 8%bv) by (cbn; tauto); exact H8
    end.
  + (* the first byte of an item: the scan *)
    unorm Hc0. bnorm Hc0.
    assert (Lk : (k < length (x_shape x))%nat).
    { destruct (Nat.lt_ge_cases k (length (x_shape x))) as [L|L]; [exact L|]. exfalso. apply Hc0.
      unfold b. replace k with (length (x_shape x)) by lia. apply srm_byte_app_end. }
    assert (Hcb : bz (hd NUL (skipn k (x_shape x))) = b) by (unfold b; symmetry; apply srm_byte_hd; exact Lk).
    assert (HL1 : (1 <= PSRM.ilen 0 (skipn k (x_shape x)))%nat).
    { rewrite (ilen_step _ _ 0 Lk), Hcb, (proj2 (Z.eqb_neq b 32)) by lia. cbn. lia. }
    pose proof (PSRM.ilen_le 0 (skipn k (x_shape x))) as HLle. rewrite length_skipn in HLle.
    destruct f as [|f'']; [lia|].
    pose proof (items_next (x_shape x) k0 k f'' Lk ltac:(rewrite Hcb; lia) Hsk) as HIT.
    rewrite HIT in HV.
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L2; [awr_ok_tac|].
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 10; 11; 15; 19; 20]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (srm_L2 B LAWS TL ABCMP ASTRCSPN x n (S (length (x_shape x) - k)) HX IHL0 (ms_regs msn) (ms_mem msn) _ k 0%nat 0%Z j f''
      HIn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Nat.add_0_r; reflexivity) HL1 Hj ltac:(lia) ltac:(lia) HV);
    [ srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
    | rewrite (HK2 19%bv) by (cbn; tauto); exact H19
    | rewrite (HK2 20%bv) by (cbn; tauto); exact H20
    | rewrite (HK2 10%bv) by (cbn; tauto); rewrite Nat.add_0_r; exact H10
    | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; rewrite Nat.add_0_r; reflexivity
    | srm_rgoal HS; srm_ucalc; reflexivity
    | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
    | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
    | rewrite (HK2 15%bv) by (cbn; tauto); exact H15 ]
    end.
- (* a ' ': the next byte *)
  unorm Hc. bnorm Hc.
  assert (Lk : (k < length (x_shape x))%nat).
  { destruct (Nat.lt_ge_cases k (length (x_shape x))) as [L|L]; [exact L|]. exfalso.
    assert (b = 0) by (unfold b; replace k with (length (x_shape x)) by lia; apply srm_byte_app_end). lia. }
  assert (Hcb : bz (hd NUL (skipn k (x_shape x))) = b) by (unfold b; symmetry; apply srm_byte_hd; exact Lk).
  assert (Hsk' : skip_sp (skipn (S k) (x_shape x)) = skip_sp (skipn k0 (x_shape x))).
  { rewrite <- Hsk, (PSRM.skip_sp_at (x_shape x) k) by lia. rewrite Hcb, Hc. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L1; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 15]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (IH x n (ms_regs msn) (ms_mem msn) _ k0 (S k) j f HX HIn IHL0 ltac:(lia) ltac:(lia)
    Hsk' Hn Hf Hj HV);
  [ srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
  | rewrite (HK2 15%bv) by (cbn; tauto); exact H15 ]
  end.
Qed.

(* ---- L0 (0x885e8): a0 = s2 + 1, s3 = s4 = s2; on to L1. The item loop holds at every fuel. ---- *)
Lemma srm_main : forall x n, OK x -> L0_stmt B x n.
Proof.
intros x n HX. induction n as [|n IHL0]; intros k j f regs m md Hn Hk Hj Hf HV HI H18 H8 H11 H15; [lia|].
unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R23 & R22 & R24 & R25 & R9 & R27).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros r Hr; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V18 : bv_unsigned (ew E 18) = x_P x + Z.of_nat k) by (subst E; apply (ew_EI_w64 regs _ 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_L0 (srm_pins sr_atoms []) [] None (mkFacts [] [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_L0)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed; first [apply Forall_nil | vm_compute; reflexivity | exact I | (split; [exact I | split; exact I])]. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L1; [awr_ok_tac|].
lazymatch type of HS with context [restrict _ ?msn] =>
assert (KM : forall a0, 0 <= a0 < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a0 = rdW (x_W x) m a0)
  by (intros a0 Ha0; exact (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0));
srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 15]%bv : list (bv 5)) HK2;
pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
pmkst HS;
eapply (srm_L1 x n (S (length (x_shape x) - k)) (ms_regs msn) (ms_mem msn) _ k k j f HX HIn IHL0
  ltac:(lia) ltac:(lia) eq_refl Hn Hf Hj HV);
[ srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity
| srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity
| srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity
| rewrite (HK2 8%bv) by (cbn; tauto); exact H8
| rewrite (HK2 11%bv) by (cbn; tauto); exact H11
| rewrite (HK2 15%bv) by (cbn; tauto); exact H15 ]
end.
Qed.
End e.
End f.
End d.
