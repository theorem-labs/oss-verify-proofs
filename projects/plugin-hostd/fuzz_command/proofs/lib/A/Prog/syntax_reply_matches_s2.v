(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and lib/A/AC8b.v at
   c8557374ad2e: the walk of syntax_reply_matches on fuzz_command.asan, the segments after a word of the reply is
   matched: JOIN (0x88708: step the reply past the word, checks C4 and C5) and JOIN2 (0x88748: back to the item loop or
   return). *)
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
  CmdPaLib PaSB PaDenot CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import syntax_reply_matches_c syntax_reply_matches_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a branch condition or register value over the walk's atoms, as a fact over Z *)
Ltac unorm H :=
  rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U, ?branch_geu_U in H;
  repeat (rewrite U_SAlu in H || rewrite U_SOff in H || rewrite U_SLit in H); cbn [zalu_raw ew ewset Nat.eqb] in H;
  repeat match goal with V : bv_unsigned (ew ?E ?n) = _ |- _ => rewrite V in H end;
  unfold zcanon, M64 in H; rewrite ?Z.add_0_r in H;
  repeat match type of H with context [?a mod 2 ^ 64] => rewrite (Z.mod_small a (2 ^ 64)) in H by lia end.
Ltac bnorm H :=
  first [ apply (proj1 (Bool.negb_true_iff _)) in H | apply (proj1 (Bool.negb_false_iff _)) in H | idtac ];
  first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H
        | apply (proj1 (Z.ltb_lt _ _)) in H | apply (proj1 (Z.ltb_ge _ _)) in H | idtac ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation STK := SYNTAX_REPLY_MATCHES_STK.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation INV := (srm_inv B).
#[local] Notation OK := (srm_ok B).
#[local] Notation AT := (srm_at B).

(* The item loop's head (L0, 0x885e8), as the statement every later segment returns to: the shape cursor s2 = P + k,
   the reply cursor s0 = R + j, a1 = " ", a5 = '>' and the rest of the match the plain proof's main_loop carries
   (lib/Prog/syntax_reply_matches.v:453-459), with the item count below n. *)
Definition L0_stmt (x : srm_ctx) (n : nat) : Prop :=
  forall k j f regs m md, (length (x_shape x) - k < n)%nat -> (k <= length (x_shape x))%nat ->
  (j <= length (x_reply x))%nat -> (length (x_shape x) - k <= f)%nat ->
  reply_matches_items (items_f f (skipn k (x_shape x))) (skipn j (x_reply x)) = reply_matches (x_shape x) (x_reply x) ->
  INV x regs m md -> getr regs 18 = w64 (x_P x + Z.of_nat k) -> getr regs 8 = w64 (x_R x + Z.of_nat j) ->
  getr regs 11 = w64 0x21120 -> getr regs 15 = w64 62 -> AT x SRM_L0 regs m md.

(* ---- JOIN2 (0x88748): the reply byte after the ' ' that ends the word; back to the item loop or return 0 ---- *)
Definition j2_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition j2_facts : list (nat * afact) := [(8%nat, mkAF 0 CEIL_HI 0); (23%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)].
Lemma srm_join2 : forall x n regs m md j2 k2 f', OK x -> INV x regs m md -> L0_stmt x n ->
  (j2 <= length (x_reply x))%nat -> (k2 <= length (x_shape x))%nat -> (length (x_shape x) - k2 < n)%nat ->
  (length (x_shape x) - k2 <= f')%nat ->
  match skipn j2 (x_reply x) with
  | [] => false
  | _ => reply_matches_items (items_f f' (skipn k2 (x_shape x))) (skipn j2 (x_reply x))
  end = reply_matches (x_shape x) (x_reply x) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j2) -> getr regs 18 = w64 (x_P x + Z.of_nat k2) ->
  getr regs 11 = w64 0x21120 -> getr regs 15 = w64 62 ->
  AT x SRM_JOIN2 regs m md.
Proof.
intros x n regs m md j2 k2 f' HX HI IHL0 Hj Hk Hn Hf HV H8 H18 H11 H15. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R23 & R22 & R24 & R25 & R9 & R27).
set (b := srm_byte (x_reply x ++ [Z_to_bv 8 0]) j2).
pose proof (srm_byte_range (x_reply x ++ [Z_to_bv 8 0]) j2) as Hb. fold b in Hb.
remember (Eimg (Ereg regs [w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 b]) E) by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E8 : ew E 8 = w64 (x_R x + Z.of_nat j2)) by (subst E; rewrite ew_EI by lia; exact H8).
assert (E23 : ew E 23 = w64 SB) by (subst E; rewrite ew_EI by lia; exact R23).
assert (E32 : ew E 32 = w64 b) by (subst E; apply (ew_EX regs [w64 b] 0); lia).
assert (V32 : bv_unsigned (ew E 32) = b) by (rewrite E32; apply w64_unsigned; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_JOIN2 (srm_pins sr_atoms []) [j2_region] None (mkFacts j2_facts [] []))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_JOIN2)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed.
  - constructor.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, j2_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8, w64_unsigned by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 32 0) b).
    + cbn [sv_denot]. rewrite E32, w64_unsigned by lia. rewrite Z.add_0_r. reflexivity.
    + simpl. lia.
    + lia.
    + rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. apply val_mem1_of_aview.
      exact (srm_reply_byte B x regs m md j2 HX HI Hj).
  - cbn. tauto.
  - unfold facts_ok, j2_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E8, E23, E32, !w64_unsigned by (unfold SB; lia). unfold CEIL_HI, SB. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ HRn] & _).
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* b <> 0: the reply goes on, back to the item loop *)
  unorm Hc. bnorm Hc.
  assert (Lj : (j2 < length (x_reply x))%nat).
  { destruct (Nat.lt_ge_cases j2 (length (x_reply x))) as [L|L]; [exact L|]. exfalso. apply Hc.
    unfold b. replace j2 with (length (x_reply x)) by lia. apply srm_byte_app_end. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L0; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a Ha; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a Ha); exact (KM1 a Ha));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([8; 11; 15; 18]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (IHL0 k2 j2 f' (ms_regs msn) (ms_mem msn) _ Hn Hk Hj Hf);
  [ destruct (skipn j2 (x_reply x)) eqn:Es;
      [apply (f_equal (@length _)) in Es; rewrite length_skipn in Es; cbn in Es; lia | exact HV]
  | exact HIn
  | rewrite (HK2 18%bv) by (cbn; tauto); exact H18
  | rewrite (HK2 8%bv) by (cbn; tauto); exact H8
  | rewrite (HK2 11%bv) by (cbn; tauto); exact H11
  | rewrite (HK2 15%bv) by (cbn; tauto); exact H15 ]
  end.
- (* b = 0: return 0 *)
  unorm Hc. bnorm Hc.
  assert (Lj : j2 = length (x_reply x)).
  { destruct (Nat.lt_ge_cases j2 (length (x_reply x))) as [L|L]; [|lia]. exfalso.
    refine (srm_byte_le (x_reply x) j2 L HRn _). unfold b in Hc. rewrite srm_byte_app_lt in Hc by exact L. exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_EPI; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a Ha; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a Ha); exact (KM1 a Ha));
  srm_kept HS HAE SRM_KEEP HK;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (srm_epi B LAWS x (ms_regs msn) (ms_mem msn) _ HX HIn)
  end.
  subst j2. rewrite skipn_all in HV. rewrite <- HV.
  srm_rgoal HS. srm_ucalc. rewrite Hc. reflexivity.
Qed.

Lemma word_end_byte : forall (r : list byte) j w, w = word_len (skipn j r) -> (j + w < length r)%nat ->
  srm_byte (r ++ [Z_to_bv 8 0]) (j + w) = 32.
Proof.
intros r j w Hw Hl. rewrite srm_byte_app_lt by exact Hl. unfold srm_byte.
destruct (PSRM.word_len_skip (skipn j r)) as [E0 | (c & t & E0 & Ec)]; rewrite <- Hw, skipn_skipn in E0.
- apply (f_equal (@length _)) in E0. rewrite length_skipn in E0. cbn in E0. lia.
- rewrite <- (hd_skipn_nth r (j + w)). replace (j + w)%nat with (w + j)%nat by lia. rewrite E0. exact Ec.
Qed.

(* ---- JOIN (0x88708): s0 += w, check C4, *s0 is '\0' (back to the item loop) or ' ' (check C5, on to JOIN2) ---- *)
Definition join_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition join_facts : list (nat * afact) :=
  [(8%nat, mkAF 0 CEIL_HI 0); (21%nat, mkAF 0 268435456 0); (23%nat, mkAF SB SB 0); (32%nat, mkAF 0 CEIL_HI 0);
   (33%nat, mkAF 0 255 0)].
Definition join_alias : list (sv * sv) := [(SAlu ALU_ADD (SOff 8 0) (SOff 21 0), SOff 32 0)].
Lemma srm_join : forall x n regs m md j w k2 f', OK x -> INV x regs m md -> L0_stmt x n ->
  w = word_len (skipn j (x_reply x)) -> (j + w <= length (x_reply x))%nat ->
  (k2 <= length (x_shape x))%nat -> (length (x_shape x) - k2 < n)%nat -> (length (x_shape x) - k2 <= f')%nat ->
  match skipn (j + w) (x_reply x) with
  | [] => reply_matches_items (items_f f' (skipn k2 (x_shape x))) []
  | _ :: [] => false
  | _ :: r'' => reply_matches_items (items_f f' (skipn k2 (x_shape x))) r''
  end = reply_matches (x_shape x) (x_reply x) ->
  getr regs 8 = w64 (x_R x + Z.of_nat j) -> getr regs 21 = w64 (Z.of_nat w) -> getr regs 26 = w64 0x21120 ->
  getr regs 18 = w64 (x_P x + Z.of_nat k2) ->
  AT x SRM_JOIN regs m md.
Proof.
intros x n regs m md j w k2 f' HX HI IHL0 Hw Hjw Hk Hn Hf HV H8 H21 H26 H18. unfold srm_at.
pose proof (srm_ok_facts B x HX) as (F1 & F2 & F3 & F4 & FP1 & FP2 & FR1 & FR2 & FL1 & FL2).
pose proof asan_consts as (C1 & _).
pose proof HI as (HJ & _ & _ & R2 & R3 & R4 & R23 & R22 & R24 & R25 & R9 & R27).
pose proof HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ HRn] & _ & _ & _ & HRA & _).
remember (x_R x + Z.of_nat (j + w)) as a eqn:Ha.
set (b := srm_byte (x_reply x ++ [Z_to_bv 8 0]) (j + w)).
pose proof (srm_byte_range (x_reply x ++ [Z_to_bv 8 0]) (j + w)) as Hb. fold b in Hb.
remember (Eimg (Ereg regs [w64 a; w64 b])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 a; w64 b]) E)
  by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (V8 : bv_unsigned (ew E 8) = x_R x + Z.of_nat j) by (subst E; apply (ew_EI_w64 regs _ 8 8%bv); [lia | reflexivity | exact H8 | lia]).
assert (V21 : bv_unsigned (ew E 21) = Z.of_nat w) by (subst E; apply (ew_EI_w64 regs _ 21 21%bv); [lia | reflexivity | exact H21 | lia]).
assert (V23 : bv_unsigned (ew E 23) = SB) by (subst E; apply (ew_EI_w64 regs _ 23 23%bv); [lia | reflexivity | exact R23 | unfold SB; lia]).
assert (V26 : bv_unsigned (ew E 26) = 0x21120) by (subst E; apply (ew_EI_w64 regs _ 26 26%bv); [lia | reflexivity | exact H26 | lia]).
assert (V22 : bv_unsigned (ew E 22) = 32) by (subst E; apply (ew_EI_w64 regs _ 22 22%bv); [lia | reflexivity | exact R22 | lia]).
assert (V32 : bv_unsigned (ew E 32) = a) by (subst E; apply (ew_EX_w64 regs _ 0); [lia | reflexivity | lia]).
assert (V33 : bv_unsigned (ew E 33) = b) by (subst E; apply (ew_EX_w64 regs _ 1); [lia | reflexivity | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS SRM_JOIN (srm_pins sr_atoms []) [join_region] None (mkFacts join_facts [] join_alias))
  (restrict (w_H (x_W x)) (mkst regs (Z_to_bv 64 (BASE + SRM_JOIN)) m (seg_rom SEGS)))).
{ subst E. apply srm_seed.
  - constructor.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, join_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite V32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 33 0) b).
    + apply sv_w64. rewrite U_SOff, V33. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. lia.
    + simpl. lia.
    + lia.
    + rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. apply val_mem1_of_aview.
      rewrite Ha. exact (srm_reply_byte B x regs m md (j + w) HX HI Hjw).
  - cbn. tauto.
  - unfold facts_ok, join_facts, join_alias. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite V8, V21, V23, V32, V33. unfold CEIL_HI, SB. rewrite !Z.pow_0_r, !Z.mod_1_r.
    split; [repeat split; lia|]. split; [exact I|]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, V8, V21, V32. unfold zcanon, M64. rewrite !Z.add_0_r.
    rewrite (Z.mod_small (x_R x + Z.of_nat j)) by lia. rewrite (Z.mod_small (Z.of_nat w)) by lia.
    f_equal. lia. }
clear HE.
assert (SHOK : sh_ok SEGS SRM_Bx [] E (mrestrict (w_H (x_W x)) m)) by constructor.
paj_run_tok RUN HS HJ SHOK SRM_Bspan.
all: first [ awr_ok_tac | idtac ].
{ (* C4: *s0 is a byte of the reply or its terminator *)
  change (rd_of SEGS (mrestrict (w_H (x_W x)) m)) with (rdW (x_W x) m). unfold SRM_Bx.
  rewrite !U_SOff, V23, V32. unfold zcanon, M64. rewrite !Z.add_0_r, !Z.mod_small by (unfold SB; lia).
  eapply (range_addressable_sub _ _ (x_R x) (Z.of_nat (length (x_reply x)) + 1));
    [ eapply (srm_ra_kept B x regs m md); [exact HX | exact HI | lia | lia | exact HRA] | lia | lia ]. }
assert (KM1 := frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
- (* *s0 = '\0': the reply is used up; back to the item loop *)
  unorm Hc. bnorm Hc.
  assert (Ljw : (j + w = length (x_reply x))%nat).
  { destruct (Nat.lt_ge_cases (j + w) (length (x_reply x))) as [L|L]; [|lia]. exfalso.
    refine (srm_byte_le (x_reply x) (j + w) L HRn _). unfold b in Hc. rewrite srm_byte_app_lt in Hc by exact L. exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_L0; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0));
  srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([18]%bv : list (bv 5)) HK2;
  pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
  pmkst HS;
  eapply (IHL0 k2 (j + w)%nat f' (ms_regs msn) (ms_mem msn) _ Hn Hk ltac:(lia) Hf);
  [ rewrite Ljw, skipn_all; rewrite Ljw, skipn_all in HV; exact HV
  | exact HIn
  | rewrite (HK2 18%bv) by (cbn; tauto); exact H18
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity
  | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity ]
  end.
- (* *s0 <> '\0': it is the ' ' that ends the word *)
  unorm Hc. bnorm Hc.
  assert (Ljw : (j + w < length (x_reply x))%nat).
  { destruct (Nat.lt_ge_cases (j + w) (length (x_reply x))) as [L|L]; [exact L|]. exfalso. apply Hc.
    unfold b. replace (j + w)%nat with (length (x_reply x)) by lia. apply srm_byte_app_end. }
  assert (B32 : b = 32) by (unfold b; apply word_end_byte; assumption).
  paj_run_tok RUN HS HJ SHOK SRM_Bspan; [awr_ok_tac|].
  lazymatch type of HS with context [restrict _ ?msn] =>
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
    by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM1 a0 Ha0))
  end.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK SRM_Bspan.
  + (* *s0 <> ' ': not a word end; impossible *)
    exfalso. unorm Hc0. bnorm Hc0. apply Hc0. rewrite B32. reflexivity.
  + unorm Hc0. bnorm Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK SRM_Bspan SRM_JOIN2.
    all: first [ awr_ok_tac | idtac ].
    { (* C5: s0 + 1 is inside the reply, after the ' ' *)
      lazymatch goal with |- range_addressable (rd_of _ (mrestrict _ (ms_mem ?msx))) _ _ _ =>
        change (rd_of SEGS (mrestrict (w_H (x_W x)) (ms_mem msx))) with (rdW (x_W x) (ms_mem msx)) end.
      unfold SRM_Bx. rewrite !U_SOff. cbn [ew ewset Nat.eqb]. rewrite V23, V32. unfold zcanon, M64.
      rewrite !Z.add_0_r, !Z.mod_small by (unfold SB; lia).
      apply (ra_agree_all _ _ _ _ KM2); [lia | lia|].
      eapply (range_addressable_sub _ _ (x_R x) (Z.of_nat (length (x_reply x)) + 1));
        [ eapply (srm_ra_kept B x regs m md); [exact HX | exact HI | lia | lia | exact HRA] | lia | lia ]. }
    lazymatch type of HS with context [restrict _ ?msn] =>
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W x) (ms_mem msn) a = rdW (x_W x) m a)
      by (intros a0 Ha0; rewrite (frame_ro_keep _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) a0 Ha0); exact (KM2 a0 Ha0));
    srm_kept HS HAE SRM_KEEP HK; srm_kept HS HAE ([18]%bv : list (bv 5)) HK2;
    pose proof (srm_inv_next B x regs m md (ms_regs msn) (ms_mem msn) _ HX HI HJ KM HK) as HIn;
    pmkst HS;
    eapply (srm_join2 x n (ms_regs msn) (ms_mem msn) _ (S (j + w)) k2 f' HX HIn IHL0 ltac:(lia) Hk Hn Hf);
    [ rewrite (PSRM.hd_skipn_S (x_reply x) (j + w) Ljw) in HV; cbv beta iota in HV; exact HV
    | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; lia
    | rewrite (HK2 18%bv) by (cbn; tauto); exact H18
    | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity
    | srm_rgoal HS; srm_ucalc; rewrite Z.mod_small by lia; reflexivity ]
    end.
Qed.
End e.
End f.
End d.
