(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_memptr_cmp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Ltac zsign_range v := unfold zsign; destruct (v <? 0); [lia|]; destruct (0 <? v); lia.

#[using="IC"] Lemma memptr_cmp_spec_A : memptr_cmp_stmt_A.
Proof.
  unfold memptr_cmp_stmt_A, memptr_cmp_stmt_A_at, memptr_cmp_entryA.
  intros MP T n S lo tok str slack q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros MPC TOK TL N0 STR NONUL PAD AE0 SH SHWT SHWS MLO MHI AM AL THI SHI STRB ST CLO QHI LO MI -> ->.
  a0_prologue AE0 [(lo, q)]%Z m.
  unfold app_mem in AM. shadow_cells_lit SH. unfold A0_RT_STACK in LO.
  pose proof (rw_cells_bound asegs _ _ _ MPC) as B1. cbn [cells_size csize Nat.add memptr_cells] in B1.
  pose proof (bytes_at_bound _ _ _ _ TOK) as B2. pose proof (bytes_at_bound _ _ _ _ STR) as B3.
  rewrite length_app in B3. cbn [length] in B3.
  unfold memptr_cells in MPC.
  carve_frame 32%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  step. step. step.
  step. step. achk SH 0%nat MP.
  zstep.
  step. step. step. achk SH 1%nat (MP + 8)%Z.
  step. step. zstep. zstep.
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (proj1 (proj1 (bytes_at_app asegs mm T (firstn (Z.to_nat n) tok) (skipn (Z.to_nat n) tok)) ltac:(rewrite firstn_skipn; exact TOK))) as TOKn;
    pose proof (proj1 (proj1 (bytes_at_app asegs mm S (str ++ [Z_to_bv 8 0]) slack) ltac:(rewrite <- app_assoc; exact STR))) as STR0 end.
  pose proof SHWT as SHWT1. pose proof SHWS as SHWS1. shw_now SHWT1 MU. shw_now SHWS1 MU. env_now AE0 MU WM.
  destruct (P0.H_memptr_cmp.strncmp_model_some str (firstn (Z.to_nat n) tok) (@nil byte) n ltac:(lia) ltac:(rewrite firstn_length; lia)) as (v & HM & HV).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_strncmp IC) with (ls := firstn (Z.to_nat n) tok) (rs := str ++ [Z_to_bv 8 0]) (lo := lo) (v := v);
      rewrite ?firstn_length, ?length_app; cbn [length];
      first [ exact TOKn | exact STR0 | exact HM | exact MI | exact AE | reflexivity | lia
            | (eapply accessible_sub; [exact (proj1 SHWT1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWT1)) | lia | lia | lia])
            | (eapply accessible_sub; [exact (proj1 SHWS1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWS1)) | lia | lia | lia])
            | rng_tac | assumption ]
    | post_call asegs mm ] end.
  clear SHWT1 SHWS1.
  step. if_cases K; zify_cond K.
  -
    zstep. zstep. step.
    pose proof SHWS as SHWS1. shw_now SHWS1 MU. env_now AE0 MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_strlen IC) with (str := str) (slack := slack) (lo := lo);
        first [ exact STR | exact NONUL | exact PAD | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1)) | exact AE | reflexivity
              | lia | rng_tac | assumption ]
      | post_call asegs mm ] end.
    clear SHWS1.
    step. step. step. if_cases K2; zify_cond K2.
    + step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: zsign_range v.
    + zstep. step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: lia.
  - step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: zsign_range v.
Qed.

#[using="IC"] Lemma memptr_cmp_nocase_spec_A : memptr_cmp_nocase_stmt_A.
Proof.
  unfold memptr_cmp_nocase_stmt_A, memptr_cmp_stmt_A_at, memptr_cmp_nocase_entryA.
  intros MP T n S lo tok str slack q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros MPC TOK TL N0 STR NONUL PAD AE0 SH SHWT SHWS MLO MHI AM AL THI SHI STRB ST CLO QHI LO MI -> ->.
  a0_prologue AE0 [(lo, q)]%Z m.
  unfold app_mem in AM. shadow_cells_lit SH. unfold A0_RT_STACK in LO.
  pose proof (rw_cells_bound asegs _ _ _ MPC) as B1. cbn [cells_size csize Nat.add memptr_cells] in B1.
  pose proof (bytes_at_bound _ _ _ _ TOK) as B2. pose proof (bytes_at_bound _ _ _ _ STR) as B3.
  rewrite length_app in B3. cbn [length] in B3.
  unfold memptr_cells in MPC.
  carve_frame 32%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  step. step. step.
  step. step. achk SH 0%nat MP.
  zstep.
  step. step. step. achk SH 1%nat (MP + 8)%Z.
  step. step. zstep. zstep.
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (proj1 (proj1 (bytes_at_app asegs mm T (firstn (Z.to_nat n) tok) (skipn (Z.to_nat n) tok)) ltac:(rewrite firstn_skipn; exact TOK))) as TOKn;
    pose proof (proj1 (proj1 (bytes_at_app asegs mm S (str ++ [Z_to_bv 8 0]) slack) ltac:(rewrite <- app_assoc; exact STR))) as STR0 end.
  pose proof SHWT as SHWT1. pose proof SHWS as SHWS1. shw_now SHWT1 MU. shw_now SHWS1 MU. env_now AE0 MU WM.
  destruct (P0.H_memptr_cmp.strncasecmp_model_some str (firstn (Z.to_nat n) tok) (@nil byte) n ltac:(lia) ltac:(rewrite firstn_length; lia)) as (v & HM & HV).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_strncasecmp IC) with (ls := firstn (Z.to_nat n) tok) (rs := str ++ [Z_to_bv 8 0]) (lo := lo) (v := v);
      rewrite ?firstn_length, ?length_app; cbn [length];
      first [ exact TOKn | exact STR0 | exact HM | exact MI | exact AE | reflexivity | lia
            | (eapply accessible_sub; [exact (proj1 SHWT1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWT1)) | lia | lia | lia])
            | (eapply accessible_sub; [exact (proj1 SHWS1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWS1)) | lia | lia | lia])
            | rng_tac | assumption ]
    | post_call asegs mm ] end.
  clear SHWT1 SHWS1.
  step. if_cases K; zify_cond K.
  -
    zstep. zstep. step.
    pose proof SHWS as SHWS1. shw_now SHWS1 MU. env_now AE0 MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_strlen IC) with (str := str) (slack := slack) (lo := lo);
        first [ exact STR | exact NONUL | exact PAD | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1)) | exact AE | reflexivity
              | lia | rng_tac | assumption ]
      | post_call asegs mm ] end.
    clear SHWS1.
    step. step. step. if_cases K2; zify_cond K2.
    + step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: first [zsign_range v| lia].
    + zstep. step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: lia.
  - step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: first [zsign_range v| lia].
Qed.
End W.
