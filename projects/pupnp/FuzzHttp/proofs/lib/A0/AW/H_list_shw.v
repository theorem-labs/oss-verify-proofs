(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_list_access H_memptr_cmp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto H_memptr_cmp AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.

#[using="Type"] Lemma ListHead_shw : forall (L first last size flh fk ffree fcmp lo : Z)
    (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m L (llist_cells first last size flh fk ffree fcmp) ->
  L <> 0 -> 0 <= size < 2^63 -> 0 <= first < 2^64 ->
  asan_env asegs m -> shw m L 96 ->
  0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
  mem_inv asegs m -> a0 = wz L ->
  evt asegs (ListHead_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc first size lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListHead_entryA) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LC NZ SZ FRG AE0 SHL LLO LHI AL ST CLO QHI LO MI ->. unfold ListHead_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  pose proof (rw_cells_bound asegs _ _ _ LC) as BL. cbn [cells_size csize Nat.add llist_cells] in BL.
  unfold llist_cells in LC.
  carve_frame 16%nat ST.
  step. fix_lit_store. step. fix_lit_store.
  step. if_cases K; zify_cond K; condn K. { exfalso. lia. }
  pose proof SHL as SHL1. shw_now SHL1 MU.
  do 9 cstep.
  step. if_cases K2; zify_cond K2; condn K2.
  - step. step. step. step.
    env_now AE0 MU WM.
    match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
    subst size. unfold ListHead_post_A. cbn [Z.eqb]. finish.
  - do 6 cstep.
    step. step. step.
    env_now AE0 MU WM.
    match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
    unfold ListHead_post_A. destruct (Z.eqb_spec size 0); [lia|]. finish.
Qed.

#[using="Type"] Lemma ListNext_shw : forall (L N pv nx it lo : Z)
    (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m N (node_cells pv nx it) ->
  L <> 0 -> N <> 0 -> 0 <= nx < 2^64 -> (0 < L /\ L + 96 < 2^64) ->
  asan_env asegs m -> shw m N 24 ->
  0x609000 <= N -> N + 24 <= alloc_ceiling -> N mod 8 = 0 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
  mem_inv asegs m -> a0 = wz L -> a1 = wz N ->
  evt asegs (ListNext_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L nx lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListNext_entryA) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros NC LNZ NNZ NX LR AE0 SHN NLO NHI AL ST CLO QHI LO MI -> ->. unfold ListNext_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  pose proof (rw_cells_bound asegs _ _ _ NC) as BN. cbn [cells_size csize Nat.add node_cells] in BN.
  unfold node_cells in NC.
  carve_frame 16%nat ST.
  step. fix_lit_store. step. fix_lit_store.
  zstep.
  zstep. if_cases K; zify_cond K; condn K. { exfalso; lia. }
  zstep. if_cases K2; zify_cond K2; condn K2. { exfalso; lia. }
  pose proof SHN as SHN1. shw_now SHN1 MU.
  do 8 cstep.
  zstep.
  zstep. zstep. zstep. zstep. zstep.
  change (Z.land _ nx) with (P0.H_list_access.listnext_expr nx (L + 24)). rewrite P0.H_list_access.listnext_eval by lia.
  zstep. step. step. step.
  env_now AE0 MU WM.
  match goal with P : stk asegs _ lo _ |- _ => release_frame FR P q end.
  finish.
Qed.

Hypothesis IC : icpt_contracts.
Ltac zsign_range v := unfold zsign; destruct (v <? 0); [lia|]; destruct (0 <? v); lia.

#[using="IC"] Lemma memptr_cmp_nocase_shw : forall (MP T n S lo : Z) (tok str slack : list byte)
    (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m MP (memptr_cells T n) ->
  bytes_at asegs m T tok -> Z.of_nat (length tok) >= n -> 1 <= n <= 2^43 ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  asan_env asegs m -> shw m MP 16 ->
  shw m T n -> shw m S (Z.of_nat (length str) + 1) ->
  0x609000 <= MP -> MP + 16 <= alloc_ceiling -> MP mod 8 = 0 ->
  T + Z.of_nat (length tok) <= alloc_ceiling -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
  Z.of_nat (length str) + 1 <= 2^43 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 32 - A0_RT_STACK ->
  mem_inv asegs m -> a0 = wz MP -> a1 = wz S ->
  evt asegs (memptr_cmp_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz memptr_cmp_nocase_entryA) fc None m (seg_rom asegs)).
Proof.
  unfold memptr_cmp_nocase_entryA.
  intros MP T n S lo tok str slack q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros MPC TOK TL N0 STR NONUL PAD AE0 SHM SHWT SHWS MLO MHI AL THI SHI STRB ST CLO QHI LO MI -> ->.
  a0_prologue AE0 [(lo, q)]%Z m.
  unfold A0_RT_STACK in LO.
  pose proof (rw_cells_bound asegs _ _ _ MPC) as B1. cbn [cells_size csize Nat.add memptr_cells] in B1.
  pose proof (bytes_at_bound _ _ _ _ TOK) as B2. pose proof (bytes_at_bound _ _ _ _ STR) as B3.
  rewrite length_app in B3. cbn [length] in B3.
  unfold memptr_cells in MPC.
  carve_frame 32%nat ST.
  step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
  pose proof SHM as SHM1. shw_now SHM1 MU.
  do 7 cstep.
  zstep.
  do 5 cstep.
  step. step. zstep. zstep.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (proj1 (proj1 (bytes_at_app asegs mm T (firstn (Z.to_nat n) tok) (skipn (Z.to_nat n) tok)) ltac:(rewrite firstn_skipn; exact TOK))) as TOKn;
    pose proof (proj1 (proj1 (bytes_at_app asegs mm S (str ++ [Z_to_bv 8 0]) slack) ltac:(rewrite <- app_assoc; exact STR))) as STR0 end.
  clear SHM1.
  pose proof SHWT as SHWT1. pose proof SHWS as SHWS1. shw_now SHWT1 MU. shw_now SHWS1 MU. env_now AE0 MU WM.
  destruct (P0.H_memptr_cmp.strncasecmp_model_some str (firstn (Z.to_nat n) tok) (@nil byte) n ltac:(lia) ltac:(rewrite firstn_length; lia)) as (v & HM & HV).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_strncasecmp IC) with (ls := firstn (Z.to_nat n) tok) (rs := str ++ [Z_to_bv 8 0]) (lo := lo) (v := v);
      rewrite ?firstn_length, ?length_app; cbn [length];
      first [ rng_tac | exact TOKn | exact STR0 | exact HM | exact MI | exact AE | reflexivity | lia
            | (eapply accessible_sub; [exact (proj1 SHWT1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWT1)) | lia | lia | lia])
            | (eapply accessible_sub; [exact (proj1 SHWS1) | lia | lia])
            | (eapply sh_readable_sub; [exact (proj1 (proj2 SHWS1)) | lia | lia | lia])
            | assumption ]
    | post_call asegs mm ] end.
  clear SHWT1 SHWS1.
  step. if_cases K; zify_cond K.
  - zstep. zstep. step.
    pose proof SHWS as SHWS1. shw_now SHWS1 MU. env_now AE0 MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (ic_strlen IC) with (str := str) (slack := slack) (lo := lo);
        first [ rng_tac | exact STR | exact NONUL | exact PAD | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1)) | exact AE | reflexivity
              | lia | assumption ]
      | post_call asegs mm ] end.
    clear SHWS1.
    step. step. step. if_cases K2; zify_cond K2.
    + step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: first [zsign_range v| lia].
    + zstep. step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: lia.
  - step. step. step. step. step. step. env_now AE0 MU WM. release_to q. finish. all: first [zsign_range v| lia].
Qed.
End W.
