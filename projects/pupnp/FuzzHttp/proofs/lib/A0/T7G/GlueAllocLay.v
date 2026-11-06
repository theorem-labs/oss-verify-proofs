(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout PEnv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit.
Import ListNotations.
Open Scope Z_scope.

Definition top_of (V : nat -> Z) : Z := 32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat).
Definition AL_of (V : nat -> Z) : alayout :=
  mkAL (4096 * V 208%nat + -4096 * V 209%nat + 65536) (4096 * V 226%nat)
       (mkAT (4096 * V 228%nat) (4096 * V 227%nat) (top_of V) (top_of V + -8388608))
       (4096 * V 377%nat) (mkDL (4096 * V 453%nat) (4096 * V 454%nat) 8388608) (4096 * V 310%nat).

Definition E_of (V : nat -> Z) : penv := mkPEnv (Z_to_bv 64 (V 45%nat)) 1 1.

Section Lay.
Context {HC : HasCeiling}.
Variable V : nat -> Z.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis CEIL : alloc_ceiling = 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608.

Definition ent_ok (b n : Z) : Prop :=
  0 < b /\ (b + n <= 65536 \/ 65536 + 6262784 <= b) /\ (b + n <= 2147446784 \/ 2147446784 + 17592186048512 <= b)
  /\ b + n <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608.

#[using="HP"] Lemma sp_digits : 4294901760 <= V 0%nat <= 4294967295 /\ 0 <= V 6%nat <= 255 /\ 0 <= V 10%nat <= 7 /\ 0 <= V 344%nat <= 1
  /\ 0 <= 16 * V 6%nat - 4096 * V 344%nat + 3935 <= 4095.
Proof.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10. pf V HP (PVar 344 0 1) P344.
  pf V HP (PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095) PR.
  split; [exact P0|]. split; [exact P6|]. split; [exact P10|]. split; [exact P344|].
  unfold two64 in PR. change (2^64) with 18446744073709551616 in PR. clear - P6 P344 PR. Z.div_mod_to_equations. lia.
Qed.

Ltac ent_tac P D1 D2 D3 :=
  unfold ent_ok; split; [lia|]; split; [first [exact D1 | right; lia]|]; split; [exact D2|];
  destruct sp_digits as (S0 & S6 & S10 & S344 & _); destruct D3 as [D3|D3]; [exact D3| exfalso; lia].

#[using="HP"] Lemma ent_208 : ent_ok (4096 * V 208%nat) 137439023104.
Proof.
  pf V HP (PVar 208 4295491576 34326181871) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P I D2 D3.
Qed.
#[using="HP"] Lemma ent_226 : ent_ok (4096 * V 226%nat) 8388608.
Proof.
  pf V HP (PVar 226 1545 34359734272) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P I D2 D3.
Qed.
#[using="HP"] Lemma ent_227 : ent_ok (4096 * V 227%nat) 4096.
Proof.
  pf V HP (PVar 227 1 34359736319) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6262784) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P D1 D2 D3.
Qed.
#[using="HP"] Lemma ent_228 : ent_ok (4096 * V 228%nat) 65536.
Proof.
  pf V HP (PVar 228 1545 34359736304) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P I D2 D3.
Qed.
#[using="HP"] Lemma ent_310 : ent_ok (4096 * V 310%nat) 4096.
Proof.
  pf V HP (PVar 310 1 34359736319) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6262784) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P D1 D2 D3.
Qed.
#[using="HP"] Lemma ent_377 : ent_ok (4096 * V 377%nat) 11571200.
Proof.
  pf V HP (PVar 377 1545 34359733495) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P I D2 D3.
Qed.
#[using="HP"] Lemma ent_453 : ent_ok (4096 * V 453%nat) 1048576.
Proof.
  pf V HP (PVar 453 1545 34359736064) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P I D2 D3.
Qed.
#[using="HP"] Lemma ent_454 : ent_ok (4096 * V 454%nat) 8388608.
Proof.
  pf V HP (PVar 454 1545 34359734272) P.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZLit 2147446784) 17592186048512) D2.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D3.
  ent_tac P I D2 D3.
Qed.

Definition ents : list (Z * Z) :=
  [ (4096 * V 208%nat, 137439023104); (4096 * V 226%nat, 8388608); (4096 * V 228%nat, 65536); (4096 * V 227%nat, 4096); (4096 * V 377%nat, 11571200); (4096 * V 453%nat, 1048576); (4096 * V 454%nat, 8388608); (4096 * V 310%nat, 4096) ].
#[using="HP"] Lemma ent_apart : forall i j, (i < j)%nat -> (j < 8)%nat ->
  apart (fst (nth i ents (0,0))) (snd (nth i ents (0,0))) (fst (nth j ents (0,0))) (snd (nth j ents (0,0))).
Proof.
  intros i j IJ J8.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try (exfalso; lia); cbn [nth ents fst snd]; unfold apart.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536) D. destruct D as [D|D]; [right| left]; exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. destruct D as [D|D]; [right| left]; exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. destruct D as [D|D]; [right| left]; exact D.
  - pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. destruct D as [D|D]; [right| left]; exact D.
Qed.

#[using="HP"] Lemma space_facts : 4096 * V 208%nat <= 4096 * V 208%nat + -4096 * V 209%nat + 65536
  /\ 4096 * V 208%nat + -4096 * V 209%nat + 65536 + (K_SPACE + 4096) <= 4096 * V 208%nat + 137439023104
  /\ (4096 * V 208%nat + -4096 * V 209%nat + 65536) mod 65536 = 0.
Proof.
  pf V HP (PVar 208 4295491576 34326181871) P208. pf V HP (PVar 209 0 15) P209.
  pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) PR.
  change 65535 with (Z.ones 16) in PR. rewrite Z.land_ones in PR by lia. change (2^16) with 65536 in PR. unfold two64 in PR. change (2^64) with 18446744073709551616 in PR.
  split; [lia|]. split; [lia|]. clear - P208 P209 PR. Z.div_mod_to_equations. lia.
Qed.

#[using="HP CEIL"] Lemma region_of_ent : forall b n b' n', ent_ok b n -> b <= b' -> b' + n' <= b + n -> 0 < n' -> b' mod 4096 = 0 -> region_ok (b', n').
Proof.
  intros b n b' n' (E0 & E1 & E2 & E3) B1 B2 N0 M. destruct sp_digits as (S0 & S6 & S10 & S344 & _).
  unfold region_ok. cbn [fst snd]. split; [| split; [lia| exact M]].
  destruct E1 as [E1|E1]; [left; lia|]. destruct E2 as [E2|E2]; [right; left; lia| right; right; lia].
Qed.

#[using="HP CEIL"] Theorem alayout_ok_of : alayout_ok (AL_of V).
Proof.
  destruct sp_digits as (S0 & S6 & S10 & S344 & SR). destruct space_facts as (SF1 & SF2 & SF3).
  pose proof ent_208 as E208. pose proof ent_226 as E226. pose proof ent_227 as E227. pose proof ent_228 as E228.
  pose proof ent_310 as E310. pose proof ent_377 as E377. pose proof ent_453 as E453. pose proof ent_454 as E454.
  assert (M4 : forall x, (4096 * x) mod 4096 = 0) by (intros x; rewrite Z.mul_comm; apply Z.mod_mul; lia).
  unfold alayout_ok. split; [| split; [| split; [| split; [| split]]]].
  - unfold al_regions, AL_of. cbn [al_space al_parr al_thread al_fsb al_depot al_dtls at_ctx at_thr DN0 SS0].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (region_of_ent _ _ _ _ E208); [exact SF1| exact SF2| lia|]. clear - SF3. Z.div_mod_to_equations. lia.
    + apply (region_of_ent _ _ _ _ E226); [lia| lia| lia| apply M4].
    + apply (region_of_ent _ _ _ _ E228); [lia| lia| lia| apply M4].
    + apply (region_of_ent _ _ _ _ E227); [lia| lia| lia| apply M4].
    + apply (region_of_ent _ _ _ _ E377); [lia| lia| lia| apply M4].
    + apply (region_of_ent _ _ _ _ E453); [lia| lia| lia| apply M4].
    + apply (region_of_ent _ _ _ _ E454); [lia| lia| lia| apply M4].
    + apply (region_of_ent _ _ _ _ E310); [lia| lia| lia| apply M4].
  - intros i j IJ J8. pose proof (ent_apart i j IJ J8) as A. revert A.
    unfold al_regions, AL_of. cbn [al_space al_parr al_thread al_fsb al_depot al_dtls at_ctx at_thr DN0 SS0].
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try (exfalso; lia);
      cbn [nth ents fst snd]; unfold apart; clear - SF1 SF2; intros A; lia.
  - exact SF3.
  - unfold thread_layout_ok, AL_of, top_of. cbn [al_thread at_ctx at_thr at_top at_bottom].
    destruct E228 as (A0 & A1 & A2 & A3). destruct E227 as (B0 & B1 & B2 & B3).
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536) D.
    pf V HP (PVar 228 1545 34359736304) P228.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    split; [split; [| lia]|].
    { right. destruct A2 as [A2|A2]; [left; lia| right; lia]. }
    split; [lia|]. split; [split; [| lia]|].
    { destruct B1 as [B1|B1]; [left; lia|]. destruct B2 as [B2|B2]; [right; left; lia| right; right; lia]. }
    split; [lia|]. split; [destruct D as [D|D]; [right| left]; lia|]. split; [apply M4|]. split; [apply M4|].
    split; [lia|]. split; [lia|]. split; [change (2^47) with 140737488355328; lia|].
    clear - S0. Z.div_mod_to_equations. lia.
  - unfold dl_ok, AL_of. cbn [al_depot DN0 SS0 SWIN].
    destruct E453 as (A0 & A1 & A2 & A3). destruct E454 as (B0 & B1 & B2 & B3).
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608) D.
    pf V HP (PVar 453 1545 34359736064) P453. pf V HP (PVar 454 1545 34359734272) P454.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    change (2^20) with 1048576.
    split; [split; [| lia]|].
    { destruct A2 as [A2|A2]; [left; lia| right; lia]. }
    split; [lia|]. split; [apply M4|]. split; [split; [| lia]|].
    { destruct B2 as [B2|B2]; [left; lia| right; lia]. }
    split; [lia|]. split; [apply M4|]. split; [lia|]. split; [reflexivity|]. exact D.
  - cbn. lia.
Qed.
End Lay.
