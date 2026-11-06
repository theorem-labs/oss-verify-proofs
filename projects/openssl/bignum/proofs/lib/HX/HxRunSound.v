(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section RunSound.
Variable segs : list Segment.
Variable stop : w64 -> bool.
Variable rho : valuation.

Definition same_dirs (M M' : mem) : Prop :=
  forall t, match mget M t, mget M' t with
            | Some rg, Some rg' => same_dir rg rg'
            | None, None => True
            | _, _ => False
            end.

Lemma same_dir_refl (rg : region) : same_dir rg rg.
Proof. repeat split. Qed.

Lemma same_dir_trans (a b c : region) : same_dir a b -> same_dir b c -> same_dir a c.
Proof. intros (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). repeat split; congruence. Qed.

Lemma same_dirs_refl (M : mem) : same_dirs M M.
Proof. intros t. destruct (mget M t); [apply same_dir_refl | exact I]. Qed.

Lemma same_dirs_trans (M1 M2 M3 : mem) : same_dirs M1 M2 -> same_dirs M2 M3 -> same_dirs M1 M3.
Proof.
  intros H1 H2 t. specialize (H1 t). specialize (H2 t).
  destruct (mget M1 t), (mget M2 t), (mget M3 t); try contradiction; try exact I. eapply same_dir_trans; eassumption.
Qed.

Definition in_wr (M : mem) (z : Z) : Prop :=
  exists t rg, mget M t = Some rg /\ rg_wr rg = true /\ rbase rho t rg <= z < rbase rho t rg + to_Z (rg_size rg).

Definition mem_frame (M : mem) (m m' : word -> option byte) : Prop :=
  (forall z, 0 <= z < 2 ^ 64 -> ~ in_wr M z -> m' (wa z) = m (wa z))
  /\ (forall x, wview segs m x <> None -> wview segs m' x <> None).

Lemma rbase_same_dir (t : int) (rg rg' : region) : same_dir rg rg' -> rbase rho t rg' = rbase rho t rg.
Proof. intros (E & _). unfold rbase. rewrite E. reflexivity. Qed.

Definition res_state (r : rres) : sstate := match r with RRun X => X | RStop X => X | RStuck _ X => X end.

Definition run_post (S : sstate) (ms : machine_state) (S' : sstate) : Prop :=
  exists ms', msteps segs ms ms' /\ R segs rho S' ms'
              /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
              /\ same_dirs (s_mem S) (s_mem S') /\ mem_frame (s_mem S) (ms_mem ms) (ms_mem ms').

Lemma mem_step_dirs (S S' : sstate) (ic ic' : icache) : hx_step segs ic S = (ic', SNext S') -> same_dirs (s_mem S) (s_mem S').
Proof.
  intros H. unfold hx_step in H. destruct (hx_fetch segs ic (s_pc S)) as [[d ic1]|]; [|discriminate]. injection H as _ H.
  assert (Hst : forall a sz v M', hx_store segs (s_mem S) (s_abs S) a sz v = Some M' -> same_dirs (s_mem S) M').
  { intros a sz v M' Hs. unfold hx_store in Hs. destruct (resolve (s_mem S) (s_abs S) a (nbytes sz)) as [[[t rg] off]|] eqn:Er; [|discriminate].
    destruct (rg_wr rg); [|discriminate]. destruct (_ <=? 8)%uint63; [|discriminate]. injection Hs as <-.
    assert (Eg : mget (s_mem S) t = Some rg).
    { unfold resolve in Er. destruct a as [w|t' o| |]; [| |discriminate|discriminate].
      - destruct (wh w); [discriminate|]. destruct (abs_find _ _ _) as [[t' off']|]; [|discriminate].
        destruct (mget (s_mem S) t') as [rg'|] eqn:E; [|discriminate]. destruct (rg_abs rg'); [|discriminate].
        destruct (_ && _); [|discriminate]. injection Er as <- <- <-. exact E.
      - destruct (wh o); [discriminate|]. destruct (mget (s_mem S) t') as [rg'|] eqn:E; [|discriminate].
        destruct (rg_abs rg'); [discriminate|]. destruct (in_rg _ _ _); [|discriminate]. injection Er as <- <- <-. exact E. }
    intros t2. rewrite (mget_mset (s_mem S) t t2 _ (mget_lt _ _ _ Eg)).
    destruct (Z.eqb_spec (to_Z t) (to_Z t2)) as [E|E].
    - apply to_Z_inj in E. subst t2. rewrite Eg. apply same_dir_wr_cell.
    - destruct (mget (s_mem S) t2); [apply same_dir_refl | exact I]. }
  destruct d; cbn [hx_exec] in H; try discriminate;
    repeat match type of H with
           | (match ?x with _ => _ end) = _ => destruct x eqn:?; try discriminate
           | (if ?x then _ else _) = _ => destruct x eqn:?; try discriminate
           end;
    try (injection H as <-; cbn [s_mem with_reg_pc with_pc with_mem_pc with_all]; try apply same_dirs_refl; eapply Hst; eassumption).
Qed.

End RunSound.
