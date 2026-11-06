(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import MState Mem Exec.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section RunSound.
Variable segs : list Segment.
Variable stop : w64 -> bool.
Variable rho : valuation.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition in_wr (M : mem) (z : Z) : Prop :=
  exists t rg, mget M t = Some rg /\ rg_wr rg = true /\ rbase rho t rg <= z < rbase rho t rg + to_Z (rg_size rg).

Definition mem_frame (M : mem) (m m' : word -> option byte) : Prop :=
  (forall z, 0 <= z < 2 ^ 64 -> ~ in_wr M z -> m' (wa z) = m (wa z))
  /\ (forall x, wview segs m x <> None -> wview segs m' x <> None).

Lemma mem_frame_refl (M : mem) (m : word -> option byte) : mem_frame M m m.
Proof. split; auto. Qed.

Lemma rbase_same_dir (t : int) (rg rg' : region) : same_dir rg rg' -> rbase rho t rg' = rbase rho t rg.
Proof. intros (E & _). unfold rbase. rewrite E. reflexivity. Qed.

Lemma in_wr_same_dirs (M M' : mem) (z : Z) : same_dirs M M' -> in_wr M' z -> in_wr M z.
Proof.
  intros Hd (t & rg' & Eg & Ew & Hz). specialize (Hd t). rewrite Eg in Hd. destruct (mget M t) as [rg|] eqn:E; [|contradiction].
  exists t, rg. split; [exact E|]. pose proof (rbase_same_dir t rg rg' Hd) as Eb. destruct Hd as (_ & Es & _ & Ewr & _).
  rewrite Ewr in Ew. rewrite Es, Eb in Hz. auto.
Qed.

Lemma mem_frame_trans (M M' : mem) (m1 m2 m3 : word -> option byte) :
  same_dirs M M' -> mem_frame M m1 m2 -> mem_frame M' m2 m3 -> mem_frame M m1 m3.
Proof.
  intros Hd [F1 W1] [F2 W2]. split.
  - intros z Hz Hn. rewrite F2; [apply F1; assumption | assumption |]. intros X. apply Hn. exact (in_wr_same_dirs M M' z Hd X).
  - intros x Hx. apply W2, W1, Hx.
Qed.

(* [comment removed for export] *)
Lemma step_frame (S S' : sstate) (ms ms' : machine_state) :
  R segs rho S ms -> mem_step rho (s_mem S) (ms_mem ms) (ms_mem ms') -> mem_frame (s_mem S) (ms_mem ms) (ms_mem ms').
Proof.
  intros HR [->|(t & rg & off & bs & Eg & Ew & -> & Hin)]; [apply mem_frame_refl|].
  destruct HR as (_ & _ & _ & _ & [HRr _]). destruct (HRr t rg Eg) as (HB0 & HB1 & _).
  pose proof (to_Z_bounded off) as Bo. split.
  - intros z Hz Hn. rewrite write_to_mem_spec by (unfold two63 in *; lia). rewrite wa_unsigned by exact Hz.
    destruct ((rbase rho t rg + to_Z off <=? z) && (z <? rbase rho t rg + to_Z off + Z.of_nat (length bs))) eqn:E; [|reflexivity].
    exfalso. apply Hn. exists t, rg. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. split; [exact Eg|]. split; [exact Ew | lia].
  - intros x Hx. apply wview_write_mono. exact Hx.
Qed.

Definition res_state (r : rres) : sstate := match r with RRun X => X | RStop X => X | RStuck _ X => X end.

(* [comment removed for export] *)
Definition run_post (S : sstate) (ms : machine_state) (S' : sstate) : Prop :=
  exists ms', msteps segs ms ms' /\ R segs rho S' ms'
              /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
              /\ same_dirs (s_mem S) (s_mem S') /\ mem_frame (s_mem S) (ms_mem ms) (ms_mem ms').

Lemma run_post_refl (S : sstate) (ms : machine_state) : R segs rho S ms -> run_post S ms S.
Proof.
  intros HR. exists ms. split; [apply msteps_refl|]. split; [exact HR|]. repeat (split; [reflexivity|]).
  split; [apply same_dirs_refl | apply mem_frame_refl].
Qed.

Lemma run_post_trans (S1 S2 S3 : sstate) (ms1 : machine_state) :
  run_post S1 ms1 S2 -> (forall ms2, R segs rho S2 ms2 -> run_post S2 ms2 S3) -> run_post S1 ms1 S3.
Proof.
  intros (ms2 & M1 & R2 & F1 & C1 & O1 & D1 & Fr1) K. destruct (K ms2 R2) as (ms3 & M2 & R3 & F2 & C2 & O2 & D2 & Fr2).
  exists ms3. split; [eapply msteps_trans; eassumption|]. split; [exact R3|].
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [eapply same_dirs_trans; eassumption | eapply mem_frame_trans; eassumption].
Qed.

(* [comment removed for export] *)
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

Theorem hx_step1_sound (ic ic' : icache) (S : sstate) (r : rres) (ms : machine_state) :
  ic_ok segs ic -> R segs rho S ms -> hx_step1 segs stop ic S = (ic', r) -> ic_ok segs ic' /\ run_post S ms (res_state r).
Proof.
  intros Hic HR H. unfold hx_step1 in H. destruct (stop (s_pc S)).
  - injection H as <- <-. split; [exact Hic | apply run_post_refl; exact HR].
  - destruct (hx_step segs ic S) as [ic1 [S1|c S1]] eqn:Es; injection H as <- <-.
    + destruct (hx_step_sound segs rho ic ic1 S S1 ms Hic HR Es) as (Hic1 & ms' & Hst & HR' & Hf & Hc & Ho & Hm & _).
      split; [exact Hic1|]. exists ms'. split; [apply msteps_one; exact Hst|]. split; [exact HR'|].
      repeat (split; [assumption|]). split; [exact (mem_step_dirs S S1 ic ic1 Es) | exact (step_frame S S1 ms ms' HR Hm)].
    + (* [comment removed for export] *)
      assert (S1 = S).
      { unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|]; [|injection Es as _ _ <-; reflexivity].
        injection Es as _ Es. destruct d; cbn [hx_exec] in Es; try discriminate;
          repeat match type of Es with
                 | (match ?x with _ => _ end) = _ => destruct x; try discriminate
                 | (if ?x then _ else _) = _ => destruct x; try discriminate
                 end; try discriminate; injection Es as _ <-; reflexivity. }
      subst S1. split; [|apply run_post_refl; exact HR].
      unfold hx_step in Es. destruct (hx_fetch segs ic (s_pc S)) as [[d ic2]|] eqn:Ef; [|injection Es as <- _; exact Hic].
      injection Es as <- _. exact (proj1 (hx_fetch_sound segs ic ic2 (s_pc S) d Hic Ef)).
Qed.

Theorem hx_run_sound (n : nat) : forall (ic ic' : icache) (S : sstate) (r : rres) (ms : machine_state),
  ic_ok segs ic -> R segs rho S ms -> hx_run segs stop n ic S = (ic', r) -> ic_ok segs ic' /\ run_post S ms (res_state r).
Proof.
  induction n as [|n IH]; intros ic ic' S r ms Hic HR H; cbn [hx_run] in H.
  - exact (hx_step1_sound ic ic' S r ms Hic HR H).
  - destruct (hx_run segs stop n ic S) as [ic1 r1] eqn:E1. destruct (IH ic ic1 S r1 ms Hic HR E1) as [Hic1 P1].
    destruct r1 as [S1|S1|c S1]; try (injection H as <- <-; split; [exact Hic1 | exact P1]).
    split.
    + destruct P1 as (ms1 & _ & R1 & _). exact (proj1 (IH ic1 ic' S1 r ms1 Hic1 R1 H)).
    + apply (run_post_trans S (res_state (RRun S1)) (res_state r) ms P1). intros ms2 R2. exact (proj2 (IH ic1 ic' S1 r ms2 Hic1 R2 H)).
Qed.

(* [comment removed for export] *)
Corollary hx_run_evt (n : nat) (ic ic' : icache) (S : sstate) (r : rres) (ms : machine_state) :
  ic_ok segs ic -> R segs rho S ms -> hx_run segs stop n ic S = (ic', r) ->
  evt segs (fun ms' => R segs rho (res_state r) ms' /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
                       /\ mem_frame (s_mem S) (ms_mem ms) (ms_mem ms')) ms.
Proof.
  intros Hic HR H. destruct (proj2 (hx_run_sound n ic ic' S r ms Hic HR H)) as (ms' & Hm & HR' & Hf & Hc & Ho & _ & Hfr).
  exists ms'. split; [exact Hm|]. auto.
Qed.

End RunSound.
