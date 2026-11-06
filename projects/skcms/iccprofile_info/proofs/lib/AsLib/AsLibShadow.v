(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymCall.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.

Definition SB : Z := 0x7fff8000.

Section WithSegs.
Variable segs : list Segment.

Definition shz (mem : word -> option byte) (a : Z) (m : Z) : Prop :=
  (a mod 8 = 0)%Z /\ forall j, (0 <= j < m)%Z -> mem (Z_to_bv 64 (SB + a / 8 + j)) = Some (Z_to_bv 8 0).

Definition shbyte (mem : word -> option byte) (a : Z) (v : Z) : Prop :=
  mem (Z_to_bv 64 (SB + a / 8)) = Some (Z_to_bv 8 v).

Definition shdata (mem : word -> option byte) (d n : Z) : Prop :=
  (d mod 8 = 0)%Z /\
  forall g, (d / 8 <= g)%Z -> (8 * g < d + n)%Z ->
    mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 (shad_byte (8 * g) d n)).

(* [comment removed for export] *)
Definition sbcell (got cellp : Z) (mem : word -> option byte) : Prop :=
  cell64 segs mem got (Z_to_bv 64 cellp) /\ cell64 segs mem cellp (Z_to_bv 64 SB).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_srl3 : forall x : word, bv_unsigned (alu64 ALU_SRL x (Z_to_bv 64 3)) = (bv_unsigned x / 8)%Z.
Proof. intros x. rewrite u_srl64, u_lit64. reflexivity. Qed.

Lemma edenot_srl3 : forall E e, bv_unsigned (edenot E (EAlu ALU_SRL e (ELit 3))) = (bv_unsigned (edenot E e) / 8)%Z.
Proof. intros E e. cbn [edenot]. apply u_srl3. Qed.

(* [comment removed for export] *)
Lemma kzero_shadow_intro : forall E mem (e : expr) (p : word) (k m : Z),
  edenot E e = p ->
  (0 <= k)%Z -> (0 <= m)%Z -> (bv_unsigned p / 8 + k + m < 2 ^ 61)%Z ->
  (forall j, (k <= j < k + m)%Z -> mem (Z_to_bv 64 (SB + bv_unsigned p / 8 + j)) = Some (Z_to_bv 8 0)) ->
  kentry_ok segs E mem (KZero (SA (EAlu ALU_SRL e (ELit 3)) (SB + k)) (ELit m)).
Proof.
  intros E mem e p k m He Hk Hm Hb Hz. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off].
  pose proof (Z.div_pos (bv_unsigned p) 8 ltac:(pose proof (u64_range p); lia) ltac:(lia)).
  rewrite edenot_srl3, He. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite (Z.mod_small m) by lia.
  unfold SB. split; [lia|].
  intros i Hi. replace (bv_unsigned p / 8 + (0x7fff8000 + k) + i)%Z with (0x7fff8000 + bv_unsigned p / 8 + (k + i))%Z by lia.
  apply Hz. lia.
Qed.

Lemma kzero_shz_intro : forall E mem (e : expr) (p : word) (m : Z),
  edenot E e = p -> shz mem (bv_unsigned p) m -> (0 <= m <= 2 ^ 47)%Z -> (bv_unsigned p < 2 ^ 47)%Z ->
  kentry_ok segs E mem (KZero (SA (EAlu ALU_SRL e (ELit 3)) SB) (ELit m)).
Proof.
  intros E mem e p m He [Hal Hz] Hm Hp.
  replace SB with (SB + 0)%Z at 1 by lia.
  eapply kzero_shadow_intro; [exact He | lia | lia | |].
  - assert (bv_unsigned p / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia.
  - intros j Hj. apply Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma kshad_intro : forall E mem (ed en : expr) (d : word) (n : Z),
  edenot E ed = d -> bv_unsigned (edenot E en) = n ->
  (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
  shdata mem (bv_unsigned d) n ->
  kentry_ok segs E mem (KShad ed en SB).
Proof.
  intros E mem ed en d n Hd Hn Hn0 Hnw [Hal Hcell]. cbn [kentry_ok].
  unfold flat, estart, elenZ. cbn [a_base a_off]. rewrite Hd, Hn.
  pose proof (u64_range d). unfold SB in *.
  split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros g Hg1 Hg2. apply Hcell; assumption.
Qed.


(* [comment removed for export] *)
Lemma kwr_shadow_intro : forall E mem (e : expr) (p : word) (k n : Z),
  edenot E e = p ->
  (0 <= k)%Z -> (0 < n)%Z -> (bv_unsigned p / 8 + k + n < 2 ^ 61)%Z ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 (SB + bv_unsigned p / 8 + k)) (Z.to_nat n) = true ->
  kentry_ok segs E mem (KWr (SA (EAlu ALU_SRL e (ELit 3)) (SB + k)) n).
Proof.
  intros E mem e p k n He Hk Hn Hb Hst. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off].
  pose proof (Z.div_pos (bv_unsigned p) 8 ltac:(pose proof (u64_range p); lia) ltac:(lia)) as Hp0.
  rewrite edenot_srl3, He. unfold SB in *.
  split; [lia|]. intros d m Hd Hm. destruct m as [|m']; [reflexivity|].
  set (base := (bv_unsigned p / 8 + (2147450880 + k))%Z).
  assert (U1 : bv_unsigned (Z_to_bv 64 (2147450880 + bv_unsigned p / 8 + k)) = base) by (subst base; rewrite u_small by lia; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (base + d)) = (base + d)%Z) by (subst base; apply u_small; lia).
  apply store_ok_of_all; [rewrite U2; subst base; lia|]. intros x Hx. rewrite U2 in Hx.
  apply (store_ok_all segs mem (Z.to_nat n) (Z_to_bv 64 (2147450880 + bv_unsigned p / 8 + k)) ltac:(rewrite U1, Z2Nat.id by lia; subst base; lia) Hst).
  rewrite Z2Nat.id by lia. rewrite U1. lia.
Qed.

End WithSegs.
