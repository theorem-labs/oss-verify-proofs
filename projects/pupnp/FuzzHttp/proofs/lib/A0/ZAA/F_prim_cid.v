(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim ATacA.
Import ListNotations.
Open Scope Z_scope.

Definition smear (x : Z) : Z :=
  let x1 := Z.lor x (Z.shiftr x 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in Z.lor x5 (Z.shiftr x5 32).
Fixpoint check_from (f : Z -> bool) (n : nat) (x : Z) : bool :=
  match n with O => true | S n' => f x && check_from f n' (x + 1) end.
Lemma check_from_ok : forall f n x, check_from f n x = true -> forall y, x <= y < x + Z.of_nat n -> f y = true.
Proof.
  induction n as [|n IH]; intros x H y Hy; cbn in H; [lia|].
  apply andb_true_iff in H. destruct H as [H1 H2]. destruct (Z.eq_dec y x) as [->|]; [exact H1|]. apply (IH (x + 1) H2). lia.
Qed.
Lemma smear_pow : forall l x, 9 <= l <= 16 -> 2 ^ l <= x < 2 ^ (l + 1) -> smear x = 2 ^ (l + 1) - 1.
Proof.
  intros l x Hl Hx.
  assert (E : l = 9 \/ l = 10 \/ l = 11 \/ l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16) by lia.
  destruct E as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
    lazymatch goal with |- smear _ = 2 ^ (?L + 1) - 1 =>
      apply Z.eqb_eq; refine (check_from_ok (fun y => smear y =? 2 ^ (L + 1) - 1) (Z.to_nat (2 ^ L)) (2 ^ L) _ x _);
      [vm_compute; reflexivity| lia] end.
Qed.

Definition cid_code (l size : Z) : Z :=
  Z.lor (2 * l) (Z.land (Z.shiftr size (l - 1)) 1) + Z.b2z (0 <? Z.land size (2 ^ (l - 1) - 1)) + -2.

Section CID.
  Context {HC : HasCeiling}.
  Variables (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (size CB : Z) (m : mem) (s0 : word).

  Definition cid_post (v : Z) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x14 x15 x16 x17 x28,
      ms' = MS (mkR ra sp gp tp x5 x6 x7 (wz v) s1 (wz INSTANCE) (wz CB) x12 (wz 8) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
               F_ (wz 0x37e8c) fc None m (seg_rom asegs).

  #[using="Type"] Lemma cid_small : 1 <= size <= 512 ->
    evt asegs (cid_post ((size + 31) / 32))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz INSTANCE) (wz CB) (wz size) (wz 8) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x37d6c) fc None m (seg_rom asegs)).
  Proof.
    intros SZ.
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. cbn in K1. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2 SZ. clear. intros. cbn in K2. lia. }
    zstep. zstep. if_cases K3; zify_cond K3. { exfalso. revert K3 SZ. clear. intros. lia. }
    zstep. zstep. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. zstep.
    apply evt_done. unfold cid_post. repeat (lazymatch goal with |- ex _ => eexists end). reflexivity.
  Qed.

  #[using="Type"] Lemma cid_big : forall l, 513 <= size <= 65536 -> 9 <= l <= 16 -> 2 ^ l <= size < 2 ^ (l + 1) ->
    evt asegs (cid_post (cid_code l size))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz INSTANCE) (wz CB) (wz size) (wz 8) (wz size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x37d6c) fc None m (seg_rom asegs)).
  Proof.
    intros l SZ Hl HL.
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. cbn in K1. lia. }
    zstep. if_cases K2; zify_cond K2. { exfalso. revert K2 SZ. clear. intros. cbn in K2. lia. }
    zstep. zstep. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3 SZ. clear. intros. lia. }
    do 28 zstep.
    match goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.shiftr ?b 32))] => change (Z.lor a (Z.shiftr b 32)) with (smear size) end.
    rewrite (smear_pow l size) by lia.
    match goal with |- context [Z_to_bv 64 (Z.shiftr ?b 32)] => generalize (Z_to_bv 64 (Z.shiftr b 32)); intros jt1 end.
    assert (E : l = 9 \/ l = 10 \/ l = 11 \/ l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16) by lia.
    destruct E as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
      match goal with |- context [Z_to_bv 64 (2 ^ (?L + 1) - 1)] =>
        let v := eval vm_compute in (2 ^ (L + 1) - 1) in change (2 ^ (L + 1) - 1) with v;
        let lo := eval vm_compute in (2 ^ L) in change (2 ^ L) with lo in HL;
        let hi := eval vm_compute in (2 ^ (L + 1)) in change (2 ^ (L + 1)) with hi in HL end;
      do 27 zstep;
      apply evt_done; unfold cid_post, cid_code; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity.
  Qed.
End CID.
