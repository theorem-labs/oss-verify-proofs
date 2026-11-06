(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Bytes.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require F_memmove.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit.
Import ListNotations.
Open Scope Z_scope.

Notation slice := F_memmove.slice.
Notation mm_result := F_memmove.mm_result.
Notation usF := F_memmove.usF.
Notation usB := F_memmove.usB.

Definition imemmove_entry : Z := 0x69940.

Definition imemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a7 t3 t4 t5 t6 : word) (D S n U : Z) (us : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1' a2' a3 a4 a5 a6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' U (mm_result us (Z.to_nat (S - U)) (Z.to_nat (D - U)) (Z.to_nat n)).

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n U : Z) (us : list byte).
  Notation L := (Z.of_nat (length us)).
  Notation W := [(D, D + n)].
  Hypothesis ARR : u8arr asegs m U us.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis HS : U <= S /\ S + n <= U + L.
  Hypothesis HD : U <= D /\ D + n <= U + L.
  Hypothesis Hn : 0 <= n < 2^62.
  Hypothesis H64 : S < 2^64 /\ D < 2^64.

  Definition sof := Z.to_nat (S - U).
  Definition dof := Z.to_nat (D - U).
  Definition nn := Z.to_nat n.

  Notation POST := (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a7 t3 t4 t5 t6 D S n U us m).
  Notation STT pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz pc) fc None mm (seg_rom asegs)).

  Definition INV (m1 : mem) (us1 : list byte) : Prop :=
    u8arr asegs m1 U us1 /\ mem_inv asegs m1 /\ munch W m m1 /\ wmono asegs m m1.

  #[using="m ARR HS HD Hn"] Lemma bounds : 0 <= U /\ U + L <= 2^64 /\ Z.of_nat sof = S - U /\ Z.of_nat dof = D - U /\ Z.of_nat nn = n
                 /\ (sof + nn <= length us)%nat /\ (dof + nn <= length us)%nat.
  Proof. pose proof (u8arr_bound _ _ _ _ ARR). unfold sof, dof, nn. lia. Qed.

  Ltac open_inv H := destruct H as (AR & MI & MU & WM).

  #[using="n us Hn"] Lemma u8arr_read1 : forall m1 us1 (o : nat) b a, u8arr asegs m1 U us1 -> nth_error us1 o = Some b ->
    a = wa (U + Z.of_nat o) -> ov_read_bytes asegs m1 a 1 = Some [b].
  Proof.
    intros m1 us1 o b a H Hnth ->. eapply (u8arr_read asegs m1 U us1 (Z.of_nat o)); [exact H| rewrite Nat2Z.id; exact Hnth| lia| reflexivity].
  Qed.

  #[using="S ARR HS HD Hn"] Lemma mm_store : forall m1 us1 (off : nat) xs a,
    INV m1 us1 -> length us1 = length us -> (off + length xs <= length us)%nat ->
    (D <= U + Z.of_nat off /\ U + Z.of_nat off + Z.of_nat (length xs) <= D + n) ->
    a = wa (U + Z.of_nat off) ->
    store_ok asegs m1 a (length xs) = true /\
    INV (write_to_mem m1 a xs) (upd_bytes us1 off xs).
  Proof.
    intros m1 us1 off xs a I Hl Ho Hin Ha; open_inv I. pose proof bounds as B.
    split.
    { eapply (u8arr_store_ok_n asegs m1 U us1 (Z.of_nat off) (length xs) a AR); [lia| rewrite Hl; lia | rewrite Ha; f_equal; lia]. }
    subst a. split; [|split; [|split]].
    - rewrite <- (Nat2Z.id off) at 2. apply (u8arr_write_bytes asegs m1 U us1 (Z.of_nat off) xs AR); [lia|]. rewrite Nat2Z.id, Hl. lia.
    - apply mem_inv_store; [exact MI|]. eapply (u8arr_store_ok_n asegs m1 U us1 (Z.of_nat off)); [exact AR| lia| rewrite Hl; lia| reflexivity].
    - apply munch_write; [exact MU| lia| lia|]. cbn [inside]. left. lia.
    - apply wmono_write. exact WM.
  Qed.

  Ltac mst_fin I2 xs bytes_tac :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs0) _) =>
      replace bs0 with xs by bytes_tac;
      repeat match goal with
      | H : store_ok _ m1 _ _ = true |- _ => clear H
      | H : ov_read_bytes _ m1 _ _ = Some _ |- _ => clear H
      | H : u8arr _ m1 _ _ |- _ => clear H
      | H : mem_inv _ m1 |- _ => clear H
      | H : munch _ _ m1 |- _ => clear H
      | H : wmono _ _ m1 |- _ => clear H
      | H : INV m1 _ |- _ => clear H
      | H : length _ = length us |- _ => clear H
      end;
      let m' := fresh "m" in remember (write_to_mem m1 a xs) as m' eqn:E; clear E; try clear m1;
      pose proof I2 as I2'; destruct I2' as (AR & MI & MU & WM)
    end.
  Ltac by_byte := symmetry; apply le1_zxb.

  #[using="Type"] Lemma mm_ret : forall m1 x11 x12 x13 x14 x15 x16,
    INV m1 (mm_result us sof dof nn) ->
    evt asegs POST (STT 0x69994 m1 x11 x12 x13 x14 x15 x16).
  Proof.
    intros m1 x11 x12 x13 x14 x15 x16 I; open_inv I.
    zstep. finish.
  Qed.

  #[using="ARR HS HD Hn"] Lemma mm_fwd : forall (j k : nat) m1 x14 x15 x16,
    (nn - k = j)%nat -> (k < nn)%nat -> (dof < sof)%nat ->
    INV m1 (usF us sof dof k) ->
    evt asegs POST (STT 0x69950 m1 (wz (S + Z.of_nat k)) (wz (D + n)) (wz (D + Z.of_nat k)) x14 x15 x16).
  Proof.
    induction j as [|j IH]; intros k m1 x14 x15 x16 Hj Hk Hds I; [lia|]. pose proof bounds as B.
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usF us sof dof k) = length us) by (apply F_memmove.usF_length; lia).
    destruct (nth_error us (sof + k)) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }
    pose proof (u8arr_read1 m1 (usF us sof dof k) (sof + k) b (wz (S + Z.of_nat k)) AR
                  ltac:(rewrite F_memmove.usF_nth by lia; exact Hb) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep.
    destruct (mm_store m1 (usF us sof dof k) (dof + k) [b] (wz (D + Z.of_nat k)) I LEN1 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    cbn [length] in SOK. zstep. mst_fin I2 [b] by_byte.
    rewrite (F_memmove.usF_step1 us sof dof k b) in I2; [| lia | lia | lia | exact Hb].
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - replace (D + Z.of_nat k + 1) with (D + Z.of_nat (k + 1)) by lia.
      replace (S + Z.of_nat k + 1) with (S + Z.of_nat (k + 1)) by lia.
      apply (IH (k + 1)%nat); try lia. exact I2.
    - assert (k + 1 = nn)%nat by lia.
      zstep. apply mm_ret. rewrite <- F_memmove.usF_n. replace nn with (k + 1)%nat. exact I2.
  Qed.

  #[using="ARR HS HD Hn"] Lemma mm_bwd : forall (r : nat) m1 x14 x15 x16,
    (1 <= r)%nat -> (r <= nn)%nat -> (sof < dof)%nat -> INV m1 (usB us sof dof nn r) ->
    evt asegs POST (STT 0x69978 m1 (wz S) (wz 1) (wz (Z.of_nat r - 1)) x14 x15 x16).
  Proof.
    induction r as [|r IH]; intros m1 x14 x15 x16 Hr1 Hr Hsd I; [lia|]. pose proof bounds as B.
    pose proof I as I'; open_inv I'.
    assert (LEN1 : length (usB us sof dof nn (Datatypes.S r)) = length us) by (apply F_memmove.usB_length; lia).
    destruct (nth_error us (sof + r)) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }
    pose proof (u8arr_read1 m1 (usB us sof dof nn (Datatypes.S r)) (sof + r) b (wz (S + (Z.of_nat (Datatypes.S r) - 1))) AR
                  ltac:(rewrite F_memmove.usB_nth by lia; exact Hb) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep.
    cbv beta. zstep. zstep. zstep.
    destruct (mm_store m1 (usB us sof dof nn (Datatypes.S r)) (dof + r) [b] (wz (D + (Z.of_nat (Datatypes.S r) - 1))) I LEN1 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(unfold wa; f_equal; lia)) as [SOK I2].
    cbn [length] in SOK. zstep. mst_fin I2 [b] by_byte.
    replace (dof + r)%nat with (dof + (Datatypes.S r - 1))%nat in I2 by lia.
    rewrite (F_memmove.usB_step1 us sof dof nn (Datatypes.S r) b) in I2; [| lia | lia | lia | lia | lia | replace (sof + (Datatypes.S r - 1))%nat with (sof + r)%nat by lia; exact Hb].
    replace (Datatypes.S r - 1)%nat with r in I2 by lia.
    zstep. if_cases K; zify_cond K.
    - replace (Z.of_nat (Datatypes.S r) - 1 + -1) with (Z.of_nat r - 1) by lia.
      apply IH; try lia. exact I2.
    - assert (r = 0)%nat by lia. subst r.
      apply mm_ret. rewrite <- F_memmove.usB_0. exact I2.
  Qed.

  #[using="ARR MI0"] Lemma inv0 : INV m us.
  Proof. split; [exact ARR|]. split; [exact MI0|]. split; [apply munch_refl| apply wmono_refl]. Qed.

  #[using="ARR MI0 HS HD Hn H64"] Lemma imemmove_body : forall a1 a2 a3 a4 a5 a6, a1 = wz S -> a2 = wz n ->
    evt asegs POST (STT imemmove_entry m a1 a2 a3 a4 a5 a6).
  Proof.
    intros a1 a2 a3 a4 a5 a6 -> ->. unfold imemmove_entry. pose proof bounds as B. pose proof inv0 as I0.
    zstep. if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia.
    -
      zstep. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by lia.
      +
        apply mm_ret. unfold mm_result. replace sof with dof by (unfold sof, dof; f_equal; lia).
        rewrite F_memmove.upd_bytes_slice_same by lia. exact I0.
      + zstep. if_cases K3; zify_cond K3.
        * apply mm_ret. replace nn with 0%nat by (unfold nn; lia). rewrite <- F_memmove.usF_n, F_memmove.usF_0. exact I0.
        * zstep. zstep.
          replace (n + -1) with (Z.of_nat nn - 1) by lia.
          apply mm_bwd; try lia. rewrite F_memmove.usB_n. exact I0.
    - zstep. if_cases K3; zify_cond K3.
      + apply mm_ret. replace nn with 0%nat by (unfold nn; lia). rewrite <- F_memmove.usF_n, F_memmove.usF_0. exact I0.
      + zstep. zstep.
        pose proof (mm_fwd nn 0%nat m a4 a5 a6 ltac:(lia) ltac:(lia) ltac:(unfold sof, dof; lia)) as HF.
        cbn [Z.of_nat] in HF. rewrite !Z.add_0_r in HF. apply HF. rewrite F_memmove.usF_0. exact I0.
  Qed.
End Proofs.

Lemma imemmove_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n U : Z) (us : list byte),
  u8arr asegs m U us -> mem_inv asegs m ->
  (U <= S /\ S + n <= U + Z.of_nat (length us)) -> (U <= D /\ D + n <= U + Z.of_nat (length us)) ->
  0 <= n < 2^62 -> S < 2^64 /\ D < 2^64 ->
  evt asegs (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a7 t3 t4 t5 t6 D S n U us m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz imemmove_entry) fc None m (seg_rom asegs)).
Proof. intros. eapply imemmove_body; try eassumption; reflexivity. Qed.
