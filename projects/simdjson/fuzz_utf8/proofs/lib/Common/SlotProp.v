(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec StoreOk AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MallocDefs MallocSpec MallocNodes2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Sem.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Definition slot_sem (vs : list Z) (M : word -> option byte) : Prop :=
    match vs with
    | [st; sd; nn; o; W; idx; p] =>
        enframe_post_g segs M idx nn sd st o
        /\ p = st + 16 * o
        /\ sd = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W)
        /\ ((w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48)
        /\ 16 <= sd < 2 ^ 31 /\ sd mod 16 = 0 /\ st mod 16 = 0
        /\ 16 + sd * idx <= st /\ st + sd < 2 ^ 64
        /\ 0 <= idx <= w_lastidx W /\ idx < 32 /\ sd * idx + 4096 <= 16 * 65536
        /\ 0 <= nn /\ nn + 16 * o + 4 <= sd
    | _ => False
    end.

  (* [comment removed for export] *)
  Definition slot_agree (M M' : word -> option byte) (st sd p nn : Z) : Prop :=
    forall x : word, (st - 4 <= bv_unsigned x < p \/ p + nn <= bv_unsigned x <= st + sd - 4) -> M' x = M x.

  Lemma u64_of_Z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z : word) = z.
  Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. exact Hz. Qed.


  Lemma slot_sem_frame : forall vs M M',
    match vs with
    | [st; sd; nn; o; W; idx; p] => slot_agree M M' st sd p nn
    | _ => True
    end ->
    slot_sem vs M -> slot_sem vs M'.
  Proof.
    intros vs M M' Hag Hs.
    destruct vs as [|st [|sd [|nn [|o [|W [|idx [|p [|]]]]]]]]; try exact Hs.
    cbn [slot_sem] in Hs |- *.
    destruct Hs as (EP & REST). split; [|exact REST].
    destruct REST as (Hp & Hsd & Hsc & [Hsd2a Hsd2b] & Hmod & Hst16 & Hsi & Hnw & [Hidx1 Hidx2] & Hi32 & Hq & Hn & Hfit).
    destruct EP as [Pp Pe PR Pq P4 P3 P2 Pz P5 P4' S3 S2 Pr]. subst Pp Pe PR Pq.
    assert (AG1 : forall a : Z, 0 <= a < 2 ^ 64 -> (st - 4 <= a < p \/ p + nn <= a <= st + sd - 4) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hr. apply Hag. rewrite u64_of_Z by exact Ha. exact Hr. }
    assert (AGn : forall (a : Z) (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
              (st - 4 <= a /\ a + Z.of_nat k <= p \/ p + nn <= a /\ a + Z.of_nat k <= st + sd - 3) ->
              rdn segs M' (Z_to_bv 64 a) k = rdn segs M (Z_to_bv 64 a) k).
    { intros a k Ha Hk Hr. apply rdn_ext; rewrite u64_of_Z by lia; [lia|].
      intros x Hx. apply Hag. lia. }
    assert (Hsinn : 0 <= sd * idx) by nia.
    constructor; cbn zeta.
    - rewrite AG1; [exact P4 | lia | lia].
    - rewrite AG1; [exact P3 | lia | lia].
    - rewrite AGn; [exact P2 | lia | cbn; lia | cbn; lia].
    - intros Hr. rewrite AG1; [exact (Pz Hr) | lia | lia].
    - intros Hr. rewrite AG1; [exact (P5 Hr) | lia | lia].
    - intros Hr. rewrite AGn; [exact (P4' Hr) | lia | cbn; lia | cbn; lia].
    - intros Ho. rewrite AG1; [exact (S3 Ho) | lia | lia].
    - intros Ho. rewrite AGn; [exact (S2 Ho) | lia | cbn; lia | cbn; lia].
    - exact Pr.
  Qed.

  (* [comment removed for export] *)
  Definition GPm (id : nat) (vs : list Z) (M : word -> option byte) : Prop :=
    if Nat.eqb id MN2.SLOT_ID then slot_sem vs M else False.

  Lemma GPm_slot : forall vs M, GPm MN2.SLOT_ID vs M <-> slot_sem vs M.
  Proof. intros. unfold GPm. rewrite Nat.eqb_refl. tauto. Qed.

  (* [comment removed for export] *)
  Lemma GPm_frame : forall id args E M M',
    (forall a, APS.in_fp E (g_fp MN2.Gm id args) a = true -> M' a = M a) ->
    GPm id (map (uE E) args) M -> GPm id (map (uE E) args) M'.
  Proof.
    intros id args E M M' Hfp H. unfold GPm in *. destruct (Nat.eqb_spec id MN2.SLOT_ID) as [->|Hne]; [|exact H].
    unfold MN2.Gm in Hfp. cbn [g_fp] in Hfp. rewrite Nat.eqb_refl in Hfp.
    destruct args as [|start [|sd [|nn [|o [|W [|idx [|p [|]]]]]]]]; try exact H.
    cbn [map] in H |- *.
    pose proof H as H0. cbn [slot_sem] in H0.
    destruct H0 as (EP & Hp & Hsd & Hsc & [Hsd16 Hsd31] & Hmod & Hst16 & Hsi & Hnw & [Hidx1 Hidx2] & Hi32 & Hq & Hn & Hfit).
    destruct EP as [Pp Pe PR Pq _ _ _ _ _ _ _ _ Pr]. subst Pp Pe PR Pq.
    pose proof (u64_range (edenot E start)) as R1. pose proof (u64_range (edenot E nn)) as R2.
    pose proof (u64_range (edenot E p)) as R3. pose proof (u64_range (edenot E sd)) as R4. pose proof (u64_range (edenot E o)) as R5.
    unfold uE in *.
    assert (Hsinn : 0 <= bv_unsigned (edenot E sd) * bv_unsigned (edenot E idx)) by nia.
    apply (slot_sem_frame _ M M'); [|exact H]. cbn [map].
    set (us := bv_unsigned (edenot E start)) in *. set (usd := bv_unsigned (edenot E sd)) in *.
    set (un := bv_unsigned (edenot E nn)) in *. set (uo := bv_unsigned (edenot E o)) in *. set (up := bv_unsigned (edenot E p)) in *.
    assert (A1 : bv_unsigned (alu64 ALU_ADD (edenot E start) (edenot E (ELit (-4)))) = us - 4).
    { rewrite u_add64, edenot_lit, u_lit64a. fold us. replace ((-4) mod 2 ^ 64) with (2 ^ 64 - 4) by reflexivity.
      replace (us + (2 ^ 64 - 4)) with ((us - 4) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (A2 : bv_unsigned (alu64 ALU_ADD (alu64 ALU_SUB (edenot E p) (edenot E start)) (edenot E (ELit 4))) = 16 * uo + 4).
    { rewrite u_add64, u_sub64, edenot_lit, u_lit64a. fold us up. rewrite Hp.
      replace (us + 16 * uo - us) with (16 * uo) by lia. rewrite (Z.mod_small (16 * uo)) by lia. rewrite (Z.mod_small 4) by lia.
      apply Z.mod_small. lia. }
    assert (A3 : bv_unsigned (alu64 ALU_ADD (edenot E p) (edenot E nn)) = up + un).
    { rewrite u_add64. fold up un. apply Z.mod_small. lia. }
    assert (A4 : bv_unsigned (alu64 ALU_ADD (alu64 ALU_SUB (alu64 ALU_ADD (edenot E start) (edenot E sd)) (alu64 ALU_ADD (edenot E p) (edenot E nn)))
                                (edenot E (ELit (-3)))) = us + usd - up - un - 3).
    { rewrite u_add64, u_sub64, !u_add64, edenot_lit, u_lit64a. fold us usd up un.
      rewrite (Z.mod_small (us + usd)) by lia. rewrite (Z.mod_small (up + un)) by lia.
      rewrite (Z.mod_small (us + usd - (up + un))) by lia.
      replace ((-3) mod 2 ^ 64) with (2 ^ 64 - 3) by reflexivity.
      replace (us + usd - (up + un) + (2 ^ 64 - 3)) with ((us + usd - up - un - 3) + 1 * 2 ^ 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    intros x Hx. apply Hfp. unfold MN2.slot_fp, APS.in_fp. cbn [existsb fst snd].
    unfold estart, elenZ. cbn [a_base a_off]. rewrite !mkAlu_denot. rewrite A1, A2, A3, A4.
    destruct Hx as [Hx|Hx].
    - apply Bool.orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
    - apply Bool.orb_true_iff. right. apply Bool.orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma Gm_ok : forall segs' GP v, g_vcok MN2.Gm v = true -> APS.vc_holds segs' GP v.   (* [comment removed for export] *)
  Proof. intros segs' GP v H. discriminate H. Qed.
End Sem.
