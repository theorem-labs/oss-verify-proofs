(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk MemSplit SymExec SymExec3 SymExec3Sound.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition run : Type := (Z * list Z)%type.

Fixpoint apply_runs (rs : list run) (D : word -> option byte) : word -> option byte :=
  match rs with
  | [] => D
  | (a, bs) :: rest => wbytes (apply_runs rest D) (Z_to_bv 64 a) (map (Z_to_bv 8) bs)
  end.

Inductive lkind := LKStack | LKData (a : Z) (bs : list Z) | LKBad.

Definition classify (spv : N) (slo shi dlim : Z) (e : sentry) : lkind :=
  match e with
  | SE (SA (EVar v) off) w _ =>
      if (N.eqb v spv && Z.leb slo off && Z.leb (off + Z.of_nat w) shi)%bool then LKStack else LKBad
  | SE (SA (ELit 0) a) w (ELit z) =>
      if (Z.leb 0 a && Z.leb (a + Z.of_nat w) dlim && Nat.leb w 8)%bool
      then LKData a (map bv_unsigned (word_to_le_bytes w (Z_to_bv 64 z))) else LKBad
  | _ => LKBad
  end.

Fixpoint log_split_ok (spv : N) (slo shi dlim : Z) (log : list sentry) : bool :=
  match log with
  | [] => true
  | e :: rest => match classify spv slo shi dlim e with LKBad => false | _ => log_split_ok spv slo shi dlim rest end
  end.

Fixpoint abs_runs (spv : N) (slo shi dlim : Z) (log : list sentry) : list run :=
  match log with
  | [] => []
  | e :: rest =>
      match classify spv slo shi dlim e with
      | LKData a bs => (a, bs) :: abs_runs spv slo shi dlim rest
      | _ => abs_runs spv slo shi dlim rest
      end
  end.

Lemma map_Z_to_bv_bv_unsigned : forall (bs : list byte), map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH, Z_to_bv_bv_unsigned. reflexivity. Qed.

Section Split.
  Variable sp0 : word.
  Variable mem0 : word -> option byte.
  Variable E : env.
  Variable spv : N.
  Variables slo shi dlim : Z.

  Hypothesis Hspe_lo : (win_lo sp0 <= bv_unsigned (ev E spv) + slo)%Z.
  Hypothesis Hspe_hi : (bv_unsigned (ev E spv) + shi <= bv_unsigned sp0)%Z.
  Hypothesis Hdlim : (0 <= dlim <= win_lo sp0)%Z.

  Lemma split_sound : forall log J D,
    log_split_ok spv slo shi dlim log = true ->
    wfJ sp0 J ->
    exists J', wfJ sp0 J' /\
      mem_denot E (cmem sp0 mem0 J D) log = cmem sp0 mem0 J' (apply_runs (abs_runs spv slo shi dlim log) D).
  Proof.
    induction log as [|e rest IH]; intros J D Hok HJ.
    - exists J. split; [exact HJ | reflexivity].
    - cbn [log_split_ok abs_runs] in Hok |- *.
      pose proof (u64_range sp0) as Hsp. pose proof (u64_range (ev E spv)) as Hv.
      destruct e as [[b off] w v]. cbn [mem_denot].
      destruct (classify spv slo shi dlim (SE (SA b off) w v)) as [|a bs|] eqn:Hc; [ | | discriminate].
      +
        destruct (IH J D Hok HJ) as (J1 & HJ1 & ->).
        unfold classify in Hc. destruct b as [z0| v' | | | | | |]; try discriminate.
        1:{ destruct z0; try discriminate. destruct v; try discriminate.
            match type of Hc with (if ?c then _ else _) = _ => destruct c; discriminate end. }
        match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end.
        apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
        apply N.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst v'.
        eexists. split; [apply wfJ_wbytes; exact HJ1|].
        unfold adenot. cbn [a_base a_off edenot].
        apply wbytes_cmem_win.
        * unfold v_addi. rewrite u_small by lia. lia.
        * unfold v_addi. rewrite u_small by lia. rewrite length_N_to_le_bytes. lia.
      +
        destruct (IH J D Hok HJ) as (J1 & HJ1 & ->).
        unfold classify in Hc. destruct b as [z0| | | | | | |]; try discriminate.
        2:{ match type of Hc with (if ?c then _ else _) = _ => destruct c; discriminate end. }
        destruct z0; try discriminate. destruct v as [z| | | | | | |]; try discriminate.
        match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hb; [|discriminate] end.
        apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
        apply Z.leb_le in H1. apply Z.leb_le in H2. apply Nat.leb_le in H3.
        injection Hc as <- <-.
        exists J1. split; [exact HJ1|].
        cbn [apply_runs]. rewrite map_Z_to_bv_bv_unsigned.
        unfold adenot. cbn [a_base a_off edenot].
        pose proof stack_max_size_pos as Hsm. unfold win_lo in *.
        assert (Hoff : (0 <= off /\ off + Z.of_nat w <= bv_unsigned sp0 - stack_max_size)%Z) by lia.
        replace (v_addi (Z_to_bv 64 0) off) with (Z_to_bv 64 off)
          by (unfold v_addi; rewrite u_small by lia; f_equal; lia).
        apply wbytes_cmem_data. unfold win_lo. rewrite u_small by lia. rewrite length_N_to_le_bytes. lia.
  Qed.
End Split.

Fixpoint lookup_byte (rs : list run) (x : Z) : option Z :=
  match rs with
  | [] => None
  | (a, bs) :: rest =>
      if (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool then Some (nth (Z.to_nat (x - a)) bs 0%Z)
      else lookup_byte rest x
  end.

Fixpoint lookup_runs (rs : list run) (x : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S k => match lookup_byte rs x, lookup_runs rs (x + 1) k with
           | Some b, Some r => Some (b :: r)
           | _, _ => None
           end
  end.

Fixpoint runs_ok (rs : list run) : bool :=
  match rs with
  | [] => true
  | (a, bs) :: rest => (Z.leb 0 a && Z.leb (a + Z.of_nat (length bs)) (2 ^ 64) && runs_ok rest)%bool
  end.

Lemma apply_runs_at : forall rs D (x : Z), (0 <= x < 2 ^ 64)%Z -> runs_ok rs = true ->
  apply_runs rs D (Z_to_bv 64 x) =
  match lookup_byte rs x with Some b => Some (Z_to_bv 8 b) | None => D (Z_to_bv 64 x) end.
Proof.
  induction rs as [|[a bs] rest IH]; intros D x Hx Hok; cbn [apply_runs lookup_byte runs_ok] in *; [reflexivity|].
  apply andb_prop in Hok as [Hok Hrest]. apply andb_prop in Hok as [H0 H1].
  apply Z.leb_le in H0. apply Z.leb_le in H1.
  destruct (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool eqn:Hin.
  - apply andb_prop in Hin as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb.
    rewrite wbytes_inside.
    3: { rewrite length_map, !u_small by lia. lia. }
    2: { rewrite length_map, u_small by lia. lia. }
    rewrite !u_small by lia. f_equal. apply map_nth.
  - apply Bool.andb_false_iff in Hin.
    assert (Hout : (x < a \/ a + Z.of_nat (length bs) <= x)%Z).
    { destruct Hin as [Hin|Hin]; [apply Z.leb_gt in Hin | apply Z.ltb_ge in Hin]; lia. }
    destruct bs as [|b0 bs'].
    + cbn [map wbytes]. apply IH; assumption.
    + rewrite wbytes_outside.
      * apply IH; assumption.
      * rewrite length_map, u_small by (cbn [length] in *; lia). lia.
      * rewrite length_map, !u_small by (cbn [length] in *; lia). exact Hout.
Qed.

