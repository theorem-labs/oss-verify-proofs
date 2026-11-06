(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import DivergeSim SpinAlg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Local Open Scope Z_scope.

Definition pc_self_jump_b (pc : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w =>
      if is_ecall w then false else
      match decode_any w with
      | Some (Jal rd imm, _) => is_x0 rd && (bv_signed imm =? 0)%Z
      | _ => false
      end
  | None => false
  end.

Lemma is_self_jump_pc : forall ms,
  is_self_jump segs ms = true -> pc_self_jump_b (bv_unsigned (ms_pc ms)) = true.
Proof.
  intros ms H. unfold is_self_jump in H. unfold pc_self_jump_b.
  rewrite Z_to_bv_bv_unsigned.
  destruct (ms_svc_pending ms); [discriminate |]. exact H.
Qed.

Fixpoint scan_pcs (fuel : nat) (pc : Z) (acc : bool) : bool :=
  match fuel with
  | O => acc
  | S f => scan_pcs f (pc + 1) (if Z.even pc then acc && negb (pc_self_jump_b pc) else acc)
  end.

Lemma scan_pcs_acc : forall fuel pc acc, scan_pcs fuel pc acc = true -> acc = true.
Proof.
  induction fuel as [|f IH]; intros pc acc H; cbn [scan_pcs] in H; [exact H |].
  apply IH in H. destruct (Z.even pc); [| exact H]. apply andb_prop in H. tauto.
Qed.

Lemma scan_pcs_sound : forall fuel pc acc a,
  scan_pcs fuel pc acc = true -> Z.even a = true -> pc <= a < pc + Z.of_nat fuel -> pc_self_jump_b a = false.
Proof.
  induction fuel as [|f IH]; intros pc acc a H He Ha.
  - cbn in Ha. lia.
  - cbn [scan_pcs] in H.
    destruct (Z.eq_dec a pc) as [-> | Hne].
    + apply scan_pcs_acc in H. rewrite He in H. apply andb_prop in H as [_ H].
      destruct (pc_self_jump_b pc); [discriminate H | reflexivity].
    + apply (IH (pc + 1) _ a H He). rewrite Nat2Z.inj_succ in Ha. lia.
Qed.

Definition seg_no_spin_b (seg : Segment) : bool :=
  scan_pcs (N.to_nat (seg_size seg)) (Z.of_N (seg_base seg)) true.

Definition seg_is_code (seg : Segment) : bool := seg_executable seg && negb (seg_writable seg).

Definition no_spin_b : bool := forallb (fun seg => if seg_is_code seg then seg_no_spin_b seg else true) segs.

Lemma find_segment_range : forall l addr n seg,
  find_segment l addr n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= addr /\ addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros addr n seg H; cbn in H; [discriminate H |].
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | lia].
  - destruct (IH addr n seg H) as (Hin & H1 & H2). split; [right; exact Hin | lia].
Qed.

Lemma fetch_word_range : forall a w,
  fetch_word segs a = Some w ->
  exists seg, In seg segs /\ seg_is_code seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a
              /\ bv_unsigned a < Z.of_N (seg_base seg) + Z.of_N (seg_size seg) /\ Z.even (bv_unsigned a) = true.
Proof.
  intros a w H. unfold fetch_word in H.
  destruct (bv_unsigned a mod 2 =? 0) eqn:Hev; [| discriminate H]. cbn [negb] in H.
  assert (He : Z.even (bv_unsigned a) = true).
  { apply Z.eqb_eq in Hev. apply Z.even_spec. apply Z.mod_divide in Hev; [| lia].
    destruct Hev as [m Hm]. exists m. lia. }
  unfold code_read in H.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N 4)) as [seg|] eqn:Hf; [| discriminate H].
  destruct (seg_executable seg && negb (seg_writable seg)) eqn:Hx; [| discriminate H].
  destruct (find_segment_range _ _ _ _ Hf) as (Hin & H1 & H2).
  exists seg. split; [exact Hin | split; [exact Hx | split; [lia | split; [lia | exact He]]]].
Qed.

Theorem no_spin_b_sound : no_spin_b = true -> ~ spin_site_present segs.
Proof.
  intros Hb [ms Hms].
  pose proof (is_self_jump_pc ms Hms) as Hpc.
  unfold pc_self_jump_b in Hpc.
  destruct (fetch_word segs (Z_to_bv 64 (bv_unsigned (ms_pc ms)))) as [w|] eqn:Hfw; [| discriminate Hpc].
  rewrite Z_to_bv_bv_unsigned in Hfw.
  destruct (fetch_word_range _ _ Hfw) as (seg & Hin & Hx & H1 & H2 & He).
  unfold no_spin_b in Hb. pose proof (proj1 (forallb_forall _ _) Hb seg Hin) as Hb'. clear Hb. rename Hb' into Hb.
  cbn beta in Hb. rewrite Hx in Hb.
  unfold seg_no_spin_b in Hb.
  assert (Hf : pc_self_jump_b (bv_unsigned (ms_pc ms)) = false).
  { apply (scan_pcs_sound _ _ _ _ Hb He). rewrite N_nat_Z. lia. }
  unfold pc_self_jump_b in Hf. rewrite Z_to_bv_bv_unsigned, Hfw in Hf. rewrite Hf in Hpc. discriminate Hpc.
Qed.

End WithSegs.
