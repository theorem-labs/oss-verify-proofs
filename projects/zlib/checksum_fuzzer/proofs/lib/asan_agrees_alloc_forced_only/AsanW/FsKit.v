(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg ABytes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_in H :=
  repeat match type of H with
  | context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v in H
  end.
Ltac lit_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  end.

Ltac addr_diff_g E A :=
  let k := addr_diff E A in
  let ok := eval vm_compute in (Z.ltb k 65536) in
  lazymatch ok with true => k end.

Ltac solve_load_g :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_g :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2 H3; cbn in *; [exact I|].
  destruct H as [D H]. split; [lia|]. eapply IH; eauto.
Qed.

Definition dc_at (m : word -> option byte) (A n : Z) : Prop :=
  exists bs, rw_cells asegs m A [CB (Z.to_nat n) bs].





Lemma dc_at_any2 : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> (0 <= A /\ A + n <= 0x10000 \/ 0x5f7000 <= A) -> dc_at m' A n.
Proof.
  intros m m' A n [bs [[[WF _] [B0 [B1 BR]]] [W0 [W1 WR]]]] WM HA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in *.
  rewrite app_nil_r in B1, BR. cbn in WF. rewrite Nat.add_0_r in W1, WR.
  assert (RD : forall i, 0 <= i < Z.of_nat (length bs) -> exists b, m' (wa (A + i)) = Some b).
  { intros i Hi. specialize (WR i ltac:(lia)). apply WM in WR.
    rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia).
    destruct (m' (wa (A + i))) as [b|]; [exists b; reflexivity| congruence]. }
  assert (BS : forall k, (k <= length bs)%nat -> exists bs' : list byte, length bs' = k /\
            forall i, (i < k)%nat -> m' (wa (A + Z.of_nat i)) = nth_error bs' i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - destruct (IH ltac:(lia)) as (bs' & L & E). destruct (RD (Z.of_nat k) ltac:(lia)) as [b Hb].
      exists (bs' ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE].
      + rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
      + rewrite nth_error_app1 by lia. apply E. lia. }
  destruct (BS (length bs) ltac:(lia)) as (bs' & L & E).
  exists bs'. split; [split; [cbn; destruct WF as [WF _]; split; [lia| exact I]|]|].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. unfold mrd. rewrite (E i ltac:(lia)).
    destruct (nth_error bs' i) eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply WM. apply WR. lia.
Qed.
Lemma dc_at_any : forall m m' A n,
  dc_at m A n -> wmono asegs m m' -> 0x5f7000 <= A -> dc_at m' A n.
Proof. intros m m' A n D W H. eapply dc_at_any2; [exact D | exact W | right; exact H]. Qed.

Lemma seg_rom_high : forall a : word, 0x5f7000 <= bv_unsigned a -> seg_rom asegs a = None.
Proof. intros a Ha. unfold seg_rom. rewrite ref_memory_read_none; [reflexivity| cbn; lia| lia]. Qed.
Lemma mrd_high : forall m a, 0x5f7000 <= a < 2^64 -> mrd asegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|]. apply seg_rom_high. rewrite wa_unsigned by lia. lia.
Qed.
End CANSEC1.
