(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs ECH_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac extend_munch MU WM MU' WM' ::=
  lazymatch type of MU with munch ?W ?m ?m0 =>
  lazymatch type of MU' with munch ?W' m0 ?m1 =>
    let T := fresh "MUx" in
    assert (T : munch W m m1)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU'];
          let xa := fresh "xa" in let Hxa := fresh "Hxa" in
          intros xa Hxa; unfold outside in Hxa |- *; cbn in Hxa |- *;
          first [ solve [clear - Hxa; tauto] | lia ]);
    clear MU; rename T into MU;
    let T2 := fresh "WMx" in
    pose proof (wmono_trans _ _ _ _ WM WM') as T2; clear WM; rename T2 into WM;
    clear MU' WM'   (* [comment removed for export] *)
  end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac carry MU WM ::=
  lazymatch type of MU with
  | munch ?W ?m0 ?m1 =>
      repeat match goal with
      | H : rw_cells ?segs m0 ?A ?cs |- _ =>
          first [ apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MU WM) in H; [| cbn; lia]
                | change (stale (rw_cells segs m0 A cs)) in H ]
      | H : bytes_at ?segs m0 ?A ?bs |- _ =>
          first [ apply (fun HH => @bytes_at_transport segs W m0 m1 A bs HH MU) in H; [| cbn; lia]
                | change (stale (bytes_at segs m0 A bs)) in H ]
      | H : stk ?segs m0 ?lo ?hi |- _ =>
          first [ apply (fun HH => @stk_transport_disjoint segs W m0 m1 lo hi HH MU WM) in H; [| cbn; lia]
                | change (stale (stk segs m0 lo hi)) in H ]
      | H : u32arr ?segs m0 ?A ?ws |- _ =>
          first [ apply (fun HH => @u32arr_transport segs W m0 m1 A ws HH MU WM) in H; [| cbn [disjoint_from]; rewrite ?length_map; simpl_arr_sizes; lia]
                | change (stale (u32arr segs m0 A ws)) in H ]
      | H : u64arr ?segs m0 ?A ?ws |- _ =>
          first [ apply (fun HH => @u64arr_transport segs W m0 m1 A ws HH MU WM) in H; [| cbn [disjoint_from]; rewrite ?length_map; simpl_arr_sizes; lia]
                | change (stale (u64arr segs m0 A ws)) in H ]
      | H : u8arr ?segs m0 ?A ?bs |- _ =>
          first [ apply (fun HH => @u8arr_transport segs W m0 m1 A bs HH MU WM) in H; [| cbn [disjoint_from]; lia]
                | change (stale (u8arr segs m0 A bs)) in H ]
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac land MU WM ::=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; land_exs PO; destruct_ands PO; subst ms';
  lazymatch type of MU with munch _ _ ?m0 =>
    match goal with MUc : munch _ m0 ?m1 |- _ =>
      match goal with WMc : wmono _ m0 m1 |- _ =>
        rewrite ?unsigned_lit in MUc by lia;
        repeat match goal with H : context [bv_unsigned (Z_to_bv 64 _)] |- _ =>
          lazymatch type of H with munch _ _ _ => fail | _ => progress (rewrite ?unsigned_lit in H by lia) end end;
        carry MUc WMc; extend_munch MU WM MUc WMc
      end
    end
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    repeat match goal with H : mem_inv _ ?mx |- _ => lazymatch mx with mc => fail | _ => clear H end end;
    repeat match goal with H : stale _ |- _ => clear H end;
    try (lazymatch goal with _ : stk _ mc _ _ |- _ => idtac end;
         match goal with H : stk _ mc _ _ |- _ => rename H into ST end)
  end;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end);
  repeat match goal with H : ?v = Z_to_bv 64 _ |- _ => is_var v; subst v end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac spec_as Q SPEC := pose proof SPEC as Q; hnf in Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_256P : forall x P, 0 < P -> (x mod (256 * P)) mod 256 = x mod 256 /\ (x mod (256 * P)) / 256 = (x / 256) mod P.
Proof.
  intros x P HP. rewrite Z.rem_mul_r by lia. split.
  - replace (x mod 256 + 256 * ((x / 256) mod P)) with (x mod 256 + ((x / 256) mod P) * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
  - replace (x mod 256 + 256 * ((x / 256) mod P)) with (((x / 256) mod P) * 256 + x mod 256) by ring.
    rewrite Z.div_add_l by lia. rewrite (Z.div_small (x mod 256)) by (apply Z.mod_pos_bound; lia). lia.
Qed.
Lemma Z_to_le_bytes_mod : forall n x y, x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n) -> Z_to_le_bytes n x = Z_to_le_bytes n y.
Proof.
  induction n as [|n IH]; intros x y E; [reflexivity|].
  cbn [Z_to_le_bytes]. replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) in E by lia.
  rewrite Z.pow_add_r in E by lia. change (2 ^ 8) with 256 in E.
  assert (P : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  destruct (mod_256P x _ P) as [X1 X2]. destruct (mod_256P y _ P) as [Y1 Y2].
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite <- X1, <- Y1, E. reflexivity.
  - apply IH. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite <- X2, <- Y2, E. reflexivity.
Qed.

Lemma le4_sx32 : forall v : word, le4 (sx32 v) = le4 v.
Proof.
  intros v. unfold le4, sx32. apply Z_to_le_bytes_mod. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 32 * 2 ^ 32).
  set (u := bv_unsigned v). set (z := bv_swrap 32 u).
  assert (E1 : (z mod (2 ^ 32 * 2 ^ 32)) mod 2 ^ 32 = z mod 2 ^ 32).
  { rewrite Z.rem_mul_r by lia. replace (z mod 2 ^ 32 + 2 ^ 32 * ((z / 2 ^ 32) mod 2 ^ 32)) with (z mod 2 ^ 32 + ((z / 2 ^ 32) mod 2 ^ 32) * 2 ^ 32) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia. }
  rewrite E1. subst z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. f_equal. lia.
Qed.

Lemma rw_cells_C4_sx32 : forall segs m A pre v post,
  rw_cells segs m A (pre ++ C4 (sx32 v) :: post) -> rw_cells segs m A (pre ++ C4 v :: post).
Proof.
  intros segs m A pre v post [[WF B] W]. split; [split|].
  - apply cells_wf_app in WF. destruct WF as [W1 [_ W3]]. apply cells_wf_app. split; [exact W1| split; [exact I| exact W3]].
  - rewrite cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite le4_sx32 in B. exact B.
  - rewrite cells_size_app in *. exact W.
Qed.
