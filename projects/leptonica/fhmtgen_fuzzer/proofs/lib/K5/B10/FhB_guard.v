(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_deserkit LeptB_guard LeptB_guard2 Fh_lowkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma negxor_ltb1 : forall X off, 0 < X < 2^63 -> 0 <= off < 2^63 -> (Z.lxor ((- X) mod 18446744073709551616) off <? 1) = false.
Proof.
  intros X off HX HO. apply Z.ltb_ge.
  assert (E : (- X) mod 18446744073709551616 = 18446744073709551616 - X).
  { rewrite <- (Z.mod_add (- X) 1 18446744073709551616) by lia. replace (18446744073709551616 - X) with (- X + 1 * 18446744073709551616) by lia.
    apply Z.mod_small. lia. }
  rewrite E.
  assert (NN : 0 <= Z.lxor (18446744073709551616 - X) off) by (apply Z.lxor_nonneg; lia).
  assert (NZ : Z.lxor (18446744073709551616 - X) off <> 0) by (intros H0; apply Z.lxor_eq in H0; lia).
  lia.
Qed.
Lemma pos_ltb0 : forall E, 0 < E < 18446744073709551616 -> (0 <? E mod 18446744073709551616) = true.
Proof. intros E HE. rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma lxor_bias : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n) as [<-|NE]; [| apply andb_false_r].
  rewrite andb_true_r. destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma slt1_pos : forall x, 0 < x < 2^63 -> (Z.lxor x 9223372036854775808 <? 9223372036854775809) = false.
Proof. intros x Hx. rewrite lxor_bias by lia. apply Z.ltb_ge. lia. Qed.

Ltac nullchk_fix :=
  repeat match goal with
  | |- context [Z.lxor ((- ?X) mod 18446744073709551616) ?o <? 1] => rewrite (negxor_ltb1 X o) by lia
  | |- context [0 <? ?E mod 18446744073709551616] => rewrite (pos_ltb0 E) by lia
  end.
Ltac ltb_fix :=
  repeat match goal with
  | |- context [Z.lxor ?x 9223372036854775808 <? 9223372036854775809] => rewrite (slt1_pos x) by lia
  | |- context [Z.lxor ?x 9223372036854775808 <? 9223372036854775808] => rewrite (slt0_nonneg x) by lia
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      match c with context [?a <? ?b] =>
        first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end
  end; cbn [Z.b2z]; change (Z.lxor 0 0) with 0; change (Z.lxor 0 1) with 1; change (Z.lxor 1 0) with 1; change (Z.lxor 1 1) with 0.
Ltac kfix := nullchk_fix; ltb_fix.
(* [comment removed for export] *)
Ltac kstep As Ad := first [ fwalk1 As Ad | progress kfix; fwalk1 As Ad ].
Ltac fwalkb As Ad stops := repeat (tryif at_stop stops then fail else kstep As Ad).
(* [comment removed for export] *)
Ltac zeq := first [ lia
                  | rewrite ?slt1_pos, ?slt0_nonneg by lia; reflexivity          (* [comment removed for export] *)
                  | rewrite pos_ltb0 by lia; reflexivity                         (* [comment removed for export] *)
                  | match goal with |- context [0 <? ?E] => replace (0 <? E) with true by (symmetry; apply Z.ltb_lt; lia) end; reflexivity
                  | repeat rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia); rewrite ?Z.mod_small by lia; lia
                  | change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; Z.div_mod_to_equations; lia
                  | symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; Z.div_mod_to_equations; lia ].
(* [comment removed for export] *)
Ltac canon_regz n C := canon_reg_with n C ltac:(zeq).   (* [comment removed for export] *)
Ltac cell_eq1 := first [ reflexivity | apply (f_equal C8); apply (f_equal (Z_to_bv 64)); zeq ].
Ltac cells_eq := repeat (apply (f_equal2 (@cons cell)); [ cell_eq1 | ]); reflexivity.

(* [comment removed for export] *)
Lemma cb_split8_in : forall (m : mem) A pre post (n : nat) bs,
  rw_cells asegs m A (pre ++ CB (8 + n) bs :: post) ->
  rw_cells asegs m A (pre ++ CB 8 (firstn 8 bs) :: CB n (skipn 8 bs) :: post).
Proof.
  intros m A pre post n bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. cbn. split; [rewrite firstn_length; lia|]. split; [rewrite skipn_length; lia| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite (app_assoc (firstn 8 bs) (skipn 8 bs)). rewrite firstn_skipn. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *.
    replace (8 + (n + cells_size post))%nat with (8 + n + cells_size post)%nat by lia. exact Hw.
Qed.
Ltac slots_split H :=
  repeat (lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let rec go pre rest :=
      lazymatch rest with
      | ?c :: ?post =>
          lazymatch c with
          | CB ?k ?b =>
              lazymatch eval vm_compute in (Nat.ltb 8 k) with
              | true => let k' := eval vm_compute in (k - 8)%nat in
                        change (CB k b) with (CB (8 + k') b) in H;
                        apply (cb_split8_in m A pre post k' b) in H; cbn [app] in H
              | false => let pre' := eval cbn [app] in (pre ++ [c]) in go pre' post
              end
          | _ => let pre' := eval cbn [app] in (pre ++ [c]) in go pre' post
          end
      end in
    go (@nil cell) cs end).
