(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefUpdWin1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateInit1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition A5_4 : Z := 2779096485.
Definition A5_4s : Z := -1515870811.
Definition A5_8 : Z := 11936128518282651045.
Definition a5_vals : list Z :=
  [A5_8; A5_4; A5_4s; A5_4s; A5_4s; A5_4s; A5_4; A5_8; A5_8; A5_8; A5_4; A5_4; A5_4; A5_4; A5_8; A5_8; A5_4;
   A5_4; A5_4; A5_4; A5_8; A5_8; A5_4; A5_4; A5_4; A5_4; A5_4; A5_4; A5_8; A5_4s; A5_4s; A5_4].

Definition ir2_wrap (wb : Z) : Z := if wb <? 0 then 0 else Z.shiftr wb 4 + 5.
Definition ir2_wb (wb : Z) : Z := if wb <? 0 then - wb else if wb <? 48 then Z.land wb 15 else wb.

(* zlib 1.4: inflateInit2_ zmemzero's the state, so [init] (the allocator's bytes) is no longer read; inflateReset2
   sets reqwrap / reqbits beside wrap / wbits, and inflateReset restores wrap from reqwrap (the same value) *)
Definition s_pre (init : Z -> Z) (b : blk) (wb : Z) : inflate_state :=
  iset_wrap (iset_reqbits (iset_wbits (iset_reqwrap (iset_wrap (iset_mode (iset_window (iset_window_blk
    (is_of_oracle lay_ref (fun _ => 0) b) None) (arr_make 0 0)) HEAD)
               (ir2_wrap wb)) (ir2_wrap wb)) (ir2_wb wb)) (ir2_wb wb)) (ir2_wrap wb).
Definition z_pre (zc : ZCall) : zstrm := zs_set_msg MSG_NULL (zc_strm zc).

Section Model.

  Lemma ir2_bad_cases : forall wb,
    (ir2_bad wb = true)
    \/ (ir2_bad wb = false /\ -15 <= wb < 0 /\ wbits_valid (- wb) = true)
    \/ (ir2_bad wb = false /\ 0 <= wb <= 47 /\ wbits_valid (Z.land wb 15) = true).
  Proof.
    intros wb. destruct (ir2_bad wb) eqn:E; [left; reflexivity | right].
    unfold ir2_bad in E. apply Bool.orb_false_iff in E as [E1 E3]. apply Bool.orb_false_iff in E1 as [E1 E2].
    apply Bool.negb_false_iff in E3. apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
    destruct (Z.ltb_spec wb 0); [left | right]; (split; [reflexivity | split; [lia | exact E3]]).
  Qed.

  Lemma inflateInit2_m_eq : forall {St} (hooks : zhooks St) zc wb (g : St),
    inflateInit2_m ivar_ref hooks zc wb g =
    sbind (zalloc hooks 1 7176) (fun r =>
     match r with
     | None => sret (None, zret0 (z_pre zc) Z_MEM_ERROR)
     | Some (b, init) =>
         if ir2_bad wb then sbind (zfree hooks b) (fun _ => sret (None, zret0 (z_pre zc) Z_STREAM_ERROR))
         else sret (Some (ireset_s (s_pre init b wb)), zret0 (ireset_z (s_pre init b wb) (z_pre zc)) Z_OK)
     end) g.
  Proof.
    intros St hooks zc wb g.
    unfold inflateInit2_m. cbn [iv_lay ivar_ref]. unfold SIZEOF_inflate_state, z_pre.
    unfold sbind. f_equal. extensionality p. destruct p as [[[b init]|] g1]; cbn [fst snd]; [|reflexivity].
    unfold inflateReset2.
    replace (inflateStateCheck _) with false by reflexivity.
    unfold ir2_bad, s_pre, ir2_wrap, ir2_wb.
    destruct (Z.ltb_spec wb 0) as [Hneg|Hpos].
    - replace (47 <? wb) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.ltb_spec wb (-15)) as [H15|H15]; cbn [orb]; [reflexivity|].
      unfold wbits_valid.
      destruct (Z.eqb_spec (- wb) 0) as [E0|E0]; [exfalso; lia|]. cbn [negb andb orb].
      replace (15 <? - wb) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (- wb <=? 15) with true by (symmetry; apply Z.leb_le; lia).
      destruct (Z.ltb_spec (- wb) 8) as [H8|H8]; destruct (Z.leb_spec 8 (- wb)) as [H8'|H8']; try (exfalso; lia); cbn [andb orb negb]; [reflexivity|].
      replace (is_window_blk _) with (@None blk) by reflexivity. unfold sbind at 1. cbn [sret mbind fst snd].
      rewrite inflateReset_same by reflexivity. replace (inflateStateCheck _) with false by reflexivity.
      rewrite inflateReset_eq by reflexivity. reflexivity.
    - replace (47 <? wb) with (negb (wb <? 48)) by (destruct (Z.ltb_spec 47 wb); destruct (Z.ltb_spec wb 48); try reflexivity; exfalso; lia).
      replace (wb <? -15) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (Z.ltb_spec wb 48) as [H48|H48]; cbn [negb orb].
      + unfold wbits_valid.
        pose proof (Z.land_nonneg wb 15) as HL0.
        assert (HL1 : Z.land wb 15 <= 15) by (rewrite land15_mod; pose proof (Z.mod_pos_bound wb (2 ^ 4) ltac:(lia)); lia).
        replace (15 <? Z.land wb 15) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (Z.land wb 15 <=? 15) with true by (symmetry; apply Z.leb_le; lia).
        destruct (Z.eqb_spec (Z.land wb 15) 0) as [E0|E0]; cbn [negb andb orb].
        * replace (is_window_blk _) with (@None blk) by reflexivity. unfold sbind at 1. cbn [sret mbind fst snd].
          rewrite inflateReset_same by reflexivity. replace (inflateStateCheck _) with false by reflexivity.
      rewrite inflateReset_eq by reflexivity. reflexivity.
        * destruct (Z.ltb_spec (Z.land wb 15) 8) as [H8|H8]; destruct (Z.leb_spec 8 (Z.land wb 15)) as [H8'|H8']; try (exfalso; lia); cbn [andb orb negb]; [reflexivity|].
          replace (is_window_blk _) with (@None blk) by reflexivity. unfold sbind at 1. cbn [sret mbind fst snd].
          rewrite inflateReset_same by reflexivity. replace (inflateStateCheck _) with false by reflexivity.
      rewrite inflateReset_eq by reflexivity. reflexivity.
      + destruct (Z.eqb_spec wb 0) as [E0|E0]; [exfalso; lia|]. cbn [negb andb].
        replace (15 <? wb) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Bool.orb_true_r. reflexivity.
  Qed.

End Model.

Lemma ir2_ranges : forall wb, ir2_bad wb = false -> 0 <= ir2_wrap wb < 8 /\ 0 <= ir2_wb wb <= 15 /\ -15 <= wb <= 47.
Proof.
  intros wb H. destruct (ir2_bad_cases wb) as [E|[(_ & Hr & _)|(_ & Hr & _)]]; [rewrite H in E; discriminate| |]; unfold ir2_wrap, ir2_wb.
  - rewrite (proj2 (Z.ltb_lt wb 0)) by lia. lia.
  - rewrite (proj2 (Z.ltb_ge wb 0)) by lia. rewrite (proj2 (Z.ltb_lt wb 48)) by lia.
    pose proof (Z.land_nonneg wb 15). assert (Z.land wb 15 <= 15) by (rewrite land15_mod; pose proof (Z.mod_pos_bound wb (2 ^ 4) ltac:(lia)); lia).
    assert (0 <= Z.shiftr wb 4 < 3) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Section Calls.
End Calls.

Section Proofs.
End Proofs.
