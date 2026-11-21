(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs Z_itab_pure Z_itab_ldefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].

Lemma itab_fill : forall j X root max cnt wk tb ms (opv bits val hs next incr : Z)
    x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31,
  ITL X root max PC_IT_FILL (mkLS x1 x6 x7 x8 x9 x10 x16 x22 x23 x24 x25 x26 x27 x30 x31) cnt wk tb ms ->
  x26 = wz opv -> x24 = wz bits -> x25 = wz val -> x27 = wz (- incr) -> x1 = wz (hs - incr) -> x22 = wz (Z.of_nat j * incr) ->
  x8 = wz (il_As (tx_L X) + 1384 + 4 * next) ->
  itx_ok X -> (1 <= j)%nat -> incr = 2 ^ bits -> 0 <= bits <= 15 -> 0 <= hs -> 0 <= next -> Z.of_nat j * incr <= 32768 ->
  next + hs + Z.of_nat j * incr < 1444 + incr -> arr_len tb = 1444 -> ty32 tb -> 0 <= opv < 256 -> 0 <= val < 65536 ->
  evt psegs (ITL X root max PC_IT_INCR0 (mkLS x1 x6 x7 x8 x9 (wz 0) x16 (wz 0) x23 x24 x25 x26 x27 x30 x31) cnt wk
              (fill_iter (code_pack opv bits val) hs next incr j tb)) ms.
Proof.
  induction j as [|j IH]; [intros; lia|].
  intros until x31. intros HL E26 E24 E25 E27 E1 E22 E8 XO Hj Hincr Rbits Rhs Rnext Rfill Rroom LT TYT Ropv Rval.
  itl_open HL. subst x26 x24 x25 x27 x1 x22 x8.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY]. unfold Z_ITABLE_STACK in XLO.
  assert (Hi1 : 1 <= incr <= 32768).
  { rewrite Hincr. split; [change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia| change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]. }
  assert (Hji : 0 <= Z.of_nat j * incr) by nia.
  unfold PC_IT_FILL at 1. zs. rewrite addw_neg by lia.
  replace (Z.of_nat (S j) * incr - incr) with (Z.of_nat j * incr) by lia.
  zs. zs. zs. rewrite zext32_x4' by lia. zs.
  set (idx := next + (hs + Z.of_nat j * incr)).
  pose proof (TYT idx) as Rc. set (A := il_As (tx_L X) + 1384) in *.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.

  pose proof (u32arr_store_ok_part m A (av32 tb 1444) idx 0 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_b0 m0 A tb 1444 idx w opv Gc ltac:(lia) ltac:(lia) Rc ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_b0 (arr_get tb idx) opv)) 1444 ltac:(lia)) as L32.
  pose proof (put_b0_range (arr_get tb idx) opv Rc) as Rc1.

  pose proof (u32arr_store_ok_part _ A _ idx 1 1 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le1 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_b1 m0 A tb 1444 idx _ w bits Gc ltac:(lia) ltac:(lia) Rc1 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 1) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_b1 (put_b0 (arr_get tb idx) opv) bits)) 1444 ltac:(lia)) as L32.
  pose proof (put_b1_range _ bits Rc1) as Rc2.

  pose proof (u32arr_store_ok_part _ A _ idx 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h1 m0 A tb 1444 idx _ w val Gc ltac:(lia) ltac:(lia) Rc2 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put3_pack in Gc. clear Rc Rc1 Rc2.
  pose proof (av32_zlength (arr_set tb idx (code_pack opv bits val)) 1444 ltac:(lia)) as L32.
  zs. zs. rewrite fill_iter_S. fold idx. br_cases K.
  -
    eapply IH; [itl_close| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
               | split; assumption| lia| exact Hincr| lia| lia| lia| lia| lia| | | lia| lia].
    + subst idx. rewrite arr_len_set. exact LT.
    + intros i. subst idx. rewrite arr_get_set. destruct (_ && _); [apply code_pack_ty| apply TYT].
  -
    assert (j = 0%nat) by nia. subst j. cbn [fill_iter]. apply evt_done. unfold PC_IT_INCR0. itl_close.
Qed.
