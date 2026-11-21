From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure.
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
Lemma itab_fill : forall j X root max cnt wk tb ms (opv bits val hs next incr hw : Z)
    x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31,
  ITL X root max PC_IT_FILL (mkLS x1 x6 x7 x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31) cnt wk tb ms ->
  x23 = wz hw -> x19 = wz val -> x28 = wz (- incr) -> x31 = wz (hs + Z.of_nat j * incr - incr) -> x7 = wz (Z.of_nat j * incr) -> x18 = wz 1 ->
  x9 = wz (il_As (tx_L X) + 1384 + 4 * next) ->
  itx_ok X -> (1 <= j)%nat -> incr = 2 ^ bits -> 0 <= bits <= 15 -> 0 <= hs -> 0 <= next -> Z.of_nat j * incr <= 32768 ->
  next + hs + Z.of_nat j * incr < 1444 + incr -> arr_len tb = 1444 -> ty32 tb -> 0 <= opv < 256 -> 0 <= val < 65536 ->
  0 <= hw < 4294967296 -> hw mod 65536 = bits * 256 + opv ->
  evt usegs (fun ms' => exists x1' x27' x31',
    ITL X root max PC_IT_INCR0 (mkLS x1' x6 (wz 0) x9 x16 x18 x19 x20 x21 x22 x23 x25 x26 x27' x28 x29 x30 x31') cnt wk
        (fill_iter (code_pack opv bits val) hs next incr j tb) ms') ms.
Proof.
  induction j as [|j IH]; [intros; lia|].
  intros until x31. intros HL E23 E19 E28 E31 E7 E18 E9 XO Hj Hincr Rbits Rhs Rnext Rfill Rroom LT TYT Ropv Rval Rhw Ehw.
  itl_open HL. subst x23 x19 x28 x31 x7 x18 x9.
  destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]. unfold Z_ITABLE_STACK in XLO.
  assert (Hi1 : 1 <= incr <= 32768).
  { rewrite Hincr. split; [change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia| change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]. }
  assert (Hji : 0 <= Z.of_nat j * incr) by nia.
  replace (hs + Z.of_nat (S j) * incr - incr) with (hs + Z.of_nat j * incr) by lia.
  set (idx := next + (hs + Z.of_nat j * incr)).
  pose proof (TYT idx) as Rc. set (A := il_As (tx_L X) + 1384) in *.
  pose proof (av32_zlength tb 1444 ltac:(lia)) as L32.
  unfold PC_IT_FILL at 1. zs. zs. rewrite zext32_x4' by lia. zs. ustep PC_IT_TRAP. ustep PC_IT_TRAP. ustep PC_IT_TRAP. ustep PC_IT_TRAP.
  zs. rewrite addw_neg by lia. replace (Z.of_nat (S j) * incr - incr) with (Z.of_nat j * incr) by lia.
  zs. rewrite land_ones32 by lia. zs. rewrite shl2. zs.
  pose proof (u32arr_store_ok_part m A (av32 tb 1444) idx 0 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h0 m0 A tb 1444 idx w (bits * 256 + opv) Gc ltac:(lia) ltac:(lia) Rc ltac:(rewrite unsigned_lit by lia; rewrite Ehw; symmetry; apply Z.mod_small; lia)) as Gc';
      replace (A + 4 * idx) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  pose proof (av32_zlength (arr_set tb idx (put_h0 (arr_get tb idx) (bits * 256 + opv))) 1444 ltac:(lia)) as L32.
  pose proof (put_h0_range (arr_get tb idx) (bits * 256 + opv) Rc) as Rc1.
  pose proof (u32arr_store_ok_part _ A _ idx 2 2 _ Gc ltac:(rewrite av32_length; lia) ltac:(lia) ltac:(cbn; lia) eq_refl) as SOK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      pose proof (av32_put_h1 m0 A tb 1444 idx _ w val Gc ltac:(lia) ltac:(lia) Rc1 ltac:(rewrite unsigned_lit by lia; reflexivity)) as Gc';
      replace (A + 4 * idx + 2) with E in Gc' by lia end.
  clear Gc L32. store_done. rename Gc' into Gc.
  rewrite put2_pack in Gc by lia.
  replace ((bits * 256 + opv) mod 256) with opv in Gc by (Z.div_mod_to_equations; lia).
  replace ((bits * 256 + opv) / 256) with bits in Gc by (Z.div_mod_to_equations; lia). clear Rc Rc1.
  pose proof (av32_zlength (arr_set tb idx (code_pack opv bits val)) 1444 ltac:(lia)) as L32.
  zs. zs. rewrite fill_iter_S. fold idx. br_cases K.
  -
    eapply IH; [itl_close| reflexivity| reflexivity| reflexivity| f_equal; lia| reflexivity| reflexivity| reflexivity
               | split; assumption| lia| exact Hincr| lia| lia| lia| lia| lia| | | lia| lia| lia| exact Ehw].
    + subst idx. rewrite arr_len_set. exact LT.
    + intros i. subst idx. rewrite arr_get_set. destruct (_ && _); [apply code_pack_ty| apply TYT].
  -
    assert (j = 0%nat) by nia. subst j. cbn [fill_iter]. apply evt_done. do 3 eexists. unfold PC_IT_INCR0. itl_close.
Qed.
