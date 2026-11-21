From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Zh_kit Z_infl_iface Z_infl_pure2 Z_itab_kit Z_itab_defs Z_itab_ldefs Z_ukit Z_itab_exit Z_itab_head Z_itab_next Z_itab_sub Z_itab_init.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_itab_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees ItableModel ItableModel2 RefInflateSafeTY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.simpl_sizes ::=
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end; cbn [length].
Lemma le2_wz_wrap16 : forall v, le2 (wz v) = le2 (wz (wrap16 v)).
Proof.
  intros v. apply le2_wz_mod. rewrite unsigned_lit_wrap, wrap16_mod, Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 48). reflexivity.
Qed.
Record ITSM (X : itx) (low : list cell) (cnt o w tb : arr) (m : mem) : Prop := mkITSM {
  sm_low : rw_cells usegs m (bv_unsigned (tx_sp X) + -208) low;
  sm_ofs : u8arr usegs m (bv_unsigned (tx_sp X) + -166) (u16s (av16s o 1 15));
  sm_cnt : u8arr usegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  sm_sav : rw_cells usegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  sm_stk : stk usegs m (tx_lo X) (bv_unsigned (tx_sp X) + -208);
  sm_work : u8arr usegs m (il_As (tx_L X) + 808) (u16s (av16 w 288));
  sm_codes : u32arr usegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  sm_lens : u8arr usegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320));
  sm_mi : mem_inv usegs m;
  sm_mu : munch (tx_W1 X) (tx_m0 X) m;
  sm_wm : wmono usegs (tx_m0 X) m }.
Lemma ITSM_ITM : forall X low cnt o w tb m, ITSM X low cnt o w tb m -> ITM X low cnt o w tb m.
Proof. intros X low cnt o w tb m [A B C D E F G H I J K]. split; try assumption. Qed.
Definition sort_post (X : itx) (low : list cell) (cnt o w tb : arr) (x5 x6 x17 : word) : machine_state -> Prop :=
  fun ms' => exists x1 x7 x8 x9 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) x12 (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_TYPE) (tx_fc X) None m' (seg_rom usegs)
    /\ ITSM X low cnt o w tb m'.
Lemma itm_sort_k_offs_ty : forall lens lens_ofs k o0 work,
  (forall i, 0 <= arr_get o0 i < 65536) -> forall i, 0 <= arr_get (fst (itm_sort_k lens lens_ofs k o0 work)) i < 65536.
Proof.
  intros lens lens_ofs k o0 work B. unfold itm_sort_k.
  destruct (Z_lt_le_dec k 0).
  - rewrite forZ_nil by lia. exact B.
  - apply (ModelRel.forZ_ind (fun _ ow => forall i, 0 <= arr_get (fst ow) i < 65536)); [| exact B | lia].
    intros j [o w] _ H i. cbn [sort_body fst] in *.
    destruct (negb _); cbn [fst]; [|apply H]. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H].
Qed.
Lemma itab_sort_loop : forall n X low cnt o0 w0 tb m (sym : Z)
    (x1 x5 x6 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word),
  let o := fst (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) in
  let w := snd (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) in
  ITSM X low cnt o w tb m -> Z.of_nat (cells_size low) = 42 ->
  itx_ok X -> 0 <= sym < tx_codes X -> tx_codes X - sym <= Z.of_nat n ->
  (forall i, 0 <= arr_get o0 i < 65536) -> arr_len o0 = 16 -> ty16 w0 -> arr_len w0 = 288 -> ty16 (tx_lens X) ->
  (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  snd (itm_sort_ok_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 288) = true ->
  evt usegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) (wz 1) x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (18446744073709551615 - tx_lensA X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz sym) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz 0) (wz 16) (wz (18446744073709551615 - (bv_unsigned (tx_sp X) + -168))) (wz (tx_codes X)))
        (tx_F X) (wz PC_IT_SORT) (tx_fc X) None m (seg_rom usegs)).
Proof.
  induction n as [|n IH]; intros until x27; intros o w SM SZ XO Rsym Rn TYO0 LO0 TYW0 LW0 TYL L15 SOK; [lia|].
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  destruct SM as [LOW OFS CNT SAV ST Gw Gc Gl MI MU WM]. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16s_zlength o 1 15 ltac:(lia)) as L16o. pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c.
  pose proof (av16_zlength w 288 ltac:(lia)) as L16w. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * 320 < 2 ^ 62 /\ tx_lensA X mod 2 = 0) by (unfold tx_lensA; lia).
  pose proof (itm_sort_k_len (tx_lens X) (tx_lofs X) sym o0 w0) as [LO LW]. fold o in LO. fold w in LW.
  pose proof (itm_sort_k_offs_ty (tx_lens X) (tx_lofs X) sym o0 w0 TYO0) as TYO. fold o in TYO.
  pose proof (itm_sort_k_work_range (tx_lens X) (tx_lofs X) sym o0 w0 TYW0) as TYW. fold w in TYW.
  set (l := arr_get (tx_lens X) (tx_lofs X + sym)). pose proof (TYL (tx_lofs X + sym)) as Rl. pose proof (L15 sym ltac:(lia)) as Rl15. fold l in Rl, Rl15.
  assert (TAIL : forall m1 (y9 y18 y19 : word),
    ITSM X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (sym + 1) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (sym + 1) o0 w0)) tb m1 ->
    evt usegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
      (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) (wz 1) y9 (wz (ity_code (tx_ty X)))
               (wz (tx_lensA X)) (wz (18446744073709551615 - tx_lensA X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz sym) x17
               y18 y19 x20 x21 x22 x23 x24 x25 x26 x27 (wz 0) (wz 16) (wz (18446744073709551615 - (bv_unsigned (tx_sp X) + -168))) (wz (tx_codes X)))
          (tx_F X) (wz PC_IT_SORTN) (tx_fc X) None m1 (seg_rom usegs))).
  { intros m1 y9 y18 y19 SM1. pose proof SM1 as [LOW1 OFS1 CNT1 SAV1 ST1 Gw1 Gc1 Gl1 MI1 MU1 WM1].
    unfold PC_IT_SORTN. zs. zs. br_cases KE.
    -
      replace (sym + 1) with (tx_codes X) in SM1 by lia.
      apply evt_done. unfold sort_post, PC_IT_TYPE. do 21 eexists. split; [reflexivity| exact SM1].
    - eapply (IH X low cnt o0 w0 tb m1 (sym + 1)); [exact SM1| exact SZ| exact XO'| lia| lia| exact TYO0| exact LO0| exact TYW0| exact LW0| exact TYL| exact L15| exact SOK]. }
  rewrite itm_sort_k_step in TAIL by lia. unfold sort_body in TAIL.
  rewrite (surjective_pairing (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0)) in TAIL. fold o w l in TAIL.
  unfold PC_IT_SORT. zs. rewrite (shl1 sym). ustep PC_IT_TRAP. ustep PC_IT_TRAP. zs.
  pose proof (u16arr_read usegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + sym) _ (wa (tx_lensA X + 2 * sym)) Gl
                (av16_nth (tx_lens X) 320 (tx_lofs X + sym) ltac:(lia)) ltac:(lia) ltac:(unfold tx_lensA; f_equal; lia)) as RD.
  zs. rewrite zx16_small by lia. clear RD. fold l. zs. br_cases K.
  -
    replace (l =? 0) with true in TAIL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in TAIL.
    apply TAIL. split; assumption.
  - replace (l =? 0) with false in TAIL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in TAIL.
    pose proof (TYO l) as Rol. set (ol := arr_get o l) in *.
    assert (Rol2 : ol < 288).
    { pose proof (itm_sort_ok_k_inv (tx_lens X) (tx_lofs X) o0 w0 288 sym ltac:(lia)
                    (itm_sort_ok_k_le (tx_lens X) (tx_lofs X) o0 288 (tx_codes X) (sym + 1) ltac:(lia) SOK)) as [_ B].
      fold o l in B. specialize (B ltac:(lia)). lia. }
    ustep PC_IT_TRAP. zs. rewrite (shl1 l). ustep PC_IT_TRAP. zs.
    pose proof (u16arr_read usegs _ (bv_unsigned (tx_sp X) + -166) (av16s o 1 15) (l - 1) _ (wa (bv_unsigned (tx_sp X) + -168 + 2 * l)) OFS
                  (av16s_nth o 1 15 (l - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD.
    replace (1 + (l - 1)) with l in RD by lia. fold ol in RD.
    zs. rewrite zx16_small by lia. clear RD. zs. zs. rewrite (shl1 ol). zs.
    pose proof (u16arr_store_ok usegs _ (bv_unsigned (tx_sp X) + -166) (av16s o 1 15) (l - 1) (wa (bv_unsigned (tx_sp X) + -166 + 2 * (l - 1))) OFS
                  ltac:(rewrite av16s_length; lia) eq_refl) as SOK0.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?wv)) _) =>
      let E := addr_expr a0 in
      pose proof (av16s_write m0 (bv_unsigned (tx_sp X) + -166) o 1 15 (l - 1) wv (wrap16 (ol + 1)) OFS ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(apply le2_wz_wrap16)) as OFS';
      unfold u16arr in OFS'; replace (bv_unsigned (tx_sp X) + -166 + 2 * (l - 1)) with E in OFS' by lia end.
    replace (1 + (l - 1)) with l in OFS' by lia.
    pose proof (av16s_zlength (arr_set o l (wrap16 (ol + 1))) 1 15 ltac:(lia)) as L16o'.
    clear OFS L16o. store_done. rename OFS' into OFS. try clear SOK0.
    ustep PC_IT_TRAP. zs. zs. rewrite xor_guard1 by lia. ustep PC_IT_TRAP. ustep PC_IT_TRAP. ustep PC_IT_TRAP. ustep PC_IT_TRAP.
    st16 Gw w 288 (il_As (tx_L X) + 808) ol (wrap16 sym) ltac:(apply le2_wz_wrap16).
    zs. apply TAIL. split; try assumption.
Qed.
Definition PC_IT_SORT0 : Z := 0x22074.
Lemma itab_sort : forall X low cnt o0 w0 tb m
    (x1 x5 x6 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  ITSM X low cnt o0 w0 tb m -> Z.of_nat (cells_size low) = 42 ->
  itx_ok X -> (forall i, 0 <= arr_get o0 i < 65536) -> arr_len o0 = 16 -> ty16 w0 -> arr_len w0 = 288 -> ty16 (tx_lens X) ->
  (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  snd (itm_sort_ok_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 288) = true ->
  evt usegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -208)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_SORT0) (tx_fc X) None m (seg_rom usegs)).
Proof.
  intros until x31; intros SM SZ XO TYO0 LO0 TYW0 LW0 TYL L15 SOK.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY XAL]; unfold Z_ITABLE_STACK in XLO.
  pose proof SM as [LOW OFS CNT SAV ST Gw Gc Gl MI MU WM]. pose proof (it_saved_bound _ m SAV) as BSP.
  assert (RLA : 0 < tx_lensA X /\ tx_lensA X + 2 * 320 < 2 ^ 62 /\ tx_lensA X mod 2 = 0) by (unfold tx_lensA; lia).
  unfold PC_IT_SORT0. zs. br_cases K.
  -
    rewrite !itm_sort_k_0 by lia. cbn [fst snd].
    apply evt_done. unfold sort_post, PC_IT_TYPE. do 21 eexists. split; [reflexivity| exact SM].
  - ustep PC_IT_TRAP. zs. zs. al2 (tx_lensA X). zs. rewrite shl_32. zs. rewrite (zb_lxor_ones (tx_lensA X)) by lia. zs. zs. rewrite zb_lxor_ones by lia.
    zs. rewrite mul32_shr32 by lia. zs. replace (0 <? il_As (tx_L X) + 808) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. zs.
    eapply (itab_sort_loop (Z.to_nat (tx_codes X)) X low cnt o0 w0 tb m 0);
      [cbv zeta; rewrite !itm_sort_k_0 by lia; cbn [fst snd]; exact SM| exact SZ| exact XO'| lia| lia| exact TYO0| exact LO0| exact TYW0| exact LW0| exact TYL| exact L15| exact SOK].
Qed.
