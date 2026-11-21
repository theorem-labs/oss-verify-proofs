(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Zh_kit Z_infl_iface Z_itab_kit Z_itab_defs. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_itab_pure. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_itab_ldefs.
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

Lemma le2_wz_wrap16 : forall v, le2 (wz v) = le2 (wz (wrap16 v)).
Proof.
  intros v. apply le2_wz_mod. rewrite unsigned_lit_wrap, wrap16_mod, Z.mod_mod by lia. apply Z.mod_mod_divide. exists (2 ^ 48). reflexivity.
Qed.

Record ITSM (X : itx) (low : list cell) (cnt o w tb : arr) (m : mem) : Prop := mkITSM {
  sm_low : rw_cells psegs m (bv_unsigned (tx_sp X) + -192) low;
  sm_ofs : u8arr psegs m (bv_unsigned (tx_sp X) + -166) (u16s (av16s o 1 15));
  sm_cnt : u8arr psegs m (bv_unsigned (tx_sp X) + -136) (u16s (av16 cnt 16));
  sm_sav : rw_cells psegs m (bv_unsigned (tx_sp X) + -104) (it_saved X);
  sm_stk : stk psegs m (tx_lo X) (bv_unsigned (tx_sp X) + -192);
  sm_work : u8arr psegs m (il_As (tx_L X) + 808) (u16s (av16 w 288));
  sm_codes : u32arr psegs m (il_As (tx_L X) + 1384) (av32 tb 1444);
  sm_lens : u8arr psegs m (il_As (tx_L X) + 168) (u16s (av16 (tx_lens X) 320));
  sm_mi : mem_inv psegs m;
  sm_mu : munch (tx_W1 X) (tx_m0 X) m;
  sm_wm : wmono psegs (tx_m0 X) m }.

Lemma ITSM_ITM : forall X low cnt o w tb m, ITSM X low cnt o w tb m -> ITM X low cnt o w tb m.
Proof. intros X low cnt o w tb m [A B C D E F G H I J K]. split; try assumption. Qed.

Definition sort_post (X : itx) (low : list cell) (cnt o w tb : arr) (x5 x6 x17 : word) : machine_state -> Prop :=
  fun ms' => exists x1 x7 x8 x9 x12 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
                 (wz (tx_lensA X)) x12 (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_TYPE) (tx_fc X) None m' (seg_rom psegs)
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
    (x1 x5 x6 x8 x9 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word),
  let o := fst (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) in
  let w := snd (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) in
  ITSM X low cnt o w tb m -> Z.of_nat (cells_size low) = 26 ->
  itx_ok X -> 0 <= sym < tx_codes X -> tx_codes X - sym <= Z.of_nat n ->
  (forall i, 0 <= arr_get o0 i < 65536) -> arr_len o0 = 16 -> ty16 w0 -> arr_len w0 = 288 -> ty16 (tx_lens X) ->
  (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  snd (itm_sort_ok_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 288) = true ->
  evt psegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz sym) x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (tx_lensA X + 2 * sym)) x29 x30 x31) (tx_F X) (wz PC_IT_SORT) (tx_fc X) None m (seg_rom psegs)).
Proof.
  induction n as [|n IH]; intros until x31; intros o w SM SZ XO Rsym Rn TYO0 LO0 TYW0 LW0 TYL L15 SOK; [lia|].
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  destruct SM as [LOW OFS CNT SAV ST Gw Gc Gl MI MU WM]. unfold tx_W1 in MU. pose proof (it_saved_bound _ m SAV) as BSP.
  pose proof (av16s_zlength o 1 15 ltac:(lia)) as L16o. pose proof (av16_zlength cnt 16 ltac:(lia)) as L16c.
  pose proof (av16_zlength w 288 ltac:(lia)) as L16w. pose proof (av32_zlength tb 1444 ltac:(lia)) as L32. pose proof (av16_zlength (tx_lens X) 320 ltac:(lia)) as L16l.
  pose proof (itm_sort_k_len (tx_lens X) (tx_lofs X) sym o0 w0) as [LO LW]. fold o in LO. fold w in LW.
  pose proof (itm_sort_k_offs_ty (tx_lens X) (tx_lofs X) sym o0 w0 TYO0) as TYO. fold o in TYO.
  pose proof (itm_sort_k_work_range (tx_lens X) (tx_lofs X) sym o0 w0 TYW0) as TYW. fold w in TYW.
  set (l := arr_get (tx_lens X) (tx_lofs X + sym)). pose proof (TYL (tx_lofs X + sym)) as Rl. pose proof (L15 sym ltac:(lia)) as Rl15. fold l in Rl, Rl15.

  assert (TAIL : forall m1 (y29 y30 y31 : word),
    ITSM X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (sym + 1) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (sym + 1) o0 w0)) tb m1 ->
    evt psegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
      (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 (wz (bv_unsigned (tx_sp X) + -168)) x8 x9 (wz (ity_code (tx_ty X)))
               (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) (wz sym) x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (wz (tx_lensA X + 2 * sym)) y29 y30 y31) (tx_F X) (wz PC_IT_SORTN) (tx_fc X) None m1 (seg_rom psegs))).
  { intros m1 y29 y30 y31 SM1. pose proof SM1 as [LOW1 OFS1 CNT1 SAV1 ST1 Gw1 Gc1 Gl1 MI1 MU1 WM1].
    unfold PC_IT_SORTN. zs. zs. zs. br_cases KE.
    -
      replace (sym + 1) with (tx_codes X) in SM1 by lia.
      apply evt_done. unfold sort_post, PC_IT_TYPE. do 21 eexists. split; [reflexivity| exact SM1].
    - replace (tx_lensA X + 2 * sym + 2) with (tx_lensA X + 2 * (sym + 1)) by lia.
      eapply (IH X low cnt o0 w0 tb m1 (sym + 1)); [exact SM1| exact SZ| exact XO'| lia| lia| exact TYO0| exact LO0| exact TYW0| exact LW0| exact TYL| exact L15| exact SOK]. }
  rewrite itm_sort_k_step in TAIL by lia. unfold sort_body in TAIL.
  change (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0) with (fst (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0), snd (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0)) in TAIL || idtac.
  rewrite (surjective_pairing (itm_sort_k (tx_lens X) (tx_lofs X) sym o0 w0)) in TAIL. fold o w l in TAIL.
  unfold PC_IT_SORT.
  pose proof (u16arr_read psegs _ (il_As (tx_L X) + 168) (av16 (tx_lens X) 320) (tx_lofs X + sym) _ (wa (tx_lensA X + 2 * sym)) Gl
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
    zs. zs.
    pose proof (u16arr_read psegs _ (bv_unsigned (tx_sp X) + -166) (av16s o 1 15) (l - 1) _ (wa (bv_unsigned (tx_sp X) + -168 + (l ≪ 1))) OFS
                  (av16s_nth o 1 15 (l - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    replace (1 + (l - 1)) with l in RD by lia. fold ol in RD.
    zs. rewrite zx16_small by lia. clear RD. zs. zs.
    replace (l ≪ 1) with (2 * l) by (rewrite Z.shiftl_mul_pow2 by lia; lia).

    pose proof (u16arr_store_ok psegs _ (bv_unsigned (tx_sp X) + -166) (av16s o 1 15) (l - 1) (wa (bv_unsigned (tx_sp X) + -166 + 2 * (l - 1))) OFS
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

    zs. replace (ol ≪ 1) with (2 * ol) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    st16 Gw w 288 (il_As (tx_L X) + 808) ol (wrap16 sym) ltac:(apply le2_wz_wrap16).
    zs. apply TAIL. split; try assumption.
Qed.

Lemma land_ones32 : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x H. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. change (2^32) with 4294967296. lia. Qed.

Definition PC_IT_SORT0 : Z := 0x1f594.

Lemma itab_sort : forall X low cnt o0 w0 tb m
    (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  ITSM X low cnt o0 w0 tb m -> Z.of_nat (cells_size low) = 26 ->
  itx_ok X -> (forall i, 0 <= arr_get o0 i < 65536) -> arr_len o0 = 16 -> ty16 w0 -> arr_len w0 = 288 -> ty16 (tx_lens X) ->
  (forall i, 0 <= i < tx_codes X -> arr_get (tx_lens X) (tx_lofs X + i) <= 15) ->
  snd (itm_sort_ok_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 288) = true ->
  evt psegs (sort_post X low cnt (fst (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) (snd (itm_sort_k (tx_lens X) (tx_lofs X) (tx_codes X) o0 w0)) tb x5 x6 x17)
    (MS (mkR x1 (wz (bv_unsigned (tx_sp X) + -192)) (tx_gp X) (tx_tp X) x5 x6 x7 x8 x9 (wz (ity_code (tx_ty X)))
             (wz (tx_lensA X)) (wz (tx_codes X)) (wz (il_As (tx_L X) + 160)) (wz (tx_bitsA X)) (wz (il_As (tx_L X) + 808)) x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (tx_F X) (wz PC_IT_SORT0) (tx_fc X) None m (seg_rom psegs)).
Proof.
  intros until x31; intros SM SZ XO TYO0 LO0 TYW0 LW0 TYL L15 SOK.
  pose proof XO as XO'. destruct XO as [XLO XAS XWIN XCO ARRS LAY]; unfold Z_ITABLE_STACK in XLO.
  pose proof SM as [LOW OFS CNT SAV ST Gw Gc Gl MI MU WM]. pose proof (it_saved_bound _ m SAV) as BSP.
  unfold PC_IT_SORT0. zs. br_cases K.
  -
    rewrite !itm_sort_k_0 by lia. cbn [fst snd].
    apply evt_done. unfold sort_post, PC_IT_TYPE. do 21 eexists. split; [reflexivity| exact SM].
  - zs. zs. zs. rewrite land_ones32 by lia. zs. zs. zs.
    replace (wz (tx_lensA X)) with (wz (tx_lensA X + 2 * 0)) at 2 by (f_equal; lia).
    eapply (itab_sort_loop (Z.to_nat (tx_codes X)) X low cnt o0 w0 tb m 0);
      [cbv zeta; rewrite !itm_sort_k_0 by lia; cbn [fst snd]; exact SM| exact SZ| exact XO'| lia| lia| exact TYO0| exact LO0| exact TYW0| exact LW0| exact TYL| exact L15| exact SOK].
Qed.
