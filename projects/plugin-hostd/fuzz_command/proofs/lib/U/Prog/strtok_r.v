From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strspn_c strcspn_c strtok_r_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma spn_len_le : forall set s, (spn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn; [lia|]. destruct (in_set set x); cbn; lia. Qed.

Lemma cspn_len_le : forall set s, (cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn; [lia|]. destruct (existsb _ set); cbn; lia. Qed.

Lemma nth_cstr : forall (str : list byte) p, ~ In (Z_to_bv 8 0) str -> (p <= length str)%nat ->
  exists b, nth_error (str ++ [Z_to_bv 8 0]) p = Some b /\ (bv_unsigned b = 0%Z <-> p = length str).
Proof.
  intros str p NZ Hp. destruct (Nat.eq_dec p (length str)) as [E|E].
  - exists (Z_to_bv 8 0). split; [|split; intros; [assumption | reflexivity]].
    rewrite nth_error_app2 by lia. rewrite E, Nat.sub_diag. reflexivity.
  - destruct (nth_error str p) as [b|] eqn:Hb.
    2:{ apply nth_error_None in Hb. lia. }
    exists b. split. { rewrite nth_error_app1 by lia. exact Hb. }
    split; [|intros; lia]. intros H0. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b by (apply bv_eq; rewrite H0; reflexivity). eapply nth_error_In; eauto.
Qed.

Lemma upd_cut : forall (str : list byte) j b, (j < length str)%nat ->
  upd (str ++ [Z_to_bv 8 0]) j b = (firstn j str ++ b :: skipn (S j) str) ++ [Z_to_bv 8 0].
Proof.
  induction str as [|x s IH]; intros j b Hj; cbn in Hj; [lia|].
  destruct j as [|j]; cbn; [reflexivity|]. f_equal. apply IH. lia.
Qed.

Theorem strtok_r_holds : strspn_contract -> strcspn_contract -> strtok_r_contract.
Proof.
  intros SSPN SCSPN. unfold strtok_r_contract, STRTOK_R. intros until can.
  intros SLOT HC STRP NONUL SEPB SEPNZ GOT GUARD ST LO SEPS SLOTS SGOT SGUARD MI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (rw_cells_bound _ _ _ _ SLOT) as PB. cbn [cells_size csize Nat.add] in PB.
  pose proof (bytes_at_bound _ _ _ _ SEPB) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 8);
    (C + Z.of_nat (tok_j sep str), C + Z.of_nat (tok_j sep str) + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (Z.eq_dec C 0) as [C0|CNZ].
  { clear STRP.
    assert (A0 : bv_unsigned a0 = 0%Z /\ bv_unsigned pv = 0%Z).
    { revert HC. destruct (Z.eqb_spec (bv_unsigned a0) 0); intros HC; lia. }
    clear HC. subst C.
    carve_frame 32%nat ST.
    apply (rw_cells_split_CB rsegs _ _ [] 32%nat _ [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app firstn skipn] in FR.
    do 8 step.
    step. if_cases K; zify_cond K.
    { exfalso. lia. }
    step. step. if_cases K2; zify_cond K2.
    2:{ exfalso. lia. }
    do 7 step.
    release_frame FR ST (bv_unsigned sp).
    assert (PV : pv = Z_to_bv 64 0) by (apply bv_eq; rewrite K2; reflexivity).
    subst pv.
    finish.
    intros H; exfalso; apply H; reflexivity. }
  destruct (STRP CNZ) as (STR & SLK & PAD & SEPC & SEPP). clear STRP.
  pose proof (u8arr_bound _ _ _ _ STR) as CB. rewrite length_app in CB. cbn [length] in CB.
  pose proof (bytes_at_bound _ _ _ _ SLK) as KB.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat _ [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mm _) =>
    assert (MAIN : forall c x10 : word, bv_unsigned c = C ->
      evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 a2 c x10 a1 a2 a3 a4 a5 a6 a7
                          a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x21278) fc None mm (seg_rom rsegs)))
  end.
  { intros c x10 Hc. clear HC. subst C.
    assert (FULL : bytes_at rsegs m1 (bv_unsigned c) (str ++ Z_to_bv 8 0 :: slack)).
    { replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact (proj1 STR)|]. rewrite length_app. cbn [length].
      replace (bv_unsigned c + Z.of_nat (length str + 1))%Z with (bv_unsigned c + Z.of_nat (length str) + 1)%Z by lia.
      exact SLK. }
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str sep lo can);
        rewrite ?unsigned_lit by lia; first [exact (proj1 STR) | eassumption | lia]
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; unfold strspn_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
        post_call rsegs mm ]
    end.
    match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
    cbv delta [mkR].
    pose proof (spn_len_le sep str) as Hi.
    destruct (nth_cstr str (spn_len sep str) NONUL Hi) as (b & Hb & Hb0).
    step.
    pose proof (u8arr_read rsegs _ (bv_unsigned c) _ (Z.of_nat (spn_len sep str)) b _ STR
                  ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD.
    step. clear RD.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    step. if_cases K; zify_cond K; rewrite unsigned_lit in K by lia.
    - assert (Ein : spn_len sep str = length str) by (apply Hb0; exact K).
      step.
      assert (SOK : store_ok rsegs x14 a2 8 = true).
      { exact (rw_cells_store_ok_at rsegs x14 (bv_unsigned a2) [C8 pv] 0%nat (C8 pv) 8%nat a2 SLOT eq_refl eq_refl
                 ltac:(symmetry; apply wa_of_var; lia)). }
      step.
      replace (write_to_mem x14 a2) with (write_to_mem x14 (wa (bv_unsigned a2 + Z.of_nat 0)))
        by (f_equal; first [apply wa_of_var | symmetry; apply wa_of_var]; lia).
      clear SOK.
      mem_after_store.
      do 7 step.
      release_frame FR ST (bv_unsigned sp).
      assert (TR : tok_ret (bv_unsigned c) sep str = 0%Z).
      { unfold tok_ret, tok_i. rewrite Ein, Nat.eqb_refl, orb_true_r. reflexivity. }
      assert (TS : tok_save (bv_unsigned c) sep str = 0%Z).
      { unfold tok_save, tok_j, tok_i. rewrite Ein, skipn_all. cbn [cspn_len].
        rewrite Nat.add_0_r, Nat.leb_refl, orb_true_r. reflexivity. }
      assert (TC : tok_cut sep str = str).
      { unfold tok_cut, tok_j, tok_i. rewrite Ein, skipn_all. cbn [cspn_len].
        rewrite Nat.add_0_r, Nat.ltb_irrefl. reflexivity. }
      apply evt_done. unfold strtok_r_post. rewrite TR, TS, TC.
      do 15 eexists. split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      intros _. split; assumption.
    - assert (Ilt : (spn_len sep str < length str)%nat) by (destruct (Nat.eq_dec (spn_len sep str) (length str)) as [E|E]; [exfalso; apply K, Hb0, E| lia]).
      clear Hb Hb0.
      assert (SUF : bytes_at rsegs x14 (bv_unsigned c + Z.of_nat (spn_len sep str)) (skipn (spn_len sep str) str ++ Z_to_bv 8 0 :: slack)).
      { pose proof FULL as FU. rewrite <- (firstn_skipn (spn_len sep str) str), <- app_assoc in FU.
        apply bytes_at_app in FU. destruct FU as [_ FU]. rewrite firstn_length_le in FU by lia. exact FU. }
      assert (NZ2 : ~ In (Z_to_bv 8 0) (skipn (spn_len sep str) str)).
      { intros HIn. apply NONUL. rewrite <- (firstn_skipn (spn_len sep str) str). apply in_or_app. right. exact HIn. }
      pose proof (length_skipn (spn_len sep str) str) as LSK.
      do 3 step.
      unfold SSP_GOT, SSP_GUARD in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply (SCSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (skipn (spn_len sep str) str) slack sep lo can);
          rewrite ?unsigned_lit by lia; try unfold CSPN_SSP_GOT, CSPN_SSP_GUARD;
          first [ exact SUF | exact NZ2 | eassumption | lia
                | intros HL; specialize (PAD HL); rewrite LSK, Nat2Z.inj_sub by lia;
                  match goal with |- ((- ?x) mod 8 <= _)%Z =>
                    replace x with (bv_unsigned c + Z.of_nat (length str) + 1)%Z by lia end; exact PAD ]
        | let ms' := fresh "ms'" in let PO := fresh "PO" in
          intros ms' PO; unfold strcspn_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
          post_call rsegs mm ]
      end.
      match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
      cbv delta [mkR].
      step.
      pose proof (cspn_len_le sep (skipn (spn_len sep str) str)) as Hk.
      assert (Hj : (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str) <= length str)%nat) by lia.
      assert (TJ : tok_j sep str = (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str))%nat) by reflexivity.
      assert (TR : tok_ret (bv_unsigned c) sep str = (bv_unsigned c + Z.of_nat (spn_len sep str))%Z).
      { unfold tok_ret, tok_i. rewrite (proj2 (Z.eqb_neq _ _) CNZ).
        destruct (Nat.eqb_spec (spn_len sep str) (length str)); [lia|]. reflexivity. }
      destruct (nth_cstr str _ NONUL Hj) as (b2 & Hb2 & Hb20).
      pose proof (u8arr_read rsegs _ (bv_unsigned c) _ (Z.of_nat (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str))) b2 _ STR
                    ltac:(rewrite Nat2Z.id; exact Hb2) ltac:(lia) eq_refl) as RD.
      step. clear RD.
      pose proof (bv_unsigned_in_range 8 b2) as BR2. unfold bv_modulus in BR2. cbn in BR2.
      step. if_cases K2; zify_cond K2; rewrite unsigned_lit in K2 by lia.
      + assert (Ejn : (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str))%nat = length str) by (apply Hb20; exact K2).
        assert (SOK : store_ok rsegs x29 a2 8 = true).
        { exact (rw_cells_store_ok_at rsegs x29 (bv_unsigned a2) [C8 pv] 0%nat (C8 pv) 8%nat a2 SLOT eq_refl eq_refl
                   ltac:(symmetry; apply wa_of_var; lia)). }
        step.
        replace (write_to_mem x29 a2) with (write_to_mem x29 (wa (bv_unsigned a2 + Z.of_nat 0)))
          by (f_equal; first [apply wa_of_var | symmetry; apply wa_of_var]; lia).
        clear SOK.
        mem_after_store.
        do 7 step.
        release_frame FR ST (bv_unsigned sp).
        assert (TS : tok_save (bv_unsigned c) sep str = 0%Z).
        { unfold tok_save, tok_j, tok_i. rewrite Ejn, Nat.leb_refl, orb_true_r. reflexivity. }
        assert (TC : tok_cut sep str = str).
        { unfold tok_cut, tok_j, tok_i. rewrite Ejn, Nat.ltb_irrefl. reflexivity. }
        apply evt_done. unfold strtok_r_post. rewrite TR, TS, TC.
        do 15 eexists. split; [reflexivity|].
        repeat match goal with |- _ /\ _ => split end; try eassumption.
        intros _. split; assumption.
      + assert (Jlt : (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str) < length str)%nat).
        { destruct (Nat.eq_dec (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str)) (length str)) as [E|E];
            [exfalso; apply K2, Hb20, E| lia]. }
        step.
        assert (SOK : store_ok rsegs x29 a2 8 = true).
        { exact (rw_cells_store_ok_at rsegs x29 (bv_unsigned a2) [C8 pv] 0%nat (C8 pv) 8%nat a2 SLOT eq_refl eq_refl
                   ltac:(symmetry; apply wa_of_var; lia)). }
        step.
        replace (write_to_mem x29 a2) with (write_to_mem x29 (wa (bv_unsigned a2 + Z.of_nat 0)))
          by (f_equal; first [apply wa_of_var | symmetry; apply wa_of_var]; lia).
        clear SOK.
        mem_after_store.
        pose proof (u8arr_store_ok rsegs _ (bv_unsigned c) _ (Z.of_nat (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str))) (wa (bv_unsigned c + Z.of_nat (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str)))) STR
                      ltac:(rewrite length_app; cbn [length]; lia) eq_refl) as SOK2.
        pose proof (u8arr_write rsegs _ (bv_unsigned c) _ (Z.of_nat (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str))) (Z_to_bv 8 0) STR
                      ltac:(rewrite length_app; cbn [length]; lia)) as STR2.
        step.
        replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity.
        store_done.
        do 8 step.
        release_frame FR ST (bv_unsigned sp).
        replace (bv_unsigned c + Z.of_nat (spn_len sep str) + Z.of_nat (cspn_len sep (skipn (spn_len sep str) str)) + 1)%Z
          with (tok_save (bv_unsigned c) sep str) in SLOT.
        2:{ unfold tok_save. rewrite (proj2 (Z.eqb_neq _ _) CNZ).
            destruct (Nat.leb_spec (length str) (tok_j sep str)); [lia|]. cbn [orb]. lia. }
        assert (TC : tok_cut sep str = firstn (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str)) str ++ Z_to_bv 8 0 :: skipn (S (spn_len sep str + cspn_len sep (skipn (spn_len sep str) str))) str).
        { unfold tok_cut. rewrite TJ, (proj2 (Nat.ltb_lt _ _) Jlt). reflexivity. }
        rewrite Nat2Z.id, (upd_cut str _ _ Jlt) in STR2.
        apply evt_done. unfold strtok_r_post. rewrite TR, TC.
        do 15 eexists. split; [reflexivity|].
        repeat match goal with |- _ /\ _ => split end; try eassumption.
        intros _. split; assumption. }
  step. if_cases K; zify_cond K.
  { apply (MAIN a0 a0). revert HC. destruct (Z.eqb_spec (bv_unsigned a0) 0); intros HC; lia. }
  step. step. if_cases K2; zify_cond K2.
  { exfalso. revert HC. destruct (Z.eqb_spec (bv_unsigned a0) 0); intros HC; lia. }
  apply (MAIN pv a0). revert HC. destruct (Z.eqb_spec (bv_unsigned a0) 0); intros HC; lia.
Qed.
