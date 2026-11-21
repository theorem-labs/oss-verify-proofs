(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItTable.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeK.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeA5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeR.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateSafeF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NC_lens_list : forall lens ofs n, 0 <= n -> NC (lens_list lens ofs n) = n.
Proof.
  intros lens ofs n Hn. unfold NC, lens_list, zlength. rewrite length_map, length_seq. lia.
Qed.

Lemma lens_list_forall : forall (P : Z -> Prop) lens ofs n,
  (forall i, ofs <= i < ofs + n -> P (arr_get lens i)) -> Forall P (lens_list lens ofs n).
Proof.
  intros P lens ofs n H. unfold lens_list. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as [k [<- Hk]]. apply in_seq in Hk. apply H. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TableArms.
  Variable iv : ivariant.
Variable flush : Z.

  Lemma arm_CODELENS_safe : arm_safe CODELENS (arm_CODELENS ivar_ref flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_CODELENS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT).
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & CA2 & CA3 & CS & CL0).
    assert (HP0 : PHIr r <= PHI w0).
    { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank CODELENS) with 0 in HP. unfold PHIr. lia. }
    assert (HCL : CL s c r).
    { unfold CL. repeat (split; [first [assumption | lia]|]). exact HWB. }
    apply POST_bind.
    pose proof (codelens_while_spec c 321 s r HCL ltac:(cbn; lia)) as W.
    destruct (codelens_while 321 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact (proj1 W)|destruct W].
    destruct W as [(-> & HCL1 & Hh1 & En1 & Ed1 & P1 & Ep1 & Q1 & _)|(Hm1 & HW1 & P1 & Ep1 & Ei1 & Eo1)].
    2:{ (* [comment removed for export] *)
        arun gs_eq. rewrite Hm1. change (BAD =? BAD) with true. cbv iota. rewrite aret_eq. apply POST_ARun; [exact HW1|].
        lazymatch goal with |- _ < PHI ?w => set (PW0 := PHI w) in *; clearbody PW0 end.
        unfold PHI. cbn [w_s w_c w_r]. rewrite Hm1. change (rank BAD) with 0. unfold PHIr in *. lia. }
    destruct (Q1 (proj2 Hh)) as [P1' Hb1]. clear Q1 P1.
    pose proof HCL1 as (HC1 & HR1 & E1 & HCm1 & _ & Hnl1 & Hnd1 & Hh1' & HLs1 & HT1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    arun gs_eq. rewrite E1. change (CODELENS =? BAD) with false. cbv iota.
    acase C256.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1. apply CORE_length; exact HC1.
        + eapply REGS_cview; [exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    (* [comment removed for export] *)
    pose proof (inflate_table_TBLg LENS (is_lens s1) 0 (is_nlen s1) (is_codes s1) 0 9 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_LENS; rewrite CB3; lia)) as TL.
    match goal with |- context [inflate_table LENS ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table LENS a1 a2 a3 a4 a5 a6 a7) as [[[[retL tblL] nextL] lenbitsL] workL] end.
    destruct TL as [[TL5 TL6] TL].
    cbv beta iota. aflat. arun us_eq. aflat. arun ur_eq.
    acase CrL.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1; [rewrite TL6; reflexivity | rewrite TL5; reflexivity | apply CORE_length; exact HC1].
        + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    assert (RL0 : retL = 0) by (destruct (Z.eqb_spec retL 0); [assumption|discriminate CrL]).
    specialize (TL RL0). destruct TL as (TL1 & TL2 & TL3 & TL4). cbn [it_room] in TL2. unfold ENOUGH_LENS in TL2.
    (* [comment removed for export] *)
    arun gs_eq. sacc.
    pose proof (inflate_table_TBLg DISTS (is_lens s1) (is_nlen s1) (is_ndist s1) tblL nextL 6 workL
                  ltac:(lia) ltac:(rewrite TL6, CB2; lia) ltac:(intros i Hi; apply HLs1; lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; lia) ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; unfold ENOUGH_DISTS; rewrite TL5, CB3; lia)) as TD.
    match goal with |- context [inflate_table DISTS ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table DISTS a1 a2 a3 a4 a5 a6 a7) as [[[[retD tblD] nextD] distbitsD] workD] end.
    destruct TD as [[TD5 TD6] TD].
    cbv beta iota. aflat. arun us_eq. aflat. arun ur_eq.
    acase CrD.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
        + eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    assert (RD0 : retD = 0) by (destruct (Z.eqb_spec retD 0); [assumption|discriminate CrD]).
    specialize (TD RD0). destruct TD as (TD1 & TD2 & TD3 & TD4). cbn [it_room] in TD2. unfold ENOUGH_DISTS in TD2.
    aflat. arun set_mode_eq.
    match goal with |- POST _ (_ ?w) => assert (HW3 : WINV w) end.
    { winv_split.
      - core_keep HC1; [rewrite TD6, TL6; reflexivity | rewrite TD5, TL5; reflexivity | apply CORE_length; exact HC1].
      - eapply REGS_cview; [apply REGS_ret; apply REGS_ret; exact HR1|reflexivity|reflexivity].
      - split; [common_keep HCm1|]. split; [exact Hb1|]. unfold tables. sacc. split.
        + cbn [cpok]. split; [lia|]. exists (nextL - 0). split; [lia|].
          apply (TBLg_ext LENS (fun x => arr_get tblL (0 + x))); [|exact TL3]. intros x Hx. apply TD4. lia.
        + cbn [cpok]. split; [lia|]. exists (nextD - nextL). split; [lia|]. exact TD3.
      - exact HWF1.
      - exact HWB1. }
    acase Cz.
    - aleave. exact HW3.
    - match goal with |- POST _ (_ (mkW ?s3 ?c3 ?r3)) => apply (POST_arm LEN_ (arm_LEN_ ivar_ref) w0 s3 c3 r3 arm_LEN__safe HW3) end.
      + reflexivity.
      + phi_goal. unfold PHIr in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition LL (s : inflate_state) (c : icall) (r : iregs) : Prop :=
    CORE s /\ REGS c r /\ is_mode s = LENLENS /\ common s /\ ir_bits r < 8
    /\ 4 <= is_ncode s <= 19 /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s <= is_ncode s
    /\ (forall k, 0 <= k < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a k) <= 7)
    /\ ir_out r = arr_len (ic_outbuf c) /\ (is_wbits s = 0 -> ir_put r = 0).

  Lemma lenlens_while1_S : forall k w,
    lenlens_while1 (S k) w = (do s0 <- gs (fun s0 => s0) ;
                              if is_have s0 <? is_ncode s0 then
                                NEEDBITS 3 ;;
                                do b <- BITS 3 ;
                                do s1 <- gs (fun s1 => s1) ;
                                set_lens (arr_get order_a (is_have s1)) b ;;
                                us (fun s1 => iset_have s1 (wrap32 (is_have s1 + 1))) ;;
                                DROPBITS 3 ;;
                                lenlens_while1 k
                              else aret tt)%am w.
  Proof. reflexivity. Qed.

  Lemma lenlens_while1_spec : forall c k s r,
    LL s c r -> is_ncode s - is_have s <= Z.of_nat k ->
    match lenlens_while1 k (mkW s c r) with
    | ARun _ (mkW s' c' r') => c' = c /\ LL s' c' r' /\ is_have s' = is_ncode s' /\ is_ncode s' = is_ncode s
        /\ is_nlen s' = is_nlen s /\ is_ndist s' = is_ndist s /\ PHIr r' <= PHIr r /\ ir_put r' = ir_put r
        /\ (is_have s < is_ncode s -> PHIr r' + 8 <= PHIr r)
        /\ is_codes s' = is_codes s /\ is_work s' = is_work s
    | ALeave w' => WINV w'
    | ARet _ _ => False
    end.
  Proof.
    intros c k. induction k as [|k IH]; intros s r HLL Hk.
    - cbn [lenlens_while1]. unfold aret. pose proof HLL as (_ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
      cbn in Hk. repeat (split; [first [reflexivity | assumption | lia]|]); first [reflexivity | assumption | lia].
    - pose proof HLL as (HC & HR & E & HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs & HWF & HWB). regs_open HR.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      rewrite lenlens_while1_S. mrun gs_eq. cbn [w_s].
      destruct (Z.ltb_spec (is_have s) (is_ncode s)) as [LT|GE].
      2:{ unfold aret. repeat (split; [first [reflexivity | assumption | lia]|]); first [reflexivity | assumption | lia]. }
      rewrite ?abind_assoc. unfold abind at 1.
      destruct (NEEDBITS_spec c 3 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
      2:{ rewrite EQ. pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
          unfold WINV. cbn [w_s w_c w_r]. rewrite E. mred. split; [exact HC|]. split; [exact HR1|].
          split; [|split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB]]. repeat (split; [first [assumption | lia]|]). exact HLs. }
      rewrite EQ. cbv beta iota.
      pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
      pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
      mrun BITS_eq. mrun gs_eq. cbn [w_s]. unfold set_lens. mrun us_eq. mrun us_eq. mrun DROPBITS_eq. sacc.
      rewrite (BITSv_mod (ir_hold r1) 3) by lia. pose proof (mod_pow2_range (ir_hold r1) 3 ltac:(lia)) as MV.
      rewrite wrap16_id by lia. rewrite !wrap32_id by lia.
      pose proof (order_a_range (is_have s) ltac:(lia)) as OR.
      match goal with |- context [lenlens_while1 k (mkW ?s1 ?c1 ?r1')] =>
        specialize (IH s1 r1'); assert (HLL1 : LL s1 c r1') end.
      { unfold LL. sacc. split; [core_keep HC; apply CORE_length; exact HC|].
        split; [apply REGS_holdbits; [exact HR1|]; apply HB_drop; [split; [exact RB1|exact RHO1]|lia]|].
        split; [exact E|]. split; [common_keep HCm|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split.
        - intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
          replace ((0 <=? arr_get order_a (is_have s)) && (arr_get order_a (is_have s) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
          destruct (Z.eqb_spec (arr_get order_a (is_have s)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [lia|].
          apply HLs. destruct (Z.eq_dec j (is_have s)) as [->|]; [congruence|lia].
        - split; [rewrite Eo1; exact HWF|rewrite Ep1; exact HWB]. }
      specialize (IH HLL1 ltac:(sacc; lia)).
      destruct (lenlens_while1 k _) as [u [s' c' r'] | w' | rc w']; [|exact IH|exact IH].
      revert IH. sacc. intros (-> & HLL' & Hh' & Enc & Enl & End & P' & Ep' & _ & Ecd & Ewk).
      unfold PHIr in *. revert P'. sacc. intros P'.
      repeat (split; [first [reflexivity | assumption | lia]|]). exact Ewk.
  Qed.

  Lemma lenlens_while2_S : forall k w,
    lenlens_while2 (S k) w = (do s0 <- gs (fun s0 => s0) ;
                              if is_have s0 <? 19 then
                                set_lens (arr_get order_a (is_have s0)) 0 ;;
                                us (fun s1 => iset_have s1 (wrap32 (is_have s1 + 1))) ;;
                                lenlens_while2 k
                              else aret tt)%am w.
  Proof. reflexivity. Qed.

  Lemma lenlens_while2_spec : forall c k s r,
    CORE s -> 0 <= is_have s <= 19 -> 19 - is_have s <= Z.of_nat k ->
    (forall j, 0 <= j < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a j) <= 7) ->
    exists lens', lenlens_while2 k (mkW s c r) = ARun tt (mkW (iset_have (iset_lens s lens') 19) c r)
      /\ arr_len lens' = 320 /\ (forall j, 0 <= j < 19 -> 0 <= arr_get lens' (arr_get order_a j) <= 7).
  Proof.
    intros c k. induction k as [|k IH]; intros s r HC Hh Hk HLs.
    - exists (is_lens s). cbn in Hk. assert (E19 : is_have s = 19) by lia.
      pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      split; [cbn [lenlens_while2]; unfold aret; f_equal; rewrite <- E19; destruct s; reflexivity|].
      split; [exact CA1|]. intros j Hj. apply HLs. lia.
    - pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CA1 & _).
      rewrite lenlens_while2_S. unfold abind at 1. rewrite gs_eq. cbn [w_s].
      destruct (Z.ltb_spec (is_have s) 19) as [LT|GE].
      + unfold set_lens. rewrite ?abind_assoc. unfold abind at 1. rewrite us_eq. unfold abind at 1. rewrite us_eq. sacc.
        change (wrap16 0) with 0. rewrite wrap32_id by lia.
        pose proof (order_a_range (is_have s) ltac:(lia)) as OR.
        match goal with |- context [lenlens_while2 k (mkW ?s1 _ _)] =>
          destruct (IH s1 r) as (lens' & EQ & HL' & HLs') end.
        * core_keep HC. apply CORE_length; exact HC.
        * sacc. lia.
        * sacc. lia.
        * sacc. intros j Hj. rewrite arr_get_set. unfold arr_inb. rewrite CA1.
          replace ((0 <=? arr_get order_a (is_have s)) && (arr_get order_a (is_have s) <? 320)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
          destruct (Z.eqb_spec (arr_get order_a (is_have s)) (arr_get order_a j)) as [Ej|Ej]; cbn [andb]; [lia|].
          apply HLs. destruct (Z.eq_dec j (is_have s)) as [->|]; [congruence|lia].
        * exists lens'. rewrite EQ. revert HL' HLs'. sacc. intros HL' HLs'. split; [destruct s; reflexivity|]. split; [exact HL'|exact HLs'].
      + exists (is_lens s). assert (E19 : is_have s = 19) by lia.
        split; [unfold aret; f_equal; rewrite <- E19; destruct s; reflexivity|].
        split; [exact CA1|]. intros j Hj. apply HLs. lia.
  Qed.

  Lemma arm_LENLENS_safe : arm_safe LENLENS (arm_LENLENS ivar_ref flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_LENLENS.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR.
    destruct HMF as (HCm & Hb8 & Hnc & Hnl & Hnd & Hh & HLs).
    assert (HP0 : PHIr r <= PHI w0).
    { unfold PHI at 1 in HP. cbn [w_s w_c w_r] in HP. rewrite E in HP. change (rank LENLENS) with 0 in HP. unfold PHIr. lia. }
    assert (HLL : LL s c r) by (unfold LL; repeat (split; [first [assumption | lia]|]); exact HWB).
    apply POST_bind.
    pose proof (lenlens_while1_spec c 19 s r HLL ltac:(cbn; lia)) as W1.
    destruct (lenlens_while1 19 (mkW s c r)) as [u [s1 c1 r1] | w1 | rc w1]; [|exact W1|destruct W1].
    destruct W1 as (-> & HLL1 & Hh1 & Enc & Enl & End & P1 & Ep1 & Q1 & Ecd & Ewk). specialize (Q1 (proj2 Hh)).
    pose proof HLL1 as (HC1 & HR1 & E1 & HCm1 & Hb1 & Hnc1 & Hnl1 & Hnd1 & Hh1' & HLs1 & HWF1 & HWB1).
    pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB1 & CB2 & CB3 & _ & _).
    apply POST_bind.
    destruct (lenlens_while2_spec c 19 s1 r1 HC1 ltac:(lia) ltac:(cbn; lia) HLs1) as (lens19 & EQ2 & HL19 & HLs19).
    rewrite EQ2.
    assert (HLs' : forall i, 0 <= i < 0 + 19 -> 0 <= arr_get lens19 i <= 7).
    { intros i Hi. destruct (order_a_onto i ltac:(lia)) as [j [Hj <-]]. apply HLs19. exact Hj. }
    arun gs_eq. sacc.
    pose proof (inflate_table_TBLg CODES lens19 0 19 (is_codes s1) 0 7 (is_work s1)
                  ltac:(lia) ltac:(rewrite CB2; lia) ltac:(intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(cbn [ty_ok]; rewrite NC_lens_list by lia; split; [lia|]; split; [lia|]; apply lens_list_forall; intros i Hi; pose proof (HLs' i Hi); lia)
                  ltac:(lia) ltac:(lia) ltac:(cbn [it_room]; rewrite CB3; lia)) as TC.
    match goal with |- context [inflate_table CODES ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (inflate_table CODES a1 a2 a3 a4 a5 a6 a7) as [[[[retC tblC] nextC] lenbitsC] workC] end.
    destruct TC as [[TC5 TC6] TC].
    cbv beta iota. aflat. arun us_eq. aflat. arun ur_eq.
    acase CrC.
    { arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      - winv_split.
        + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
        + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
        + exact (proj2 HCm1).
        + exact I.
        + exact HWB1.
      - phi_goal. unfold PHIr in *. lia. }
    assert (RC0 : retC = 0) by (destruct (Z.eqb_spec retC 0); [assumption|discriminate CrC]).
    specialize (TC RC0). destruct TC as (TC1 & TC2 & TC3 & TC4). cbn [it_room] in TC2.
    aflat. arun us_eq. arun set_mode_eq.
    apply (POST_arm CODELENS (arm_CODELENS ivar_ref flush) _ _ _ _ arm_CODELENS_safe).
    - winv_split.
      + core_keep HC1; [rewrite HL19, CB1; reflexivity | rewrite TC6; reflexivity | rewrite TC5; reflexivity | apply CORE_length; exact HC1].
      + eapply REGS_cview; [apply REGS_ret; exact HR1|reflexivity|reflexivity].
      + split; [common_keep HCm1|]. split; [left; exact Hb1|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [intros i Hi; exfalso; lia|].
        cbn [cpok]. split; [lia|]. exists (nextC - 0). split; [lia|]. exact TC3.
      + exact HWF1.
      + exact HWB1.
    - reflexivity.
    - phi_norm E HP. unfold PHIr in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma arm_TABLE_safe : arm_safe TABLE (arm_TABLE ivar_ref flush).
  Proof.
    intros w0 s c r HW E HP. unfold arm_TABLE.
    pose proof HW as HW0. winv_open2 HW E HC HR. regs_open HR. destruct HMF as [HCm Hb14].
    pose proof (CORE_length s HC) as HL0.
    destruct (NEEDBITS_spec c 14 s r HR ltac:(lia)) as [(r1 & EQ & HR1 & HP1 & Hn1 & Hb1)|(r1 & EQ & HR1 & HP1 & Hb1 & Hh1)].
    2:{ eapply POST_bind_leave; [exact EQ|]. pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & _).
        apply (WINV_regs s c r r1 HW0 HR1 Eo1 Ep1). rewrite E. mred. intros _. split; [exact HCm|lia]. }
    eapply POST_bind_run; [exact EQ|]. cbv beta iota.
    pose proof (pulled_out r r1 HP1) as (Eo1 & Ep1 & El1 & _). pose proof (pulled_phi r r1 HP1) as PH1.
    pose proof HR1 as (_ & _ & _ & _ & _ & _ & [RB1 RHO1] & _).
    aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq.
    aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq.
    aflat. arun BITS_eq. aflat. arun us_eq. aflat. arun DROPBITS_eq.
    aflat. arun gs_eq. sacc.
    rewrite (wrap32_id (ir_bits r1 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5)) by lia. rewrite (wrap32_id (ir_bits r1 - 5 - 5 - 4)) by lia.
    rewrite !BITSv_mod by (repeat (try apply Z.shiftr_nonneg); lia).
    pose proof (mod_pow2_range (ir_hold r1) 5 ltac:(lia)) as M1.
    pose proof (mod_pow2_range (Z.shiftr (ir_hold r1) 5) 5 ltac:(lia)) as M2.
    pose proof (mod_pow2_range (Z.shiftr (Z.shiftr (ir_hold r1) 5) 5) 4 ltac:(lia)) as M3.
    match goal with |- POST _ (_ (mkW _ _ ?r4)) => set (r' := r4) in *; assert (HR' : REGS c r') end.
    { subst r'. apply REGS_holdbits; [apply REGS_holdbits; [apply REGS_holdbits; [exact HR1|]|]|].
      all: repeat (apply HB_drop); try (split; [exact RB1|exact RHO1]); lia. }
    acase Cbad.
    - arun set_msg_eq. rewrite set_mode_eq. apply POST_ARun.
      + winv_split.
        * core_keep HC. exact HL0.
        * eapply REGS_cview; [exact HR'|reflexivity|reflexivity].
        * exact (proj2 HCm).
        * exact I.
        * subst r'. sacc. rewrite Ep1. exact HWB.
      + phi_norm E HP. subst r'. sacc. lia.
    - apply Bool.orb_false_iff in Cbad as [C1 C2]. apply Z.ltb_ge in C1. apply Z.ltb_ge in C2.
      aflat. arun us_eq. arun set_mode_eq.
      apply (POST_arm LENLENS (arm_LENLENS ivar_ref flush) _ _ _ _ arm_LENLENS_safe).
      + winv_split.
        * core_keep HC. exact HL0.
        * exact HR'.
        * split; [common_keep HCm|]. subst r'. sacc. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          intros k Hk. exfalso. lia.
        * subst r'. sacc. rewrite Eo1. exact HWF.
        * subst r'. sacc. rewrite Ep1. exact HWB.
      + reflexivity.
      + phi_norm E HP. subst r'. sacc. lia.
  Qed.
End TableArms.
