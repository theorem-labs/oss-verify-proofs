From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandTac strncmp_c strcmp_c check_words_add_c.
Import ListNotations.
Open Scope Z_scope.

Ltac str_prem :=
  first [ assumption
        | apply notin_nul_lit; vm_compute; reflexivity
        | lazymatch goal with |- bytes_at _ _ (bv_unsigned (Z_to_bv 64 ?z)) _ =>
            change (bv_unsigned (Z_to_bv 64 z)) with z end;
          apply lit_at; [assumption | vm_compute; reflexivity | lia | cbn; lia] ].

Ltac replace_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Ltac strcmp_eq SC sv :=
  eapply evt_cut;
  [ eapply SC with (sx := sv) (sy := sv); str_prem
  | let ms' := fresh "ms'" in let rr := fresh "rr" in let x11 := fresh "x11" in
    let x12 := fresh "x12" in let x13 := fresh "x13" in let E := fresh "E" in let Hrr := fresh "Hrr" in
    intros ms' (rr & x11 & x12 & x13 & E & Hrr); subst ms';
    replace_ret;
    let RR0 := fresh "RR0" in
    assert (RR0 : rr = Z_to_bv 64 0) by (apply Hrr; reflexivity);
    subst rr; clear Hrr ].

Ltac add_tail SC FR ST sp sv2 sv3 :=
  zstep; zstep; zstep;
  let HNA := fresh "HNA" in if_cases HNA;
  [ exfalso; vm_compute in HNA; discriminate HNA
  | zstep; zstep; zstep;
    strcmp_eq SC sv2;
    zstep;
    let HZ2 := fresh "HZ2" in if_cases HZ2;
    [ exfalso; vm_compute in HZ2; discriminate HZ2
    | zstep; zstep; zstep;
      strcmp_eq SC sv3;
      zstep;
      let HZ3 := fresh "HZ3" in if_cases HZ3;
      [ exfalso; vm_compute in HZ3; discriminate HZ3
      | do 8 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish ] ] ].

Lemma bytes_eqb_false : forall a b, a <> b -> bytes_eqb a b = false.
Proof. intros a b H. destruct (bytes_eqb a b) eqn:E; [apply bytes_eqb_iff in E; contradiction | reflexivity]. Qed.

Ltac matched SC SGr FR ST sp r w3 w4 x2 x3 X2 X3 H3b HW4 MU IP ND F0 :=
  let XP := fresh "XP" in
  assert (XP : x2 = w3) by (rewrite X2; unfold add_placement; rewrite (proj2 (Z.ltb_lt 3 r)), IP by lia; reflexivity);
  let XN := fresh "XN" in
  assert (XN : add_next r w3 = 4) by (unfold add_next; rewrite <- X2, XP, ND; reflexivity);
  clear X2; subst x2;
  zstep;
  let RD := fresh "RD" in
  pose proof (bytes_at_read rsegs _ _ _ 0 1 H3b ltac:(lia) ltac:(rewrite length_app; cbn; lia)) as RD;
  change (skipn (Z.to_nat 0) (w3 ++ [NUL])) with (w3 ++ [NUL]) in RD; rewrite F0 in RD;
  lazymatch type of H3b with bytes_at _ _ (bv_unsigned ?p) _ =>
    rewrite (wa_of_var p (bv_unsigned p + 0) ltac:(lia)) in RD end;
  zstep; clear RD; zstep; zstep;
  let HD := fresh "HD" in if_cases HD;
  [ zstep;
    let HB := fresh "HB" in if_cases HB;
    [ zify_cond HB; try rewrite SGr in HB;
      let XC := fresh "XC" in
      assert (XC : x3 = S_DASH) by (rewrite X3; unfold add_client; rewrite XN, (proj2 (Z.ltb_ge 4 r)) by lia; reflexivity);
      clear X3; subst x3;
      zstep; zstep; add_tail SC FR ST sp w3 S_DASH
    | zify_cond HB; try rewrite SGr in HB;
      let XC := fresh "XC" in
      assert (XC : x3 = w4) by (rewrite X3; unfold add_client; rewrite XN, (proj2 (Z.ltb_lt 4 r)) by lia; reflexivity);
      clear X3; subst x3;
      let H4s := fresh "H4s" in let H4d := fresh "H4d" in let H4b := fresh "H4b" in
      let H4n := fresh "H4n" in let H4sd := fresh "H4sd" in
      destruct (HW4 ltac:(lia)) as (H4s & H4d & [H4b H4n] & H4sd);
      unfold outside_stack, disjoint_from in H4d, H4sd;
      lazymatch type of MU with munch ?W ?mA ?mB =>
        apply (bytes_at_transport rsegs W mA mB _ _) in H4s; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ];
        apply (bytes_at_transport rsegs W mA mB _ _) in H4b; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
      end;
      apply bytes_ro8 in H4s;
      do 4 zstep; add_tail SC FR ST sp w3 w4 ]
  | exfalso; vm_compute in HD; discriminate HD ].

Theorem check_words_add_holds : strcmp_contract -> strncmp_contract -> check_words_add_contract.
Proof.
  intros SC SNC. unfold strncmp_contract in SNC. unfold check_words_add_contract, CHECK_WORDS_ADD, CHECK_WORDS_ADD_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros r nargs p3 p4 q2 q3 w3 w4 x2 x3.
  intros MI ST LO IE RR HA2 HW3 HW4 RN HN HND HQ2 HQ3 N4 X2 X3.
  subst a2 nargs.
  destruct (HQ2 eq_refl) as (Q2s & Q2d & [Q2b Q2n] & Q2sd). clear HQ2.
  destruct (HQ3 eq_refl) as (Q3s & Q3d & [Q3b Q3n] & Q3sd). clear HQ3.
  unfold void_post, outside_stack, disjoint_from, CALL_NARGS, CALL_ARGS, IMG_END in *.
  apply bytes_ro4 in HN. apply bytes_ro8 in Q2s, Q3s.
  replace (bv_unsigned a0 + 8 + 16) with (bv_unsigned a0 + 24) in * by lia.
  replace (bv_unsigned a0 + 8 + 24) with (bv_unsigned a0 + 32) in * by lia.
  assert (SGr : bv_signed (Z_to_bv 64 r) = r).
  { rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec r (2^63)); lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  destruct (Z_le_gt_dec r 3) as [Rle|Rgt].
  - clear HW3 HW4.
    assert (XP : x2 = S_DASH).
    { rewrite X2. unfold add_placement. rewrite (proj2 (Z.ltb_ge 3 r)) by lia. reflexivity. }
    assert (XN : add_next r w3 = 3) by (unfold add_next; rewrite <- X2, XP; reflexivity).
    assert (XC : x3 = S_DASH).
    { rewrite X3. unfold add_client. rewrite XN, (proj2 (Z.ltb_ge 3 r)) by lia. reflexivity. }
    clear X2 X3. subst x2 x3.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 64%nat ST.
    do 14 zstep.
    zstep. if_cases HR.
    + zify_cond HR. rewrite SGr in HR.
      zstep. zstep.
      zstep. if_cases HD.
      * exfalso. vm_compute in HD. discriminate HD.
      * do 3 zstep.
        zstep. if_cases HB.
        -- zstep. zstep. add_tail SC FR ST sp S_DASH S_DASH.
        -- exfalso. zify_cond HB. change (bv_signed (Z_to_bv 64 (Z.b2z (0 <? 0) + 3))) with 3 in HB.
           rewrite SGr in HB. lia.
    + exfalso. zify_cond HR. rewrite SGr in HR. lia.
  - destruct (HW3 ltac:(lia)) as (H3s & H3d & [H3b H3n] & H3sd). clear HW3.
    apply bytes_ro8 in H3s. unfold outside_stack, disjoint_from in H3d, H3sd.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 64%nat ST.
    do 14 zstep.
    zstep. if_cases HR.
    + exfalso. zify_cond HR. rewrite SGr in HR. lia.
    + do 5 zstep.
      eapply evt_cut.
      { eapply SC with (sx := w3) (sy := S_OWN); str_prem. }
      intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'. replace_ret.
      zstep. if_cases HZ1.
      * zify_cond HZ1. apply bv0_iff, Hrr in HZ1.
        assert (IP : is_placement_b w3 = true) by (rewrite HZ1; reflexivity).
        assert (ND : bytes_eqb w3 S_DASH = false) by (rewrite HZ1; reflexivity).
        assert (F0 : firstn 1 (w3 ++ [NUL]) = [Z_to_bv 8 111]) by (rewrite HZ1; reflexivity).
        matched SC SGr FR ST sp r w3 w4 x2 x3 X2 X3 H3b HW4 MU IP ND F0.
      * zify_cond HZ1.
        assert (NO : w3 <> S_OWN) by (intros EO; apply Hrr in EO; subst rr; apply HZ1; reflexivity).
        clear Hrr.
        do 4 zstep.
        eapply evt_cut.
        { eapply SC with (sx := w3) (sy := S_DEFAULT); str_prem. }
        intros ms' (rr2 & y11 & y12 & y13 & E & Hrr). subst ms'. replace_ret.
        zstep. if_cases HZ2.
        -- zify_cond HZ2. apply bv0_iff, Hrr in HZ2.
           assert (IP : is_placement_b w3 = true) by (rewrite HZ2; reflexivity).
           assert (ND : bytes_eqb w3 S_DASH = false) by (rewrite HZ2; reflexivity).
           assert (F0 : firstn 1 (w3 ++ [NUL]) = [Z_to_bv 8 100]) by (rewrite HZ2; reflexivity).
           matched SC SGr FR ST sp r w3 w4 x2 x3 X2 X3 H3b HW4 MU IP ND F0.
        -- zify_cond HZ2.
           assert (NDf : w3 <> S_DEFAULT) by (intros ED; apply Hrr in ED; subst rr2; apply HZ2; reflexivity).
           clear Hrr.
           do 5 zstep.
           destruct (strncmp_prefix w3 S_POOL H3n ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(discriminate))
             as (v & Hv & Hv0).
           eapply evt_cut.
           { eapply SNC with (ls := w3 ++ [NUL]) (rs := S_POOL ++ [NUL]) (v := v).
             - exact H3b.
             - str_prem.
             - replace (bv_unsigned (Z_to_bv 64 5)) with (Z.of_nat (length S_POOL)) by reflexivity. exact Hv.
             - exact MI. }
           intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 &
                       E & MU1 & WM1 & MI1 & HB1 & HB2).
           subst ms'. clear HB1 HB2.
           lazymatch type of MU1 with munch _ ?mA ?mB => transport_after_call rsegs mA mB MU1 WM1 end.
           clear MU1 WM1 MI.
           replace_ret.
           pose proof (strncmp_model_range _ _ _ _ Hv) as VR.
           destruct (Z.eq_dec v 0) as [V0|VN].
           ++ subst v.
              assert (PF : firstn 5 w3 = S_POOL) by (apply Hv0; reflexivity).
              assert (IP : is_placement_b w3 = true).
              { unfold is_placement_b. apply orb_true_iff. right. apply prefixb_iff. exact PF. }
              assert (ND : bytes_eqb w3 S_DASH = false).
              { apply bytes_eqb_false. intros ED. rewrite ED in PF. apply (f_equal (@length byte)) in PF.
                vm_compute in PF. discriminate PF. }
              assert (F0 : firstn 1 (w3 ++ [NUL]) = [Z_to_bv 8 112]).
              { rewrite <- (firstn_skipn 5 w3), PF. reflexivity. }
              zstep. if_cases HZ3.
              ** exfalso. vm_compute in HZ3. discriminate HZ3.
              ** matched SC SGr FR ST sp r w3 w4 x2 x3 X2 X3 H3b HW4 MU IP ND F0.
           ++ zstep. if_cases HZ3.
              ** assert (PFn : prefixb w3 S_POOL = false).
                 { destruct (prefixb w3 S_POOL) eqn:PB; [|reflexivity]. exfalso. apply VN, Hv0, prefixb_iff, PB. }
                 assert (IPf : is_placement_b w3 = false).
                 { unfold is_placement_b. rewrite (bytes_eqb_false _ _ NO), (bytes_eqb_false _ _ NDf), PFn. reflexivity. }
                 assert (XP : x2 = S_DASH) by (rewrite X2; unfold add_placement; rewrite IPf, andb_false_r; reflexivity).
                 assert (XN : add_next r w3 = 3) by (unfold add_next; rewrite <- X2, XP; reflexivity).
                 assert (XC : x3 = w3) by (rewrite X3; unfold add_client; rewrite XN, (proj2 (Z.ltb_lt 3 r)) by lia; reflexivity).
                 clear X2 X3. subst x2 x3.
                 zstep. zstep. zstep. if_cases HD.
                 --- exfalso. vm_compute in HD. discriminate HD.
                 --- do 3 zstep. try change (Z.b2z (0 <? 0) + 3) with 3.
                     zstep. if_cases HB.
                     +++ exfalso. zify_cond HB. rewrite SGr in HB. lia.
                     +++ do 4 zstep. add_tail SC FR ST sp S_DASH w3.
              ** exfalso. zify_cond HZ3. destruct (Z_lt_le_dec v 0) as [Vn|Vp].
                 --- assert (M : v mod 18446744073709551616 = v + 18446744073709551616)
                       by (symmetry; apply Z.mod_unique with (-1); lia).
                     lia.
                 --- rewrite Z.mod_small in HZ3 by lia. lia.
Qed.
