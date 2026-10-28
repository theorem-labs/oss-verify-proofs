(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SeqExec EnframeArith.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib A_imsetv A_vsnp_num.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Ltac2 gd_tbl_AW_PfNum () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.B.A_vsnp_num.ndig"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "dig"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Walk.prefix_eq"; "Walk.pr_range"; "Walk.pr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.inside"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].


(* [comment removed for export] *)
Definition dig (base v n : Z) : Z := (v / base ^ n) mod base.

Lemma dig_bound : forall base v n, 2 <= base -> 0 <= dig base v n < base.
Proof. intros base v n Hb. unfold dig. apply Z.mod_pos_bound. lia. Qed.

Lemma dig_step : forall base v n, 2 <= base -> 0 <= v -> 0 <= n -> dig base (v / base) n = dig base v (n + 1).
Proof.
  intros base v n Hb Hv Hn. unfold dig. rewrite Z.pow_add_r, Z.pow_1_r by lia.
  rewrite (Z.mul_comm (base ^ n) base). rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ndig_top : forall base k v, 2 <= base -> 0 < v < base ^ Z.of_nat k -> dig base v (ndig base k v - 1) <> 0.
Proof.
  intros base k; induction k as [|k IH]; intros v Hb Hv.
  - change (base ^ Z.of_nat 0) with (base ^ 0) in Hv. rewrite Z.pow_0_r in Hv. lia.
  - cbn [ndig]. destruct (Z.ltb_spec0 v base) as [LT|GE].
    + unfold dig. change (1 - 1) with 0. rewrite Z.pow_0_r, Z.div_1_r, Z.mod_small by lia. lia.
    + rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia.
      assert (H : 0 < v / base < base ^ Z.of_nat k) by nia.
      specialize (IH (v / base) Hb H). pose proof (ndig_ge1 base k (v / base)).
      replace (1 + ndig base k (v / base) - 1) with (ndig base k (v / base) - 1 + 1) by lia.
      rewrite <- dig_step by lia. exact IH.
Qed.

Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j -> nth_error (upd l i x) j = nth_error l j.
Proof.
  intros X l; induction l as [|y l IH]; intros i j x Hij; [destruct i; reflexivity|].
  destruct i as [|i], j as [|j]; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma swrap32_id : forall v, -2^31 <= v < 2^31 -> bv_swrap 32 v = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (Z.of_N 32) with 32.
  change (2 ^ (32 - 1)) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma negw_neg : forall x, 0 <= x < 2^31 -> bv_swrap 32 (0 - (- x) mod 18446744073709551616) = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (Z.of_N 32) with 32.
  change (2 ^ (32 - 1)) with 2147483648. lia.
Qed.

Lemma u64s_repeat0 : forall k, u64s (repeat (Z_to_bv 64 0) k) = repeat (Z_to_bv 8 0) (8 * k).
Proof.
  induction k; [reflexivity|]. cbn [repeat u64s]. rewrite IHk. replace (8 * S k)%nat with (8 + 8 * k)%nat by lia.
  rewrite repeat_app. f_equal.
Qed.

Ltac ret_lit := lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma apn_dloopC : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pk,$0.Pj,$1.Pv,$1.Pbase,$1.PNB,$1.Pa2z,$1.Pws,(2.(3.&40.))Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))P,(6.(7.+2.R20.)(7.R20.+10.))P,(8.#1.R24.)P,(6.(7.=R23.)(9.R23.(:.R22.(;.R25.))))P,(9.R24.(:.+2.+40.))P,(7.=R26.)P,(7.(<.R27.(;.R28.))+1>.)P,(6.(7.(<.(=.(:.+2.+14.))(>.+8.(;.R29.)))R24.)(7.R24.(:.+2.+14.)))P,(?.$10.R8.R26.R24.)P,(11.$0.(12.(3.&40.)R25.)#1>.)P,(13.VCS,R28.+?0.)P,(9.=R29.)P,(9.(<.R2:.+?0.)(:.+2.+3?.))P,(14.$10.R=.)(15.$10.VAL,VCS,Lms',$16.(17.$1.LJ,$1.(17.(3.&40.)La3',(3.&40.)(17.(3.&40.)La4',(3.&40.)(17.(3.&40.)Ls5',(3.&40.)(17.(2.(3.&40.))Lws',(2.(3.&40.))(17.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(6.(11.$1.R6.(18.R34.R37.R35.))(6.(11.$16.R7.(19.(1:.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(1;.&40.(=.(<.R36.R6.)))(1;.&40.(1<.+1>.(<.R36.R6.)))(1;.&40.(1<.R32.(>.+8.R6.)))R5.R4.R25.R24.R23.R22.R21.(1;.&40.R34.)R3.(1;.&40.(<.R33.(>.+8.(<.R36.R6.))))R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(1;.&40.+7>214.)R16.(1=.(3.&40.))R1.(1>.$10.)))(6.(?.$10.R1.R33.R2.)(6.(11.$0.(12.(3.&40.)R2.)#1>.)(6.Pi,$1.P,(6.(7.R37.R1.)(9.R1.(<.R37.R7.)))(11.(5.(3.&40.))(1?.(3.&40.)R4.(20.R2.))(21.(3.&40.)(1;.&40.(22.R36.R37.(1<.R2.R38.)))))(6.Pi,$1.P,(7.=R1.)P,(23.(6.(7.R38.R2.)(9.R2.(<.R38.R8.))))(11.(5.(3.&40.))(1?.(3.&40.)R5.(20.R3.))(1?.(3.&40.)R34.(20.R3.)))(6.(24.(25.(26.$1.$1.)(27.$1.$1.R33.(<.R33.+?0.))(28.(26.$1.$1.)))R15.R1.)(6.(29.$10.R15.R1.)(14.$10.R1.)))))))))))))))(19.(1:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(1;.&40.(=.R2?.))(1;.&40.(1<.+1>.R2?.))(1;.&40.R2;.)R20.R1?.R1>.R1=.R1<.R1;.R1:.(1;.&40.R2=.)(1;.&40.R2>.)(1;.&40.(<.R2<.(>.+8.R2?.)))R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(1;.&40.+7>1>8.)R?.(1=.(3.&40.))R>.(1>.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros k. induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf). intros until m; intros Hb K1 Hv V64 Hj Hjk Ha2 ARR LEN CR NB0 NBH MI.
    al_facts.
    assert (SOK : store_ok asegs m (Z_to_bv 64 (NB + 8 * j)) 8 = true).
    { eapply (u64arr_store_ok asegs m NB ws j); [exact ARR | rewrite LEN; lia | unfold wa; f_equal; lia]. }
    (* [comment removed for export] *)
    zstep. if_falseU.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite ?(m_divu (Z_to_bv 64 v) (Z_to_bv 64 base)) by (rewrite unsigned_lit by lia; lia). unfold v_divu. rewrite ?unsigned_lit by lia.
    rewrite !swrap32_mod64 by lia.
    replace (- j + -1) with (- (j + 1)) by lia. replace (30 - j + -1) with (30 - (j + 1)) by lia.
    replace (NB + 8 * j + 8) with (NB + 8 * (j + 1)) by lia.
    rewrite ?(Z.mod_small (v / base * base)) by (clear - Hb Hv V64; nia).
    replace (v - v / base * base) with (dig base v 0) by (unfold dig; rewrite Z.pow_0_r, Z.div_1_r, Z.mod_eq by lia; lia).
    lazymatch goal with |- context [write_to_mem m _ (le8 ?w)] =>
      pose proof (u64arr_write asegs m NB ws j w ARR ltac:(rewrite LEN; lia)) as ARR1 end.
    replace (wa (NB + 8 * j)) with (Z_to_bv 64 (NB + 8 * j) : word) in ARR1 by reflexivity.
    set (m1 := write_to_mem m (Z_to_bv 64 (NB + 8 * j)) _) in *.
    assert (MU1 : munch [(NB, NB + 240)] m m1).
    { subst m1. change (Z_to_bv 64 (NB + 8 * j)) with (wa (NB + 8 * j)). apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; left; lia]. }
    assert (WM1 : wmono asegs m m1) by (subst m1; apply wmono_write; apply wmono_refl).
    assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    lazymatch type of ARR1 with u64arr _ _ _ ?wsx => set (ws1 := wsx) in *; assert (LEN1 : length ws1 = 30%nat) by (subst ws1; rewrite upd_length; exact LEN) end.
    assert (N1s : nth_error ws1 (Z.to_nat j) = Some (Z_to_bv 64 (dig base v 0))).
    { subst ws1. apply nth_error_upd_same. rewrite LEN. lia. }
    assert (N1o : forall i, 0 <= i -> i <> j -> nth_error ws1 (Z.to_nat i) = nth_error ws (Z.to_nat i)).
    { intros i Hi Hij. subst ws1. apply nth_error_upd_other. lia. }
    clearbody m1 ws1. clear SOK.
    destruct (Z_lt_le_dec v base) as [LT|GE].
    - (* [comment removed for export] *)
      if_falseU. apply evtA_done.
      exists 1. eexists _, _, _, ws1, m1. split.
      { destruct k; cbn [ndig]; [lia|]. destruct (Z.ltb_spec0 v base); [reflexivity | lia]. }
      split; [replace (a2z - 8 * 1) with (a2z + -8) by lia; reflexivity|].
      split; [exact ARR1|]. split; [exact LEN1|].
      split; [intros i Hi; replace i with j by lia; rewrite Z.sub_diag; exact N1s|].
      split; [intros i Hi Hn; apply N1o; lia|].
      split; [exact MU1|]. split; [exact WM1| exact MI1].
    - (* [comment removed for export] *)
      if_trueU.
      destruct k as [|k']; [lia|].
      assert (HV' : 0 <= v / base < base ^ Z.of_nat k').
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia. clear - Hv Hb GE. nia. }
      assert (K1' : (1 <= k')%nat).
      { destruct k'; [|lia]. exfalso. change (base ^ Z.of_nat 0) with (base ^ 0) in HV'. rewrite Z.pow_0_r in HV'. clear - HV' Hb GE. nia. }
      eapply (evtA_mono asegs AL CS).
      + replace (a2z + -8) with (a2z - 8) by lia.
        eapply (IH k' ltac:(lia) (j + 1) (v / base) base NB (a2z - 8) ws1); [exact Hb | exact K1' | exact HV' | ..]; try eassumption; try lia.
        all: try (apply Z.div_lt_upper_bound; [lia|]; clear - V64 Hb Hv; nia).
        all: try (clear - V64 Hb Hv GE; nia).
      + cbn beta. (intros ms' dd_H; ddestruct dd_H as (J & a3' & a4' & s5' & ws' & m' & HJ & -> & ARR' & LEN' & DG' & OT' & MU' & WM' & MI')).
        pose proof (ndig_ge1 base k' (v / base)) as J1. rewrite <- HJ in J1.
        exists (1 + J). eexists _, _, _, ws', m'. split.
        { cbn [ndig]. destruct (Z.ltb_spec0 v base); [lia|]. rewrite HJ. reflexivity. }
        split; [replace (j + (1 + J)) with (j + 1 + J) by lia; replace (a2z - 8 * (1 + J)) with (a2z - 8 - 8 * J) by lia; reflexivity|].
        split; [exact ARR'|]. split; [exact LEN'|].
        split.
        { intros i Hi. destruct (Z.eq_dec i j) as [->|NE].
          - rewrite OT' by lia. rewrite Z.sub_diag. exact N1s.
          - rewrite DG' by lia. replace (i - j) with (i - (j + 1) + 1) by lia. rewrite <- dig_step by lia. reflexivity. }
        split; [intros i Hi Hn; rewrite OT' by lia; apply N1o; lia|].
        split; [eapply munch_trans; [exact MU1 | exact MU']|]. split; [eapply wmono_trans; [exact WM1 | exact WM']| exact MI'].
  Qed.

  (* [comment removed for export] *)
  Definition pr (b : byte) : Prop := bv_unsigned b <> 0 /\ bv_unsigned b <> 27.
  Definition prefix_eq (bs bs' : list byte) (n : Z) : Prop := forall i, 0 <= i < n -> nth_error bs' (Z.to_nat i) = nth_error bs (Z.to_nat i).
  Definition pr_range (bs : list byte) (a b : Z) : Prop := forall i, a <= i < b -> exists x, nth_error bs (Z.to_nat i) = Some x /\ pr x.

  #[using="Type"] Lemma prefix_eq_refl : forall bs n, prefix_eq bs bs n. Proof. intros bs n i _. reflexivity. Qed.
  #[using="Type"] Lemma prefix_eq_trans : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pbs1,(2.(3.&8.))Pbs2,(2.(3.&8.))Pbs3,(2.(3.&8.))Pn1,$1.Pn2,$1.P,(2:.R5.R4.R2.)P,(2:.R5.R4.R2.)P,(7.R4.R3.)(2:.R8.R6.R5.)")
(* [comment removed for export] *).
  Proof. intros bs1 bs2 bs3 n1 n2 H1 H2 Hn i Hi. rewrite H2 by lia. apply H1. lia. Qed.
  #[using="Type"] Lemma prefix_eq_upd : forall bs n i b, n <= i -> prefix_eq bs (upd bs (Z.to_nat i) b) n.
  Proof. intros bs n i b Hn k Hk. apply nth_error_upd_other. lia. Qed.
  #[using="Type"] Lemma pr_range_prefix : forall bs bs' a b n, pr_range bs a b -> prefix_eq bs bs' n -> 0 <= a -> b <= n -> pr_range bs' a b.
  Proof. intros bs bs' a b n H1 H2 Ha Hb i Hi. rewrite H2 by lia. apply H1. lia. Qed.
  #[using="Type"] Lemma pr_range_snoc : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pbs,(2.(3.&8.))Pa,$1.Pi,$1.Pb,(3.&8.)P,(2;.R4.R3.R2.)P,(6.(7.=R4.)(7.R4.R3.))P,(9.R4.(;.(12.(3.&8.)R6.)))P,(2<.R4.)(2;.(2=.(3.&8.)R8.(20.R6.)R5.)R7.(<.R6.+1.))")
(* [comment removed for export] *).
  Proof.
    intros bs a i b H Ha Hi Hb k Hk. destruct (Z.eq_dec k i) as [->|NE].
    - exists b. split; [apply nth_error_upd_same; lia| exact Hb].
    - rewrite nth_error_upd_other by lia. apply H. lia.
  Qed.
  #[using="Type"] Lemma pr_range_empty : forall bs a, pr_range bs a a. Proof. intros bs a i Hi. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma out_store : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pm,P,(3.&40.)(5.(3.&8.))PBUF,$1.Pi,$1.Pbs,(2.(3.&8.))Pb,(3.&8.)P,(2>.$10.R5.R4.R2.)P,(6.(7.=R4.)(9.R4.(;.(12.(3.&8.)R3.))))P,(9.=R6.)P,(9.(<.R7.(;.(12.(3.&8.)R5.)))(:.+2.+3?.))P,(14.$10.R9.)(6.(11.$2?.(30.$10.R:.(1;.&40.(<.R9.R8.))#1.)$31.)(6.(2>.$10.(32.R:.(1;.&40.(<.R9.R8.))(25.(3.&8.)R6.(28.(3.&8.))))R9.(2=.(3.&8.)R7.(20.R8.)R6.))(6.(14.$10.(32.R:.(1;.&40.(<.R9.R8.))(25.(3.&8.)R6.(28.(3.&8.)))))(6.(29.$10.R:.(32.R:.(1;.&40.(<.R9.R8.))(25.(3.&8.)R6.(28.(3.&8.)))))PW,(2.$33.)Pm0,P,(3.&40.)(5.(3.&8.))P,(24.R2.R1.R<.)P,(34.R3.(<.R<.R;.)+1.)(24.R4.R3.(32.R>.(1;.&40.(<.R=.R<.))(25.(3.&8.)R:.(28.(3.&8.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros m BUF i bs b ARR Hi B0 BH MI.
    assert (SOK : store_ok asegs m (Z_to_bv 64 (BUF + i)) 1 = true) by (eapply (u8arr_store_ok asegs m BUF bs i); [exact ARR| lia| reflexivity]).
    split; [exact SOK|]. split; [exact (u8arr_write asegs m BUF bs i b ARR Hi)|].
    split; [apply mem_inv_store; [exact MI| exact SOK]|].
    split; [apply wmono_write; apply wmono_refl|].
    intros W m0 MU IN. change (Z_to_bv 64 (BUF + i)) with (wa (BUF + i)). apply munch_write; [exact MU| lia| cbn [length]; lia| exact IN].
  Qed.


  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma apn_padloop : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pn,$0.Pidx,$1.Pt,$1.Pnp,$1.PNB,$1.PCC,$1.PBUF,$1.Poff,$1.PE,$1.Ppz,$1.Pws,(2.(3.&40.))Pbs,(2.(3.&8.))Pw,(3.&40.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm0,P,(3.&40.)(5.(3.&8.))Pm,P,(3.&40.)(5.(3.&8.))P,(11.$1.(1<.R28.R27.)(;.R29.))P,(7.-1.R28.)P,(6.(7.=R2:.)(9.R2:.+1>.))P,(7.=R29.)P,(9.(<.R2:.R2<.)(:.+2.+14.))P,(6.(7.=R25.)(7.R25.+1.))P,(?.$10.R7.R2;.R25.)P,(11.$0.(12.(3.&40.)R26.)#1>.)P,(13.VCS,R2=.+?0.)P,(9.=R2>.)P,(7.(<.R2?.+?0.)R2>.)P,Pi,$1.P,(6.(9.R33.R1.)(7.R1.R34.))(11.(5.(3.&40.))(1?.(3.&40.)R2<.(20.R2.))(21.(3.&40.)(1;.&40.=)))P,P,(7.=R33.)(6.(11.(5.(3.&40.))(1?.(3.&40.)R2<.(20.R34.))(21.(3.&40.)R2:.))(23.(11.$1.(35.&40.R2:.)=)))P,(36.$10.R>.R31.(25.$37.(38.(1;.&40.(<.R30.R2?.)))(28.$37.)))P,(13.VCS,R32.+8.)P,(7.(<.R33.+8.)R32.)P,(2>.$10.R11.R33.R2>.)P,(13.VCS,R34.(;.(12.(3.&8.)R2?.)))P,(9.(<.R35.(;.(12.(3.&8.)R30.)))(:.+2.+3?.))P,(7.=R35.)P,(7.(<.(<.R37.R36.)(1<.R3<.R3;.))R35.)P,(7.R36.(<.R38.(;.(12.(3.&8.)R33.))))P,(24.(25.(26.$1.$1.)(27.$1.$1.R3;.(<.R3;.+?0.))(25.(26.$1.$1.)(27.$1.$1.R3:.(<.R3:.+8.))(25.(26.$1.$1.)(27.$1.$1.R39.(<.R39.(;.(12.(3.&8.)R34.))))(28.(26.$1.$1.)))))R18.R17.)P,(29.$10.R19.R18.)P,(14.$10.R19.)(15.$10.VAL,VCS,Lms',$16.(17.(3.&40.)La1',(3.&40.)(17.(3.&40.)La3',(3.&40.)(17.(3.&40.)La4',(3.&40.)(17.(3.&40.)Ls4',(3.&40.)(17.(3.&40.)Lpc',(3.&40.)(17.(2.(3.&8.))Lbs',(2.(3.&8.))(17.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(6.(11.$16.R8.(19.(1:.R3=.R3<.R3;.R3:.R39.R38.R37.(1;.&40.R42.)(1;.&40.R45.)R36.R7.(1;.&40.R46.)R6.R5.R33.R32.R31.R30.(1;.&40.R41.)R4.R2?.R2>.(1;.&40.(<.R47.(1<.R49.R48.)))R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.R3.R24.(1=.(3.&40.))R1.(1>.$10.)))(6.(39.(6.(7.=R48.)(6.(11.(3.&40.)R3.(1;.&40.+7>29<.))(6.(11.(3.&40.)R7.(1;.&40.R48.))(6.(11.(3.&40.)R4.(1;.&40.(<.R48.+1.)))(11.(3.&40.)R6.R3>.)))))(6.(11.$1.R48.-1.)(6.(11.(3.&40.)R3.(1;.&40.+7>2:<.))(11.(3.&40.)R4.(1;.&40.=)))))(6.(?.$10.R1.R46.R40.)(6.(36.$10.R1.R45.(25.$37.(38.(1;.&40.(<.(<.R44.R43.)(1<.R49.R48.))))(28.$37.)))(6.(2>.$10.R1.R44.R2.)(6.(11.$0.(12.(3.&8.)R2.)(12.(3.&8.)R3?.))(6.(2:.R3?.R2.R43.)(6.(2;.R2.R43.(<.R43.(1<.R49.R48.)))(6.(24.(25.(26.$1.$1.)(27.$1.$1.R46.(<.R46.+?0.))(25.(26.$1.$1.)(27.$1.$1.R45.(<.R45.+8.))(25.(26.$1.$1.)(27.$1.$1.R44.(<.R44.(;.(12.(3.&8.)R3?.))))(28.(26.$1.$1.)))))R23.R1.)(6.(29.$10.R23.R1.)(14.$10.R1.))))))))))))))))))(19.(1:.R35.R34.R33.R32.R31.R30.R2?.(1;.&40.R3:.)(1;.&40.R3=.)R2>.(1;.&40.R41.)(1;.&40.R3>.)R2=.R2<.R2;.R2:.R29.R28.(1;.&40.R39.)(1;.&40.(<.R41.+1.))R27.R26.(1;.&40.R3?.)R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(1;.&40.+7>270.)R1<.(1=.(3.&40.))R1:.(1>.$10.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until m; intros Hn Ht Hidx Hnp Hnpi Hpz ARR LEN CRN NB0 NBCC ZS TOP CCH CRC CCB OUT CRB BH OFF ROOM EH MU WM MI; al_facts.
    - (* [comment removed for export] *)
      assert (T0 : 0 <= t) by lia. destruct (TOP T0) as [TW TNZ]. replace idx with t in * by lia.
      pose proof (u64arr_read asegs m NB ws t w (Z_to_bv 64 (NB + 8 * t)) ARR TW T0 eq_refl) as RDW.
      zstep. zstep. replace (Z.shiftl t 3) with (8 * t) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep. if_trueU.
      apply evtA_done. eexists _, _, _, _, _, bs, m.
      rewrite Z.sub_diag, !Z.add_0_r. split; [reflexivity|].
      split; [left; repeat split; exact T0|].
      split; [exact ARR|]. split; [exact CCH|]. split; [exact OUT|]. split; [reflexivity|]. split; [apply prefix_eq_refl|]. split; [apply pr_range_empty|].
      split; [exact MU|]. split; [exact WM| exact MI].
    - assert (ZW : nth_error ws (Z.to_nat idx) = Some (Z_to_bv 64 0)) by (apply ZS; lia).
      pose proof (u64arr_read asegs m NB ws idx _ (Z_to_bv 64 (NB + 8 * idx)) ARR ZW ltac:(lia) eq_refl) as RDW.
      zstep. zstep. replace (Z.shiftl idx 3) with (8 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      zstep. zstep.
      zstep. zstep.
      if_falseU. zstep. zstep. zstep.
      assert (OFFL : off < Z.of_nat (length bs)) by lia.
      assert (LORC : Z.lor pz (Z.b2z (idx <? 1)) = 0 \/ Z.lor pz (Z.b2z (idx <? 1)) = 1).
      { assert (PZ : pz = 0 \/ pz = 1) by lia. destruct (idx <? 1); destruct PZ as [-> | ->]; vm_compute; auto. }
      destruct LORC as [EQ|EQ]; rewrite EQ; [if_trueU; zstep; set (ch := 32) | if_falseU; zstep; zstep; set (ch := 48)].
      all: assert (PRC : pr (Z_to_bv 8 ch)) by (subst ch; split; vm_compute; discriminate).
      all: ddestruct (out_store m BUF off bs (Z_to_bv 8 ch) OUT ltac:(lia) ltac:(lia) BH MI) as (SOK & OUT1 & MI1 & WM1 & MU1).
      all: zstep.
      all: replace (le1 (Z_to_bv 64 ch)) with [Z_to_bv 8 ch] by (subst ch; reflexivity).
      all: specialize (MU1 _ _ MU ltac:(cbn [inside]; right; right; left; lia)).
      all: apply (wmono_trans asegs _ _ _ WM) in WM1.
      all: apply (rw_cells_frame asegs m CC _ (BUF + off) [Z_to_bv 8 ch]) in CCH; [| lia | cbn [length]; lia | cbn; lia].
      all: apply (u64arr_frame asegs m NB ws (BUF + off) [Z_to_bv 8 ch]) in ARR; [| lia | cbn [length]; lia | rewrite LEN; cbn [length]; lia].
      all: change (wa (BUF + off)) with (Z_to_bv 64 (BUF + off)) in *.
      all: set (m1 := write_to_mem m (Z_to_bv 64 (BUF + off)) [Z_to_bv 8 ch]) in *; clearbody m1.
      all: clear SOK RDW.
      all: zstep.
      all: zstep.
      all: zstep.
      all: zstep.
      all: zstep.
      all: zstep.
      all: zstep.
      all: rewrite !swrap32_id by lia.
      all: replace (idx + 0) with idx by lia.
      all: assert (LEN1 : length (upd bs (Z.to_nat off) (Z_to_bv 8 ch)) = length bs) by apply upd_length.
      all: assert (PE1 : prefix_eq bs (upd bs (Z.to_nat off) (Z_to_bv 8 ch)) off) by (apply prefix_eq_upd; lia).
      all: assert (PR1 : pr_range (upd bs (Z.to_nat off) (Z_to_bv 8 ch)) off (off + 1)) by (apply pr_range_snoc; [apply pr_range_empty| lia| lia| exact PRC]).
      all: destruct (Z.eq_dec idx 0) as [I0|I0].
      1,3: subst idx; if_trueU; apply evtA_done; eexists _, _, _, _, _, _, m2; replace (0 - t) with 1 by lia; (split; [reflexivity|]);
           (split; [right; repeat split; first [lia | reflexivity]|]); (split; [exact ARR|]); (split; [exact CCH|]); (split; [exact OUT1|]); (split; [exact LEN1|]);
           (split; [exact PE1|]); (split; [exact PR1|]); (split; [exact MU1|]); (split; [exact WM1| exact MI1]).
      all: if_falseU.
      all: replace (Z_to_bv 64 idx) with (Z_to_bv 64 (idx + -1 + 1)) by (f_equal; lia).
      all: eapply (evtA_mono asegs AL CS); [eapply (IH (idx + -1) t (np + 1) NB CC BUF (off + 1) E pz ws _ w); try rewrite LEN1; try eassumption; try lia; try (intros i Hi; apply ZS; lia) | ].
      1,3: replace (BUF + (off + 1)) with (BUF + off + 1) by lia; exact CCH.
      all: cbn beta; (intros ms' dd_H; ddestruct dd_H as (a1' & a3' & a4' & s4' & pc' & bs' & m' & -> & EX & ARR' & CCH' & OUT' & LEN' & PE' & PR' & MU' & WM' & MI')).
      all: eexists a1', a3', a4', s4', pc', bs', m'.
      all: replace (np + 1 + (idx + -1 - t)) with (np + (idx - t)) by lia.
      all: split; [reflexivity|]. 
      all: split; [exact EX|]. 
      all: split; [exact ARR'|].
      all: split; [replace (BUF + off + (idx - t)) with (BUF + (off + 1) + (idx + -1 - t)) by lia; exact CCH'|].
      all: split; [exact OUT'|]. 
      all: split; [rewrite LEN'; exact LEN1|].
      all: split; [eapply prefix_eq_trans; [exact PE1| exact PE'| lia]|].
      all: split; [|split; [rewrite <- LEN1; exact MU'|split; [exact WM'| exact MI']]].
      all: intros i Hi; destruct (Z.eq_dec i off) as [->|NE]; [rewrite PE' by lia; apply PR1; lia| apply PR'; lia].
  Qed.

  #[using="Type"] Lemma u64arr_read4 : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pm,P,(3.&40.)(5.(3.&8.))PA,$1.Pws,(2.(3.&40.))Pi,$1.Pw,(3.&40.)Pa,(3.&40.)P,(?.$10.R6.R5.R4.)P,(11.(5.(3.&40.))(1?.(3.&40.)R5.(20.R4.))(21.(3.&40.)R3.))P,(7.=R5.)P,(11.(3.&40.)R4.(3:.(<.R8.(>.+8.R6.))))(11.(5.(2.(3.&8.)))(3;.$10.R:.R5.#4.)(21.(2.(3.&8.))(3<.R6.)))")
(* [comment removed for export] *).
  Proof.
    intros m A ws i w a [Hb _] Hn Hi ->.
    destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
    replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
    rewrite (bytes_at_ov_read asegs m A (u64s ws) (8 * Z.to_nat i) 4 Hb).
    2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite CellsX.le8_split4, <- app_assoc.
    rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
    rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
  Qed.

  #[using="Type"] Lemma le1_lit : forall x, 0 <= x < 2^64 -> le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
  Proof. intros x Hx. unfold le1. cbn [Z_to_le_bytes]. rewrite unsigned_lit by lia. reflexivity. Qed.

  #[using="Type"] Lemma hexdig_cases : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pd,$1.P,(6.(7.=R1.)(9.R1.+10.))(39.(11.$1.R2.=)(39.(11.$1.R2.+1.)(39.(11.$1.R2.+2.)(39.(11.$1.R2.+3.)(39.(11.$1.R2.+4.)(39.(11.$1.R2.+5.)(39.(11.$1.R2.+6.)(39.(11.$1.R2.+7.)(39.(11.$1.R2.+8.)(39.(11.$1.R2.+9.)(39.(11.$1.R2.+:.)(39.(11.$1.R2.+;.)(39.(11.$1.R2.+<.)(39.(11.$1.R2.+=.)(39.(11.$1.R2.+>.)(11.$1.R2.+?.))))))))))))))))")
(* [comment removed for export] *).
  Proof. intros; lia. Qed.
  #[using="Type"] Lemma hexdig_lt10 : forall d, 0 <= d < 16 -> (Z.land d 254 <? 10) = (d <? 10).
  Proof. intros d Hd. pose proof (hexdig_cases d Hd) as C. repeat (destruct C as [-> | C]; [reflexivity|]). subst d. reflexivity. Qed.
  #[using="Type"] Lemma hexdig_pr_lo : forall d, 0 <= d < 10 -> 0 <= Z.lor d 48 < 256 /\ pr (Z_to_bv 8 (Z.lor d 48)).
  Proof.
    intros d Hd. pose proof (hexdig_cases d ltac:(lia)) as C.
    repeat (destruct C as [-> | C]; [first [lia | split; [vm_compute; split; [discriminate| reflexivity] | split; vm_compute; discriminate]]|]). lia.
  Qed.
  #[using="Type"] Lemma hexdig_pr_hi : forall d lo, 10 <= d < 16 -> lo = 87 \/ lo = 55 -> pr (Z_to_bv 8 (lo + d)).
  Proof.
    intros d lo Hd Hlo. pose proof (hexdig_cases d ltac:(lia)) as C.
    repeat (destruct C as [-> | C]; [first [lia | destruct Hlo as [-> | ->]; split; vm_compute; discriminate]|]).
    subst d. destruct Hlo as [-> | ->]; split; vm_compute; discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma apn_emitloop : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pn,$0.Pi,$1.PNB,$1.PCC,$1.PBUF,$1.Poff,$1.PE,$1.Plo,$1.Pws,(2.(3.&40.))Pbs,(2.(3.&8.))Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa0,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm0,P,(3.&40.)(5.(3.&8.))Pm,P,(3.&40.)(5.(3.&8.))P,(11.$1.R25.(;.R26.))P,(9.R26.+1>.)P,(39.(11.$1.R21.+57.)(11.$1.R21.+37.))P,(?.$10.R4.R27.R21.)P,(11.$0.(12.(3.&40.)R22.)#1>.)P,(13.VCS,R29.+?0.)P,(9.=R2:.)P,(7.(<.R2;.+?0.)R2:.)P,Pk,$1.P,(6.(7.=R1.)(7.R1.R2>.))(17.$1.Ld,$1.(6.(11.(5.(3.&40.))(1?.(3.&40.)R29.(20.R3.))(21.(3.&40.)(1;.&40.R1.)))(6.(7.=R1.)(9.R1.+10.))))P,(36.$10.R:.R2<.(25.$37.(38.(1;.&40.(<.R2;.R2:.)))(28.$37.)))P,(13.VCS,R2=.+8.)P,(7.(<.R2>.+8.)R2=.)P,(2>.$10.R=.R2>.R29.)P,(13.VCS,R2?.(;.(12.(3.&8.)R2:.)))P,(9.(<.R30.(;.(12.(3.&8.)R2;.)))(:.+2.+3?.))P,(7.=R30.)P,(7.(<.(<.R32.R31.)(<.R35.+1.))R30.)P,(7.R31.(<.R33.(;.(12.(3.&8.)R2>.))))P,(24.(25.(26.$1.$1.)(27.$1.$1.R36.(<.R36.+?0.))(25.(26.$1.$1.)(27.$1.$1.R35.(<.R35.+8.))(25.(26.$1.$1.)(27.$1.$1.R34.(<.R34.(;.(12.(3.&8.)R2?.))))(28.(26.$1.$1.)))))R14.R13.)P,(29.$10.R15.R14.)P,(14.$10.R15.)(15.$10.VAL,VCS,Lms',$16.(17.(3.&40.)La3',(3.&40.)(17.(3.&40.)La4',(3.&40.)(17.(3.&40.)La6',(3.&40.)(17.(3.&40.)La7',(3.&40.)(17.(2.(3.&8.))Lbs',(2.(3.&8.))(17.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(6.(11.$16.R7.(19.(1:.R38.R37.R36.R35.R34.R33.R32.(1;.&40.R3<.)(1;.&40.R3?.)R31.(1;.&40.=)(1;.&40.R3;.)R6.R5.(1;.&40.+:.)R4.R3.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(1;.&40.+7>2?0.)R1?.(1=.(3.&40.))R1.(1>.$10.)))(6.(?.$10.R1.R40.R3:.)(6.(36.$10.R1.R3?.(25.$37.(38.(1;.&40.(<.(<.R3>.R3=.)(<.R41.+1.))))(28.$37.)))(6.(2>.$10.R1.R3>.R2.)(6.(11.$0.(12.(3.&8.)R2.)(12.(3.&8.)R39.))(6.(2:.R39.R2.R3=.)(6.(2;.R2.R3=.(<.R3=.(<.R41.+1.)))(6.(24.(25.(26.$1.$1.)(27.$1.$1.R40.(<.R40.+?0.))(25.(26.$1.$1.)(27.$1.$1.R3?.(<.R3?.+8.))(25.(26.$1.$1.)(27.$1.$1.R3>.(<.R3>.(;.(12.(3.&8.)R39.))))(28.(26.$1.$1.)))))R1>.R1.)(6.(29.$10.R1>.R1.)(14.$10.R1.))))))))))))))))(19.(1:.R31.R30.R2?.R2>.R2=.R2<.R2;.(1;.&40.R35.)(1;.&40.R38.)R2:.(1;.&40.(<.R3:.+1.))(1;.&40.R34.)(1;.&40.(<.R37.R36.))(1;.&40.(<.R39.(>.+8.R3:.)))(1;.&40.+:.)R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(1;.&40.+7>378.)R18.(1=.(3.&40.))R16.(1>.$10.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until m; intros Hn Hi Hlo ARR LEN CRN NB0 NBCC DG CCH CRC CCB OUT CRB BH OFF ROOM EH MU WM MI; al_facts.
    all: ddestruct (DG i ltac:(lia)) as (d & DW & DB).
    all: pose proof (u64arr_read4 m NB ws i _ (Z_to_bv 64 (NB + 8 * i)) ARR DW ltac:(lia) eq_refl) as RDW.
    all: zstep.
    all: if_falseU.
    all: zstep.
    all: rewrite sx32_small by lia.
    all: zstep.
    all: zstep.
    all: assert (CND : bv_ltu (Z_to_bv 64 (Z.land d 254)) (Z_to_bv 64 10) = (d <? 10)).
    1,3: (unfold bv_ltu; rewrite <- (hexdig_lt10 d DB); pose proof (hexdig_cases d DB) as C;
          repeat (destruct C as [-> | C]; [reflexivity|]); subst d; reflexivity).
    all: rewrite CND; clear CND.
    all: assert (OFFL : off < Z.of_nat (length bs)) by lia.
    all: destruct (Z_lt_le_dec d 10) as [DLT|DGE].
    1,3: replace (d <? 10) with true by (symmetry; apply Z.ltb_lt; exact DLT); cbn [negb]; cbv iota; zstep; zstep;
         destruct (hexdig_pr_lo d ltac:(lia)) as [CHB PRC]; set (ch := Z.lor d 48) in *.
    3,4: replace (d <? 10) with false by (symmetry; apply Z.ltb_ge; exact DGE); cbn [negb]; cbv iota; zstep;
         pose proof (hexdig_pr_hi d lo ltac:(lia) Hlo) as PRC; assert (CHB : 0 <= lo + d < 256) by lia; set (ch := lo + d) in *.
    all: ddestruct (out_store m BUF off bs (Z_to_bv 8 ch) OUT ltac:(lia) ltac:(lia) BH MI) as (SOK & OUT1 & MI1 & WM1 & MU1).
    all: zstep.
    all: rewrite (le1_lit ch) by lia.
    all: specialize (MU1 _ _ MU ltac:(cbn [inside]; right; right; left; lia)).
    all: apply (wmono_trans asegs _ _ _ WM) in WM1.
    all: apply (rw_cells_frame asegs m CC _ (BUF + off) [Z_to_bv 8 ch]) in CCH; [| lia | cbn [length]; lia | cbn; lia].
    all: apply (u64arr_frame asegs m NB ws (BUF + off) [Z_to_bv 8 ch]) in ARR; [| lia | cbn [length]; lia | rewrite LEN; cbn [length]; lia].
    all: change (wa (BUF + off)) with (Z_to_bv 64 (BUF + off)) in *.
    all: set (m1 := write_to_mem m (Z_to_bv 64 (BUF + off)) [Z_to_bv 8 ch]) in *; clearbody m1.
    all: clear SOK RDW.
    all: zstep.
    all: zstep.
    all: zstep.
    all: zstep.
    all: zstep.
    all: zstep.
    all: assert (LEN1 : length (upd bs (Z.to_nat off) (Z_to_bv 8 ch)) = length bs) by apply upd_length.
    all: assert (PE1 : prefix_eq bs (upd bs (Z.to_nat off) (Z_to_bv 8 ch)) off) by (apply prefix_eq_upd; lia).
    all: assert (PR1 : pr_range (upd bs (Z.to_nat off) (Z_to_bv 8 ch)) off (off + 1)) by (apply pr_range_snoc; [apply pr_range_empty| lia| lia| exact PRC]).
    1,3: assert (I0 : i = 0) by lia; subst i; if_trueU; apply evtA_done; eexists _, _, _, _, _, m2; (split; [reflexivity|]);
         (split; [exact ARR|]); (split; [exact CCH|]); (split; [exact OUT1|]); (split; [exact LEN1|]);
         (split; [exact PE1|]); (split; [exact PR1|]); (split; [exact MU1|]); (split; [exact WM1| exact MI1]).
    all: rewrite bv_lts_zero_l, unsigned_lit by lia; replace ((0 <? i) && (i <? 2 ^ 63))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia); cbn [negb]; cbv iota.
    all: replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + -1 + 1)) by (f_equal; lia).
    all: replace (NB + 8 * i + -8) with (NB + 8 * (i + -1)) by lia.
    all: replace (BUF + off + 1) with (BUF + (off + 1)) in * by lia.
    all: eapply (evtA_mono asegs AL CS); [eapply (IH (i + -1) NB CC BUF (off + 1) E lo ws _); try rewrite LEN1; try eassumption; try lia; try (intros k Hk; apply DG; lia) | ].
    all: cbn beta; (intros ms' dd_H; ddestruct dd_H as (a3' & a4' & a6' & a7' & bs' & m' & -> & ARR' & CCH' & OUT' & LEN' & PE' & PR' & MU' & WM' & MI')).
    all: eexists a3', a4', a6', a7', bs', m'.
    all: split; [reflexivity|]. 
    all: split; [exact ARR'|].
    all: split; [replace (BUF + off + (i + 1)) with (BUF + (off + 1) + (i + -1 + 1)) by lia; exact CCH'|].
    all: split; [exact OUT'|]. 
    all: split; [rewrite LEN'; exact LEN1|].
    all: split; [eapply prefix_eq_trans; [exact PE1| exact PE'| lia]|].
    all: split; [|split; [rewrite <- LEN1; exact MU'|split; [exact WM'| exact MI']]].
    all: intros k Hk; destruct (Z.eq_dec k off) as [->|NE]; [rewrite PE' by lia; apply PR1; lia| apply PR'; lia].
  Qed.

  #[using="Type"] Lemma u64arr_app : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pm,P,(3.&40.)(5.(3.&8.))PA,$1.Pl1,(2.(3.&40.))Pl2,(2.(3.&40.))(3=.(?.$10.R4.R3.(3>.(3.&40.)R2.R1.))(6.(?.$10.R4.R3.R2.)(?.$10.R4.(<.R3.(>.+8.(;.(12.(3.&40.)R2.))))R1.)))")
(* [comment removed for export] *).
  Proof.
    intros m A l1 l2. unfold u64arr. rewrite u64s_app, app_length.
    pose proof (bytes_at_app asegs m A (u64s l1) (u64s l2)) as BA. rewrite u64s_length in BA.
    replace (A + Z.of_nat (8 * length l1)) with (A + 8 * Z.of_nat (length l1)) in BA by lia.
    replace (8 * Z.of_nat (length l1 + length l2)) with (8 * Z.of_nat (length l1) + 8 * Z.of_nat (length l2)) by lia.
    rewrite (CellsX.wr_at_app asegs m A (8 * Z.of_nat (length l1)) (8 * Z.of_nat (length l2))) by lia.
    tauto.
  Qed.
  #[using="Type"] Lemma u64arr_u8arr : forall m A ws, u64arr asegs m A ws <-> u8arr asegs m A (u64s ws).
  Proof. intros m A ws. unfold u64arr, u8arr. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. tauto. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma nb_zero_pre : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pm,P,(3.&40.)(5.(3.&8.))PNB,$1.Pws,(2.(3.&40.))PJ,$1.Pml,$1.P,(?.$10.R5.R4.R3.)P,(11.$0.(12.(3.&40.)R4.)#1>.)P,(7.=R4.)P,(9.R5.R4.)P,(7.R5.+1>.)(17.(2.(3.&8.))Lds,(2.(3.&8.))(6.(2>.$10.R;.(<.R:.(>.+8.R8.))R1.)(11.$1.(;.(12.(3.&8.)R1.))(>.+8.(1<.R7.R8.)))))")
(* [comment removed for export] *).
  Proof.
    intros m NB ws J ml ARR LEN HJ HJm Hml.
    rewrite <- (firstn_skipn (Z.to_nat J) ws) in ARR. apply u64arr_app in ARR. destruct ARR as [_ ARR].
    rewrite <- (firstn_skipn (Z.to_nat (ml - J)) (skipn (Z.to_nat J) ws)) in ARR. apply u64arr_app in ARR. destruct ARR as [ARR _].
    rewrite length_firstn, LEN in ARR. replace (NB + 8 * Z.of_nat (Nat.min (Z.to_nat J) 30)) with (NB + 8 * J) in ARR by lia.
    apply u64arr_u8arr in ARR. eexists. split; [exact ARR|].
    rewrite u64s_length, length_firstn, length_skipn, LEN. lia.
  Qed.

  #[using="Type"] Lemma nb_zero_post : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pm,P,(3.&40.)(5.(3.&8.))Pm',P,(3.&40.)(5.(3.&8.))PNB,$1.Pws,(2.(3.&40.))PJ,$1.Pml,$1.P,(?.$10.R6.R4.R3.)P,(11.$0.(12.(3.&40.)R4.)#1>.)P,(7.=R4.)P,(9.R5.R4.)P,(7.R5.+1>.)P,(7.=R9.)P,(24.(25.(26.$1.$1.)(27.$1.$1.(<.R:.(>.+8.R8.))(<.(<.R:.(>.+8.R8.))(>.+8.(1<.R7.R8.))))(28.(26.$1.$1.)))R<.R;.)P,(29.$10.R=.R<.)P,(2>.$10.R=.(<.R<.(>.+8.R:.))(3?.(3.&8.)(1;.&8.=)(20.(>.+8.(1<.R9.R:.)))))(17.(2.(3.&40.))Lws2,(2.(3.&40.))(6.(?.$10.R?.R>.R1.)(6.(11.$0.(12.(3.&40.)R1.)#1>.)(6.Pi,$1.P,(6.(7.=R1.)(9.R1.R=.))(11.(5.(3.&40.))(1?.(3.&40.)R3.(20.R2.))(1?.(3.&40.)R?.(20.R2.)))Pi,$1.P,(6.(7.R=.R1.)(9.R1.R<.))(11.(5.(3.&40.))(1?.(3.&40.)R3.(20.R2.))(21.(3.&40.)(1;.&40.=)))))))")
(* [comment removed for export] *).
  Proof.
    intros m m' NB ws J ml ARR LEN HJ HJm Hml NB0 MU WM Z8.
    set (A := firstn (Z.to_nat J) ws). set (C := skipn (Z.to_nat (ml - J)) (skipn (Z.to_nat J) ws)).
    assert (LA : length A = Z.to_nat J) by (unfold A; rewrite length_firstn, LEN; lia).
    assert (LC : length C = Z.to_nat (30 - ml)) by (unfold C; rewrite !length_skipn, LEN; lia).
    pose proof ARR as ARR0.
    rewrite <- (firstn_skipn (Z.to_nat J) ws) in ARR. apply u64arr_app in ARR. destruct ARR as [ARRA ARR]. fold A in ARRA.
    rewrite <- (firstn_skipn (Z.to_nat (ml - J)) (skipn (Z.to_nat J) ws)) in ARR. apply u64arr_app in ARR. destruct ARR as [_ ARRC]. fold C in ARRC.
    rewrite length_firstn, LEN in ARRC. rewrite length_firstn, length_skipn, LEN in ARRC. fold A in ARRC.
    replace (NB + 8 * Z.of_nat (Nat.min (Z.to_nat J) 30) + 8 * Z.of_nat (Nat.min (Z.to_nat (ml - J)) (30 - Z.to_nat J))) with (NB + 8 * ml) in ARRC by lia.
    pose proof (u64arr_bound asegs m NB ws ARR0) as BND. rewrite LEN in BND.
    apply (u64arr_transport asegs [(NB + 8 * J, NB + 8 * J + 8 * (ml - J))] m m' NB A) in ARRA; [| exact MU | exact WM | cbn [disjoint_from]; rewrite LA; split; [lia| exact I]].
    apply (u64arr_transport asegs [(NB + 8 * J, NB + 8 * J + 8 * (ml - J))] m m' (NB + 8 * ml) C) in ARRC; [| exact MU | exact WM | cbn [disjoint_from]; rewrite LC; split; [lia| exact I]].
    assert (ARRZ : u64arr asegs m' (NB + 8 * J) (repeat (Z_to_bv 64 0) (Z.to_nat (ml - J)))).
    { apply u64arr_u8arr. rewrite u64s_repeat0. replace (8 * Z.to_nat (ml - J))%nat with (Z.to_nat (8 * (ml - J))) by lia. exact Z8. }
    exists (A ++ repeat (Z_to_bv 64 0) (Z.to_nat (ml - J)) ++ C).
    split. { apply u64arr_app. split; [exact ARRA|]. rewrite LA. replace (NB + 8 * Z.of_nat (Z.to_nat J)) with (NB + 8 * J) by lia.
             apply u64arr_app. split; [exact ARRZ|]. rewrite repeat_length. replace (NB + 8 * J + 8 * Z.of_nat (Z.to_nat (ml - J))) with (NB + 8 * ml) by lia. exact ARRC. }
    split. { rewrite !length_app, repeat_length, LA, LC. lia. }
    split.
    - intros i Hi. rewrite nth_error_app1 by lia. unfold A. rewrite nth_error_firstn. replace (Z.to_nat i <? Z.to_nat J)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
    - intros i Hi. rewrite nth_error_app2 by lia. rewrite nth_error_app1 by (rewrite repeat_length; lia).
      apply nth_error_repeat. rewrite LA. lia.
  Qed.

  #[using="Type"] Lemma stk_release_u64 : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pm,P,(3.&40.)(5.(3.&8.))Plo,$1.PA,$1.Pws,(2.(3.&40.))P,(40.$10.R4.R3.R2.)P,(?.$10.R5.R3.R2.)P,(7.R5.R4.)(40.$10.R7.R6.(<.R5.(>.+8.(;.(12.(3.&40.)R4.)))))")
(* [comment removed for export] *).
  Proof.
    intros m lo A ws ST ARR Hle. apply u64arr_u8arr in ARR. apply rw_cells_of_u8arr in ARR.
    pose proof (stk_release asegs m lo A _ ST ARR Hle) as H. cbn [cells_size csize] in H. rewrite u64s_length, Nat.add_0_r in H.
    replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) in H by lia. exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem apn_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfNum ()) "Pv,$1.Pbase,$1.Pml,$1.Ppz,$1.Pup,$1.PSPA,$1.Plo,$1.PCC,$1.PBUF,$1.Poff,$1.PE,$1.Pbs,(2.(3.&8.))Pra,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))P,(6.(7.=R25.)(9.R25.(:.+2.+40.)))P,(39.(11.$1.R25.+:.)(11.$1.R25.+10.))P,(6.(7.=R25.)(9.R25.+1>.))P,(6.(7.=R25.)(7.R25.+1.))P,(6.(7.=R25.)(7.R25.+1.))P,(40.$10.R6.R24.R25.)P,(7.+65?000.R25.)P,(7.R26.(1<.R27.+150.))P,(7.R28.R26.)P,(13.VCS,R28.(1<.R29.R28.))P,(36.$10.R;.R28.(25.$37.(38.(1;.&40.(<.R27.R26.)))(28.$37.)))P,(13.VCS,R29.+8.)P,(7.(<.R2:.+8.)R29.)P,(2>.$10.R>.R2:.R27.)P,(13.VCS,R2;.(;.(12.(3.&8.)R28.)))P,(9.(<.R2<.(;.(12.(3.&8.)R29.)))(:.+2.+3?.))P,(7.=R2<.)P,(7.(<.(<.R2>.R2=.)(41.(18.R35.#14.R36.)R34.))R2<.)P,(7.R2=.(<.R2?.(;.(12.(3.&8.)R2<.))))P,(14.$10.R14.)(15.$10.VAL,VCS,Lms',$16.(17.(3.&40.)La1',(3.&40.)(17.(3.&40.)La2',(3.&40.)(17.(3.&40.)La3',(3.&40.)(17.(3.&40.)La4',(3.&40.)(17.(3.&40.)La5',(3.&40.)(17.(3.&40.)La6',(3.&40.)(17.(3.&40.)La7',(3.&40.)(17.(2.(3.&8.))Lbs',(2.(3.&8.))(17.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(6.(11.$16.R:.(19.(1:.R37.(1;.&40.R3>.)R36.R35.R34.R33.R32.R31.R30.(1;.&40.(41.(18.R42.#14.R43.)R41.))R9.R8.R7.R6.R5.R4.R3.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R21.(42.R37.)R20.(1=.(3.&40.))R1.(1>.$10.)))(6.(40.$10.R1.R3=.R3>.)(6.(36.$10.R1.R3<.(25.$37.(38.(1;.&40.(<.(<.R3;.R3:.)(41.(18.R42.#14.R43.)R41.))))(28.$37.)))(6.(2>.$10.R1.R3;.R2.)(6.(11.$0.(12.(3.&8.)R2.)(12.(3.&8.)R38.))(6.(2:.R38.R2.R3:.)(6.(2;.R2.R3:.(<.R3:.(41.(18.R42.#14.R43.)R41.)))(6.(24.(25.(26.$1.$1.)(27.$1.$1.R3=.R3>.)(25.(26.$1.$1.)(27.$1.$1.R3<.(<.R3<.+8.))(25.(26.$1.$1.)(27.$1.$1.R3;.(<.R3;.(;.(12.(3.&8.)R38.))))(28.(26.$1.$1.)))))R1?.R1.)(6.(29.$10.R1?.R1.)(14.$10.R1.)))))))))))))))))))(19.(1:.R2=.(1;.&40.R34.)R2<.R2;.R2:.R29.R28.R27.R26.(1;.&40.R32.)(1;.&40.R2?.)(1;.&40.R39.)(1;.&40.R38.)(1;.&40.R37.)(1;.&40.R36.)(1;.&40.=)(1;.&40.R35.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(1;.&40.+7>118.)R16.(1=.(3.&40.))R15.(1>.$10.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros Hv Hbase Hml Hpz Hup ST LOIMG SPL SPCC SCS CCH CRC CCB OUT CRB BH OFF ROOM EH MI. al_facts.
    pose proof (munch_refl [(lo, SPA); (CC, CC + 8); (BUF, BUF + Z.of_nat (length bs))] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ndig_ge1 base 20 v) as J1.
    assert (J20 : ndig base 20 v <= 20). { pose proof (ndig_le base 20 v ltac:(lia)) as H. change (Z.max 1 (Z.of_nat 20)) with 20 in H. apply H. destruct Hbase as [-> | ->]; lia. }
    set (J := ndig base 20 v) in *. set (L := Z.max J ml) in *.
    carve_frame 336%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. 
    (* [comment removed for export] *)
    eapply (evtA_cut asegs AL CS).
    { destruct Hbase as [Hb|Hb]; destruct (Z.eq_dec v 0) as [V0|V0].
      - zstep. if_trueU. zstep. if_trueU. zstep. if_falseU. zstep. zstep. apply evtA_done. refine (eq_refl : (fun ms' => ms' = _) _).
      - zstep. if_trueU. zstep. if_trueU. zstep. if_trueU. zstep. apply evtA_done. reflexivity.
      - zstep. if_falseU. zstep. zstep. if_falseU. zstep. if_falseU. zstep. zstep. if_falseU. zstep. zstep. apply evtA_done. reflexivity.
      - zstep. if_falseU. zstep. zstep. if_falseU. zstep. if_falseU. zstep. zstep. if_trueU. zstep. apply evtA_done. reflexivity. }
    cbn beta. intros ms' ->.
    zstep. if_falseU. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply (evtA_cut asegs AL CS).
    { destruct (Z.eq_dec pz 0) as [P0|P0]; [if_trueU | if_falseU; zstep]; apply evtA_done; [refine (eq_refl : (fun ms' => ms' = _) _) | reflexivity]. }
    cbn beta. intros ms' ->.
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ ?cs => split_for_access FR asegs m0 (SPA + -336) cs 8%nat 240%nat end.
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: CB 240 ?X :: ?rest) =>
      set (nb0 := X) in *;
      ddestruct (CellsX.rw_cells_split3 asegs m0 (SPA + -336) [c1] [CB 240 nb0] rest FR) as (FR0 & FRN & FR1); clear FR end.
    cbn [cells_size csize Nat.add] in FRN, FR1.
    replace (SPA + -336 + Z.of_nat 8) with (SPA + -328) in * by lia. replace (SPA + -328 + Z.of_nat 240) with (SPA + -88) in * by lia.
    assert (NBL : length nb0 = 240%nat). { destruct FRN as [[WF _] _]. cbn in WF. destruct WF as [WF _]. exact WF. }
    apply u8arr_of_rw_cells in FRN.
    set (NB := SPA + -328) in *.
    eapply (evtA_cut asegs AL CS).
    { eapply (imsetv_spec AL IMG ALWF CS CSOK) with (P := NB) (n := 240) (b := Z_to_bv 8 170) (ds := nb0); try eassumption; try reflexivity; try lia.
      intros x Hx. apply SCS. unfold NB in Hx. lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a1' & a3' & m1 & -> & MU1 & WM1 & MI1 & NBA)).
    transport_after_call asegs m0 m1 MU1 WM1. clear MU1 WM1.
    assert (NBW : u64arr asegs m1 NB (repeat (Z_to_bv 64 0xaaaaaaaaaaaaaaaa) 30)).
    { apply u64arr_u8arr.
      replace (u64s (repeat (Z_to_bv 64 0xaaaaaaaaaaaaaaaa) 30)) with (repeat (Z_to_bv 8 170) (Z.to_nat 240)); [exact NBA|].
      apply list_bv_eq. vm_compute. reflexivity. }
    clear NBA. ret_lit. rewrite Z.land_0_r, Z.sub_0_r.
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z.land ml 255) with ml by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    replace (Z.shiftl ml 3) with (8 * ml) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (Z_to_bv 64 NB) with (Z_to_bv 64 (NB + 8 * 0)) by (f_equal; lia).
    eapply (evtA_cut asegs AL CS).
    { eapply (apn_dloopC 20 0 v base NB (8 * ml) (repeat (Z_to_bv 64 0xaaaaaaaaaaaaaaaa) 30)); try eassumption; try reflexivity; try lia.
      intros x Hx. apply SCS. unfold NB in Hx. lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (J' & a3d & a4d & s5d & ws1 & m2 & HJ & -> & NBW1 & LEN1 & DG1 & OT1 & MU2 & WM2 & MI2)).
    fold J in HJ. subst J'.
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
    zstep. zstep.
    replace (0 + J) with J in * by lia. rewrite negw_neg by lia.
    eapply (evtA_cut asegs AL CS) with (P := fun ms' => exists (ra' a3' : word) (j0 : list byte) (ws2 : list word) (m3 : mem),
       ms' = MS (mkR ra' (Z_to_bv 64 (SPA + -336)) gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 CC) (Z_to_bv 64 L) (Z_to_bv 64 (L - 1)) (Z_to_bv 64 NB) a3' a4d
                     (Z_to_bv 64 pz) (Z_to_bv 64 0) (Z_to_bv 64 up) (Z_to_bv 64 up) (Z_to_bv 64 pz) (Z_to_bv 64 L) s5d (Z_to_bv 64 (NB + 8 * J))
                     (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 ml) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x7e270) fc None m3 (seg_rom asegs)
       /\ u64arr asegs m3 NB ws2 /\ length ws2 = 30%nat
       /\ (forall i, 0 <= i < J -> nth_error ws2 (Z.to_nat i) = Some (Z_to_bv 64 (dig base v i)))
       /\ (forall i, J <= i < L -> nth_error ws2 (Z.to_nat i) = Some (Z_to_bv 64 0))
       /\ rw_cells asegs m3 CC [C8 (Z_to_bv 64 (BUF + off))] /\ u8arr asegs m3 BUF bs /\ stk asegs m3 lo (SPA + -336)
       /\ rw_cells asegs m3 (SPA + -336) [CB 8 j0] /\ rw_cells asegs m3 (SPA + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ munch [(lo, SPA); (CC, CC + 8); (BUF, BUF + Z.of_nat (length bs))] m m3 /\ wmono asegs m m3 /\ mem_inv asegs m3).
    { destruct (Z_lt_le_dec J ml) as [JLT|JGE].
      2:{ (* [comment removed for export] *)
          if_trueU. zstep. zstep.
          rewrite zb_lxor_ones by (apply Z.mod_pos_bound; lia).
          replace (18446744073709551615 - - J mod 18446744073709551616) with (J - 1) by lia.
          assert (LJ : L = J) by (unfold L; lia).
          destruct (Z.eq_dec J ml) as [JE|JNE]; [if_falseU; zstep | if_trueU].
          all: zstep; zstep; zstep.
          all: rewrite swrap32_id by lia; rewrite ?Z.add_0_l; rewrite <- ?JE; apply evtA_done; rewrite LJ.
          all: eexists _, _, _, ws1, m2; split; [reflexivity|].
          all: split; [exact NBW1|]; split; [exact LEN1|]; split; [intros i Hi; rewrite DG1 by lia; rewrite Z.sub_0_r; reflexivity|]; split; [intros i Hi; lia|].
          all: split; [exact CCH|]; split; [exact OUT|]; split; [exact ST|]; split; [exact FR0|]; split; [exact FR1|]; split; [exact MU|]; split; [exact WM| exact MI2]. }
      (* [comment removed for export] *)
      if_falseU. zstep. zstep. zstep.
      ddestruct (nb_zero_pre m2 NB ws1 J ml NBW1 LEN1 ltac:(lia) JLT ltac:(lia)) as (ds & DSA & DSL).
      replace (8 * ml - 8 * J) with (8 * (ml - J)) by lia.
      eapply (evtA_cut asegs AL CS).
      { eapply (imsetv_spec AL IMG ALWF CS CSOK) with (P := NB + 8 * J) (n := 8 * (ml - J)) (b := Z_to_bv 8 0) (ds := ds); try eassumption; try reflexivity; try (unfold NB; lia).
        intros x Hx. apply SCS. unfold NB in Hx. lia. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a1z & a3z & m3 & -> & MU3 & WM3 & MI3 & Z8)).
      ddestruct (nb_zero_post m2 m3 NB ws1 J ml NBW1 LEN1 ltac:(lia) JLT ltac:(lia) ltac:(unfold NB; lia) MU3 WM3 Z8) as (ws2 & NBW2 & LEN2 & DG2 & ZR2).
      clear NBW1 Z8 DSA.
      transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.
      ret_lit. zstep. zstep.
      if_trueU. zstep. zstep. zstep. zstep.
      assert (LJ : L = ml) by (unfold L; lia).
      rewrite !swrap32_id by lia. rewrite ?Z.add_0_l. apply evtA_done. rewrite LJ.
      eexists _, _, _, ws2, m3. split; [reflexivity|].
      split; [exact NBW2|]. split; [exact LEN2|]. split; [intros i Hi; rewrite DG2 by lia; rewrite DG1 by lia; rewrite Z.sub_0_r; reflexivity|]. split; [exact ZR2|].
      split; [exact CCH|]. split; [exact OUT|]. split; [exact ST|]. split; [exact FR0|]. split; [exact FR1|]. split; [exact MU|]. split; [exact WM| exact MI3]. }
    cbn beta.
    (intros ms' dd_H; ddestruct dd_H as (rax & a3x & j0 & ws2 & m3 & -> & NBW2 & LEN2 & DG2 & ZR2 & CCH2 & OUT2 & ST2 & FR02 & FR12 & MUx & WMx & MIx)).
    clear dependent m2. clear dependent m1. clear dependent m0.
    (* [comment removed for export] *)
    assert (CRNB : crange CS NB 240) by (intros x Hx; apply SCS; unfold NB in Hx; lia).
    pose proof (munch_refl [(NB, NB + 240); (CC, CC + 8); (BUF, BUF + Z.of_nat (length bs))] m3) as MUp. pose proof (wmono_refl asegs m3) as WMp.
    replace (Z_to_bv 64 L) with (Z_to_bv 64 (L - 1 + 1)) by (f_equal; lia).
    destruct (Z.eq_dec v 0) as [V0|V0].
    - (* [comment removed for export] *)
      assert (J = 1) as JE by (unfold J; rewrite V0; destruct Hbase as [-> | ->]; reflexivity).
      eapply (evtA_cut asegs AL CS).
      { eapply (apn_padloop (Z.to_nat L) (L - 1) (-1) 0 NB CC BUF off E pz ws2 bs (Z_to_bv 64 0)); try eassumption; try lia; try (unfold NB; lia).
        - intros i Hi. destruct (Z.eq_dec i 0) as [->|NE]; [rewrite DG2 by lia; rewrite V0; reflexivity| apply ZR2; lia].
      }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a1p & a3p & a4p & s4p & pcp & bs' & m4 & -> & EX & NBW4 & CCH4 & OUT4 & LEN4 & PE4 & PR4 & MU4 & WM4 & MI4)).
      destruct EX as [(T0 & _)|(_ & -> & ->)]; [lia|].
      clear NBW2 CCH2 OUT2. transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4 MUp WMp.
      replace (L - 1 - -1) with L in * by lia. rewrite ?Z.add_0_l in *.
      zstep. zstep. zstep.
      replace (Z.lor pz 1) with 1 by (assert (pz = 0 \/ pz = 1) as [-> | ->] by lia; reflexivity).
      if_trueU. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      release_frame FR02 ST2 (SPA + -328).
      apply (stk_release_u64 m4 lo NB ws2) in ST2; [| exact NBW4 | unfold NB; lia]. rewrite LEN2 in ST2. replace (NB + 8 * Z.of_nat 30) with (SPA + -88) in ST2 by (unfold NB; lia).
      release_frame FR12 ST2 SPA.
      apply evtA_done. replace (L - 1 + 1) with L by lia. eexists _, _, _, _, _, _, _, bs', m4. split; [reflexivity|].
      split; [exact ST2|]. split; [exact CCH4|]. split; [exact OUT4|]. split; [exact LEN4|]. split; [exact PE4|]. split; [exact PR4|].
      split; [exact MUx|]. split; [exact WMx| exact MI4].
    - (* [comment removed for export] *)
      assert (VB : 0 < v < base ^ Z.of_nat 20) by (destruct Hbase as [-> | ->]; lia).
      pose proof (ndig_top base 20 v ltac:(lia) VB) as TOPNZ. fold J in TOPNZ.
      pose proof (dig_bound base v (J - 1) ltac:(lia)) as TOPB.
      eapply (evtA_cut asegs AL CS).
      { eapply (apn_padloop (Z.to_nat (L - J)) (L - 1) (J - 1) 0 NB CC BUF off E pz ws2 bs (Z_to_bv 64 (dig base v (J - 1)))); try eassumption; try lia; try (unfold NB; lia).
        - intros i Hi. apply ZR2. lia.
        - intros _. split; [apply DG2; lia|]. rewrite unsigned_lit by lia. exact TOPNZ. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a1p & a3p & a4p & s4p & pcp & bs' & m4 & -> & EX & NBW4 & CCH4 & OUT4 & LEN4 & PE4 & PR4 & MU4 & WM4 & MI4)).
      destruct EX as [(_ & -> & -> & -> & ->)|(T0 & _)]; [|lia].
      clear NBW2 CCH2 OUT2. transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4 MUp WMp.
      replace (L - 1 - (J - 1)) with (L - J) in * by lia. rewrite ?Z.add_0_l in *.
      zstep. zstep. 
      replace (Z.lor pz 1) with 1 by (assert (pz = 0 \/ pz = 1) as [-> | ->] by lia; reflexivity).
      zstep. zstep. zstep.
      rewrite bv_lts_zero_r, unsigned_lit by lia. replace (2 ^ 63 <=? J - 1) with false by (symmetry; apply Z.leb_gt; lia). cbv iota.
      zstep.
      destruct (Z.eq_dec up 0) as [U0|U0]; [if_falseU | if_trueU].
      all: zstep; zstep; zstep.
      1: if_trueU.
      2: if_falseU.
      all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep.
      all: rewrite (Z.mod_small (J - 1) 4294967296) by lia.
      all: replace (Z.shiftr (Z.shiftl (J - 1) 32 mod 18446744073709551616) 29) with (8 * (J - 1))
             by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2 ^ 32) with 4294967296; change (2 ^ 29) with 536870912; lia).
      all: fold NB.
      all: pose proof (munch_refl [(NB, NB + 240); (CC, CC + 8); (BUF, BUF + Z.of_nat (length bs'))] m4) as MUe; pose proof (wmono_refl asegs m4) as WMe.
      all: replace (BUF + off + (L - J)) with (BUF + (off + (L - J))) in * by lia.
      all: eapply (evtA_cut asegs AL CS);
           [ eapply (apn_emitloop (Z.to_nat (J - 1)) (J - 1) NB CC BUF (off + (L - J)) E _ ws2 bs'); try rewrite LEN4; try eassumption; try lia; try (unfold NB; lia) | ].
      1,4: intros k Hk; exists (dig base v k); (split; [apply DG2; lia|]); pose proof (dig_bound base v k ltac:(lia)); destruct Hbase; lia.
      1,3: apply munch_refl.
      all: cbn beta; (intros ms' dd_H; ddestruct dd_H as (a3e & a4e & a6e & a7e & bs'' & m5 & -> & NBW5 & CCH5 & OUT5 & LEN5 & PE5 & PR5 & MU5 & WM5 & MI5)).
      all: rewrite LEN4 in MU5.
      all: clear NBW4 CCH4 OUT4; transport_after_call asegs m4 m5 MU5 WM5; clear MU5 WM5 MUe WMe.
      all: zstep.
      all: rewrite (Z.mod_small (L - J + (J - 1))) by lia; rewrite swrap32_id by lia; replace (L - J + (J - 1) + 1) with L by lia.
      all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep.
      all: release_frame FR02 ST2 (SPA + -328).
      all: apply (stk_release_u64 m5 lo NB ws2) in ST2; [| exact NBW5 | unfold NB; lia]; rewrite LEN2 in ST2; replace (NB + 8 * Z.of_nat 30) with (SPA + -88) in ST2 by (unfold NB; lia).
      all: release_frame FR12 ST2 SPA.
      all: apply evtA_done; replace (L - 1 + 1) with L by lia; eexists _, _, _, _, _, _, _, bs'', m5; (split; [reflexivity|]).
      all: split; [exact ST2|]; split; [replace (BUF + off + L) with (BUF + (off + (L - J)) + (J - 1 + 1)) by lia; exact CCH5|]; split; [exact OUT5|]; split; [rewrite LEN5; exact LEN4|].
      all: split; [eapply prefix_eq_trans; [exact PE4| exact PE5| lia]|].
      all: split; [|split; [exact MUx|split; [exact WMx| exact MI5]]].
      all: intros i Hi; destruct (Z_lt_le_dec i (off + (L - J))) as [LT|GE]; [eapply pr_range_prefix; [exact PR4| exact PE5| lia| lia| lia] | apply PR5; lia].
  Qed.
End Walk.
