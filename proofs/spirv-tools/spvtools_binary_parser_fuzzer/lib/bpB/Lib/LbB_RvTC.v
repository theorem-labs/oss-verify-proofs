(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface RtB_Annot BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RvTS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4 LbB_ResvB.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rvt_runs (E : Z) : Prop :=
  rvt_T1R E /\ rvt_T1N E /\ rvt_T3a E /\ rvt_T3b E /\ rvt_T5 E /\ rvt_T7 E /\ rvt_T9D E /\ rvt_T9Z E
  /\ rvt_T11 E /\ v4_ret_ok (E + 300).

Lemma v4_ret_ok_ec8b4 : v4_ret_ok (rv_entry RESV_TYP + 300).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F fc m HQ.
  cbn [rv_entry RESV_TYP]. step. apply evt_done. exact HQ.
Qed.

Lemma rvt_runs_ec788 : rvt_runs (rv_entry RESV_TYP).
Proof.
  exact (conj rvt_T1R_ec788 (conj rvt_T1N_ec788 (conj rvt_T3a_ec788 (conj rvt_T3b_ec788 (conj rvt_T5_ec788
    (conj rvt_T7_ec788 (conj rvt_T9D_ec788 (conj rvt_T9Z_ec788 (conj rvt_T11_ec788 v4_ret_ok_ec8b4))))))))).
Qed.
Section RtS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis RUNS : rvt_runs (rv_entry RESV_TYP).

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB LBo : list block) (LF : list fframe)
            (v b cap kc ns : Z) (xs : list Z) (pid : bptr) (lo B shi spz : Z).
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - 80 /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [rv_del_ra RESV_TYP].
  Hypothesis VBAND : (0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47).
  Hypothesis OBJ : obj_win H LB LF spz lo v 24.
  Hypothesis V8 : v mod 8 = 0.
  Hypothesis XSL : Zlen xs = ns.
  Hypothesis VEC : vec32A LB m v b xs cap.
  Hypothesis OLD : v4_oldblk LBo b cap pid.
  Hypothesis OLDSH : 0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * ns)).
  Hypothesis K0 : 0 <= kc.
  Hypothesis GROW : 4 * kc <= 2 ^ 26.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - RESV_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.
  Hypothesis ADV0 : addressable m v 24.
  Hypothesis VWR : wr_at asegs m v 24.
  Hypothesis OWN : lb_own LBo m.
  Hypothesis OINC : forall bb, In bb LBo -> In bb LB.
  Hypothesis OND : List.NoDup (map blk_id LBo).

  Let E0 := rv_entry RESV_TYP.
  Let Q := resv32_post H RESV_TYP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBo LF v b xs cap kc pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [Z_to_bv 64 v; s3; s2; s1; s0; ra].

  Lemma E0R : 0 <= E0 < 0x200000 /\ E0 mod 4 = 0.
  Proof. unfold E0. cbn [rv_entry RESV_TYP]. split; [lia | reflexivity]. Qed.

  Lemma DRA : rv_del_ra RESV_TYP = E0 + 276.
  Proof. unfold E0. cbn [rv_entry rv_del_ra RESV_TYP]. reflexivity. Qed.

  Lemma rt_spz_sp : sp = Z_to_bv 64 spz.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Definition rt_T5at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    rvt_T5_pre R mk v (spz - 80) b cap A kc ns (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) (bv_unsigned s7)
      (bv_unsigned s6) (bv_unsigned s5) (bv_unsigned s4) (A + 4 * ns) (4 * kc) v 0 (E0 + 208).

  Definition rt_T7at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    rvt_T7_pre R mk v (spz - 80) b cap A kc ns (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) (bv_unsigned s7)
      (bv_unsigned s6) (bv_unsigned s5) (bv_unsigned s4) (A + 4 * ns) (4 * kc) v 0 (E0 + 208).

  Definition rt_T9at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    rvt_T9_pre R mk A (spz - 80) v cap b kc.

  Definition rt_T11at (R : bvmap 5 word) (mk : mem) : Prop :=
    rvt_T11_pre R mk (spz - 80) (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2) (bv_unsigned s3).

  Definition rt_mid (sk : as_St H) (mk : mem) (pid' : bptr) (A : Z) (Xk : list (Z * Z)) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi /\ as_RHEAP H sk ((pid', A, 4 * kc) :: LB) mk
    /\ rw_cells asegs mk (spz - 48) FRAME /\ xpres H LB spz Xk m mk /\ as_AL H sk >= as_AL H s - as_Cm H (4 * kc)
    /\ lb_own ((pid', A, 4 * kc) :: LBo) mk.

  Definition rt_wk (A : Z) (Xk : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= spz - 48)
    \/ (A <= fst iv /\ snd iv <= A + 4 * kc)
    \/ (sh A <= fst iv /\ snd iv <= sh A + nsh (4 * kc))
    \/ ((forall a, fst iv <= a < snd iv -> rin_ivs Xk a) /\ aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv
        /\ stack0_ok iv /\ (snd iv <= spz - 48 \/ spz <= fst iv) /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)).
  Lemma rt_cls : forall s' LBx p A n SP m0 a,
    as_RHEAP H s' ((p, A, n) :: LBx) m0 -> ~ In p (map blk_id LBx) -> aceil <= SP -> aclient_addr H LBx SP a ->
    SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n)).
  Proof.
    intros s' LBx p A n SP m0 a RH NI HSP Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    acb.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b0 & Hb & Hr)|[(b0 & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - left. exact Hc.
    - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      destruct b0 as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
      destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
    - right. assert (Hb' : In b0 ((p, A, n) :: LBx)) by (right; exact Hb).
      assert (Hid : blk_id b0 <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
      pose proof (ah_disj H HH _ _ _ (p, A, n) b0 RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
      destruct b0 as [[pb Ab] nb]. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
      unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct D as [D|D]; split; try lia; split; lia.
    - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
      destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
    - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
      unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct RF as [RF|RF]; split; try lia; split; lia.
    - right. assert (SA0 : 0x7fff8000 <= sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. destruct RAPP as [RP|RP]; split; try lia; split; lia.
  Qed.

  Lemma rt_xpres_mixed : forall s' p A n SP X m0 m1 m2 W,
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aceil <= SP ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB SP X m1 m2.
  Proof.
    intros s' p A n SP X m0 m1 m2 W RH NI HSP MU WM FW a Ha [Hc Hx].
    pose proof (rt_cls s' LB p A n SP m0 a RH NI HSP Hc) as CLS.
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[l h] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct H1 as [[H1 H2]|[[H1 H2]|[[H1 H2]|H1]]].
      - destruct CLS as [C|(C1 & C2 & C3)]; [pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (_ & _ & _ & _ & RC & _); cbn in RC|]; lia.
      - destruct CLS as [C|(C1 & C2 & C3)].
        + assert (sh A + nsh n <= sh aceil).
          { pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & _ & Rn & _ & RC & _). cbn in *.
            unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
          assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
        + lia.
      - destruct CLS as [C|(C1 & C2 & C3)]; lia.
      - intros K. apply Hx. apply H1. exact K. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma rt_mid_munch : forall sk mk mk' pid' A Xk W,
    rt_mid sk mk pid' A Xk -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    munch W mk mk' -> wmono asegs mk mk' -> mem_inv asegs mk' -> Forall (rt_wk A Xk) W ->
    rt_mid sk mk' pid' A Xk.
  Proof.
    intros sk mk mk' pid' A Xk W (MI & ST & (e & ERR) & RA & AC & RF & S0 & RH & FR & XP & AL & OW) ABR NI MU WM MI' FW.
    destruct SPR as (SPL & SPH & SP16). destruct LOR as [LO1 LO2].
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (SHAb : sh A + nsh (4 * kc) <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHAl : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHAC : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHIT : sh AIMG_TOP <= sh A) by (unfold sh, AIMG_TOP; Z.div_mod_to_equations; lia).
    assert (VSPZ : AIMG_TOP <= lo) by (unfold AIMG_TOP; lia).
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.

    assert (W1 : Forall (aclient_write_ok H ((pid', A, 4 * kc) :: LB)) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold rt_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & Hw & _)]]].
      - left. cbn. lia.
      - right; right; left. exists (pid', A, 4 * kc). split; [left; reflexivity | cbn; lia].
      - right; right; right; left. exists (pid', A, 4 * kc). split; [left; reflexivity | cbn; lia].
      - unfold aclient_write_ok in *.
        destruct Hw as [K|[K|[(b' & Hb & K)|[(b' & Hb & K)|K]]]]; [left; exact K | right; left; exact K | | | right; right; right; right; exact K].
        + right; right; left. exists b'. split; [right; exact Hb | exact K].
        + right; right; right; left. exists b'. split; [right; exact Hb | exact K]. }
    assert (W2 : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold rt_wk in Hw. cbn [fst snd] in Hw.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, BAPP. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & Hw & _)]]]; [left; cbn; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia | | | exact Hw].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct BF; lia | lia].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct FS4; lia | lia]. }
    assert (W3 : Forall aconst_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold rt_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia].
      - eapply (aconst_ok_app A (4 * kc)); [exact BAPP | lia | lia].
      - apply aconst_ok_high; [lia | right; left; lia]. }
    assert (W4 : Forall stack0_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold rt_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - left. cbn. unfold AHI_LO. lia.
      - eapply (stack0_ok_aapp A (4 * kc)); [exact BAPP | lia | lia].
      - right. cbn. lia. }
    destruct (client_frame H HH sk _ LF B W mk mk' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    split; [exact MI'|]. split; [eapply BakeStackRep.stk_high_transport; [exact ST | exact WM | exact VSPZ]|].
    split.
    { exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold rt_wk in Hw. cbn [fst snd cells_size csize Z.of_nat] in *.
      unfold ATP in *. destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & _ & Hw)]]]; lia. }
    split; [exact RA'|]. split; [exact AC'|]. split; [exact RF'|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]|].
    split; [exact RH'|].
    split.
    { eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold rt_wk in Hw. cbn [fst snd] in Hw.
      unfold FRAME. rewrite v4_cells_size_map_C8'. cbn [length].
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & Hw & _)]]]; lia. }
    split; [|split; [exact AL | exact (lb_own_wmono _ _ _ OW WM)]].
    eapply (xpres_trans H); [exact XP|].
    eapply (rt_xpres_mixed sk pid' A (4 * kc) spz Xk mk mk mk' W RH NI ltac:(lia) MU WM).
    eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold rt_wk in Hw. cbn [fst snd] in *.
    destruct Hw as [Hw|[Hw|[Hw|(Hw & _)]]].
    - right; right; left. lia.
    - left. exact Hw.
    - right; left. exact Hw.
    - right; right; right. exact Hw.
  Qed.

  Lemma rt_vec_facts :
    fldA m v 8 b /\ fldA m (v + 8) 8 (b + 4 * ns) /\ fldA m (v + 16) 8 (b + 4 * cap)
    /\ (forall i, 0 <= i < ns -> 0 <= Znth i xs < 2 ^ 32 /\ fldA m (b + 4 * i) 4 (Znth i xs))
    /\ 0 <= ns <= cap /\ ((b = 0 /\ cap = 0) \/ (1 <= cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap))).
  Proof.
    destruct VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2 & FE). rewrite XSL in F1, FE, Hlen.
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact FE|]. split; [lia|].
    destruct OLD as [[-> ->]|(Hc & HIn)]; [left; split; reflexivity|].
    right. split; [lia|]. split; [exact (OINC _ HIn)|]. exact (ah_blocks H HH _ _ _ _ RH0 (OINC _ HIn)).
  Qed.

  Lemma rt_E0_even : forall k, 0 <= k < 0x1000 -> k mod 4 = 0 -> 0 <= E0 + k < 2 ^ 64 /\ (E0 + k) mod 2 = 0.
  Proof.
    intros k Hk H4. destruct E0R as [R0 R4]. split; [unfold E0; lia|]. unfold E0. exact (v4_mod4_even _ _ R4 H4).
  Qed.

  Lemma rt_old_facts : 0 < cap ->
    In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap) /\ (v + 24 <= b \/ b + 4 * cap <= v) /\ b <> 0.
  Proof.
    intros Hc. pose proof rt_vec_facts as (_ & _ & _ & _ & _ & OB).
    destruct OB as [[_ C]|(_ & HIn & ABR)]; [lia|].
    destruct VEC as (_ & _ & _ & _ & Hb & _). destruct Hb as [[_ C]|(_ & _ & _ & _ & _ & D)]; [lia|].
    split; [exact HIn|]. split; [exact ABR|]. split; [exact D|]. destruct ABR as (B0 & _). lia.
  Qed.

  Lemma rt_old_own : 0 < cap -> In (pid, b, 4 * cap) LBo.
  Proof. intros Hc. destruct OLD as [[_ E]|(_ & HIo)]; [lia | exact HIo]. Qed.

  Lemma rt_rm_ne : forall q LB1 bb, List.NoDup (map blk_id LB1) -> In bb (as_lb_remove H q LB1) -> blk_id bb <> q.
  Proof.
    intros q LB1 bb ND. pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    induction LB1 as [|b' LB1 IH]; intros Hin; [destruct (L3 _ _ _ Hin)|].
    cbn [map] in ND. apply NoDup_cons_iff in ND as [ND1 ND2].
    destruct (Z.eq_dec (blk_id b') q) as [Eq|Ne].
    - destruct b' as [[q' A'] n']. cbn [blk_id fst] in Eq. subst q'. rewrite (L1 _ _ _ _ ND1) in Hin.
      intros Eb. apply ND1. rewrite <- Eb. exact (List.in_map blk_id LB1 bb Hin).
    - rewrite (L2 _ _ _ Ne) in Hin. destruct Hin as [<-|Hin]; [exact Ne | exact (IH ND2 Hin)].
  Qed.

  Lemma rt_rm_incl : forall q bb, In bb (as_lb_remove H q LBo) -> In bb (as_lb_remove H q LB).
  Proof.
    intros q bb Hb. pose proof (ah_lb_remove H HH) as (_ & _ & L3).
    apply (lb_remove_keep H HH); [exact (ah_nodup H HH _ _ _ RH0) | exact (OINC _ (L3 _ _ _ Hb)) | exact (rt_rm_ne q LBo bb OND Hb)].
  Qed.

  Lemma rt_blk_shad : forall sk mk LBx p A n, as_RHEAP H sk LBx mk -> In (p, A, n) LBx ->
    exists sbs, SHAD mk A sbs /\ Z.of_nat (length sbs) = nsh n.
  Proof.
    intros sk mk LBx p A n RH HIn.
    pose proof (ah_blk_shvis H HH _ _ _ _ _ _ RH HIn) as SV. unfold shvis in SV.
    pose proof (ah_blocks H HH _ _ _ _ RH HIn) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn [blk_addr blk_size fst snd] in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof (v4_mod16_8 A B16) as B8.
    destruct (v4_sh_hull A n ltac:(lia) B8 Bn) as [HL1 HL2].
    assert (NS : 0 <= nsh n) by (unfold nsh; apply Z.div_pos; lia).
    destruct (stk_split asegs mk _ (sh A) _ SV ltac:(lia)) as [_ SV2].
    destruct (stk_split asegs mk _ (sh A + nsh n) _ SV2 ltac:(lia)) as [SV3 _].
    destruct (stk_carve asegs mk (sh A) (sh A + nsh n) (Z.to_nat (nsh n)) SV3 ltac:(lia)) as [_ (junk & RC)].
    rewrite Z2Nat.id in RC by lia. replace (sh A + nsh n - nsh n) with (sh A) in RC by lia.
    exists junk. split.
    - eapply SHAD_of_rw_cells; [lia | exact B8 | exact RC].
    - destruct RC as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl, Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma rt_hdr_fresh : forall sk mk pid' A n,
    as_RHEAP H sk ((pid', A, n) :: LB) mk -> ~ In pid' (map blk_id LB) -> 0 < n -> v + 24 <= A \/ A + n <= v.
  Proof.
    intros sk mk pid' A n RH NI Hn.
    destruct OBJ as (CL & _).
    pose proof (ah_blocks H HH _ _ _ (pid', A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    destruct LOR as [LO1 LO2]. unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    assert (SPC : aceil <= spz) by lia.
    destruct (Z_le_gt_dec (v + 24) A) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (A + n) v) as [D'|D']; [right; exact D'|].
    exfalso.
    assert (Ha : v <= Z.max v A < v + 24) by lia.
    pose proof (aclient_range_addr H LB spz v 24 (Z.max v A) CL Ha) as Hc.
    destruct (rt_cls sk LB pid' A n spz mk (Z.max v A) RH NI SPC Hc) as [C|(C1 & C2 & C3)]; [lia|].
    apply C2. lia.
  Qed.

  Lemma rt_band_of_aapp : forall A n, aapp A n -> (0 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A.
  Proof. intros A n HA. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in HA. destruct HA; [left|right]; lia. Qed.

  Lemma rt_xc_hdr : 0 < cap -> xclient_range H LB spz (v4_oldx b (4 * cap)) v 24.
  Proof.
    intros Hc. destruct (rt_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (CL & _).
    split; [exact CL|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma rt_xc_hdrsh : 0 < cap -> xclient_range H LB spz (v4_oldx b (4 * cap)) (sh v) 3.
  Proof.
    intros Hc. destruct (rt_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS.
    split; [exact CLS|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof (v4_app_sh b (4 * cap) v 24 ltac:(lia) ltac:(lia) VB (rt_band_of_aapp _ _ BAPP)) as D1. rewrite v4_nsh24 in D1.
    pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
    rewrite v4_nsh24 in D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Definition rt_X0 : list (Z * Z) := if b =? 0 then [] else [(sh b, sh b + nsh (4 * cap))].
  Definition rt_X1 : list (Z * Z) := (v, v + 24) :: rt_X0.

  Lemma rt_xc_old : 0 < cap -> xclient_range H LB spz rt_X0 b (4 * cap).
  Proof.
    intros Hc. destruct (rt_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    split; [eapply (aclient_range_block H); [exact HIn | lia | lia]|].
    unfold rt_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    pose proof (v4_app_sh b (4 * cap) b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (rt_band_of_aapp _ _ BAPP)) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma rt_X1_sub : forall a, rin_ivs rt_X1 a -> rin_ivs ((v, v + 24) :: v4_oldx b (4 * cap)) a.
  Proof.
    intros a Ha. unfold rt_X1, rt_X0, v4_oldx in Ha |- *. destruct (b =? 0); cbn [rin_ivs fst snd] in Ha |- *; tauto.
  Qed.

  Lemma rt_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
  Proof.
    induction W as [|[l h] W IH]; intros a n a' n' D H1 H2; [exact I|]. cbn in D |- *. destruct D as [D1 D2].
    split; [lia | exact (IH a n a' n' D2 H1 H2)].
  Qed.

  Lemma rt_wr_sub : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n'.
  Proof.
    intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
  Qed.

  Lemma rt_CB0 : forall mk a, 0 <= a <= 2 ^ 64 -> rw_cells asegs mk a [CB 0 []].
  Proof.
    intros mk a Ha. split; [split|].
    - cbn. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
    - cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  Qed.

  Lemma rt_shvis0 : forall mk, shvis mk 0 0.
  Proof.
    intros mk. unfold shvis. change (sh (hull_lo 0)) with 2147450880. change (sh (hull_hi 0)) with 2147450880.
    split; [lia|]. split; [lia|]. intros a Ha. lia.
  Qed.

  Lemma rt_shk4 : forall mk A, addressable mk A 4 -> LbB_Kit.shk mk A 4.
  Proof.
    intros mk A [_ SH]. pose proof SH as (SA0 & _).
    destruct (shk_of_SHAD mk A (shadow_of 4) A SH ltac:(change (Z.of_nat (length (shadow_of 4))) with 1; lia)) as (bb & Hb & K).
    rewrite Z.sub_diag in Hb. change (nth_error (shadow_of 4) (Z.to_nat (0 / 8))) with (Some (b8 4)) in Hb. injection Hb as <-. exact K.
  Qed.

  Lemma rt_acl_sub : forall LBx SP A n A' n', aclient_range H LBx SP A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    aclient_range H LBx SP A' n'.
  Proof.
    intros LBx SP A n A' n' K H1 H2 H3. unfold aclient_range in *.
    destruct K as [K|[K|[(bb & Hb & K1 & K2)|[(bb & Hb & K1 & K2)|[K|[K|K]]]]]].
    - left. lia.
    - right; left. intros a Ha. apply K. lia.
    - right; right; left. exists bb. split; [exact Hb | lia].
    - right; right; right; left. exists bb. split; [exact Hb | lia].
    - right; right; right; right; left. lia.
    - right; right; right; right; right; left. lia.
    - right; right; right; right; right; right. lia.
  Qed.

  Lemma rt_xcl_sub : forall X A n A' n', xclient_range H LB spz X A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    xclient_range H LB spz X A' n'.
  Proof.
    intros X A n A' n' [K KX] H1 H2 H3. split; [exact (rt_acl_sub _ _ _ _ _ _ K H1 H2 H3)|].
    eapply Forall_impl; [|exact KX]. intros [l h] Hlh. cbn [fst snd] in *. lia.
  Qed.

  Lemma rt_fld_xpres : forall X mk a k z, xpres H LB spz X m mk -> xclient_range H LB spz X a (Z.of_nat k) ->
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fldA m a k z -> fldA mk a k z.
  Proof.
    intros X mk a k z XP XC H0 H1 Hf. unfold fldA in *. eapply fld_agree; [exact H0 | exact H1 | exact Hf |].
    intros a' Ha'. hnf in Ha'.
    destruct (XP a' ltac:(lia) (xclient_range_addr H LB spz X a (Z.of_nat k) a' XC Ha')) as [E _]. exact E.
  Qed.

  Lemma rt_SHAD_xpres : forall X mk A' sbs, xpres H LB spz X m mk -> SHAD m A' sbs ->
    xclient_range H LB spz X (sh A') (Z.of_nat (length sbs)) -> SHAD mk A' sbs.
  Proof.
    intros X mk A' sbs XP (S0 & S8 & [UB UW]) XC. split; [exact S0|]. split; [exact S8|].
    split; [eapply (xpres_bytes_at H); [exact XP | exact UB | exact XC] | eapply (xpres_wr_at H); [exact XP | exact UW | exact XC]].
  Qed.

  Lemma rt_apres_of_xpres_nil : forall mk, xpres H LB spz [] m mk -> apres H LB spz m mk.
  Proof. intros mk XP a Ha Hc. apply XP; [exact Ha|]. split; [exact Hc | intros K; exact K]. Qed.

  Lemma rt_mid_weaken : forall sk mk pid' A X X', rt_mid sk mk pid' A X -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
    rt_mid sk mk pid' A X'.
  Proof.
    intros sk mk pid' A X X' (MI & ST & ERR & RA & AC & RF & S0 & RH & FR & XP & AL & OW) HX.
    repeat (split; [assumption|]). split; [eapply (xpres_weaken H); [exact XP | lia | intros bb Hb; exact Hb | exact HX]|].
    split; assumption.
  Qed.

  Lemma rt_wk_hdr : forall A Xk, (forall a, v <= a < v + 24 -> rin_ivs Xk a) -> rt_wk A Xk (v, v + 24).
  Proof.
    intros A Xk HX. right; right; right. cbn [fst snd].
    destruct OBJ as (_ & _ & WO & FW & CO & SD).
    pose proof LOR as [LO1 LO2]. unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    split; [exact HX|]. split; [exact WO|]. split; [exact FW|]. split; [exact CO|].
    split; [unfold stack0_ok; cbn [fst snd]; destruct VBAND; [right | left]; unfold AHI_LO; lia|].
    split; [lia|]. right. unfold ATP. destruct VBAND; lia.
  Qed.

  Lemma rt_wk_oldsh : 0 < cap -> forall A Xk, (forall a, sh b <= a < sh b + nsh (4 * cap) -> rin_ivs Xk a) ->
    rt_wk A Xk (sh b, sh b + nsh (4 * cap)).
  Proof.
    intros Hc A Xk HX. destruct (rt_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    pose proof (v4_app_sh (as_FSB H) AFS_SIZE b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (rt_band_of_aapp _ _ FS4)) as DF.
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHH. unfold AHI_LO in SHH.
    assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    right; right; right. cbn [fst snd].
    split; [exact HX|].
    split; [right; right; right; left; exists (pid, b, 4 * cap); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [lia | unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]|].
    split; [apply stack0_ok_sh; lia|].
    split; [lia|]. right. unfold ATP. lia.
  Qed.

  Lemma rt_hdr_X0 : forall mk, xpres H LB spz rt_X0 m mk ->
    fldA mk v 8 b /\ fldA mk (v + 8) 8 (b + 4 * ns) /\ fldA mk (v + 16) 8 (b + 4 * cap) /\ addressable mk v 24
    /\ wr_at asegs mk v 24.
  Proof.
    intros mk XP.
    pose proof rt_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    assert (VB2 : 0 <= v /\ v + 24 < 2 ^ 64) by (destruct VBAND; lia).
    assert (XCH : xclient_range H LB spz rt_X0 v 24).
    { destruct OBJ as (CL & _). split; [exact CL|]. unfold rt_X0. destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
      assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
      pose proof (v4_app_sh v 24 b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (XCS : xclient_range H LB spz rt_X0 (sh v) 3).
    { destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS. split; [exact CLS|]. unfold rt_X0.
      destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      assert (D : v + 24 <= b \/ b + 4 * cap <= v) by (destruct (rt_old_facts ltac:(lia)) as (_ & _ & D & _); exact D).
      pose proof (v4_sh_apart v 24 b (4 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
      rewrite v4_nsh24 in D2.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    split; [eapply rt_fld_xpres; [exact XP | eapply rt_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F0]|].
    split; [eapply rt_fld_xpres; [exact XP | eapply rt_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F1]|].
    split; [eapply rt_fld_xpres; [exact XP | eapply rt_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F2]|].
    split.
    - destruct ADV0 as [AN SV]. split; [exact AN|]. eapply rt_SHAD_xpres; [exact XP | exact SV |].
      rewrite shadow_of_length by lia. rewrite v4_nsh24. exact XCS.
    - eapply (xpres_wr_at H); [exact XP | exact VWR | exact XCH].
  Qed.

  Let HANN : annotate_gen_stmt := annotate_gen_ok.
  Lemma rt_mainR : kc <= cap -> forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 kc) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 E0) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros KC msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof RUNS as (B1R & _ & _ & _ & _ & _ & _ & _ & _ & RET).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof rt_vec_facts as (F0 & F1 & F2 & FE & C0 & OB).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 kc) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    assert (PRE : rvt_T1_pre R0 m v kc spz b cap ns).
    { unfold rvt_T1_pre. rewrite HR0.
      repeat match goal with |- _ /\ _ => split end;
        first [ reflexivity | exact rt_spz_sp | assumption | lia
              | (eapply wr_at_of_stk_win; [exact ST0 | lia | lia])
              | (eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]) ]. }
    destruct (B1R R0 F fc m v kc spz b cap ns PRE KC)
      as (R1 & M1 & Hms & MU1 & WM1 & Q1 & Q2 & Q3 & Q4 & Q5 & K2 & K10 & K11 & K12 & K13 & K14 & KK).
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    assert (SWL : aceil <= spz - 40) by lia.
    destruct (stack_window_ok H LB LF (spz - 40) spz SWL FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 40, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (ST1 : stk asegs M1 lo spz) by (apply (stk_high_transport m M1 lo spz ST0 WM1); unfold AIMG_TOP; lia).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia | exact I]. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XPF : forall X, xpres H LB spz X m M1).
    { intros X. eapply (xpres_of_munch H s LB spz X [(spz - 40, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (OW1 : lb_own LBo M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    destruct (rt_hdr_X0 M1 (XPF _)) as (_ & _ & _ & ADV1 & WV1).
    assert (VEC1 : vec32A LB M1 v b xs cap).
    { unfold vec32A. eapply vec32_frame; [exact VEC|].
      intros x Hx. unfold vec32_fp in Hx.
      destruct Hx as [Hx|[NZ Hx]]; hnf in Hx.
      - assert (XC : xclient_range H LB spz [] v 24) by (destruct OBJ as (CL & _); split; [exact CL | apply Forall_nil]).
        destruct (XPF [] x ltac:(destruct VBAND; lia) (xclient_range_addr H LB spz [] v 24 x XC ltac:(lia))) as [E _].
        exact E.
      - assert (Hc : 0 < cap) by (destruct OB as [[E _]|(Hc & _)]; [contradiction | lia]).
        pose proof (rt_xc_old Hc) as XC.
        destruct (XPF rt_X0 x ltac:(lia) (xclient_range_addr H LB spz rt_X0 b (4 * cap) x XC ltac:(lia))) as [E _].
        exact E. }
    assert (SH1 : 0 < cap -> SHAD M1 b (cc_gen (4 * cap) (4 * Zlen xs))).
    { intros Hc. rewrite XSL. destruct OB as [[_ E]|(_ & HIn & _)]; [lia|].
      eapply (rt_SHAD_xpres [] M1); [exact (XPF []) | exact (OLDSH Hc) |].
      rewrite cc_gen_length by lia. split; [|apply Forall_nil].
      exact (aclient_range_block_sh H LB spz pid b (4 * cap) HIn). }
    assert (G1 : getr R1 1 = ra) by (rewrite (KK 1%bv ltac:(inb)), HR0; reflexivity).
    assert (G2 : getr R1 2 = sp) by (rewrite K2; unfold wz; symmetry; exact rt_spz_sp).
    assert (G3 : getr R1 3 = gp) by (rewrite (KK 3%bv ltac:(inb)), HR0; reflexivity).
    assert (G4 : getr R1 4 = tp) by (rewrite (KK 4%bv ltac:(inb)), HR0; reflexivity).
    assert (G8 : getr R1 8 = s0) by (rewrite (KK 8%bv ltac:(inb)), HR0; reflexivity).
    assert (G9 : getr R1 9 = s1) by (rewrite (KK 9%bv ltac:(inb)), HR0; reflexivity).
    assert (G18 : getr R1 18 = s2) by (rewrite (KK 18%bv ltac:(inb)), HR0; reflexivity).
    assert (G19 : getr R1 19 = s3) by (rewrite (KK 19%bv ltac:(inb)), HR0; reflexivity).
    assert (G20 : getr R1 20 = s4) by (rewrite (KK 20%bv ltac:(inb)), HR0; reflexivity).
    assert (G21 : getr R1 21 = s5) by (rewrite (KK 21%bv ltac:(inb)), HR0; reflexivity).
    assert (G22 : getr R1 22 = s6) by (rewrite (KK 22%bv ltac:(inb)), HR0; reflexivity).
    assert (G23 : getr R1 23 = s7) by (rewrite (KK 23%bv ltac:(inb)), HR0; reflexivity).
    assert (G24 : getr R1 24 = s8) by (rewrite (KK 24%bv ltac:(inb)), HR0; reflexivity).
    assert (G25 : getr R1 25 = s9) by (rewrite (KK 25%bv ltac:(inb)), HR0; reflexivity).
    assert (G26 : getr R1 26 = s10) by (rewrite (KK 26%bv ltac:(inb)), HR0; reflexivity).
    assert (G27 : getr R1 27 = s11) by (rewrite (KK 27%bv ltac:(inb)), HR0; reflexivity).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R1 5) (getr R1 6) (getr R1 7) s0 s1 (getr R1 10)
                                   (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                              F (ret_pc ra) fc None M1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { rewrite (rfull_eq R1 HF1). apply RET.
      rewrite G1, G2, G3, G4, G8, G9, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R1 5), (getr R1 6), (getr R1 7), (getr R1 10), (getr R1 11), (getr R1 12), (getr R1 13), (getr R1 14),
      (getr R1 15), (getr R1 16), (getr R1 17), (getr R1 28), (getr R1 29), (getr R1 30), (getr R1 31), M1, errv, s, pid, b, cap.
    cbn [cfg_ms cfg_model]. rewrite SPZ.
    rewrite (proj2 (Z.leb_le kc cap) KC). cbv zeta.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact (XPF _)|].
    split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [lia | exact SH1]|].
    split; [intros Hk; exfalso; lia|].
    split; [exact RH1|]. split; [exact VEC1|]. split; [exact ADV1|].
    split; [exact WV1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. exact S01.
  Qed.

  Section RtN.
  Hypothesis CK : cap < kc.
  Hypothesis AOK : as_alloc_ok H s LB (4 * kc).
  Hypothesis CM : as_Cm H (4 * kc) + as_Cf H (4 * cap) <= as_AL H s.

  Lemma rt_s_end : forall (msF1 : machine_state) (mo1 : Model) (s1' : as_St H) (m1 : mem) (R1 : bvmap 5 word) (pid' : bptr) (A : Z) (e1 : word),
    as_VIS H s1' msF1 = MS R1 F (Z_to_bv 64 (E0 + 276)) fc None m1 (seg_rom asegs) -> rfull R1 ->
    rt_T11at R1 m1 -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 20 = s4 -> getr R1 21 = s5 -> getr R1 22 = s6 -> getr R1 23 = s7 ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (4 * cap)) m m1 ->
    ablock_range H A (4 * kc) -> as_RHEAP H s1' (v4_newLB H LB b pid pid' A (4 * kc)) m1 ->
    vec32A (v4_newLB H LB b pid pid' A (4 * kc)) m1 v A xs kc ->
    SHAD m1 A (cc_gen (4 * kc) (4 * ns)) -> addressable m1 v 24 ->
    wr_at asegs m1 v 24 -> lb_own (v4_newLB H LBo b pid pid' A (4 * kc)) m1 ->
    as_RFS H LF m1 -> ACONST m1 -> stack0 m1 lo shi ->
    as_AL H s1' >= as_AL H s - (as_Cm H (4 * kc) + as_Cf H (4 * cap)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 s1' m1 R1 pid' A e1 VIS1 HF1 B11P G3 G4 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 XP1 ABR RH1 VEC1 SH1 ADV1 WV1 OW1 RF1 AC1 S01 AL1.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & _ & T11 & RET).
    destruct (T11 R1 F fc m1 (spz - 80) (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                (bv_unsigned s3) B11P)
      as (R' & M' & Hms & EM & K1 & K2 & K8 & K9 & K18 & K19 & KK).
    subst M'.
    assert (HF' : rfull R') by exact (msteps_full asegs _ _ Hms HF1).
    assert (K3 : getr R' 3 = gp) by (rewrite (KK 3%bv ltac:(inb)); exact G3).
    assert (K4 : getr R' 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
    assert (K20 : getr R' 20 = s4) by (rewrite (KK 20%bv ltac:(inb)); exact G20).
    assert (K21 : getr R' 21 = s5) by (rewrite (KK 21%bv ltac:(inb)); exact G21).
    assert (K22 : getr R' 22 = s6) by (rewrite (KK 22%bv ltac:(inb)); exact G22).
    assert (K23 : getr R' 23 = s7) by (rewrite (KK 23%bv ltac:(inb)); exact G23).
    assert (K24 : getr R' 24 = s8) by (rewrite (KK 24%bv ltac:(inb)); exact G24).
    assert (K25 : getr R' 25 = s9) by (rewrite (KK 25%bv ltac:(inb)); exact G25).
    assert (K26 : getr R' 26 = s10) by (rewrite (KK 26%bv ltac:(inb)); exact G26).
    assert (K27 : getr R' 27 = s11) by (rewrite (KK 27%bv ltac:(inb)); exact G27).
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R' 5) (getr R' 6) (getr R' 7) s0 s1 (getr R' 10)
                                   (getr R' 11) (getr R' 12) (getr R' 13) (getr R' 14) (getr R' 15) (getr R' 16) (getr R' 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R' 28) (getr R' 29) (getr R' 30) (getr R' 31))
                              F (ret_pc ra) fc None m1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { eapply evt_of_msteps; [exact Hms|]. rewrite (rfull_eq R' HF'). apply RET.
      rewrite K1, K2, K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. unfold wz.
      rewrite !Z_to_bv_bv_unsigned. replace (spz - 80 + 80) with spz by lia. rewrite <- rt_spz_sp. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 10), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14),
      (getr R' 15), (getr R' 16), (getr R' 17), (getr R' 28), (getr R' 29), (getr R' 30), (getr R' 31), m1, e1, s1', pid', A, kc.
    cbn [cfg_ms cfg_model]. rewrite SPZ.
    rewrite (proj2 (Z.leb_gt kc cap) CK). cbv zeta.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact XP1|].
    split; [intros Hk; exfalso; lia|].
    split; [intros _; split; [reflexivity|]; split; [exact ABR|]; split; [rewrite XSL; exact SH1 | exact AL1]|].
    split; [exact RH1|]. split; [exact VEC1|]. split; [exact ADV1|].
    split; [exact WV1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. exact S01.
  Qed.

  Lemma rt_s9 : forall (msF8 : machine_state) (mo8 : Model) (sk8 : as_St H) (m8 : mem) (R8 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk8 msF8 = MS R8 F (Z_to_bv 64 (E0 + 208)) fc None m8 (seg_rom asegs) -> rfull R8 ->
    rt_T9at R8 m8 A -> getr R8 3 = gp -> getr R8 4 = tp -> getr R8 8 = Z_to_bv 64 0 ->
    getr R8 20 = s4 -> getr R8 21 = s5 -> getr R8 22 = s6 -> getr R8 23 = s7 ->
    getr R8 24 = s8 -> getr R8 25 = s9 -> getr R8 26 = s10 -> getr R8 27 = s11 ->
    as_AKREL H sk8 (mkCfg msF8 mo8) -> as_MPRES H mo mo8 ->
    rt_mid sk8 m8 pid' A rt_X1 -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m8 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * ns)); C8 (Z_to_bv 64 (A + 4 * kc))] ->
    bytes_at asegs m8 A (le4s xs) ->
    SHAD m8 A (cc_gen (4 * kc) (4 * ns)) -> addressable m8 v 24 ->
    as_SR H Q (mkCfg msF8 mo8).
  Proof.
    intros msF8 mo8 sk8 m8 R8 pid' A VIS8 HF8 T9P G3 G4 G8 G20 G21 G22 G23 G24 G25 G26 G27 KR8 MP8 MID ABR NI HDR BUF SHA ADV8.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & T9D & T9Z & _ & _).
    pose proof MID as (MI8 & ST8 & (e8 & ERR8) & RA8 & AC8 & RF8 & S08 & RH8 & FR8 & XP8 & AL8 & OW8).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof rt_vec_facts as (F0 & F1 & F2 & FE & C0 & OB).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (FL : forall mk (w : word) k a, rw_cells asegs mk (spz - 48) FRAME -> cell_at FRAME k = Some (C8 w) ->
              a = spz - 48 + Z.of_nat k -> fldA mk a 8 (bv_unsigned w)).
    { intros mk w k a FR CA Ea. subst a. unfold fldA, fld. rewrite Z_to_bv_bv_unsigned. rewrite <- rdn_of_ov.
      exact (rw_cells_read asegs mk _ _ k _ FR CA). }
    assert (B11F : forall R mk, getr R 2 = wz (spz - 80) -> rw_cells asegs mk (spz - 48) FRAME -> rt_T11at R mk).
    { intros R mk R2 FR. unfold rt_T11at, rvt_T11_pre.
      split; [exact R2|].
      split; [eapply (FL mk ra 40%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s0 32%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s1 24%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s2 16%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s3 8%nat); [exact FR | reflexivity | lia]|].
      lia. }
    assert (HNEW : v + 24 <= A \/ A + 4 * kc <= v) by (eapply rt_hdr_fresh; [exact RH8 | exact NI | lia]).
    assert (VEC9 : forall m9 LB9, rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * ns)); C8 (Z_to_bv 64 (A + 4 * kc))] ->
              bytes_at asegs m9 A (le4s xs) -> In (A, 4 * kc) (lbl LB9) -> vec32A LB9 m9 v A xs kc).
    { intros m9 LB9 HC HB HIn.
      pose proof (rw_cells_split3 _ _ _ _ _ HC) as (C0' & C8' & C16').
      pose proof (mdef_of_rw_cells_hi _ _ _ HC ltac:(unfold AIMG_TOP; lia)) as MD. cbn [cells_size csize] in MD.
      unfold vec32A, vec32. rewrite XSL.
      split; [lia|]. split; [lia|]. split; [exact MD|]. split; [lia|].
      split; [right; split; [lia|]; split; [exact A16|]; split; [lia|]; split; [lia|]; split; [exact HIn | exact HNEW]|].
      split; [apply fld_of_rw_cells8; [exact C0' | lia]|].
      split; [apply fld_of_rw_cells8; [exact C8' | lia]|].
      split; [apply fld_of_rw_cells8; [exact C16' | lia]|].
      intros i Hi. split; [exact (proj1 (FE i Hi))|]. apply fld_of_le4s; [exact HB | lia]. }
    destruct (Z.eq_dec b 0) as [Z0|NZ].
    -
      destruct (T9Z R8 F fc m8 A (spz - 80) v cap b kc T9P Z0) as (R9 & M9 & Hms & EM9 & K2 & K10 & K11 & KK).
      subst M9.
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R9 HF9) in VIS1.
      eapply (rt_s_end msF1 mo1 sk8 m8 R9 pid' A e8 VIS1 HF9).
      + exact (B11F R9 m8 K2 FR8).
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 20%bv ltac:(inb)). exact G20.
      + rewrite (KK 21%bv ltac:(inb)). exact G21.
      + rewrite (KK 22%bv ltac:(inb)). exact G22.
      + rewrite (KK 23%bv ltac:(inb)). exact G23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR1.
      + eapply (ah_mpres_trans H HH); [exact MP8 | exact MP1].
      + exact MI8.
      + exact ST8.
      + exact ERR8.
      + exact RA8.
      + eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact rt_X1_sub].
      + exact ABR.
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact RH8.
      + apply VEC9; [exact HDR | exact BUF | ]. unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + exact SHA.
      + exact ADV8.
      + exact (proj2 HDR).
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact OW8.
      + exact RF8.
      + exact AC8.
      + exact S08.
      + assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia.
    -
      assert (Hc : 0 < cap) by (destruct OB as [[E1 _]|(Hc & _)]; [contradiction | lia]).
      destruct (rt_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & _).
      destruct (T9D R8 F fc m8 A (spz - 80) v cap b kc T9P NZ) as (R9 & M9 & Hms & EM9 & K1 & K2w & K10 & K11 & KK).
      subst M9.
      assert (K2 : getr R9 2 = Z_to_bv 64 (spz - 80)) by exact K2w.
      pose proof (msteps_full asegs _ _ Hms HF8) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR8 | exact VIS8 | exact HF8 | exact Hms |].
      intros msF9 mo9 KR9 MP9 VIS9.
      assert (K4 : getr R9 4 = tp) by (rewrite (KK 4%bv ltac:(inb)); exact G4).
      assert (K8 : getr R9 8 = Z_to_bv 64 0) by (rewrite (KK 8%bv ltac:(inb)); exact G8).
      assert (HINx : In (pid, b, 4 * cap) ((pid', A, 4 * kc) :: LB)) by (right; exact HIn).
      assert (HINo : In (pid, b, 4 * cap) ((pid', A, 4 * kc) :: LBo)) by (right; exact (rt_old_own Hc)).
      destruct (rw_cells_of_own _ m8 (pid, b, 4 * cap) OW8 HINo ltac:(cbn [blk_addr blk_size fst snd]; exact OI) ltac:(cbn [blk_addr blk_size fst snd]; lia)) as (obs & OC8).
      cbn [blk_addr blk_size fst snd] in OC8.
      destruct (rt_blk_shad sk8 m8 _ pid b (4 * cap) RH8 HINx) as (sbs & SHB & SHL).
      assert (CFB : as_Cf H (4 * cap) <= as_AL H sk8) by lia.
      assert (SP80 : (spz - 80) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
      destruct (rt_E0_even 276 ltac:(lia) eq_refl) as [ER1 ER2].
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (p := pid) (A := b) (n := 4 * cap) (LB := (pid', A, 4 * kc) :: LB) (lo := lo) (B := B)
          (errv := e8) (CH := []) (bs := obs) (sbs := sbs);
          [ exact VIS9 | exact RH8 | exact KR9 | exact HINx | exact CFB | exact OC8 | exact SHB | exact SHL
          | exact RA8 | rewrite K2, u64_of_Z by lia; lia
          | rewrite K2, u64_of_Z by lia; exact (proj1 (stk_split asegs m8 lo (spz - 80) spz ST8 ltac:(lia)))
          | exact LO1 | rewrite K2, u64_of_Z by lia; unfold AFREE_STACK; lia
          | rewrite K4; exact ERR8 | exact MI8 | rewrite K4; exact TPV | rewrite K2, u64_of_Z by lia; exact SP80 | exact AC8
          | rewrite K8, u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite K1; cbn [map]; unfold wz; rewrite u64_of_Z by lia; pose proof DRA as DRA0; unfold E0 in DRA0; rewrite <- DRA0; exact TRO
          | exact K10 ]. }
      intros c2 POST. destruct c2 as [msF2 mo2].
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m9 & s9'
                        & VIS2 & KR2 & MP2 & MI9 & ST9 & ERR9 & RA9 & AP9 & RH9 & AC9 & AL9).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite K1 in VIS2. unfold wz in VIS2. rewrite (ret_pc_even (rv_entry RESV_TYP + 276) ER1 ER2) in VIS2.
      rewrite K2, u64_of_Z in ST9, AP9 by lia. rewrite K4 in ERR9.
      assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
      pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
      assert (RMx : as_lb_remove H pid ((pid', A, 4 * kc) :: LB) = (pid', A, 4 * kc) :: as_lb_remove H pid LB).
      { apply L2. cbn [blk_id fst]. exact NEQ. }
      rewrite RMx in AP9, RH9.
      assert (XPF0 : xpres H LB (spz - 80) (v4_oldx b (4 * cap)) m8 m9).
      { eapply (xpres_of_apres_rm H HH sk8 LB ((pid', A, 4 * kc) :: LB) (spz - 80) _ m8 m8 m9 pid b (4 * cap) RH8 HINx);
          [intros bb Hb; right; exact Hb | rewrite RMx; exact AP9 | |].
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia.
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. right. left. cbn [fst snd]. lia. }
      assert (XPF : xpres H LB spz (v4_oldx b (4 * cap)) m8 m9)
        by (eapply (xpres_weaken H); [exact XPF0 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]).
      assert (HDR9 : rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * ns)); C8 (Z_to_bv 64 (A + 4 * kc))]).
      { eapply (xpres_rw_cells H); [exact XPF | exact HDR | exact (rt_xc_hdr Hc)]. }
      assert (FR9 : rw_cells asegs m9 (spz - 48) FRAME) by (eapply (apres_rw_cells H); [exact AP9 | exact FR8 | left; lia]).
      assert (INA : In (pid', A, 4 * kc) ((pid', A, 4 * kc) :: as_lb_remove H pid LB)) by (left; reflexivity).
      eapply (rt_s_end msF2 mo2 s9' m9 _ pid' A e8 VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      + apply B11F; [exact K2w | exact FR9].
      + exact (eq_trans (KK 3%bv ltac:(inb)) G3).
      + exact K4.
      + exact (eq_trans (KK 20%bv ltac:(inb)) G20).
      + exact (eq_trans (KK 21%bv ltac:(inb)) G21).
      + exact (eq_trans (KK 22%bv ltac:(inb)) G22).
      + exact (eq_trans (KK 23%bv ltac:(inb)) G23).
      + exact (eq_trans (KK 24%bv ltac:(inb)) G24).
      + exact (eq_trans (KK 25%bv ltac:(inb)) G25).
      + exact (eq_trans (KK 26%bv ltac:(inb)) G26).
      + exact (eq_trans (KK 27%bv ltac:(inb)) G27).
      + exact KR2.
      + eapply (ah_mpres_trans H HH); [exact MP8 | eapply (ah_mpres_trans H HH); [exact MP9 | exact MP2]].
      + exact MI9.
      + eapply (stk_merge asegs); [exact ST9 | | lia].
        eapply (apres_stk H); [exact AP9 | exact (proj2 (stk_split asegs m8 lo (spz - 80) spz ST8 ltac:(lia))) | lia].
      + exact ERR9.
      + exact RA9.
      + eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact rt_X1_sub] |].
        eapply (xpres_weaken H); [exact XPF | lia | intros bb Hb; exact Hb | intros a Ha; right; exact Ha].
      + exact ABR.
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. exact RH9.
      + apply VEC9; [exact HDR9 | |].
        * eapply (apres_bytes_at H); [exact AP9 | exact BUF |]. rewrite le4s_length. eapply (aclient_range_block H); [exact INA | lia |].
          unfold Zlen in XSL. lia.
        * unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + eapply (apres_SHAD H); [exact AP9 | exact SHA |]. rewrite cc_gen_length by lia. eapply (aclient_range_block_sh H). exact INA.
      + destruct ADV8 as [AN (SA0 & SA8 & [UB UW])]. split; [exact AN|]. split; [exact SA0|]. split; [exact SA8|].
        assert (XCS : xclient_range H LB spz (v4_oldx b (4 * cap)) (sh v) (Z.of_nat (length (shadow_of 24)))).
        { rewrite shadow_of_length by lia. rewrite v4_nsh24. exact (rt_xc_hdrsh Hc). }
        split; [eapply (xpres_bytes_at H); [exact XPF | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XPF | exact UW | exact XCS]].
      + exact (proj2 HDR9).
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
        eapply (lb_own_apres H); [| exact AP9 | intros bb [Hb|Hb]; [left; exact Hb | right; exact (rt_rm_incl _ _ Hb)]].
        eapply lb_own_incl; [| exact OW8]. intros bb [Hb|Hb]; [left; exact Hb | right; exact (L3 _ _ _ Hb)].
      + exact (RFS_via_apres H HH LF _ _ m8 m9 RF8 AP9).
      + exact AC9.
      + eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP9) | exact S08 | apply Forall_nil].
      + lia.
  Qed.

  Lemma rt_s8 : forall (msF7 : machine_state) (mo7 : Model) (sk7 : as_St H) (m7 : mem) (R7 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk7 msF7 = MS R7 F (Z_to_bv 64 AANNOTATE_CC) fc None m7 (seg_rom asegs) -> rfull R7 ->
    getr R7 1 = Z_to_bv 64 (E0 + 208) -> getr R7 10 = Z_to_bv 64 A -> getr R7 11 = Z_to_bv 64 (A + 4 * kc) ->
    getr R7 12 = Z_to_bv 64 (A + 4 * kc) -> getr R7 13 = Z_to_bv 64 (A + 4 * ns) ->
    rt_T9at R7 m7 A -> getr R7 3 = gp -> getr R7 4 = tp -> getr R7 8 = Z_to_bv 64 0 ->
    getr R7 20 = s4 -> getr R7 21 = s5 -> getr R7 22 = s6 -> getr R7 23 = s7 ->
    getr R7 24 = s8 -> getr R7 25 = s9 -> getr R7 26 = s10 -> getr R7 27 = s11 ->
    as_AKREL H sk7 (mkCfg msF7 mo7) -> as_MPRES H mo mo7 ->
    rt_mid sk7 m7 pid' A rt_X1 -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * ns)); C8 (Z_to_bv 64 (A + 4 * kc))] ->
    bytes_at asegs m7 A (le4s xs) ->
    SHAD m7 A (cc_gen (4 * kc) (4 * kc)) -> addressable m7 v 24 ->
    as_SR H Q (mkCfg msF7 mo7).
  Proof.
    intros msF7 mo7 sk7 m7 R7 pid' A VIS7 HF7 G1 G10 G11 G12 G13 T9P G3 G4 G8 G20 G21 G22 G23 G24 G25 G26 G27 KR7 MP7
      MID ABR NI HDR BUF SHA ADV7.
    pose proof MID as (MI7 & ST7 & _ & _ & AC7 & _ & _ & RH7 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof rt_vec_facts as (_ & _ & _ & _ & C0 & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (HNEW : v + 24 <= A \/ A + 4 * kc <= v) by (eapply rt_hdr_fresh; [exact RH7 | exact NI | lia]).
    unfold rt_T9at, rvt_T9_pre in T9P.
    destruct T9P as (G2 & FS0 & FS8 & FS16 & FS24 & FS32 & RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
    rewrite (rfull_eq R7 HF7) in VIS7.
    eapply (ahh_evt_then H HH); [exact KR7 | exact VIS7 | |].
    { eapply HANN with (beg := A) (len := 4 * kc) (oldmid := 4 * kc) (newmid := 4 * ns) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact (v4_mod16_8 A A16).
      - lia.
      - lia.
      - lia.
      - exact AAP.
      - unfold AAPP_HI; lia.
      - exact SHA.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. exact (proj1 (stk_split asegs m7 lo (spz - 80) spz ST7 ltac:(lia))).
      - exact LO1.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI7.
      - exact AC7.
      - unfold in_app_mem. destruct (rt_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF8 mo8 KR8 MP8 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m8
                      & VIS8 & MU8 & WM8 & MI8 & ST8 & SH8 & AC8).
    rewrite G2 in MU8, ST8. unfold wz in MU8, ST8. rewrite u64_of_Z in MU8, ST8 by lia. unfold AINTRIN_STACK in MU8.
    rewrite G1 in VIS8. destruct (rt_E0_even 208 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 208) ER1 ER2) in VIS8.
    assert (W8 : Forall (rt_wk A rt_X1) [(sh A, sh A + nsh (4 * kc)); (spz - 80 - 4096, spz - 80)]).
    { apply Forall_cons; [right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (DSV : disjoint_from [(sh A, sh A + nsh (4 * kc)); (spz - 80 - 4096, spz - 80)] v 24).
    { pose proof (v4_app_sh v 24 A (4 * kc) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. destruct OBJ as (_ & _ & _ & _ & _ & SD).
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSA : disjoint_from [(sh A, sh A + nsh (4 * kc)); (spz - 80 - 4096, spz - 80)] A (4 * kc)).
    { pose proof (v4_app_sh A (4 * kc) A (4 * kc) ltac:(lia) ltac:(lia) ltac:(lia) (rt_band_of_aapp _ _ AAP)) as D.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSS : disjoint_from [(sh A, sh A + nsh (4 * kc)); (spz - 80 - 4096, spz - 80)] (sh v) (nsh 24)).
    { pose proof (v4_sh_apart v 24 A (4 * kc) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 A A16) ltac:(lia) ltac:(lia) HNEW) as D.
      pose proof (sh_nsh_high v 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; destruct VBAND; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSP : forall a, spz - 80 <= a <= spz - 8 ->
                  disjoint_from [(sh A, sh A + nsh (4 * kc)); (spz - 80 - 4096, spz - 80)] a 8).
    { intros a Ha. pose proof (sh_nsh_high A (4 * kc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2.
      unfold AHI_LO in D2. cbn. split; [lia | split; [lia | exact I]]. }
    assert (FMU : forall a z, fldA m7 a 8 z -> disjoint_from [(sh A, sh A + nsh (4 * kc)); (spz - 80 - 4096, spz - 80)] a 8 ->
                  0 <= a -> a + 8 < 2 ^ 64 -> fldA m8 a 8 z).
    { intros a z Fa D Ha0 Ha1. unfold fldA in Fa |- *. eapply fld_agree; [exact Ha0 | exact Ha1 | exact Fa |].
      intros y Hy. red in Hy. apply MU8. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia]. }
    assert (ADV8 : addressable m8 v 24) by (eapply addressable_transport; [exact ADV7 | exact MU8 | exact WM8 | exact DSS]).
    eapply (rt_s9 msF8 mo8 sk7 m8 _ pid' A VIS8 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold rt_T9at, rvt_T9_pre.
      split; [exact G2|].
      split; [eapply FMU; [exact FS0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS8 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS16 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS24 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS32 | apply DSP; lia | lia | lia]|].
      split; [exact RG1|]. split; [exact RG2|]. split; [exact RG3|]. split; [exact RG4|]. split; [exact RG5|].
      split; [exact RG6|]. split; [exact RG7|]. split; [exact RG8|]. split; [exact RG9|]. exact RG10.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G20.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR8.
    - eapply (ah_mpres_trans H HH); [exact MP7 | exact MP8].
    - eapply rt_mid_munch; [exact MID | exact ABR | exact NI | exact MU8 | exact WM8 | exact MI8 | exact W8].
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact HDR | exact MU8 | exact WM8 | exact DSV].
    - eapply bytes_at_transport; [exact BUF | exact MU8 |]. eapply rt_dj_sub; [exact DSA | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - exact SH8.
    - exact ADV8.
  Qed.

  Lemma rt_s7 : forall (msF6 : machine_state) (mo6 : Model) (sk6 : as_St H) (m6 : mem) (R6 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk6 msF6 = MS R6 F (Z_to_bv 64 970144) fc None m6 (seg_rom asegs) -> rfull R6 ->
    rt_T7at R6 m6 A -> getr R6 3 = gp -> getr R6 4 = tp -> getr R6 27 = s11 ->
    as_AKREL H sk6 (mkCfg msF6 mo6) -> as_MPRES H mo mo6 ->
    rt_mid sk6 m6 pid' A rt_X0 -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    bytes_at asegs m6 A (le4s xs) ->
    SHAD m6 A (cc_gen (4 * kc) (4 * kc)) ->
    as_SR H Q (mkCfg msF6 mo6).
  Proof.
    intros msF6 mo6 sk6 m6 R6 pid' A VIS6 HF6 T7P G3 G4 G27 KR6 MP6 MID ABR NI BUF SHA.
    pose proof RUNS as (_ & _ & _ & _ & _ & T7 & _).
    pose proof MID as (MI6 & ST6 & _ & _ & _ & _ & _ & RH6 & FR6 & XP6 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof rt_vec_facts as (_ & _ & _ & _ & C0 & OB).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (HNEW : v + 24 <= A \/ A + 4 * kc <= v) by (eapply rt_hdr_fresh; [exact RH6 | exact NI | lia]).
    destruct (rt_hdr_X0 m6 XP6) as (_ & _ & _ & ADV6 & WV6).
    unfold rt_T7at in T7P.
    destruct (T7 R6 F fc m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T7P)
      as (R7 & M7 & Hms & MU7 & WM7 & P0 & P24 & PV16 & P16 & PV8 & P8 & PV0 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13
          & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
    pose proof (msteps_full asegs _ _ Hms HF6) as HF7. cbn [ms_regs] in HF7.
    assert (MI7 : mem_inv asegs M7) by exact (msteps_mem_inv asegs _ _ Hms MI6).
    eapply (sr_blk H HH); [exact KR6 | exact VIS6 | exact HF6 | exact Hms |].
    intros msF7 mo7 KR7 MP7 VIS7. rewrite <- (rfull_eq R7 HF7) in VIS7.
    assert (MID7 : rt_mid sk6 M7 pid' A rt_X1).
    { eapply rt_mid_munch; [eapply rt_mid_weaken; [exact MID | intros a Ha; right; exact Ha] | exact ABR | exact NI
                           | exact MU7 | exact WM7 | exact MI7 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [apply rt_wk_hdr; intros a Ha; left; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof MID7 as (_ & ST7 & _ & _ & _ & _ & _ & _ & FR7 & _).
    assert (CONS8 : forall mk a w cs, rw_cells asegs mk a (C8 w :: cs) ->
                    rw_cells asegs mk a [C8 w] /\ rw_cells asegs mk (a + 8) cs).
    { intros mk a w cs Hc. change (C8 w :: cs) with ([C8 w] ++ cs) in Hc. apply rw_cells_app in Hc. exact Hc. }
    assert (JOIN8 : forall mk a w cs, rw_cells asegs mk a [C8 w] -> rw_cells asegs mk (a + 8) cs ->
                    rw_cells asegs mk a (C8 w :: cs)).
    { intros mk a w cs H1 H2. change (C8 w :: cs) with ([C8 w] ++ cs). apply rw_cells_app. split; [exact H1 | exact H2]. }
    assert (C8F : forall mk a a' z z', fldA mk a' 8 z' -> a = a' -> z = z' -> wr_at asegs mk a 8 ->
                  rw_cells asegs mk a [C8 (Z_to_bv 64 z)]).
    { intros mk a a' z z' HF -> -> HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
      split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact HF]. }
    unfold FRAME in FR7. cbn [map] in FR7.
    destruct (CONS8 _ _ _ _ FR7) as (FVv & _).
    assert (ADV7 : addressable M7 v 24).
    { eapply addressable_transport; [exact ADV6 | exact MU7 | exact WM7 |].
      pose proof (v4_app_sh v 24 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 80) 32 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (WV7 : wr_at asegs M7 v 24) by exact (wr_at_wmono _ _ _ _ WV6 WM7).
    assert (T9P : rt_T9at R7 M7 A).
    { unfold rt_T9at, rvt_T9_pre.
      split; [exact K2|].
      split; [exact P0|]. split; [exact P8|]. split; [exact P16|]. split; [exact P24|].
      split; [replace (spz - 80 + 32) with (spz - 48) by lia; exact (fld_of_rw_cells8 _ _ _ FVv ltac:(lia))|].
      split; [lia|]. split; [destruct VBAND; lia|]. split; [lia|].
      split; [destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1; lia | lia]|].
      split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|]. split; [destruct VBAND; lia|].
      split; [destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1; lia | lia]|].
      destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (HDR7 : rw_cells asegs M7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 4 * ns)); C8 (Z_to_bv 64 (A + 4 * kc))]).
    { apply JOIN8; [eapply C8F; [exact PV0 | lia | lia | eapply rt_wr_sub; [exact WV7 | lia | lia | lia]]|].
      apply JOIN8; [eapply C8F; [exact PV8 | lia | lia | eapply rt_wr_sub; [exact WV7 | lia | lia | lia]]|].
      eapply C8F; [exact PV16 | lia | lia | eapply rt_wr_sub; [exact WV7 | lia | lia | lia]]. }
    assert (DV : disjoint_from [(spz - 80, spz - 80 + 32); (v, v + 24)] A (4 * kc)) by (cbn; split; [lia | split; [lia | exact I]]).
    eapply (rt_s8 msF7 mo7 sk6 M7 R7 pid' A VIS7 HF7).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - exact K13.
    - exact T9P.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - exact K8.
    - rewrite K20. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K21. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K22. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K23. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K24. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K25. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite K26. unfold wz. apply Z_to_bv_bv_unsigned.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR7.
    - eapply (ah_mpres_trans H HH); [exact MP6 | exact MP7].
    - exact MID7.
    - exact ABR.
    - exact NI.
    - exact HDR7.
    - eapply bytes_at_transport; [exact BUF | exact MU7 |]. eapply rt_dj_sub; [exact DV | lia | rewrite le4s_length; unfold Zlen in XSL; lia].
    - eapply SHAD_transport; [exact SHA | exact MU7 | exact WM7 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh v 24 A (4 * kc) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 80) 32 A (4 * kc) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]].
    - exact ADV7.
  Qed.

  Lemma rt_s6 : forall (msF5 : machine_state) (mo5 : Model) (sk5 : as_St H) (m5 : mem) (R5 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    as_VIS H sk5 msF5 = MS R5 F (Z_to_bv 64 AASAN_MEMCPY) fc None m5 (seg_rom asegs) -> rfull R5 ->
    getr R5 1 = Z_to_bv 64 970144 -> getr R5 10 = Z_to_bv 64 A -> getr R5 11 = Z_to_bv 64 b ->
    getr R5 12 = Z_to_bv 64 (4 * ns) ->
    rt_T7at R5 m5 A -> getr R5 3 = gp -> getr R5 4 = tp -> getr R5 27 = s11 ->
    as_AKREL H sk5 (mkCfg msF5 mo5) -> as_MPRES H mo mo5 ->
    rt_mid sk5 m5 pid' A rt_X0 -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m5 A [CB (Z.to_nat (4 * ns)) jA] ->
    SHAD m5 A (cc_gen (4 * kc) (4 * kc)) -> (0 < cap -> SHAD m5 b (cc_gen (4 * cap) (4 * cap))) ->
    as_SR H Q (mkCfg msF5 mo5).
  Proof.
    intros msF5 mo5 sk5 m5 R5 pid' A jA VIS5 HF5 G1 G10 G11 G12 B7A G3 G4 G27 KR5 MP5 MID ABR NI CBA SHA OSH.
    pose proof MID as (MI5 & ST5 & _ & _ & AC5 & _ & _ & RH5 & _ & XP5 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof rt_vec_facts as (_ & _ & _ & FE & C0 & OB).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof B7A as (P2 & P8 & P9 & P18 & P19 & P22 & P23 & P24 & P25 & P20 & P21 & P26 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16
                       & FS24 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & WH & VD & WV & WS & HS0 & HS1 & HS2 & HS3 & HS4
                       & HS5 & HS6 & HS7 & HS8 & HS9 & HS10 & HS11 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & N10 & N11 & N12 & N13
                       & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22).
    assert (G2 : getr R5 2 = Z_to_bv 64 (spz - 80 - 96)) by exact P2.
    assert (OBB : (b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 4 * cap) LB /\ ablock_range H b (4 * cap))).
    { destruct OB as [E|(Hc & HIn & ABb)]; [left; exact E | right; split; [lia|]; split; assumption]. }
    assert (OB0 : 0 <= b /\ b + 4 * cap <= aceil).
    { destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (SRCB : bytes_at asegs m5 b (le4s xs)).
    { destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
      - assert (XN : xs = []) by (apply length_zero_iff_nil; unfold Zlen in XSL; lia). rewrite XN. apply bytes_at_nil. lia.
      - eapply (xpres_bytes_at H); [exact XP5 | |].
        + apply bytes_at_le4s; [intros i Hi; rewrite XSL in Hi; exact (proj2 (FE i Hi)) | lia | rewrite XSL; lia].
        + rewrite le4s_length. replace (Z.of_nat (4 * length xs)) with (4 * ns) by (unfold Zlen in XSL; lia).
          eapply rt_xcl_sub; [exact (rt_xc_old Hc) | lia | lia | lia]. }
    assert (ADA : addressable m5 A (4 * kc)) by (split; [lia | rewrite <- cc_gen_full; exact SHA]).
    rewrite (rfull_eq R5 HF5) in VIS5.
    eapply (ahh_evt_then H HH); [exact KR5 | exact VIS5 | |].
    { eapply (ah_memcpy H HH) with (src := le4s xs) (junk := jA) (lo := lo); rewrite ?G10, ?G11, ?G12, ?G2; rewrite ?u64_of_Z by lia.
      - exact SRCB.
      - rewrite le4s_length. unfold Zlen in XSL. lia.
      - exact CBA.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)]; [left; lia|].
        assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
        pose proof (ah_disj H HH _ _ _ (pid', A, 4 * kc) (pid, b, 4 * cap) RH5 (or_introl eq_refl) (or_intror HIn) NEQ) as D.
        cbn [blk_addr blk_size fst snd] in D. lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + replace (4 * ns) with 0 by lia. apply accessible_nil. unfold AAPP_HI. lia.
        + eapply (addressable_accessible m5 b (4 * cap)); [split; [lia | rewrite <- cc_gen_full; exact (OSH Hc)] | lia | lia | unfold AAPP_HI; lia].
      - eapply addressable_accessible; [exact ADA | lia | lia | unfold AAPP_HI; lia].
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + rewrite E1. replace (0 + 4 * ns) with 0 by lia. apply rt_shvis0.
        + eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_intror HIn)) | lia | lia | lia | lia | lia].
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_introl eq_refl)) | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m5 lo (spz - 80 - 96) spz ST5 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI5.
      - exact AC5.
      - lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))].
        + left. unfold ASHADOW_BASE. lia.
        + unfold in_app_mem. destruct (rt_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - unfold in_app_mem. destruct (rt_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - eapply aconst_ok_app; [exact AAP | lia | lia].
      - left; lia.
      - left; lia. }
    intros msF6 mo6 KR6 MP6 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m6
                      & VIS6 & MU6 & WM6 & MI6 & ST6 & CB6 & SB6 & AC6).
    rewrite G10, G12, G2, ?u64_of_Z in MU6 by lia. rewrite G10, G12, ?u64_of_Z in CB6 by lia. rewrite G2, u64_of_Z in ST6 by lia.
    unfold AINTRIN_STACK in MU6.
    rewrite G1 in VIS6. rewrite (ret_pc_even 970144 ltac:(lia) eq_refl) in VIS6.
    assert (W6 : Forall (rt_wk A rt_X0) [(A, A + 4 * ns); (spz - 80 - 96 - 4096, spz - 80 - 96)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (MID6 : rt_mid sk5 m6 pid' A rt_X0)
      by (eapply rt_mid_munch; [exact MID | exact ABR | exact NI | exact MU6 | exact WM6 | exact MI6 | exact W6]).
    pose proof MID6 as (_ & _ & _ & _ & _ & _ & S06 & _ & _ & XP6 & _ & _).
    destruct (rt_hdr_X0 m6 XP6) as (FV0' & FV8' & FV16' & ADV6 & _).
    assert (FT : forall a z, fldA m5 a 8 z -> spz - 80 - 96 <= a -> a + 8 <= spz -> fldA m6 a 8 z).
    { intros a z Hf Ha Hk. unfold fldA in Hf |- *. eapply fld_agree; [lia | change (Z.of_nat 8) with 8; lia | exact Hf |].
      intros y Hy. red in Hy. change (Z.of_nat 8) with 8 in Hy. apply MU6. rewrite ?u64_of_Z by lia.
      cbn [outside]. split; [lia | split; [lia | exact I]]. }
    eapply (rt_s7 msF6 mo6 sk5 m6 _ pid' A VIS6 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold rt_T7at, rvt_T7_pre.
      refine (conj P2 (conj P8 (conj P9 (conj P18 (conj P19 (conj P22 (conj P23 (conj P24 (conj P25 (conj P20 (conj P21
        (conj P26 _)))))))))))).
      refine (conj FV0' (conj FV8' (conj FV16' _))).
      do 4 (split; [eapply FT; [eassumption | lia | lia] |]).
      refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 (conj N9 _))))))))).
      refine (conj (wr_at_transport asegs _ _ _ _ WH WM6) (conj VD (conj (wr_at_transport asegs _ _ _ _ WV WM6)
        (conj (wr_at_transport asegs _ _ _ _ WS WM6) _)))).
      do 12 (split; [eapply FT; [eassumption | lia | lia] |]).
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_addressable; [exact ADV6 | change (8 * (24 / 8)) with 24; lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      split; [eapply sh0_of_stack0; [exact S06 | lia] |].
      exact (conj N10 (conj N11 (conj N12 (conj N13 (conj N14 (conj N15 (conj N16 (conj N17 (conj N18 (conj N19 (conj N20
        (conj N21 N22)))))))))))).
    - exact G3.
    - exact G4.
    - exact G27.
    - exact KR6.
    - eapply (ah_mpres_trans H HH); [exact MP5 | exact MP6].
    - exact MID6.
    - exact ABR.
    - exact NI.
    - exact (bytes_of_CB _ _ _ _ CB6).
    - eapply SHAD_transport; [exact SHA | exact MU6 | exact WM6 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh A (4 * ns) A (4 * kc) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct (rt_band_of_aapp _ _ AAP); [left|right]; lia)) as D.
      pose proof (sh_nsh_high A (4 * kc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]].
  Qed.

  Lemma rt_s5 : forall (msF4 : machine_state) (mo4 : Model) (sk4 : as_St H) (m4 : mem) (R4 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk4 msF4 = MS R4 F (Z_to_bv 64 970008) fc None m4 (seg_rom asegs) -> rfull R4 ->
    rt_T5at R4 m4 A -> getr R4 3 = gp -> getr R4 4 = tp -> getr R4 27 = s11 ->
    as_AKREL H sk4 (mkCfg msF4 mo4) -> as_MPRES H mo mo4 ->
    rt_mid sk4 m4 pid' A rt_X0 -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m4 A [CB (Z.to_nat (4 * ns)) jA] ->
    SHAD m4 A (cc_gen (4 * kc) (4 * kc)) -> SHAD m4 b (cc_gen (4 * cap) (4 * cap)) ->
    as_SR H Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 sk4 m4 R4 pid' A jA Hc VIS4 HF4 B5A G3 G4 G27 KR4 MP4 MID ABR NI CBA SHA OSH.
    pose proof RUNS as (_ & _ & _ & _ & T5 & _).
    pose proof MID as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    destruct (rt_hdr_X0 m4 XP4) as (_ & _ & _ & ADV4 & _).
    destruct (T5 R4 F fc m4 v (spz - 80) b cap A kc ns (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) (bv_unsigned s7)
                 (bv_unsigned s6) (bv_unsigned s5) (bv_unsigned s4) (A + 4 * ns) (4 * kc) v 0 (E0 + 208) B5A)
      as (R5 & M5 & Hms & EM5 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25
          & K26 & KK).
    subst M5.
    pose proof (msteps_full asegs _ _ Hms HF4) as HF5. cbn [ms_regs] in HF5.
    eapply (sr_blk H HH); [exact KR4 | exact VIS4 | exact HF4 | exact Hms |].
    intros msF5 mo5 KR5 MP5 VIS5. rewrite <- (rfull_eq R5 HF5) in VIS5.
    eapply (rt_s6 msF5 mo5 sk4 m4 R5 pid' A jA VIS5 HF5).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - pose proof B5A as BP. unfold rt_T5at, rvt_T5_pre in BP. decompose [and] BP. clear BP.
      unfold rt_T7at, rvt_T7_pre.
      repeat match goal with |- _ /\ _ => split end.
      all: try assumption.
      all: first [ eapply sh0_of_stack0; [exact S04 | lia]
                 | eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia] ].
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR5.
    - eapply (ah_mpres_trans H HH); [exact MP4 | exact MP5].
    - exact MID.
    - exact ABR.
    - exact NI.
    - exact CBA.
    - exact SHA.
    - intros _. exact OSH.
  Qed.

  Lemma rt_s4 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    0 < cap ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 AANNOTATE_CC) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = Z_to_bv 64 970008 -> getr R3 10 = Z_to_bv 64 b -> getr R3 11 = Z_to_bv 64 (b + 4 * cap) ->
    getr R3 12 = Z_to_bv 64 (b + 4 * ns) -> getr R3 13 = Z_to_bv 64 (b + 4 * cap) ->
    rt_T5at R3 m3 A -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    rt_mid sk3 m3 pid' A [] -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (4 * ns)) jA] ->
    SHAD m3 A (cc_gen (4 * kc) (4 * kc)) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA Hc VIS3 HF3 G1 G10 G11 G12 G13 B5 G3 G4 G27 KR3 MP3 MID ABR NI CBA SHA.
    pose proof B5 as (G2 & G8 & G9 & G18 & G19 & G22 & G23 & G24 & G25 & F0 & F8 & F16 & FS0 & FS8 & FS16 & FS24
                      & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & WH & P26 & WV & WS
                      & J0 & J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & Z8 & ZV8 & ZV
                      & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55 & P56).
    pose proof MID as (MI3 & ST3 & _ & _ & AC3 & _ & _ & RH3 & _ & XP3 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof rt_vec_facts as (_ & _ & _ & _ & NC & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (rt_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & NZ).
    assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 4 * cap); split; [reflexivity | exact HIn]).
    pose proof (ah_disj H HH _ _ _ (pid', A, 4 * kc) (pid, b, 4 * cap) RH3 (or_introl eq_refl) (or_intror HIn) NEQ) as DAB.
    cbn [blk_addr blk_size fst snd] in DAB.
    assert (OSH3 : SHAD m3 b (cc_gen (4 * cap) (4 * ns))).
    { eapply rt_SHAD_xpres; [exact XP3 | exact (OLDSH Hc) |]. rewrite cc_gen_length by lia.
      split; [eapply (aclient_range_block_sh H); exact HIn | apply Forall_nil]. }
    rewrite (rfull_eq R3 HF3) in VIS3.
    eapply (ahh_evt_then H HH); [exact KR3 | exact VIS3 | |].
    { eapply HANN with (beg := b) (len := 4 * cap) (oldmid := 4 * ns) (newmid := 4 * cap) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact (v4_mod16_8 b O16).
      - lia.
      - lia.
      - lia.
      - exact OAP.
      - unfold AAPP_HI; lia.
      - exact OSH3.
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs m3 lo (spz - 80 - 96) spz ST3 ltac:(lia))).
      - exact LO1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI3.
      - exact AC3.
      - unfold in_app_mem. destruct (rt_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                      & VIS4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    rewrite G2, u64_of_Z in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    rewrite G1 in VIS4. rewrite (ret_pc_even 970008 ltac:(lia) eq_refl) in VIS4.
    assert (W4 : Forall (rt_wk A rt_X0) [(sh b, sh b + nsh (4 * cap)); (spz - 80 - 96 - 4096, spz - 80 - 96)]).
    { apply Forall_cons; [|apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]].
      apply (rt_wk_oldsh Hc). intros a Ha. unfold rt_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia. }
    pose proof (v4_app_sh A (4 * kc) b (4 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (rt_band_of_aapp _ _ AAP)) as DAS.
    pose proof (v4_sh_apart A (4 * kc) b (4 * cap) ltac:(lia) ltac:(lia) (v4_mod16_8 A A16) (v4_mod16_8 b O16) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as DSS.
    pose proof (sh_nsh_high A (4 * kc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (sh_nsh_high b (4 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHB2. unfold AHI_LO in SHB2.
    assert (MID4 : rt_mid sk3 m4 pid' A rt_X0).
    { eapply rt_mid_munch; [eapply rt_mid_weaken; [exact MID | intros a Ha; destruct Ha] | exact ABR | exact NI
                           | exact MU4 | exact WM4 | exact MI4 | exact W4]. }
    pose proof MID4 as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    destruct (rt_hdr_X0 m4 XP4) as (F0' & F8' & F16' & ADV4 & WV4).
    assert (FLDT : forall a k z, spz - 80 - 96 <= a -> a + Z.of_nat k <= spz -> fldA m3 a k z -> fldA m4 a k z).
    { intros a k z Ha Hk Hf. unfold fldA in *. eapply fld_agree; [lia | lia | exact Hf |].
      intros a' Ha'. hnf in Ha'. apply MU4. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | split; [lia | exact I]]. }
    clear F0 F8 F16.
    repeat match goal with
           | Hf : fldA m3 ?a ?k ?z |- _ =>
               let Hn := fresh "T" in
               assert (Hn : fldA m4 a k z) by (apply FLDT; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hf]); clear Hf
           end.
    pose proof (wr_at_transport asegs _ _ _ _ WH WM4) as WH'.
    pose proof (wr_at_transport asegs _ _ _ _ WS WM4) as WS'.
    assert (Z8' : LbB_Kit.sh0 m4 (spz - 80 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
    assert (ZV8' : LbB_Kit.sh0 m4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV' : LbB_Kit.sh0 m4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    eapply (rt_s5 msF4 mo4 sk3 m4 _ pid' A jA Hc VIS4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold rt_T5at, rvt_T5_pre.
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G19|].
      split; [exact G22|]. split; [exact G23|]. split; [exact G24|]. split; [exact G25|].
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    - exact G3.
    - exact G4.
    - exact G27.
    - exact KR4.
    - eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
    - exact MID4.
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact CBA | exact MU4 | exact WM4 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      cbn. split; [lia | split; [lia | exact I]].
    - eapply SHAD_transport; [exact SHA | exact MU4 | exact WM4 |]. rewrite cc_gen_length by lia.
      cbn. split; [lia | split; [lia | exact I]].
    - exact SH4.
  Qed.

  Lemma rt_s3 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jall : list byte),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 (E0 + 152)) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 2 = Z_to_bv 64 (spz - 80) -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 8 = Z_to_bv 64 kc ->
    getr R2 9 = Z_to_bv 64 v -> getr R2 10 = Z_to_bv 64 A -> getr R2 18 = Z_to_bv 64 (4 * kc) ->
    getr R2 19 = Z_to_bv 64 (4 * ns) ->
    getr R2 20 = s4 -> getr R2 21 = s5 -> getr R2 22 = s6 -> getr R2 23 = s7 ->
    getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    rt_mid sk2 m2 pid' A [] -> ablock_range H A (4 * kc) -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (4 * kc)) jall] -> addressable m2 A (4 * kc) ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A jall VIS2 HF2 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR2 MP2 MID ABR NI
      CBall ADD2.
    pose proof RUNS as (_ & _ & T3a & T3b & _).
    pose proof MID as (MI2 & ST2 & _ & _ & AC2 & _ & S02 & RH2 & FR2 & XP2 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof (rt_band_of_aapp _ _ AAP) as ABND.
    pose proof rt_vec_facts as (_ & _ & _ & _ & C0 & OB).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    assert (VB2 : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    assert (XP2' : xpres H LB spz rt_X0 m m2)
      by (eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (rt_hdr_X0 m2 XP2') as (F0 & F8 & F16 & ADV2 & WV2).
    assert (WSB : wr_at asegs m2 (spz - 80) 32) by (eapply wr_at_of_stk_win; [exact ST2 | lia | lia]).
    assert (WHF : wr_at asegs m2 (spz - 80 - 96) 96) by (eapply wr_at_of_stk_win; [exact ST2 | lia | lia]).
    assert (ZV : LbB_Kit.sh0 m2 v) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV8 : LbB_Kit.sh0 m2 (v + 8)) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV16 : LbB_Kit.sh0 m2 (v + 16)) by (eapply sh0_of_addressable; [exact ADV2 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZSB : LbB_Kit.sh0 m2 (spz - 80 + 8)) by (eapply sh0_of_stack0; [exact S02 | lia]).
    assert (SHA0 : SHAD m2 A (cc_gen (4 * kc) (4 * kc))) by (rewrite cc_gen_full; exact (proj2 ADD2)).
    pose proof (sh_nsh_high A (4 * kc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (msteps_full asegs) as MSF.
    destruct OB as [[E1 E2]|(Hc & HIn & ABb)].
    -
      assert (N0 : ns = 0) by lia.
      assert (BM4 : b mod 4 = 0) by (rewrite E1; reflexivity).
      pose proof (T3b R2 F fc m2 A (spz - 80) v kc b cap ns) as T3b'.
      match type of T3b' with _ -> ?P => assert (EX : P) end.
      { apply T3b'. unfold rvt_T3b_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
      destruct EX as (R3 & M3 & Hms & MU3 & WM3 & W0 & W1 & W2 & W3 & W4 & W5 & W6 & Y7 & Y8 & Y9 & Y10 & Y11 & S24 & S16 & S8 & S0
                      & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      assert (MID3 : rt_mid sk2 M3 pid' A []).
      { eapply rt_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof MID3 as (_ & _ & _ & _ & _ & _ & S03 & _ & _ & XP3 & _ & _).
      assert (XP3' : xpres H LB spz rt_X0 m M3)
        by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (rt_hdr_X0 M3 XP3') as (F0' & F8' & F16' & ADV3 & WV3).
      rewrite G26 in W0. rewrite G25 in W1. rewrite G24 in W2. rewrite G23 in W3. rewrite G22 in W4. rewrite G21 in W5.
      rewrite G20 in W6.
      assert (W0' : fldA M3 (spz - 80 - 96) 8 (bv_unsigned s10)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (W1' : fldA M3 (spz - 80 - 88) 8 (bv_unsigned s9)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W1).
      assert (W2' : fldA M3 (spz - 80 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W2).
      assert (W3' : fldA M3 (spz - 80 - 72) 8 (bv_unsigned s7)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W3).
      assert (W4' : fldA M3 (spz - 80 - 64) 8 (bv_unsigned s6)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W4).
      assert (W5' : fldA M3 (spz - 80 - 56) 8 (bv_unsigned s5)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W5).
      assert (W6' : fldA M3 (spz - 80 - 48) 8 (bv_unsigned s4)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W6).
      pose proof (wr_at_transport asegs _ _ _ _ WHF WM3) as WHF3.
      pose proof (wr_at_transport asegs _ _ _ _ WSB WM3) as WSB3.
      assert (ZS0 : LbB_Kit.sh0 M3 (spz - 80)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS8 : LbB_Kit.sh0 M3 (spz - 80 + 8)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS16 : LbB_Kit.sh0 M3 (spz - 80 + 16)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZS24 : LbB_Kit.sh0 M3 (spz - 80 + 24)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZV3 : LbB_Kit.sh0 M3 v) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV83 : LbB_Kit.sh0 M3 (v + 8)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV163 : LbB_Kit.sh0 M3 (v + 16)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (SHA3 : SHAD M3 A (cc_gen (4 * kc) (4 * kc))).
      { eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        cbn. split; [lia | exact I]. }
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (rt_s6 msF3 mo3 sk2 M3 R3 pid' A [] VIS3 HF3).
      + exact K1.
      + exact K10.
      + exact K11.
      + exact K12.
      + unfold rt_T7at, rvt_T7_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + eapply (rt_mid_weaken _ _ _ _ [] rt_X0); [exact MID3 | intros a Ha; destruct Ha].
      + exact ABR.
      + exact NI.
      + rewrite N0. change (Z.to_nat (4 * 0)) with 0%nat. apply rt_CB0. lia.
      + exact SHA3.
      + intros Hc. lia.
    -
      pose proof ABb as (O0 & O16 & On & OI & OC & OF & OAP).
      assert (B16 : 16 <= b) by (clear - O0 O16; Z.div_mod_to_equations; lia).
      assert (BM4 : b mod 4 = 0) by (clear - O16; Z.div_mod_to_equations; lia).
      pose proof (T3a R2 F fc m2 A (spz - 80) v kc b cap ns) as T3a'.
      match type of T3a' with _ -> ?P => assert (EX : P) end.
      { apply T3a'. unfold rvt_T3a_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
      destruct EX as (R3 & M3 & Hms & MU3 & WM3 & W0 & W1 & W2 & W3 & W4 & W5 & W6 & Y7 & Y8 & Y9 & Y10 & Y11 & S24 & S16 & S8 & S0
                      & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K18 & K19 & K22 & K23 & K24 & K25 & KK).
      pose proof (MSF _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
      assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
      assert (MID3 : rt_mid sk2 M3 pid' A []).
      { eapply rt_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
        apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof MID3 as (_ & _ & _ & _ & _ & _ & S03 & _ & _ & XP3 & _ & _).
      assert (XP3' : xpres H LB spz rt_X0 m M3)
        by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (rt_hdr_X0 M3 XP3') as (F0' & F8' & F16' & ADV3 & WV3).
      rewrite G26 in W0. rewrite G25 in W1. rewrite G24 in W2. rewrite G23 in W3. rewrite G22 in W4. rewrite G21 in W5.
      rewrite G20 in W6.
      assert (W0' : fldA M3 (spz - 80 - 96) 8 (bv_unsigned s10)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (W1' : fldA M3 (spz - 80 - 88) 8 (bv_unsigned s9)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W1).
      assert (W2' : fldA M3 (spz - 80 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W2).
      assert (W3' : fldA M3 (spz - 80 - 72) 8 (bv_unsigned s7)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W3).
      assert (W4' : fldA M3 (spz - 80 - 64) 8 (bv_unsigned s6)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W4).
      assert (W5' : fldA M3 (spz - 80 - 56) 8 (bv_unsigned s5)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W5).
      assert (W6' : fldA M3 (spz - 80 - 48) 8 (bv_unsigned s4)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W6).
      pose proof (wr_at_transport asegs _ _ _ _ WHF WM3) as WHF3.
      pose proof (wr_at_transport asegs _ _ _ _ WSB WM3) as WSB3.
      assert (ZS8 : LbB_Kit.sh0 M3 (spz - 80 + 8)) by (eapply sh0_of_stack0; [exact S03 | lia]).
      assert (ZV3 : LbB_Kit.sh0 M3 v) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV83 : LbB_Kit.sh0 M3 (v + 8)) by (eapply sh0_of_addressable; [exact ADV3 | change (8 * (24 / 8)) with 24; lia]).
      assert (SHA3 : SHAD M3 A (cc_gen (4 * kc) (4 * kc))).
      { eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
        cbn. split; [lia | exact I]. }
      destruct (rw_cells_CB_split asegs m2 A (Z.to_nat (4 * kc)) (Z.to_nat (4 * ns)) jall CBall ltac:(lia)) as [CBA _].
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
      intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
      eapply (rt_s4 msF3 mo3 sk2 M3 R3 pid' A (firstn (Z.to_nat (4 * ns)) jall) ltac:(lia) VIS3 HF3).
      + exact K1.
      + exact K10.
      + exact K11.
      + exact K12.
      + exact K13.
      + unfold rt_T5at, rvt_T5_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR3.
      + eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
      + exact MID3.
      + exact ABR.
      + exact NI.
      + eapply rw_cells_transport; [exact CBA | exact MU3 | exact WM3 |]. cbn [cells_size csize].
        rewrite Nat.add_0_r, Z2Nat.id by lia.
        cbn. split; [lia | exact I].
      + exact SHA3.
  Qed.

  Lemma rt_sn : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 (E0 + 152) -> getr R1 2 = Z_to_bv 64 (spz - 80) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 kc -> getr R1 9 = Z_to_bv 64 v -> getr R1 10 = Z_to_bv 64 (4 * kc) ->
    getr R1 18 = Z_to_bv 64 (4 * kc) -> getr R1 19 = Z_to_bv 64 (4 * ns) ->
    getr R1 20 = s4 -> getr R1 21 = s5 -> getr R1 22 = s6 -> getr R1 23 = s7 ->
    getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    ACONST m1 -> as_RFS H LF m1 -> stack0 m1 lo shi -> as_RHEAP H s LB m1 -> rw_cells asegs m1 (spz - 48) FRAME ->
    xpres H LB spz [] m m1 -> lb_own LBo m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 AC1 RF1 S01 RH1 FR1 XP1 OW1.
    pose proof SPR as (SPL & SPH & SP16).
    pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof rt_vec_facts as (_ & _ & _ & _ & NC & _).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (SP80 : (spz - 80) mod 16 = 0).
    { replace (spz - 80) with (spz + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact SP16. }
    assert (CMB : as_Cm H (4 * kc) <= as_AL H s).
    { assert (CF0 : 0 <= as_Cf H (4 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia. }
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 4 * kc) (LB := LB) (lo := lo) (B := B) (errv := e1);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CMB | exact RA1 | rewrite G2, u64_of_Z by lia; lia
        | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact SP80
        | exact AC1 | exact G10 | lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p
                      & sk2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. destruct (rt_E0_even 152 ltac:(lia) eq_refl) as [ER1 ER2].
    rewrite (ret_pc_even (E0 + 152) ER1 ER2) in VIS2.
    rewrite G2, u64_of_Z in AP2, ST2 by lia. rewrite G4 in ERR2.
    pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
    cbn [blk_id fst] in NI.
    eapply (rt_s3 msF2 mo2 sk2 m2 _ p A junk VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - exact G2.
    - exact G3.
    - exact G4.
    - exact G8.
    - exact G9.
    - reflexivity.
    - exact G18.
    - exact G19.
    - exact G20.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR2.
    - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    - split; [exact MI2|].
      split; [eapply (stk_merge asegs); [exact ST2 | | lia];
              eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 80) spz ST1 ltac:(lia))) | lia]|].
      split; [exists errv2; exact ERR2|].
      split; [exact RAX2|]. split; [exact AC2|].
      split; [exact (RFS_via_apres H HH LF LB _ m1 m2 RF1 AP2)|].
      split; [eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]|].
      split; [exact RH2|].
      split; [eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]|].
      split; [eapply (xpres_trans H); [exact XP1 |];
              eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]|].
      split; [exact AL2|].
      apply lb_own_cons; [exact (own_of_rw_cells _ _ _ _ CB2 ltac:(lia)) | exact (lb_own_apres H _ _ _ _ _ OW1 AP2 OINC)].
    - exact ABR.
    - exact NI.
    - exact CB2.
    - exact ADDR.
  Qed.

  Lemma rt_mainN : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 kc) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 E0) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof RUNS as (_ & B1N & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof rt_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (OB0 : 0 <= b /\ b + 4 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 kc) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    assert (PRE : rvt_T1_pre R0 m v kc spz b cap ns).
    { unfold rvt_T1_pre. rewrite HR0.
      repeat match goal with |- _ /\ _ => split end;
        first [ reflexivity | exact rt_spz_sp | assumption | lia
              | (eapply wr_at_of_stk_win; [exact ST0 | lia | lia])
              | (eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]) ]. }
    destruct (B1N R0 F fc m v kc spz b cap ns PRE CK)
      as (R1 & M1 & Hms & MU1 & WM1 & Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14
          & K18 & K19 & KK).
    rewrite HR0 in Q1, Q2, Q3, Q4, Q5.
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    assert (SWL : aceil <= spz - 48) by lia.
    destruct (stack_window_ok H LB LF (spz - 48) spz SWL FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 48, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (ST1 : stk asegs M1 lo spz) by (apply (stk_high_transport m M1 lo spz ST0 WM1); unfold AIMG_TOP; lia).
    assert (C8F : forall a w, LbB_RwSem.fldw asegs M1 a 8 w -> spz - 48 <= a -> a + 8 <= spz -> rw_cells asegs M1 a [C8 w]).
    { intros a w Hf Ha1 Ha2. split.
      - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact Hf].
      - eapply wr_at_of_stk_win; [exact ST1 | lia | cbn; lia]. }
    assert (FRM : rw_cells asegs M1 (spz - 48) FRAME).
    { unfold FRAME. cbn [map].
      apply rw_cells_cons8; [apply C8F; [exact Q0 | lia | lia]|]. replace (spz - 48 + 8) with (spz - 40) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q1 | lia | lia]|]. replace (spz - 40 + 8) with (spz - 32) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q2 | lia | lia]|]. replace (spz - 32 + 8) with (spz - 24) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q3 | lia | lia]|]. replace (spz - 24 + 8) with (spz - 16) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q4 | lia | lia]|]. replace (spz - 16 + 8) with (spz - 8) by lia.
      apply C8F; [exact Q5 | lia | lia]. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia | exact I]. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_of_munch H s LB spz [] [(spz - 48, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (OW1 : lb_own LBo M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (rt_sn msF1 mo1 M1 R1 errv VIS1 HF1).
    - exact K1.
    - exact K2.
    - rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
    - exact K8.
    - exact K9.
    - exact K10.
    - exact K18.
    - exact K19.
    - rewrite (KK 20%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 21%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 22%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 23%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 24%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 25%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 26%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 27%bv ltac:(inb)), HR0. reflexivity.
    - exact KR1.
    - exact MP1.
    - exact MI1.
    - exact ST1.
    - exact ERR1.
    - exact RA1.
    - exact AC1.
    - exact RF1.
    - exact S01.
    - exact RH1.
    - exact FRM.
    - exact XP1.
    - exact OW1.
  Qed.
  End RtN.
End RtS.

Theorem resv_typ_ok {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> resv32_stmt H RESV_TYP.
Proof.
  intros H HH. unfold resv32_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LBo LF
    v b xs cap k pid lo B shi errv.
  intros VIS -> -> VEC V8 ADV OBJ VBAND VWR OWN OINC OND OLD OLDSH K0 GROW RH KR AOKCM TRO RA SPB SP16 SP47 ST CE LOl
    ERR MI TPV RA2 AC RF S0 SHI.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  assert (SPR : 2 ^ 45 <= bv_unsigned sp - 80 /\ bv_unsigned sp <= 2 ^ 47 /\ bv_unsigned sp mod 16 = 0).
  { unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl. split; [lia|]. split; [exact SP47 | exact SP16]. }
  assert (LOR : aceil <= lo /\ lo <= bv_unsigned sp - RESV_STACK) by (split; [exact CE | exact LOl]).
  pose proof rvt_runs_ec788 as RUNS.
  destruct (Z_lt_le_dec cap k) as [CK | CK].
  - destruct (AOKCM CK) as [AOK CM].
    eapply rt_mainN with (ns := Zlen xs) (spz := bv_unsigned sp) (kc := k) (cap := cap) (b := b) (pid := pid) (LBo := LBo);
      try eassumption; reflexivity.
  - eapply rt_mainR with (ns := Zlen xs) (spz := bv_unsigned sp) (kc := k) (cap := cap) (b := b) (pid := pid) (LBo := LBo);
      try eassumption; reflexivity.
Qed.
