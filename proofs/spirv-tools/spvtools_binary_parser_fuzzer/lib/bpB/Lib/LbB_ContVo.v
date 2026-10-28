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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_VoWS LbB_VoWHlpS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_Own LbB_ContStmt LbB_ContV4R LbB_ContV4.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma vo_vopnd_new : forall LB' m' v A n cap',
  rw_cells asegs m' v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * n)); C8 (Z_to_bv 64 (A + 20 * cap'))] ->
  0 < A -> A mod 16 = 0 -> 0 <= n <= cap' -> 0 < cap' -> A + 20 * cap' <= 2 ^ 47 -> In (A, 20 * cap') (lbl LB') ->
  (v + 24 <= A \/ A + 20 * cap' <= v) -> AIMG_TOP <= v -> v + 24 <= 2 ^ 47 ->
  vopndA LB' m' v A n cap'.
Proof.
  intros LB' m' v A n cap' HC A0 A16 Hn Hc Hhi HIn Hd Hv0 Hv1.
  pose proof (rw_cells_split3 _ _ _ _ _ HC) as (C0 & C8' & C16).
  pose proof (mdef_of_rw_cells_hi _ _ _ HC Hv0) as MD. cbn [cells_size csize] in MD.
  unfold vopndA, vec_opnd, OPND_SZ. unfold AIMG_TOP in Hv0.
  split; [lia|]. split; [lia|]. split; [exact MD|]. split; [lia|].
  split; [right; split; [lia|]; split; [exact A16|]; split; [lia|]; split; [lia|]; split; [exact HIn | exact Hd]|].
  split; [apply fld_of_rw_cells8; [exact C0 | lia]|].
  split; [apply fld_of_rw_cells8; [exact C8' | lia]|].
  apply fld_of_rw_cells8; [exact C16 | lia].
Qed.
Definition vo_runs (E : Z) : Prop :=
  vop_B1T E /\ vop_B1F E /\ vop_B3 E /\ vop_B4 E /\ vop_B5D E /\ vop_B5N E /\ vop_B9 E
  /\ voh_Q1A 0xec8f8 /\ voh_Q1Z 0xec8f8 /\ voh_Q2 0xec8f8 /\ voh_Q3 0xec8f8 /\ v4_ret_ok (E + 548).

Lemma v4_ret_ok_fc624 : v4_ret_ok (VOPND_SLOW_ENTRY + 548).
Proof. unfold VOPND_SLOW_ENTRY. v4_ret_tac. Qed.

Lemma vo_runs_fc400 : vo_runs VOPND_SLOW_ENTRY.
Proof.
  exact (conj vop_B1T_fc400 (conj vop_B1F_fc400 (conj vop_B3_fc400 (conj vop_B4_fc400 (conj vop_B5D_fc400
    (conj vop_B5N_fc400 (conj vop_B9_fc400 (conj voh_Q1A_ec8f8 (conj voh_Q1Z_ec8f8 (conj voh_Q2_ec8f8
    (conj voh_Q3_ec8f8 v4_ret_ok_fc624))))))))))).
Qed.

Section VoS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
            (v b cap src : Z) (bs : list byte) (pid : bptr) (lo B shi spz : Z).
  Hypothesis RUNS : vo_runs VOPND_SLOW_ENTRY.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis SPZ : bv_unsigned sp = spz.
  Hypothesis SPR : 2 ^ 45 <= spz - 96 /\ spz <= 2 ^ 47 /\ spz mod 16 = 0.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [VOPND_DEL_RA].
  Hypothesis VBAND : (0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47).
  Hypothesis OBJ : obj_win H LB LF spz lo v 24.
  Hypothesis V8 : v mod 8 = 0.
  Hypothesis VEC : vopndA LB m v b cap cap.
  Hypothesis OLD : (b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, OPND_SZ * cap) LB).
  Hypothesis OLDSH : 0 < cap -> SHAD m b (cc_gen (20 * cap) (20 * cap)).
  Hypothesis GROW : 20 * v4_newcap cap <= 2 ^ 26.
  Hypothesis SRC : srcb_keep H LB spz m src bs.
  Hypothesis SRCL : Z.of_nat (length bs) = 20.
  Hypothesis SRCA : in_app_mem src (src + 20).
  Hypothesis SRCD : src + 20 <= lo \/ spz <= src.
  Hypothesis SRCC : aclient_range H LB spz src 20 \/ src + 20 <= AIMG_TOP.
  Hypothesis RH0 : as_RHEAP H s LB m.
  Hypothesis AOK : as_alloc_ok H s LB (20 * v4_newcap cap).
  Hypothesis CM : as_Cm H (20 * v4_newcap cap) + as_Cf H (20 * cap) <= as_AL H s.
  Hypothesis RA0 : as_rauxv_ok H m B.
  Hypothesis SPB : spz <= B.
  Hypothesis ST0 : stk asegs m lo spz.
  Hypothesis LOR : aceil <= lo /\ lo <= spz - VOPND_STACK.
  Hypothesis MI0 : mem_inv asegs m.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis AC0 : ACONST m.
  Hypothesis RF0 : as_RFS H LF m.
  Hypothesis S00 : stack0 m lo shi.
  Hypothesis SHI : spz <= shi.
  Hypothesis ADV0 : addressable m v 24.
  Hypothesis VWR : wr_at asegs m v 24.
  Hypothesis OWN : lb_own LB m.

  Let cap' := v4_newcap cap.
  Let Q := vopnd_slow_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap pid lo B shi m mo.
  Let FRAME : list cell := map (fun w => C8 w) [Z_to_bv 64 v; s5; s4; s3; s2; s1; s0; ra].

  Lemma spz_sp : sp = Z_to_bv 64 spz.
Proof.
  Proof. rewrite <- SPZ. symmetry. apply Z_to_bv_bv_unsigned. Qed.


  Definition vo_B3at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vop_B3_pre R mk A (spz - 96) v src cap b cap'.

  Definition vo_B4at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vop_B4_pre R mk A (spz - 96) v src cap b cap'.

  Definition vo_Q1at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    voh_Q1_pre R mk v (spz - 96) b cap A cap'.

  Definition vo_Q2at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    voh_Q2_pre R mk v (spz - 96) b cap A cap' (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) (bv_unsigned s7)
      (bv_unsigned s6) src (20 * cap) cap' (sh (v + 8)) v (v + 8) (VOPND_SLOW_ENTRY + 428).

  Definition vo_Q3at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    voh_Q3_pre R mk v (spz - 96) b cap A cap' (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) (bv_unsigned s7)
      (bv_unsigned s6) src (20 * cap) cap' (sh (v + 8)) v (v + 8) (VOPND_SLOW_ENTRY + 428).

  Definition vo_B5at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vop_B5_pre R mk A (spz - 96) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
      (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5).

  Definition vo_B9at (R : bvmap 5 word) (mk : mem) (A : Z) : Prop :=
    vop_B9_pre R mk A (spz - 96) cap (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
      (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5).

  Definition vo_mid (sk : as_St H) (mk : mem) (pid' : bptr) (A : Z) (Xk : list (Z * Z)) : Prop :=
    mem_inv asegs mk /\ stk asegs mk lo spz /\ (exists e, rw_cells asegs mk (errno_addr tp) [C4 e]) /\ as_rauxv_ok H mk B
    /\ ACONST mk /\ as_RFS H LF mk /\ stack0 mk lo shi /\ as_RHEAP H sk ((pid', A, 20 * cap') :: LB) mk
    /\ rw_cells asegs mk (spz - 64) FRAME /\ xpres H LB spz Xk m mk /\ as_AL H sk >= as_AL H s - as_Cm H (20 * cap')
    /\ lb_own ((pid', A, 20 * cap') :: LB) mk.

  Definition vo_wk (A : Z) (Xk : list (Z * Z)) (iv : Z * Z) : Prop :=
    (aceil <= fst iv /\ snd iv <= spz - 64)
    \/ (A <= fst iv /\ snd iv <= A + 20 * cap')
    \/ (sh A <= fst iv /\ snd iv <= sh A + nsh (20 * cap'))
    \/ ((forall a, fst iv <= a < snd iv -> rin_ivs Xk a) /\ aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv
        /\ stack0_ok iv /\ (snd iv <= spz - 64 \/ spz <= fst iv) /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)).

  Lemma vo_cls : forall s' LBx p A n SP m0 a,
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

  Lemma vo_xpres_mixed : forall s' p A n SP X m0 m1 m2 W,
    as_RHEAP H s' ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) -> aceil <= SP ->
    munch W m1 m2 -> wmono asegs m1 m2 ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H LB SP X m1 m2.
  Proof.
    intros s' p A n SP X m0 m1 m2 W RH NI HSP MU WM FW a Ha [Hc Hx].
    pose proof (vo_cls s' LB p A n SP m0 a RH NI HSP Hc) as CLS.
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

  Lemma vo_mid_munch : forall sk mk mk' pid' A Xk W,
    vo_mid sk mk pid' A Xk -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    munch W mk mk' -> wmono asegs mk mk' -> mem_inv asegs mk' -> Forall (vo_wk A Xk) W ->
    vo_mid sk mk' pid' A Xk.
  Proof.
    intros sk mk mk' pid' A Xk W (MI & ST & (e & ERR) & RA & AC & RF & S0 & RH & FR & XP & AL & OW) ABR NI MU WM MI' FW.
    destruct SPR as (SPL & SPH & SP16). destruct LOR as [LO1 LO2].
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
    pose proof (ah_fsb H HH _ _ _ RH) as (FS1 & FS2 & FS3 & FS4).
    assert (SHAb : sh A + nsh (20 * cap') <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHAl : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHAC : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHIT : sh AIMG_TOP <= sh A) by (unfold sh, AIMG_TOP; Z.div_mod_to_equations; lia).
    assert (VSPZ : AIMG_TOP <= lo) by (unfold AIMG_TOP; lia).
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.

    assert (W1 : Forall (aclient_write_ok H ((pid', A, 20 * cap') :: LB)) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold vo_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & Hw & _)]]].
      - left. cbn. lia.
      - right; right; left. exists (pid', A, 20 * cap'). split; [left; reflexivity | cbn; lia].
      - right; right; right; left. exists (pid', A, 20 * cap'). split; [left; reflexivity | cbn; lia].
      - unfold aclient_write_ok in *.
        destruct Hw as [K|[K|[(b' & Hb & K)|[(b' & Hb & K)|K]]]]; [left; exact K | right; left; exact K | | | right; right; right; right; exact K].
        + right; right; left. exists b'. split; [right; exact Hb | exact K].
        + right; right; right; left. exists b'. split; [right; exact Hb | exact K]. }
    assert (W2 : Forall (afs_write_ok H LF) W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold vo_wk in Hw. cbn [fst snd] in Hw.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4, BAPP. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & Hw & _)]]]; [left; cbn; unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia | | | exact Hw].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct BF; lia | lia].
      - left. cbn. unfold AFS_SIZE, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. split; [destruct FS4; lia | lia]. }
    assert (W3 : Forall aconst_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold vo_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia].
      - eapply (aconst_ok_app A (20 * cap')); [exact BAPP | lia | lia].
      - apply aconst_ok_high; [lia | right; left; lia]. }
    assert (W4 : Forall stack0_ok W).
    { eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold vo_wk in Hw. cbn [fst snd] in Hw.
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & Hw & _)]]]; [| | | exact Hw].
      - left. cbn. unfold AHI_LO. lia.
      - eapply (stack0_ok_aapp A (20 * cap')); [exact BAPP | lia | lia].
      - right. cbn. lia. }
    destruct (client_frame H HH sk _ LF B W mk mk' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    split; [exact MI'|]. split; [eapply BakeStackRep.stk_high_transport; [exact ST | exact WM | exact VSPZ]|].
    split.
    { exists e. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold vo_wk in Hw. cbn [fst snd cells_size csize Z.of_nat] in *.
      unfold ATP in *. destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & _ & Hw)]]]; lia. }
    split; [exact RA'|]. split; [exact AC'|]. split; [exact RF'|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]|].
    split; [exact RH'|].
    split.
    { eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply disjoint_from_of_Forall; [exact FW|]. intros l h Hw. unfold vo_wk in Hw. cbn [fst snd] in Hw.
      unfold FRAME. rewrite v4_cells_size_map_C8'. cbn [length].
      destruct Hw as [Hw|[Hw|[Hw|(_ & _ & _ & _ & _ & Hw & _)]]]; lia. }
    split; [|split; [exact AL | exact (lb_own_wmono _ _ _ OW WM)]].
    eapply (xpres_trans H); [exact XP|].
    eapply (vo_xpres_mixed sk pid' A (20 * cap') spz Xk mk mk mk' W RH NI ltac:(lia) MU WM).
    eapply Forall_impl; [|exact FW]. intros [l h] Hw. unfold vo_wk in Hw. cbn [fst snd] in *.
    destruct Hw as [Hw|[Hw|[Hw|(Hw & _)]]].
    - right; right; left. lia.
    - left. exact Hw.
    - right; left. exact Hw.
    - right; right; right. exact Hw.
  Qed.

  Lemma vo_vec_facts :
    fldA m v 8 b /\ fldA m (v + 8) 8 (b + 20 * cap) /\ fldA m (v + 16) 8 (b + 20 * cap) /\ True
    /\ 0 <= cap /\ ((b = 0 /\ cap = 0) \/ (1 <= cap /\ In (pid, b, 20 * cap) LB /\ ablock_range H b (20 * cap))).
  Proof.
    destruct VEC as (Hv & Hv' & HD & Hlen & Hb & F0 & F1 & F2).
    split; [exact F0|]. split; [exact F1|]. split; [exact F2|]. split; [exact I|]. split; [lia|].
    destruct OLD as [[-> ->]|(Hc & HIn)]; [left; split; reflexivity|].
    right. split; [lia|]. split; [exact HIn|]. exact (ah_blocks H HH _ _ _ _ RH0 HIn).
  Qed.

  Lemma vo_capb : 0 <= cap -> cap + 1 <= cap' /\ 20 * cap' <= 2 ^ 26.
  Proof.
    intros C0. split; [|exact GROW]. unfold cap', v4_newcap.
    destruct (Z_le_gt_dec cap 1) as [L|L]; [rewrite vgrow_le1 by lia | rewrite vgrow_ge2 by lia]; lia.
  Qed.

  Lemma vo_old_facts : 0 < cap ->
    In (pid, b, 20 * cap) LB /\ ablock_range H b (20 * cap) /\ (v + 24 <= b \/ b + 20 * cap <= v) /\ b <> 0.
  Proof.
    intros Hc. pose proof vo_vec_facts as (_ & _ & _ & _ & _ & OB).
    destruct OB as [[_ C]|(_ & HIn & ABR)]; [lia|].
    destruct VEC as (_ & _ & _ & _ & Hb & _). destruct Hb as [[_ C]|(_ & _ & _ & _ & _ & D)]; [lia|].
    split; [exact HIn|]. split; [exact ABR|]. split; [exact D|]. destruct ABR as (B0 & _). lia.
  Qed.

  Lemma vo_blk_shad : forall sk mk LBx p A n, as_RHEAP H sk LBx mk -> In (p, A, n) LBx ->
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

  Lemma vo_hdr_fresh : forall sk mk pid' A n,
    as_RHEAP H sk ((pid', A, n) :: LB) mk -> ~ In pid' (map blk_id LB) -> 0 < n -> v + 24 <= A \/ A + n <= v.
  Proof.
    intros sk mk pid' A n RH NI Hn.
    destruct OBJ as (CL & _).
    pose proof (ah_blocks H HH _ _ _ (pid', A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    cbn [blk_addr blk_size fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    destruct LOR as [LO1 LO2]. unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    assert (SPC : aceil <= spz) by lia.
    destruct (Z_le_gt_dec (v + 24) A) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (A + n) v) as [D'|D']; [right; exact D'|].
    exfalso.
    assert (Ha : v <= Z.max v A < v + 24) by lia.
    pose proof (aclient_range_addr H LB spz v 24 (Z.max v A) CL Ha) as Hc.
    destruct (vo_cls sk LB pid' A n spz mk (Z.max v A) RH NI SPC Hc) as [C|(C1 & C2 & C3)]; [lia|].
    apply C2. lia.
  Qed.

  Lemma vo_band_of_aapp : forall A n, aapp A n -> (0 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A.
  Proof. intros A n HA. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO in HA. destruct HA; [left|right]; lia. Qed.

  Lemma vo_xc_hdr : 0 < cap -> xclient_range H LB spz (v4_oldx b (20 * cap)) v 24.
  Proof.
    intros Hc. destruct (vo_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (CL & _).
    split; [exact CL|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    pose proof (v4_app_sh v 24 b (20 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Lemma vo_xc_hdrsh : 0 < cap -> xclient_range H LB spz (v4_oldx b (20 * cap)) (sh v) 3.
  Proof.
    intros Hc. destruct (vo_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS.
    split; [exact CLS|].
    unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
    assert (VB : v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof (v4_app_sh b (20 * cap) v 24 ltac:(lia) ltac:(lia) VB (vo_band_of_aapp _ _ BAPP)) as D1. rewrite v4_nsh24 in D1.
    pose proof (v4_sh_apart v 24 b (20 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
    rewrite v4_nsh24 in D2.
    apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia|]. apply Forall_nil.
  Qed.

  Definition vo_X0 : list (Z * Z) := if b =? 0 then [] else [(sh b, sh b + nsh (20 * cap))].
  Definition vo_X1 : list (Z * Z) := (v, v + 24) :: vo_X0.

  Lemma vo_X1_sub : forall a, rin_ivs vo_X1 a -> rin_ivs ((v, v + 24) :: v4_oldx b (20 * cap)) a.
  Proof.
    intros a Ha. unfold vo_X1, vo_X0, v4_oldx in Ha |- *. destruct (b =? 0); cbn [rin_ivs fst snd] in Ha |- *; tauto.
  Qed.

  Lemma vo_shvis0 : forall mk, shvis mk 0 0.
  Proof.
    intros mk. unfold shvis. change (sh (hull_lo 0)) with 2147450880. change (sh (hull_hi 0)) with 2147450880.
    split; [lia|]. split; [lia|]. intros a Ha. lia.
  Qed.

  Lemma vo_acl_sub : forall LBx SP A n A' n', aclient_range H LBx SP A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
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

  Lemma vo_xcl_sub : forall X A n A' n', xclient_range H LB spz X A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
    xclient_range H LB spz X A' n'.
  Proof.
    intros X A n A' n' [K KX] H1 H2 H3. split; [exact (vo_acl_sub _ _ _ _ _ _ K H1 H2 H3)|].
    eapply Forall_impl; [|exact KX]. intros [l h] Hlh. cbn [fst snd] in *. lia.
  Qed.

  Lemma vo_fld_xpres : forall X mk a k z, xpres H LB spz X m mk -> xclient_range H LB spz X a (Z.of_nat k) ->
    0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fldA m a k z -> fldA mk a k z.
  Proof.
    intros X mk a k z XP XC H0 H1 Hf. unfold fldA in *. eapply fld_agree; [exact H0 | exact H1 | exact Hf |].
    intros a' Ha'. hnf in Ha'.
    destruct (XP a' ltac:(lia) (xclient_range_addr H LB spz X a (Z.of_nat k) a' XC Ha')) as [E _]. exact E.
  Qed.

  Lemma vo_SHAD_xpres : forall X mk A' sbs, xpres H LB spz X m mk -> SHAD m A' sbs ->
    xclient_range H LB spz X (sh A') (Z.of_nat (length sbs)) -> SHAD mk A' sbs.
  Proof.
    intros X mk A' sbs XP (S0 & S8 & [UB UW]) XC. split; [exact S0|]. split; [exact S8|].
    split; [eapply (xpres_bytes_at H); [exact XP | exact UB | exact XC] | eapply (xpres_wr_at H); [exact XP | exact UW | exact XC]].
  Qed.

  Lemma vo_apres_of_xpres_nil : forall mk, xpres H LB spz [] m mk -> apres H LB spz m mk.
  Proof. intros mk XP a Ha Hc. apply XP; [exact Ha|]. split; [exact Hc | intros K; exact K]. Qed.

  Lemma vo_mid_weaken : forall sk mk pid' A X X', vo_mid sk mk pid' A X -> (forall a, rin_ivs X a -> rin_ivs X' a) ->
    vo_mid sk mk pid' A X'.
  Proof.
    intros sk mk pid' A X X' (MI & ST & ERR & RA & AC & RF & S0 & RH & FR & XP & AL & OW) HX.
    repeat (split; [assumption|]). split; [eapply (xpres_weaken H); [exact XP | lia | intros bb Hb; exact Hb | exact HX]|].
    split; assumption.
  Qed.

  Lemma vo_wk_hdr : forall A Xk, (forall a, v <= a < v + 24 -> rin_ivs Xk a) -> vo_wk A Xk (v, v + 24).
  Proof.
    intros A Xk HX. right; right; right. cbn [fst snd].
    destruct OBJ as (_ & _ & WO & FW & CO & SD).
    pose proof LOR as [LO1 LO2]. unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    assert (SHC : 0x7fff7000 < sh aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    split; [exact HX|]. split; [exact WO|]. split; [exact FW|]. split; [exact CO|].
    split; [unfold stack0_ok; cbn [fst snd]; destruct VBAND; [right | left]; unfold AHI_LO; lia|].
    split; [lia|]. right. unfold ATP. destruct VBAND; lia.
  Qed.

  Lemma vo_wk_oldsh : 0 < cap -> forall A Xk, (forall a, sh b <= a < sh b + nsh (20 * cap) -> rin_ivs Xk a) ->
    vo_wk A Xk (sh b, sh b + nsh (20 * cap)).
  Proof.
    intros Hc A Xk HX. destruct (vo_old_facts Hc) as (HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP) & D & NZ).
    pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    pose proof (v4_app_sh (as_FSB H) AFS_SIZE b (20 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (vo_band_of_aapp _ _ FS4)) as DF.
    pose proof (sh_nsh_high b (20 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHH. unfold AHI_LO in SHH.
    assert (SHL : 0x7fff8000 <= sh b) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    right; right; right. cbn [fst snd].
    split; [exact HX|].
    split; [right; right; right; left; exists (pid, b, 20 * cap); split; [exact HIn | cbn [blk_addr blk_size fst snd]; lia]|].
    split; [left; cbn [fst snd]; split; [lia | unfold ATLS_PRIV_HI, ATP; lia]|].
    split; [apply aconst_ok_high; [apply sh_mono; unfold AIMG_TOP in *; lia | right; left; lia]|].
    split; [apply stack0_ok_sh; lia|].
    split; [lia|]. right. unfold ATP. lia.
  Qed.

  Lemma vo_hdr_X0 : forall mk, xpres H LB spz vo_X0 m mk ->
    fldA mk v 8 b /\ fldA mk (v + 8) 8 (b + 20 * cap) /\ fldA mk (v + 16) 8 (b + 20 * cap) /\ addressable mk v 24
    /\ wr_at asegs mk v 24.
  Proof.
    intros mk XP.
    pose proof vo_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    assert (VB2 : 0 <= v /\ v + 24 < 2 ^ 64) by (destruct VBAND; lia).
    assert (XCH : xclient_range H LB spz vo_X0 v 24).
    { destruct OBJ as (CL & _). split; [exact CL|]. unfold vo_X0. destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
      assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
      pose proof (v4_app_sh v 24 b (20 * cap) ltac:(lia) ltac:(lia) ltac:(lia) VB) as D.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    assert (XCS : xclient_range H LB spz vo_X0 (sh v) 3).
    { destruct OBJ as (_ & CLS & _). rewrite v4_nsh24 in CLS. split; [exact CLS|]. unfold vo_X0.
      destruct (Z.eqb_spec b 0) as [E|NE]; [apply Forall_nil|].
      destruct OB as [[E _]|(Hc & HIn & (B0 & B16 & Bn & BI & BC & BF & BAPP))]; [contradiction|].
      assert (D : v + 24 <= b \/ b + 20 * cap <= v) by (destruct (vo_old_facts ltac:(lia)) as (_ & _ & D & _); exact D).
      pose proof (v4_sh_apart v 24 b (20 * cap) ltac:(lia) ltac:(lia) V8 (v4_mod16_8 b B16) ltac:(lia) ltac:(lia) D) as D2.
      rewrite v4_nsh24 in D2.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]. }
    split; [eapply vo_fld_xpres; [exact XP | eapply vo_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F0]|].
    split; [eapply vo_fld_xpres; [exact XP | eapply vo_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F1]|].
    split; [eapply vo_fld_xpres; [exact XP | eapply vo_xcl_sub; [exact XCH | lia | cbn; lia | lia] | lia | cbn; lia | exact F2]|].
    split.
    - destruct ADV0 as [AN SV]. split; [exact AN|]. eapply vo_SHAD_xpres; [exact XP | exact SV |].
      rewrite shadow_of_length by lia. rewrite v4_nsh24. exact XCS.
    - eapply (xpres_wr_at H); [exact XP | exact VWR | exact XCH].
  Qed.

  Lemma vo_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
  Proof.
    induction W as [|[l h] W IH]; intros a n a' n' D H1 H2; [exact I|]. cbn in D |- *. destruct D as [D1 D2].
    split; [lia | exact (IH a n a' n' D2 H1 H2)].
  Qed.

  Lemma vo_wr_sub : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n'.
  Proof.
    intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
  Qed.

  Lemma vo_CB0 : forall mk a, 0 <= a <= 2 ^ 64 -> rw_cells asegs mk a [CB 0 []].
  Proof.
    intros mk a Ha. split; [split|].
    - cbn. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes app]. apply bytes_at_nil. lia.
    - cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
  Qed.

  Lemma vo_shk4 : forall mk A, addressable mk A 4 -> LbB_Kit.shk mk A 4.
  Proof.
    intros mk A [_ SH]. pose proof SH as (SA0 & _).
    destruct (shk_of_SHAD mk A (shadow_of 4) A SH ltac:(change (Z.of_nat (length (shadow_of 4))) with 1; lia)) as (bb & Hb & K).
    rewrite Z.sub_diag in Hb. change (nth_error (shadow_of 4) (Z.to_nat (0 / 8))) with (Some (b8 4)) in Hb. injection Hb as <-. exact K.
  Qed.

  Let HANN : annotate_gen_stmt := annotate_gen_ok.

  Lemma vo_s_end : forall (msF1 : machine_state) (mo1 : Model) (s1' : as_St H) (m1 : mem) (R1 : bvmap 5 word) (pid' : bptr) (A : Z) (e1 : word),
    as_VIS H s1' msF1 = MS R1 F (Z_to_bv 64 (VOPND_SLOW_ENTRY + 548)) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = ra -> getr R1 2 = sp -> getr R1 3 = gp -> getr R1 4 = tp -> getr R1 8 = s0 -> getr R1 9 = s1 ->
    getr R1 10 = Z_to_bv 64 (A + 20 * (cap + 1)) -> getr R1 18 = s2 -> getr R1 19 = s3 -> getr R1 20 = s4 ->
    getr R1 21 = s5 -> getr R1 22 = s6 -> getr R1 23 = s7 -> getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 ->
    getr R1 27 = s11 ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (20 * cap)) m m1 ->
    ablock_range H A (20 * cap') -> as_RHEAP H s1' (v4_newLB H LB b pid pid' A (20 * cap')) m1 ->
    vopndA (v4_newLB H LB b pid pid' A (20 * cap')) m1 v A (cap + 1) cap' ->
    SHAD m1 A (cc_gen (20 * cap') (20 * (cap + 1))) -> addressable m1 v 24 ->
    wr_at asegs m1 v 24 -> lb_own (v4_newLB H LB b pid pid' A (20 * cap')) m1 ->
    as_RFS H LF m1 -> ACONST m1 -> stack0 m1 lo shi ->
    as_AL H s1' >= as_AL H s - (as_Cm H (20 * cap') + as_Cf H (20 * cap)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 s1' m1 R1 pid' A e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 XP1 ABR RH1 VEC1 SH1 ADV1 WV1 OW1 RF1 AC1 S01 AL1.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RET).
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (getr R1 5) (getr R1 6) (getr R1 7) s0 s1 (Z_to_bv 64 (A + 20 * (cap + 1)))
                                   (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                              F (ret_pc ra) fc None m1 (seg_rom asegs));
      [exact KR1 | exact VIS1 | |].
    { rewrite (rfull_eq R1 HF1). apply RET.
      rewrite G1, G2, G3, G4, G8, G9, G10, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27. reflexivity. }
    intros msF2 mo2 KR2 MP2 HP. cbv beta in HP.
    exists (getr R1 5), (getr R1 6), (getr R1 7), (getr R1 11), (getr R1 12), (getr R1 13), (getr R1 14), (getr R1 15), (getr R1 16),
      (getr R1 17), (getr R1 28), (getr R1 29), (getr R1 30), (getr R1 31), m1, e1, s1', pid', A.
    cbn [cfg_ms cfg_model]. rewrite SPZ. unfold OPND_SZ.
    split; [exact HP|]. split; [exact KR2|]. split; [eapply (ah_mpres_trans H HH); eassumption|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact RA1|]. split; [exact XP1|].
    split; [exact ABR|]. split; [exact RH1|]. split; [exact VEC1|]. split; [exact SH1|]. split; [exact ADV1|].
    split; [exact WV1|]. split; [exact OW1|].
    split; [exact RF1|]. split; [exact AC1|]. split; [exact S01|]. exact AL1.
  Qed.

  Lemma vo_s9 : forall (msF9 : machine_state) (mo9 : Model) (sk9 : as_St H) (m9 : mem) (R9 : bvmap 5 word) (pid' : bptr) (A : Z) (e9 : word),
    as_VIS H sk9 msF9 = MS R9 F (Z_to_bv 64 (VOPND_SLOW_ENTRY + 512)) fc None m9 (seg_rom asegs) -> rfull R9 ->
    vo_B9at R9 m9 A -> getr R9 3 = gp -> getr R9 4 = tp ->
    getr R9 22 = s6 -> getr R9 23 = s7 -> getr R9 24 = s8 -> getr R9 25 = s9 -> getr R9 26 = s10 -> getr R9 27 = s11 ->
    as_AKREL H sk9 (mkCfg msF9 mo9) -> as_MPRES H mo mo9 ->
    mem_inv asegs m9 -> stk asegs m9 lo spz -> rw_cells asegs m9 (errno_addr tp) [C4 e9] -> as_rauxv_ok H m9 B ->
    xpres H LB spz ((v, v + 24) :: v4_oldx b (20 * cap)) m m9 ->
    ablock_range H A (20 * cap') -> as_RHEAP H sk9 (v4_newLB H LB b pid pid' A (20 * cap')) m9 ->
    vopndA (v4_newLB H LB b pid pid' A (20 * cap')) m9 v A (cap + 1) cap' ->
    SHAD m9 A (cc_gen (20 * cap') (20 * (cap + 1))) -> addressable m9 v 24 ->
    wr_at asegs m9 v 24 -> lb_own (v4_newLB H LB b pid pid' A (20 * cap')) m9 ->
    as_RFS H LF m9 -> ACONST m9 -> stack0 m9 lo shi ->
    as_AL H sk9 >= as_AL H s - (as_Cm H (20 * cap') + as_Cf H (20 * cap)) ->
    as_SR H Q (mkCfg msF9 mo9).
  Proof.
    intros msF9 mo9 sk9 m9 R9 pid' A e9 VIS9 HF9 B9P G3 G4 G22 G23 G24 G25 G26 G27 KR9 MP9 MI9 ST9 ERR9 RA9 XP9 ABR RH9
      VEC9 SH9 ADV9 WV9 OW9 RF9 AC9 S09 AL9.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & B9 & _).
    destruct (B9 R9 F fc m9 A (spz - 96) cap (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) B9P)
      as (R' & M' & Hms & EM & K1 & K2 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & KK).
    subst M'.
    pose proof (msteps_full asegs _ _ Hms HF9) as HF'. cbn [ms_regs] in HF'.
    eapply (sr_blk H HH); [exact KR9 | exact VIS9 | exact HF9 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R' HF') in VIS1.
    eapply (vo_s_end msF1 mo1 sk9 m9 R' pid' A e9 VIS1 HF').
    + rewrite K1. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite K2. unfold wz. replace (spz - 96 + 96) with spz by lia. symmetry. exact spz_sp.
    + rewrite (KK 3%bv ltac:(inb)). exact G3.
    + rewrite (KK 4%bv ltac:(inb)). exact G4.
    + rewrite K8. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite K9. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite K10. unfold wz. f_equal. lia.
    + rewrite K18. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite K19. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite K20. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite K21. unfold wz. apply Z_to_bv_bv_unsigned.
    + rewrite (KK 22%bv ltac:(inb)). exact G22.
    + rewrite (KK 23%bv ltac:(inb)). exact G23.
    + rewrite (KK 24%bv ltac:(inb)). exact G24.
    + rewrite (KK 25%bv ltac:(inb)). exact G25.
    + rewrite (KK 26%bv ltac:(inb)). exact G26.
    + rewrite (KK 27%bv ltac:(inb)). exact G27.
    + exact KR1.
    + eapply (ah_mpres_trans H HH); [exact MP9 | exact MP1].
    + exact MI9.
    + exact ST9.
    + exact ERR9.
    + exact RA9.
    + exact XP9.
    + exact ABR.
    + exact RH9.
    + exact VEC9.
    + exact SH9.
    + exact ADV9.
    + exact WV9.
    + exact OW9.
    + exact RF9.
    + exact AC9.
    + exact S09.
    + exact AL9.
  Qed.

  Lemma vo_s8 : forall (msF8 : machine_state) (mo8 : Model) (sk8 : as_St H) (m8 : mem) (R8 : bvmap 5 word) (pid' : bptr) (A : Z),
    0 < cap ->
    as_VIS H sk8 msF8 = MS R8 F (Z_to_bv 64 AOPDEL2) fc None m8 (seg_rom asegs) -> rfull R8 ->
    getr R8 1 = Z_to_bv 64 (VOPND_SLOW_ENTRY + 512) -> getr R8 10 = Z_to_bv 64 b -> getr R8 11 = Z_to_bv 64 (20 * cap) ->
    vo_B9at R8 m8 A -> getr R8 3 = gp -> getr R8 4 = tp ->
    getr R8 22 = s6 -> getr R8 23 = s7 -> getr R8 24 = s8 -> getr R8 25 = s9 -> getr R8 26 = s10 -> getr R8 27 = s11 ->
    as_AKREL H sk8 (mkCfg msF8 mo8) -> as_MPRES H mo mo8 ->
    vo_mid sk8 m8 pid' A vo_X1 -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m8 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * (cap + 1))); C8 (Z_to_bv 64 (A + 20 * cap'))] ->
    SHAD m8 A (cc_gen (20 * cap') (20 * (cap + 1))) -> addressable m8 v 24 ->
    as_SR H Q (mkCfg msF8 mo8).
  Proof.
    intros msF8 mo8 sk8 m8 R8 pid' A Hc VIS8 HF8 G1 G10 G11 B9P G3 G4 G22 G23 G24 G25 G26 G27 KR8 MP8 MID ABR NI HDR
      SHA ADV8.
    pose proof MID as (MI8 & ST8 & (e8 & ERR8) & RA8 & AC8 & RF8 & S08 & RH8 & FR8 & XP8 & AL8 & OW8).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (F0 & F1 & F2 & FE & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    unfold vo_B9at, vop_B9_pre in B9P.
    destruct B9P as (G2 & G8 & FB1 & FB8 & FB9 & FB18 & FB19 & FB20 & FB21 & N1 & N2 & N3 & N4 & N5 & N6 & N7).
    assert (FL : forall mk (w : word) k a, rw_cells asegs mk (spz - 64) FRAME -> cell_at FRAME k = Some (C8 w) ->
              a = spz - 64 + Z.of_nat k -> fldA mk a 8 (bv_unsigned w)).
    { intros mk w k a FR CA Ea. subst a. unfold fldA, fld. rewrite Z_to_bv_bv_unsigned. rewrite <- rdn_of_ov.
      exact (rw_cells_read asegs mk _ _ k _ FR CA). }
    assert (OB0 : 0 <= b /\ b + 20 * cap < 2 ^ 47 /\ (b = 0 -> cap = 0) /\ (b <> 0 -> 16 <= b)).
    { destruct OB as [[E1 E2]|(Hc0 & HIn0 & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia|].
      split; [lia|]. split; [lia|]. split; [intros E; lia|]. intros _. exact (v4_mod16_16le b O0 O16). }
    destruct OB0 as (OB1 & OB2 & OB3 & OB4).
    assert (HNEW : v + 24 <= A \/ A + 20 * cap' <= v) by (eapply vo_hdr_fresh; [exact RH8 | exact NI | lia]).
    assert (VEC9 : forall m9 LB9,
              rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * (cap + 1))); C8 (Z_to_bv 64 (A + 20 * cap'))] ->
              In (A, 20 * cap') (lbl LB9) -> vopndA LB9 m9 v A (cap + 1) cap').
    { intros m9 LB9 H1 H4. apply vo_vopnd_new; [exact H1 | lia | exact A16 | lia | lia | lia | exact H4 | exact HNEW
        | unfold AIMG_TOP; lia | lia]. }
      destruct (vo_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & NZ).
    assert (K2 : getr R8 2 = Z_to_bv 64 (spz - 96)) by exact G2. assert (K4 : getr R8 4 = tp) by exact G4.
    rewrite (rfull_eq R8 HF8) in VIS8.
      assert (HINx : In (pid, b, 20 * cap) ((pid', A, 20 * cap') :: LB)) by (right; exact HIn).
      destruct (rw_cells_of_own _ m8 (pid, b, 20 * cap) OW8 HINx ltac:(cbn [blk_addr blk_size fst snd]; exact OI) ltac:(cbn [blk_addr blk_size fst snd]; lia)) as (obs & OC8).
      cbn [blk_addr blk_size fst snd] in OC8.
      destruct (vo_blk_shad sk8 m8 _ pid b (20 * cap) RH8 HINx) as (sbs & SHB & SHL).
      assert (CFB : as_Cf H (20 * cap) <= as_AL H sk8) by (pose proof CM as CM'; change (v4_newcap cap) with cap' in CM'; lia).
      assert (SP96 : (spz - 96) mod 16 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
    assert (ER1 : 0 <= VOPND_SLOW_ENTRY + 512 < 2 ^ 64) by (unfold VOPND_SLOW_ENTRY; lia).
    assert (ER2 : (VOPND_SLOW_ENTRY + 512) mod 2 = 0) by (unfold VOPND_SLOW_ENTRY; reflexivity).
    assert (DRA : VOPND_DEL_RA = VOPND_SLOW_ENTRY + 512) by reflexivity.
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (p := pid) (A := b) (n := 20 * cap) (LB := (pid', A, 20 * cap') :: LB) (lo := lo) (B := B)
          (errv := e8) (CH := []) (bs := obs) (sbs := sbs);
          [ exact VIS8 | exact RH8 | exact KR8 | exact HINx | exact CFB | exact OC8 | exact SHB | exact SHL
          | exact RA8 | rewrite K2, u64_of_Z by lia; lia
          | rewrite K2, u64_of_Z by lia; exact (proj1 (stk_split asegs m8 lo (spz - 96) spz ST8 ltac:(lia)))
          | exact LO1 | rewrite K2, u64_of_Z by lia; unfold AFREE_STACK; lia
          | rewrite K4; exact ERR8 | exact MI8 | rewrite K4; exact TPV | rewrite K2, u64_of_Z by lia; exact SP96 | exact AC8
          | rewrite G8; unfold wz; rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; lia
          | rewrite G1; cbn [map]; try unfold wz; rewrite u64_of_Z by lia; rewrite <- DRA; exact TRO
          | exact G10 ]. }
      intros c2 POST. destruct c2 as [msF2 mo2].
      destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m9 & s9'
                        & VIS2 & KR2 & MP2 & MI9 & ST9 & ERR9 & RA9 & AP9 & RH9 & AC9 & AL9).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite G1 in VIS2. rewrite (ret_pc_even (VOPND_SLOW_ENTRY + 512) ER1 ER2) in VIS2.
      rewrite K2, u64_of_Z in ST9, AP9 by lia. rewrite G4 in ERR9.

      assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 20 * cap); split; [reflexivity | exact HIn]).
      pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
      assert (RMx : as_lb_remove H pid ((pid', A, 20 * cap') :: LB) = (pid', A, 20 * cap') :: as_lb_remove H pid LB).
      { apply L2. cbn [blk_id fst]. exact NEQ. }
      rewrite RMx in AP9, RH9.

      assert (XPF0 : xpres H LB (spz - 96) (v4_oldx b (20 * cap)) m8 m9).
      { eapply (xpres_of_apres_rm H HH sk8 LB ((pid', A, 20 * cap') :: LB) (spz - 96) _ m8 m8 m9 pid b (20 * cap) RH8 HINx);
          [intros bb Hb; right; exact Hb | rewrite RMx; exact AP9 | |].
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia.
        - intros a Ha. unfold v4_oldx. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. right. left. cbn [fst snd]. lia. }
      assert (XPF : xpres H LB spz (v4_oldx b (20 * cap)) m8 m9)
        by (eapply (xpres_weaken H); [exact XPF0 | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]).
      assert (HDR9 : rw_cells asegs m9 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * (cap + 1))); C8 (Z_to_bv 64 (A + 20 * cap'))]).
      { eapply (xpres_rw_cells H); [exact XPF | exact HDR | exact (vo_xc_hdr Hc)]. }
      assert (FR9 : rw_cells asegs m9 (spz - 64) FRAME) by (eapply (apres_rw_cells H); [exact AP9 | exact FR8 | left; lia]).
      assert (INA : In (pid', A, 20 * cap') ((pid', A, 20 * cap') :: as_lb_remove H pid LB)) by (left; reflexivity).
      eapply (vo_s9 msF2 mo2 s9' m9 _ pid' A e8 VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      + unfold vo_B9at, vop_B9_pre.
        split; [exact G2|]. split; [exact G8|].
        split; [eapply (FL m9 ra 56%nat); [exact FR9 | reflexivity | lia]|].
        split; [eapply (FL m9 s0 48%nat); [exact FR9 | reflexivity | lia]|].
        split; [eapply (FL m9 s1 40%nat); [exact FR9 | reflexivity | lia]|].
        split; [eapply (FL m9 s2 32%nat); [exact FR9 | reflexivity | lia]|].
        split; [eapply (FL m9 s3 24%nat); [exact FR9 | reflexivity | lia]|].
        split; [eapply (FL m9 s4 16%nat); [exact FR9 | reflexivity | lia]|].
        split; [eapply (FL m9 s5 8%nat); [exact FR9 | reflexivity | lia]|].
        exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 N7)))))).
      + exact G3.
      + exact G4.
      + exact G22.
      + exact G23.
      + exact G24.
      + exact G25.
      + exact G26.
      + exact G27.
      + exact KR2.
      + eapply (ah_mpres_trans H HH); [exact MP8 | exact MP2].
      + exact MI9.
      + eapply (stk_merge asegs); [exact ST9 | | lia].
        eapply (apres_stk H); [exact AP9 | exact (proj2 (stk_split asegs m8 lo (spz - 96) spz ST8 ltac:(lia))) | lia].
      + exact ERR9.
      + exact RA9.
      + eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP8 | lia | intros bb Hb; exact Hb | exact vo_X1_sub] |].
        eapply (xpres_weaken H); [exact XPF | lia | intros bb Hb; exact Hb | intros a Ha; right; exact Ha].
      + exact ABR.
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. exact RH9.
      + apply VEC9; [exact HDR9 | unfold v4_newLB; apply (lbl_in _ pid'); left; reflexivity].
      + eapply (apres_SHAD H); [exact AP9 | exact SHA |]. rewrite cc_gen_length by lia. eapply (aclient_range_block_sh H). exact INA.
      + destruct ADV8 as [AN (SA0 & SA8 & [UB UW])]. split; [exact AN|]. split; [exact SA0|]. split; [exact SA8|].
        assert (XCS : xclient_range H LB spz (v4_oldx b (20 * cap)) (sh v) (Z.of_nat (length (shadow_of 24)))).
        { rewrite shadow_of_length by lia. rewrite v4_nsh24. exact (vo_xc_hdrsh Hc). }
        split; [eapply (xpres_bytes_at H); [exact XPF | exact UB | exact XCS] | eapply (xpres_wr_at H); [exact XPF | exact UW | exact XCS]].
      + exact (proj2 HDR9).
      + unfold v4_newLB. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|].
        eapply (lb_own_apres H); [| exact AP9 | intros bb Hb; exact Hb].
        eapply lb_own_incl; [| exact OW8]. intros bb [Hb|Hb]; [left; exact Hb | right; exact (L3 _ _ _ Hb)].
      + exact (RFS_via_apres H HH LF _ _ m8 m9 RF8 AP9).
      + exact AC9.
      + eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP9) | exact S08 | apply Forall_nil].
      + lia.
  Qed.

  Lemma vo_s5 : forall (msF5 : machine_state) (mo5 : Model) (sk5 : as_St H) (m5 : mem) (R5 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk5 msF5 = MS R5 F (Z_to_bv 64 (VOPND_SLOW_ENTRY + 428)) fc None m5 (seg_rom asegs) -> rfull R5 ->
    vo_B5at R5 m5 A -> getr R5 3 = gp -> getr R5 4 = tp ->
    getr R5 22 = s6 -> getr R5 23 = s7 -> getr R5 24 = s8 -> getr R5 25 = s9 -> getr R5 26 = s10 -> getr R5 27 = s11 ->
    as_AKREL H sk5 (mkCfg msF5 mo5) -> as_MPRES H mo mo5 ->
    vo_mid sk5 m5 pid' A vo_X1 -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m5 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * (cap + 1))); C8 (Z_to_bv 64 (A + 20 * cap'))] ->
    SHAD m5 A (cc_gen (20 * cap') (20 * (cap + 1))) -> addressable m5 v 24 ->
    as_SR H Q (mkCfg msF5 mo5).
  Proof.
    intros msF5 mo5 sk5 m5 R5 pid' A VIS5 HF5 B5P G3 G4 G22 G23 G24 G25 G26 G27 KR5 MP5 MID ABR NI HDR SHA ADV5.
    pose proof RUNS as (_ & _ & _ & _ & B5D & B5N & _).
    pose proof MID as (MI5 & ST5 & (e5 & ERR5) & RA5 & AC5 & RF5 & S05 & RH5 & FR5 & XP5 & AL5 & OW5).
    pose proof SPR as (SPL & SPH & SP16).
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : 0x6e8000 <= v /\ v + 24 <= 2 ^ 47) by (destruct VBAND; lia).
    pose proof B5P as P. unfold vo_B5at, vop_B5_pre in P.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & PSP & PA & PV & PSR & PC & PN & PB & _ & _ & _ & _ & PAN & _ & _ & _ & _ & _ & _ & _ & PCN & _ & _).
    assert (FL : forall mk (w : word) k a, rw_cells asegs mk (spz - 64) FRAME -> cell_at FRAME k = Some (C8 w) ->
              a = spz - 64 + Z.of_nat k -> fldA mk a 8 (bv_unsigned w)).
    { intros mk w k a FR CA Ea. subst a. unfold fldA, fld. rewrite Z_to_bv_bv_unsigned. rewrite <- rdn_of_ov.
      exact (rw_cells_read asegs mk _ _ k _ FR CA). }
    assert (B9F : forall R mk, getr R 2 = wz (spz - 96) -> getr R 8 = wz (A + 20 * cap + 20) ->
              rw_cells asegs mk (spz - 64) FRAME -> vo_B9at R mk A).
    { intros R mk R2 R8' FR. unfold vo_B9at, vop_B9_pre.
      split; [exact R2|]. split; [exact R8'|].
      split; [eapply (FL mk ra 56%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s0 48%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s1 40%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s2 32%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s3 24%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s4 16%nat); [exact FR | reflexivity | lia]|].
      split; [eapply (FL mk s5 8%nat); [exact FR | reflexivity | lia]|].
      lia. }
    destruct (Z.eq_dec b 0) as [Z0|NZ].
    -
      destruct (B5N R5 F fc m5 A (spz - 96) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                  (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) B5P Z0)
        as (R9 & M9 & Hms & EM9 & K1 & K2 & K8 & K9 & K10 & _ & K18 & K19 & K20 & K21 & KK).
      subst M9.
      pose proof (msteps_full asegs _ _ Hms HF5) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR5 | exact VIS5 | exact HF5 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R9 HF9) in VIS1.
      assert (CF0 : 0 <= as_Cf H (20 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia).
      assert (HNEW : v + 24 <= A \/ A + 20 * cap' <= v) by (eapply vo_hdr_fresh; [exact RH5 | exact NI | lia]).
      eapply (vo_s_end msF1 mo1 sk5 m5 R9 pid' A e5 VIS1 HF9).
      + rewrite K1. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite K2. unfold wz. replace (spz - 96 + 96) with spz by lia. symmetry. exact spz_sp.
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite K8. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite K9. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite K10. unfold wz. f_equal. lia.
      + rewrite K18. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite K19. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite K20. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite K21. unfold wz. apply Z_to_bv_bv_unsigned.
      + rewrite (KK 22%bv ltac:(inb)). exact G22.
      + rewrite (KK 23%bv ltac:(inb)). exact G23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR1.
      + eapply (ah_mpres_trans H HH); [exact MP5 | exact MP1].
      + exact MI5.
      + exact ST5.
      + exact ERR5.
      + exact RA5.
      + eapply (xpres_weaken H); [exact XP5 | lia | intros bb Hb; exact Hb | exact vo_X1_sub].
      + exact ABR.
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact RH5.
      + apply vo_vopnd_new; [exact HDR | lia | exact A16 | lia | lia | lia | | exact HNEW | unfold AIMG_TOP; lia | lia].
        unfold v4_newLB. apply (lbl_in _ pid'). left. reflexivity.
      + exact SHA.
      + exact ADV5.
      + exact (proj2 HDR).
      + unfold v4_newLB. rewrite Z0. cbn [Z.eqb]. exact OW5.
      + exact RF5.
      + exact AC5.
      + exact S05.
      + lia.
    -
      assert (Hc : 0 < cap) by (destruct OB as [[E1 _]|(Hc & _)]; [contradiction | lia]).
      destruct (B5D R5 F fc m5 A (spz - 96) v src cap b cap' (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned s1) (bv_unsigned s2)
                  (bv_unsigned s3) (bv_unsigned s4) (bv_unsigned s5) B5P NZ)
        as (R9 & M9 & Hms & EM9 & K1 & K2 & K8 & _ & K10 & K11 & _ & _ & _ & KK).
      subst M9.
      pose proof (msteps_full asegs _ _ Hms HF5) as HF9. cbn [ms_regs] in HF9.
      eapply (sr_blk H HH); [exact KR5 | exact VIS5 | exact HF5 | exact Hms |].
      intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R9 HF9) in VIS1.
      eapply (vo_s8 msF1 mo1 sk5 m5 R9 pid' A Hc VIS1 HF9).
      + exact K1.
      + exact K10.
      + exact K11.
      + exact (B9F R9 m5 K2 K8 FR5).
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 22%bv ltac:(inb)). exact G22.
      + rewrite (KK 23%bv ltac:(inb)). exact G23.
      + rewrite (KK 24%bv ltac:(inb)). exact G24.
      + rewrite (KK 25%bv ltac:(inb)). exact G25.
      + rewrite (KK 26%bv ltac:(inb)). exact G26.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR1.
      + eapply (ah_mpres_trans H HH); [exact MP5 | exact MP1].
      + exact MID.
      + exact ABR.
      + exact NI.
      + exact HDR.
      + exact SHA.
      + exact ADV5.
  Qed.

  Lemma vo_sa3 : forall (msF7 : machine_state) (mo7 : Model) (sk7 : as_St H) (m7 : mem) (R7 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk7 msF7 = MS R7 F (Z_to_bv 64 AANNOTATE_CC) fc None m7 (seg_rom asegs) -> rfull R7 ->
    getr R7 1 = Z_to_bv 64 (VOPND_SLOW_ENTRY + 428) -> getr R7 10 = Z_to_bv 64 A -> getr R7 11 = Z_to_bv 64 (A + 20 * cap') ->
    getr R7 12 = Z_to_bv 64 (A + 20 * cap') -> getr R7 13 = Z_to_bv 64 (20 * cap + A + 20) ->
    vo_B5at R7 m7 A -> getr R7 3 = gp -> getr R7 4 = tp ->
    getr R7 22 = s6 -> getr R7 23 = s7 -> getr R7 24 = s8 -> getr R7 25 = s9 -> getr R7 26 = s10 -> getr R7 27 = s11 ->
    as_AKREL H sk7 (mkCfg msF7 mo7) -> as_MPRES H mo mo7 ->
    vo_mid sk7 m7 pid' A vo_X1 -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * (cap + 1))); C8 (Z_to_bv 64 (A + 20 * cap'))] ->
    SHAD m7 A (cc_gen (20 * cap') (20 * cap')) -> addressable m7 v 24 ->
    as_SR H Q (mkCfg msF7 mo7).
  Proof.
    intros msF7 mo7 sk7 m7 R7 pid' A VIS7 HF7 G1 G10 G11 G12 G13 B5P G3 G4 G22 G23 G24 G25 G26 G27 KR7 MP7 MID ABR NI
      HDR SHA ADV7.
    pose proof MID as (MI7 & ST7 & _ & _ & AC7 & _ & _ & RH7 & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (VB : (0 <= v /\ v + 24 <= 0x7fff7000) \/ 0x10007fff8000 <= v) by (destruct VBAND; [left|right]; lia).
    assert (HNEW : v + 24 <= A \/ A + 20 * cap' <= v) by (eapply vo_hdr_fresh; [exact RH7 | exact NI | lia]).
    unfold vo_B5at, vop_B5_pre in B5P.
    destruct B5P as (G2 & G8 & G9 & G18 & G19 & G20 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16 & FS24 & FS32
                     & FRa & FR0 & FR1 & FR2 & FR3 & FR4 & FR5 & RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & WS & SHV
                     & RG9 & RG10 & RG11 & RG12 & RG13 & RG14 & RG15 & RG16 & RG17 & RG18 & RG19 & RG20).
    rewrite (rfull_eq R7 HF7) in VIS7.
    eapply (ahh_evt_then H HH); [exact KR7 | exact VIS7 | |].
    { eapply HANN with (beg := A) (len := 20 * cap') (oldmid := 20 * cap') (newmid := 20 * cap + 20) (lo := lo).
      - exact G10.
      - exact G11.
      - exact G12.
      - rewrite G13. f_equal. lia.
      - exact (v4_mod16_8 A A16).
      - lia.
      - lia.
      - lia.
      - exact AAP.
      - unfold AAPP_HI; lia.
      - exact SHA.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. exact (proj1 (stk_split asegs m7 lo (spz - 96) spz ST7 ltac:(lia))).
      - exact LO1.
      - rewrite G2. unfold wz. rewrite u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI7.
      - exact AC7.
      - unfold in_app_mem. destruct (vo_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF8 mo8 KR8 MP8 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m8
                      & VIS8 & MU8 & WM8 & MI8 & ST8 & SH8 & AC8).
    rewrite G2 in MU8, ST8. unfold wz in MU8, ST8. rewrite u64_of_Z in MU8, ST8 by lia. unfold AINTRIN_STACK in MU8.
    rewrite G1 in VIS8.
    assert (ER1 : 0 <= VOPND_SLOW_ENTRY + 428 < 2 ^ 64) by (unfold VOPND_SLOW_ENTRY; lia).
    assert (ER2 : (VOPND_SLOW_ENTRY + 428) mod 2 = 0) by (unfold VOPND_SLOW_ENTRY; reflexivity).
    rewrite (ret_pc_even (VOPND_SLOW_ENTRY + 428) ER1 ER2) in VIS8.
    assert (W8 : Forall (vo_wk A vo_X1) [(sh A, sh A + nsh (20 * cap')); (spz - 96 - 4096, spz - 96)]).
    { apply Forall_cons; [right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (DSV : disjoint_from [(sh A, sh A + nsh (20 * cap')); (spz - 96 - 4096, spz - 96)] v 24).
    { pose proof (v4_app_sh v 24 A (20 * cap') ltac:(lia) ltac:(lia) ltac:(lia) VB) as D. destruct OBJ as (_ & _ & _ & _ & _ & SD).
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSA : disjoint_from [(sh A, sh A + nsh (20 * cap')); (spz - 96 - 4096, spz - 96)] A (20 * cap')).
    { pose proof (v4_app_sh A (20 * cap') A (20 * cap') ltac:(lia) ltac:(lia) ltac:(lia) (vo_band_of_aapp _ _ AAP)) as D.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSS : disjoint_from [(sh A, sh A + nsh (20 * cap')); (spz - 96 - 4096, spz - 96)] (sh v) (nsh 24)).
    { pose proof (v4_sh_apart v 24 A (20 * cap') ltac:(lia) ltac:(lia) V8 (v4_mod16_8 A A16) ltac:(lia) ltac:(lia) HNEW) as D.
      pose proof (sh_nsh_high v 24 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; destruct VBAND; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (DSP : forall a, spz - 96 <= a <= spz - 8 ->
                  disjoint_from [(sh A, sh A + nsh (20 * cap')); (spz - 96 - 4096, spz - 96)] a 8).
    { intros a Ha. pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2.
      unfold AHI_LO in D2. cbn. split; [lia | split; [lia | exact I]]. }
    assert (FMU : forall a z, fldA m7 a 8 z -> disjoint_from [(sh A, sh A + nsh (20 * cap')); (spz - 96 - 4096, spz - 96)] a 8 ->
                  0 <= a -> a + 8 < 2 ^ 64 -> fldA m8 a 8 z).
    { intros a z Fa D Ha0 Ha1. unfold fldA in Fa |- *. eapply fld_agree; [exact Ha0 | exact Ha1 | exact Fa |].
      intros y Hy. red in Hy. apply MU8. rewrite unsigned_lit by lia. eapply disjoint_outside; [exact D | lia]. }
    assert (ADV8 : addressable m8 v 24) by (eapply addressable_transport; [exact ADV7 | exact MU8 | exact WM8 | exact DSS]).
    eapply (vo_s5 msF8 mo8 sk7 m8 _ pid' A VIS8 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold vo_B5at, vop_B5_pre.
      split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G18|]. split; [exact G19|].
      split; [exact G20|].
      split; [eapply FMU; [exact FV0 | eapply vo_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FV8 | eapply vo_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FV16 | eapply vo_dj_sub; [exact DSV | lia | lia] | lia | lia]|].
      split; [eapply FMU; [exact FS0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS8 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS16 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS24 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FS32 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FRa | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR0 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR1 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR2 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR3 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR4 | apply DSP; lia | lia | lia]|].
      split; [eapply FMU; [exact FR5 | apply DSP; lia | lia | lia]|].
      split; [exact RG1|]. split; [exact RG2|]. split; [exact RG3|]. split; [exact RG4|]. split; [exact RG5|].
      split; [exact RG6|]. split; [exact RG7|]. split; [exact RG8|].
      split; [exact (wr_at_wmono _ _ _ _ WS WM8)|].
      split; [eapply sh0_of_addressable; [exact ADV8 | change (8 * (24 / 8)) with 24; lia]|].
      split; [exact RG9|]. split; [exact RG10|]. split; [exact RG11|]. split; [exact RG12|]. split; [exact RG13|].
      split; [exact RG14|]. split; [exact RG15|]. split; [exact RG16|]. split; [exact RG17|]. split; [exact RG18|].
      split; [exact RG19|]. exact RG20.
    - exact G3.
    - exact G4.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR8.
    - eapply (ah_mpres_trans H HH); [exact MP7 | exact MP8].
    - eapply vo_mid_munch; [exact MID | exact ABR | exact NI | exact MU8 | exact WM8 | exact MI8 | exact W8].
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact HDR | exact MU8 | exact WM8 | exact DSV].
    - replace (20 * (cap + 1)) with (20 * cap + 20) by lia. exact SH8.
    - exact ADV8.
  Qed.

  Lemma vo_sq3 : forall (msF6 : machine_state) (mo6 : Model) (sk6 : as_St H) (m6 : mem) (R6 : bvmap 5 word) (pid' : bptr) (A : Z),
    as_VIS H sk6 msF6 = MS R6 F (Z_to_bv 64 (0xec8f8 + 300)) fc None m6 (seg_rom asegs) -> rfull R6 ->
    vo_Q3at R6 m6 A -> getr R6 3 = gp -> getr R6 4 = tp -> getr R6 27 = s11 ->
    as_AKREL H sk6 (mkCfg msF6 mo6) -> as_MPRES H mo mo6 ->
    vo_mid sk6 m6 pid' A vo_X0 -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    SHAD m6 A (cc_gen (20 * cap') (20 * cap')) ->
    as_SR H Q (mkCfg msF6 mo6).
  Proof.
    intros msF6 mo6 sk6 m6 R6 pid' A VIS6 HF6 Q3P G3 G4 G27 KR6 MP6 MID ABR NI SHA.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q3 & _).
    pose proof MID as (MI6 & ST6 & _ & _ & _ & _ & _ & RH6 & _ & XP6 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof SRCA as SA. unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI in SA.
    assert (HNEW : v + 24 <= A \/ A + 20 * cap' <= v) by (eapply vo_hdr_fresh; [exact RH6 | exact NI | lia]).
    destruct (vo_hdr_X0 m6 XP6) as (_ & _ & _ & ADV6 & WV6).
    unfold vo_Q3at in Q3P.
    destruct (Q3 R6 F fc m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q3P)
      as (R7 & M7 & Hms & MU7 & WM7 & P0 & P24 & PV16 & P16 & PV8 & P8 & PV0 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13
          & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
    pose proof (msteps_full asegs _ _ Hms HF6) as HF7. cbn [ms_regs] in HF7.
    assert (MI7 : mem_inv asegs M7) by exact (msteps_mem_inv asegs _ _ Hms MI6).
    eapply (sr_blk H HH); [exact KR6 | exact VIS6 | exact HF6 | exact Hms |].
    intros msF7 mo7 KR7 MP7 VIS7. rewrite <- (rfull_eq R7 HF7) in VIS7.
    assert (MID7 : vo_mid sk6 M7 pid' A vo_X1).
    { eapply vo_mid_munch; [eapply vo_mid_weaken; [exact MID | intros a Ha; right; exact Ha] | exact ABR | exact NI
                           | exact MU7 | exact WM7 | exact MI7 |].
      apply Forall_cons; [left; cbn [fst snd]; lia|].
      apply Forall_cons; [apply vo_wk_hdr; intros a Ha; left; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof MID7 as (_ & ST7 & _ & _ & _ & _ & _ & _ & FR7 & _).
    assert (CONS8 : forall mk a w cs, rw_cells asegs mk a (C8 w :: cs) ->
                    rw_cells asegs mk a [C8 w] /\ rw_cells asegs mk (a + 8) cs).
    { intros mk a w cs Hc. change (C8 w :: cs) with ([C8 w] ++ cs) in Hc. apply rw_cells_app in Hc. exact Hc. }
    assert (JOIN8 : forall mk a w cs, rw_cells asegs mk a [C8 w] -> rw_cells asegs mk (a + 8) cs ->
                    rw_cells asegs mk a (C8 w :: cs)).
    { intros mk a w cs H1 H2. change (C8 w :: cs) with ([C8 w] ++ cs). apply rw_cells_app. split; [exact H1 | exact H2]. }
    assert (FW : forall mk a a' (w : word), rw_cells asegs mk a [C8 w] -> a' = a -> 0 <= a -> fldA mk a' 8 (bv_unsigned w)).
    { intros mk a a' w Hc -> Ha. apply fld_of_rw_cells8; [rewrite Z_to_bv_bv_unsigned; exact Hc | exact Ha]. }
    assert (C8F : forall mk a a' z z', fldA mk a' 8 z' -> a = a' -> z = z' -> wr_at asegs mk a 8 ->
                  rw_cells asegs mk a [C8 (Z_to_bv 64 z)]).
    { intros mk a a' z z' HF -> -> HW. pose proof HW as (HW0 & HW1 & _). split; [|exact HW].
      split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_of_rdn; [exact HW0 | rewrite length_le8; exact HW1 | rewrite length_le8; exact HF]. }
    assert (WSUB : forall mk a n a' n', wr_at asegs mk a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs mk a' n').
    { intros mk a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
      intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia. }
    unfold FRAME in FR7. cbn [map] in FR7.
    destruct (CONS8 _ _ _ _ FR7) as (FVv & FR7a). destruct (CONS8 _ _ _ _ FR7a) as (F5 & FR7b).
    destruct (CONS8 _ _ _ _ FR7b) as (F4 & FR7c). destruct (CONS8 _ _ _ _ FR7c) as (F3 & FR7d).
    destruct (CONS8 _ _ _ _ FR7d) as (F2 & FR7e). destruct (CONS8 _ _ _ _ FR7e) as (F1 & FR7f).
    destruct (CONS8 _ _ _ _ FR7f) as (F0 & Fra).
    assert (ADV7 : addressable M7 v 24).
    { eapply addressable_transport; [exact ADV6 | exact MU7 | exact WM7 |].
      pose proof (v4_app_sh v 24 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 96) 32 v 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]]. }
    assert (WV7 : wr_at asegs M7 v 24) by exact (wr_at_wmono _ _ _ _ WV6 WM7).
    assert (B5P : vo_B5at R7 M7 A).
    { unfold vo_B5at, vop_B5_pre.
      split; [exact K2|]. split; [exact K8|]. split; [exact K9|]. split; [exact K18|]. split; [exact K19|].
      split; [exact K20|].
      split; [exact PV0|]. split; [exact PV8|]. split; [exact PV16|].
      split; [exact P0|]. split; [exact P8|]. split; [exact P16|]. split; [exact P24|].
      split; [replace (spz - 96 + 32) with (spz - 64) by lia; exact (fld_of_rw_cells8 _ _ _ FVv ltac:(lia))|].
      split; [eapply FW; [exact Fra | lia | lia]|].
      split; [eapply FW; [exact F0 | lia | lia]|].
      split; [eapply FW; [exact F1 | lia | lia]|].
      split; [eapply FW; [exact F2 | lia | lia]|].
      split; [eapply FW; [exact F3 | lia | lia]|].
      split; [eapply FW; [exact F4 | lia | lia]|].
      split; [eapply FW; [exact F5 | lia | lia]|].
      split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1; lia | lia]|].
      split; [exact A16|].
      split; [eapply wr_at_of_stk_win; [exact ST7 | lia | lia]|].
      split; [eapply sh0_of_addressable; [exact ADV7 | change (8 * (24 / 8)) with 24; lia]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [destruct VBAND; lia|].
      split; [destruct VBAND; lia|]. split; [lia|]. split; [lia|]. split; [destruct SRCD; lia|]. split; [lia|].
      split; [destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1; lia | lia]|].
      destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (HDR7 : rw_cells asegs M7 v [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 20 * (cap + 1)));
                                         C8 (Z_to_bv 64 (A + 20 * cap'))]).
    { apply JOIN8; [eapply C8F; [exact PV0 | lia | lia | eapply WSUB; [exact WV7 | lia | lia | lia]]|].
      apply JOIN8; [eapply C8F; [exact PV8 | lia | lia | eapply WSUB; [exact WV7 | lia | lia | lia]]|].
      eapply C8F; [exact PV16 | lia | lia | eapply WSUB; [exact WV7 | lia | lia | lia]]. }
    eapply (vo_sa3 msF7 mo7 sk6 M7 R7 pid' A VIS7 HF7).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - exact K13.
    - exact B5P.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
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
    - eapply SHAD_transport; [exact SHA | exact MU7 | exact WM7 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh v 24 A (20 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct VBAND; [left|right]; lia)) as D.
      pose proof (v4_app_sh (spz - 96) 32 A (20 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(right; lia)) as D2.
      cbn. split; [lia | split; [lia | exact I]].
    - exact ADV7.
  Qed.

  Lemma vo_sm : forall (msF5 : machine_state) (mo5 : Model) (sk5 : as_St H) (m5 : mem) (R5 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    as_VIS H sk5 msF5 = MS R5 F (Z_to_bv 64 AASAN_MEMCPY) fc None m5 (seg_rom asegs) -> rfull R5 ->
    getr R5 1 = Z_to_bv 64 (0xec8f8 + 300) -> getr R5 10 = Z_to_bv 64 A -> getr R5 11 = Z_to_bv 64 b ->
    getr R5 12 = Z_to_bv 64 (20 * cap) ->
    vo_Q3at R5 m5 A -> getr R5 3 = gp -> getr R5 4 = tp -> getr R5 27 = s11 ->
    as_AKREL H sk5 (mkCfg msF5 mo5) -> as_MPRES H mo mo5 ->
    vo_mid sk5 m5 pid' A vo_X0 -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m5 A [CB (Z.to_nat (20 * cap)) jA] ->
    SHAD m5 A (cc_gen (20 * cap') (20 * cap')) -> (0 < cap -> SHAD m5 b (cc_gen (20 * cap) (20 * cap))) ->
    as_SR H Q (mkCfg msF5 mo5).
  Proof.
    intros msF5 mo5 sk5 m5 R5 pid' A jA VIS5 HF5 G1 G10 G11 G12 B7A G3 G4 G27 KR5 MP5 MID ABR NI CBA SHA OSH.
    pose proof MID as (MI5 & ST5 & _ & _ & AC5 & _ & _ & RH5 & _ & XP5 & _ & OW5).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & FE & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof B7A as (P2 & P8 & P9 & P18 & P19 & P22 & P23 & P24 & P25 & P20 & P21 & P26 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16
                       & FS24 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & WH & VD & WV & WS & HS0 & HS1 & HS2 & HS3 & HS4 & HS5
                       & HS6 & HS7 & HS8 & HS9 & HS10 & HS11 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & N9 & N10 & N11 & N12 & N13 & N14
                       & N15 & N16 & N17 & N18 & N19 & N20).
    assert (G2 : getr R5 2 = Z_to_bv 64 (spz - 96 - 96)) by exact P2.
    assert (OBB : (b = 0 /\ cap = 0) \/ (0 < cap /\ In (pid, b, 20 * cap) LB /\ ablock_range H b (20 * cap))).
    { destruct OB as [E|(Hc & HIn & ABb)]; [left; exact E | right; split; [lia|]; split; assumption]. }
    assert (OB0 : 0 <= b /\ b + 20 * cap <= aceil).
    { destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }

    assert (SRCB : exists ob, bytes_at asegs m5 b ob /\ Z.of_nat (length ob) = 20 * cap).
    { destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))].
      - exists []. split; [apply bytes_at_nil; lia | cbn [length Z.of_nat]; lia].
      - destruct (rw_cells_of_own _ _ (pid, b, 20 * cap) OW5 (or_intror HIn)
                    ltac:(unfold blk_addr; cbn [fst]; exact OI) ltac:(unfold blk_size; cbn [snd]; lia)) as (ob & RC).
        unfold blk_addr, blk_size in RC. cbn [fst snd] in RC.
        exists ob. split; [exact (bytes_of_CB _ _ _ _ RC)|].
        destruct RC as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. rewrite Hl, Z2Nat.id by lia.
        reflexivity. }
    destruct SRCB as (ob & SRCB & SRCL').
    assert (ADA : addressable m5 A (20 * cap')) by (split; [lia | rewrite <- cc_gen_full; exact SHA]).
    rewrite (rfull_eq R5 HF5) in VIS5.
    eapply (ahh_evt_then H HH); [exact KR5 | exact VIS5 | |].
    { eapply (ah_memcpy H HH) with (src := ob) (junk := jA) (lo := lo); rewrite ?G10, ?G11, ?G12, ?G2; rewrite ?u64_of_Z by lia.
      - exact SRCB.
      - lia.
      - exact CBA.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)]; [left; lia|].
        assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 20 * cap); split; [reflexivity | exact HIn]).
        pose proof (ah_disj H HH _ _ _ (pid', A, 20 * cap') (pid, b, 20 * cap) RH5 (or_introl eq_refl) (or_intror HIn) NEQ) as D.
        cbn [blk_addr blk_size fst snd] in D. lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + replace (20 * cap) with 0 by lia. apply accessible_nil. unfold AAPP_HI. lia.
        + eapply (addressable_accessible m5 b (20 * cap)); [split; [lia | rewrite <- cc_gen_full; exact (OSH Hc)] | lia | lia | unfold AAPP_HI; lia].
      - eapply addressable_accessible; [exact ADA | lia | lia | unfold AAPP_HI; lia].
      - destruct OBB as [[E1 E2]|(Hc & HIn & ABb)].
        + rewrite E1, E2. replace (0 + 20 * 0) with 0 by lia. apply vo_shvis0.
        + exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_intror HIn)).
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH5 (or_introl eq_refl)) | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m5 lo (spz - 96 - 96) spz ST5 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI5.
      - exact AC5.
      - lia.
      - destruct OBB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))].
        + left. unfold ASHADOW_BASE. lia.
        + unfold in_app_mem. destruct (vo_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - unfold in_app_mem. destruct (vo_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - eapply aconst_ok_app; [exact AAP | lia | lia].
      - left; lia.
      - left; lia. }
    intros msF6 mo6 KR6 MP6 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m6
                      & VIS6 & MU6 & WM6 & MI6 & ST6 & CB6 & SB6 & AC6).
    rewrite G10, G12, G2, ?u64_of_Z in MU6 by lia. rewrite G10, G12, ?u64_of_Z in CB6 by lia. rewrite G2, u64_of_Z in ST6 by lia.
    unfold AINTRIN_STACK in MU6.
    rewrite G1 in VIS6. rewrite (ret_pc_even (0xec8f8 + 300) ltac:(lia) eq_refl) in VIS6.
    assert (W6 : Forall (vo_wk A vo_X0) [(A, A + 20 * cap); (spz - 96 - 96 - 4096, spz - 96 - 96)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (MID6 : vo_mid sk5 m6 pid' A vo_X0)
      by (eapply vo_mid_munch; [exact MID | exact ABR | exact NI | exact MU6 | exact WM6 | exact MI6 | exact W6]).
    pose proof MID6 as (_ & _ & _ & _ & _ & _ & S06 & _ & _ & XP6 & _ & _).
    destruct (vo_hdr_X0 m6 XP6) as (FV0' & FV8' & FV16' & ADV6 & _).
    assert (FT : forall a z, fldA m5 a 8 z -> spz - 96 - 96 <= a -> a + 8 <= spz -> fldA m6 a 8 z).
    { intros a z Hf Ha Hk. unfold fldA in Hf |- *. eapply fld_agree; [lia | change (Z.of_nat 8) with 8; lia | exact Hf |].
      intros y Hy. red in Hy. change (Z.of_nat 8) with 8 in Hy. apply MU6. rewrite u64_of_Z by lia.
      cbn [outside]. split; [lia | split; [lia | exact I]]. }
    eapply (vo_sq3 msF6 mo6 sk5 m6 _ pid' A VIS6 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold vo_Q3at, voh_Q3_pre.
      refine (conj P2 (conj P8 (conj P9 (conj P18 (conj P19 (conj P22 (conj P23 (conj P24 (conj P25 (conj P20 (conj P21
        (conj P26 _)))))))))))).
      refine (conj FV0' (conj FV8' (conj FV16' _))).
      do 4 (split; [eapply FT; [eassumption | lia | lia] |]).
      refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 _)))))))).
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
      exact (conj N9 (conj N10 (conj N11 (conj N12 (conj N13 (conj N14 (conj N15 (conj N16 (conj N17 (conj N18 (conj N19
        N20))))))))))).
    - exact G3.
    - exact G4.
    - exact G27.
    - exact KR6.
    - eapply (ah_mpres_trans H HH); [exact MP5 | exact MP6].
    - exact MID6.
    - exact ABR.
    - exact NI.
    - eapply SHAD_transport; [exact SHA | exact MU6 | exact WM6 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh A (20 * cap) A (20 * cap') ltac:(lia) ltac:(lia) ltac:(lia) ltac:(destruct (vo_band_of_aapp _ _ AAP); [left|right]; lia)) as D.
      pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]].
  Qed.

  Lemma vo_sq2 : forall (msF4 : machine_state) (mo4 : Model) (sk4 : as_St H) (m4 : mem) (R4 : bvmap 5 word) (pid' : bptr) (A : Z)
                        (jA : list byte),
    0 < cap ->
    as_VIS H sk4 msF4 = MS R4 F (Z_to_bv 64 (0xec8f8 + 196)) fc None m4 (seg_rom asegs) -> rfull R4 ->
    vo_Q2at R4 m4 A -> getr R4 3 = gp -> getr R4 4 = tp -> getr R4 27 = s11 ->
    as_AKREL H sk4 (mkCfg msF4 mo4) -> as_MPRES H mo mo4 ->
    vo_mid sk4 m4 pid' A vo_X0 -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m4 A [CB (Z.to_nat (20 * cap)) jA] ->
    SHAD m4 A (cc_gen (20 * cap') (20 * cap')) -> SHAD m4 b (cc_gen (20 * cap) (20 * cap)) ->
    as_SR H Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 sk4 m4 R4 pid' A jA Hc VIS4 HF4 Q2P G3 G4 G27 KR4 MP4 MID ABR NI CBA SHA OSH.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Q2 & _).
    pose proof MID as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    destruct (vo_hdr_X0 m4 XP4) as (_ & _ & _ & ADV4 & _).
    destruct (Q2 R4 F fc m4 v (spz - 96) b cap A cap' (bv_unsigned s10) (bv_unsigned s9) (bv_unsigned s8) (bv_unsigned s7)
                 (bv_unsigned s6) src (20 * cap) cap' (sh (v + 8)) v (v + 8) (VOPND_SLOW_ENTRY + 428) Q2P)
      as (R5 & M5 & Hms & EM5 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25
          & K26 & KK).
    subst M5.
    pose proof (msteps_full asegs _ _ Hms HF4) as HF5. cbn [ms_regs] in HF5.
    eapply (sr_blk H HH); [exact KR4 | exact VIS4 | exact HF4 | exact Hms |].
    intros msF5 mo5 KR5 MP5 VIS5. rewrite <- (rfull_eq R5 HF5) in VIS5.
    eapply (vo_sm msF5 mo5 sk4 m4 R5 pid' A jA VIS5 HF5).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - pose proof Q2P as BP. unfold vo_Q2at, voh_Q2_pre in BP. decompose [and] BP. clear BP.
      unfold vo_Q3at, voh_Q3_pre.
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

  Lemma vo_sa1 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                        (jA : list byte),
    0 < cap ->
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 AANNOTATE_CC) fc None m3 (seg_rom asegs) -> rfull R3 ->
    getr R3 1 = Z_to_bv 64 (0xec8f8 + 196) -> getr R3 10 = Z_to_bv 64 b -> getr R3 11 = Z_to_bv 64 (b + 20 * cap) ->
    getr R3 12 = Z_to_bv 64 (b + 20 * cap) -> getr R3 13 = Z_to_bv 64 (b + 20 * cap) ->
    vo_Q2at R3 m3 A -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    vo_mid sk3 m3 pid' A [] -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (20 * cap)) jA] ->
    SHAD m3 A (cc_gen (20 * cap') (20 * cap')) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA Hc VIS3 HF3 G1 G10 G11 G12 G13 B5 G3 G4 G27 KR3 MP3 MID ABR NI CBA SHA.
    pose proof B5 as (G2 & G8 & G9 & G18 & G19 & G22 & G23 & G24 & G25 & F0 & F8 & F16 & FS0 & FS8 & FS16 & FS24
                      & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & WH & P26 & WV & WS
                      & K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & Z8 & ZV8 & ZV
                      & P44 & P45 & P46 & P47 & P48 & P49 & P50 & P51 & P52 & P53 & P54 & P55).
    pose proof MID as (MI3 & ST3 & _ & _ & AC3 & _ & _ & RH3 & _ & XP3 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct (vo_old_facts Hc) as (HIn & (O0 & O16 & On & OI & OC & OF & OAP) & OD & NZ).
    assert (NEQ : pid' <> pid) by (intros E; apply NI; rewrite E; apply in_map_iff; exists (pid, b, 20 * cap); split; [reflexivity | exact HIn]).
    pose proof (ah_disj H HH _ _ _ (pid', A, 20 * cap') (pid, b, 20 * cap) RH3 (or_introl eq_refl) (or_intror HIn) NEQ) as DAB.
    cbn [blk_addr blk_size fst snd] in DAB.
    assert (OSH3 : SHAD m3 b (cc_gen (20 * cap) (20 * cap))).
    { eapply vo_SHAD_xpres; [exact XP3 | exact (OLDSH Hc) |]. rewrite cc_gen_length by lia.
      split; [eapply (aclient_range_block_sh H); exact HIn | apply Forall_nil]. }
    rewrite (rfull_eq R3 HF3) in VIS3.
    eapply (ahh_evt_then H HH); [exact KR3 | exact VIS3 | |].
    { eapply HANN with (beg := b) (len := 20 * cap) (oldmid := 20 * cap) (newmid := 20 * cap) (lo := lo).
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
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs m3 lo (spz - 96 - 96) spz ST3 ltac:(lia))).
      - exact LO1.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI3.
      - exact AC3.
      - unfold in_app_mem. destruct (vo_band_of_aapp _ _ OAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia. }
    intros msF4 mo4 KR4 MP4 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4
                      & VIS4 & MU4 & WM4 & MI4 & ST4 & SH4 & AC4).
    rewrite G2, u64_of_Z in MU4, ST4 by lia. unfold AINTRIN_STACK in MU4.
    rewrite G1 in VIS4. rewrite (ret_pc_even (0xec8f8 + 196) ltac:(lia) eq_refl) in VIS4.
    assert (W4 : Forall (vo_wk A vo_X0) [(sh b, sh b + nsh (20 * cap)); (spz - 96 - 96 - 4096, spz - 96 - 96)]).
    { apply Forall_cons; [|apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]].
      apply (vo_wk_oldsh Hc). intros a Ha. unfold vo_X0. destruct (Z.eqb_spec b 0) as [E|_]; [contradiction|]. left. cbn [fst snd]. lia. }
    pose proof (v4_app_sh A (20 * cap') b (20 * cap) ltac:(lia) ltac:(lia) ltac:(lia) (vo_band_of_aapp _ _ AAP)) as DAS.
    pose proof (v4_sh_apart A (20 * cap') b (20 * cap) ltac:(lia) ltac:(lia) (v4_mod16_8 A A16) (v4_mod16_8 b O16) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as DSS.
    pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (sh_nsh_high b (20 * cap) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHB2. unfold AHI_LO in SHB2.
    assert (MID4 : vo_mid sk3 m4 pid' A vo_X0).
    { eapply vo_mid_munch; [eapply vo_mid_weaken; [exact MID | intros a Ha; destruct Ha] | exact ABR | exact NI
                           | exact MU4 | exact WM4 | exact MI4 | exact W4]. }
    pose proof MID4 as (_ & _ & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
    destruct (vo_hdr_X0 m4 XP4) as (F0' & F8' & F16' & ADV4 & WV4).
    assert (FLDT : forall a k z, spz - 96 - 96 <= a -> a + Z.of_nat k <= spz -> fldA m3 a k z -> fldA m4 a k z).
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
    assert (Z8' : LbB_Kit.sh0 m4 (spz - 96 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
    assert (ZV8' : LbB_Kit.sh0 m4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV' : LbB_Kit.sh0 m4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    eapply (vo_sq2 msF4 mo4 sk3 m4 _ pid' A jA Hc VIS4 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold vo_Q2at, voh_Q2_pre.
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

  Lemma vo_sq1 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                        (jA : list byte),
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 0xec8f8) fc None m3 (seg_rom asegs) -> rfull R3 ->
    vo_Q1at R3 m3 A -> getr R3 1 = Z_to_bv 64 (VOPND_SLOW_ENTRY + 428) -> getr R3 3 = gp -> getr R3 4 = tp ->
    getr R3 8 = Z_to_bv 64 (v + 8) -> getr R3 9 = Z_to_bv 64 v -> getr R3 18 = Z_to_bv 64 (sh (v + 8)) ->
    getr R3 19 = Z_to_bv 64 cap' -> getr R3 20 = Z_to_bv 64 (20 * cap) -> getr R3 21 = Z_to_bv 64 src ->
    getr R3 22 = s6 -> getr R3 23 = s7 -> getr R3 24 = s8 -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    vo_mid sk3 m3 pid' A [] -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (20 * cap)) jA] ->
    SHAD m3 A (cc_gen (20 * cap') (20 * cap')) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA VIS3 HF3 Q1P G1 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR3 MP3 MID ABR NI
      CBA SHA.
    pose proof RUNS as (_ & _ & _ & _ & _ & _ & _ & Q1A & Q1Z & _).
    pose proof Q1P as Q1r. unfold vo_Q1at, voh_Q1_pre in Q1r.
    destruct Q1r as (Q10 & Q11 & Q2 & QAC & F0 & F8 & F16 & FS0 & FS8 & FS16 & FS24 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19
                     & WH & P21 & WV & WS & Z0 & Z8 & Z16 & ZS8 & P28 & P29 & P30 & P31 & P32 & P33 & P34 & P35 & P36 & P37 & P38 & P39).
    pose proof MID as (MI3 & ST3 & _ & _ & AC3 & _ & S03 & RH3 & _ & XP3 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    pose proof (msteps_full asegs) as MSF.
    assert (MIDW : forall M4, munch [(spz - 96 - 96, spz - 96)] m3 M4 -> wmono asegs m3 M4 -> mem_inv asegs M4 ->
                     vo_mid sk3 M4 pid' A []).
    { intros M4 MU4 WM4 MI4. eapply vo_mid_munch; [exact MID | exact ABR | exact NI | exact MU4 | exact WM4 | exact MI4 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (FLDT : forall M4 a k z, munch [(spz - 96 - 96, spz - 96)] m3 M4 -> spz - 96 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                     fldA m3 a k z -> fldA M4 a k z).
    { intros M4 a k z MU4 Ha Hk Hf. unfold fldA in *. eapply fld_agree; [lia | lia | exact Hf |].
      intros a' Ha'. hnf in Ha'. apply MU4. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | exact I]. }
    assert (CBT : forall M4, munch [(spz - 96 - 96, spz - 96)] m3 M4 -> wmono asegs m3 M4 ->
                    rw_cells asegs M4 A [CB (Z.to_nat (20 * cap)) jA]).
    { intros M4 MU4 WM4. eapply rw_cells_transport; [exact CBA | exact MU4 | exact WM4 |].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. split; [lia | exact I]. }
    assert (SHT : forall M4, munch [(spz - 96 - 96, spz - 96)] m3 M4 -> wmono asegs m3 M4 ->
                    SHAD M4 A (cc_gen (20 * cap') (20 * cap'))).
    { intros M4 MU4 WM4. eapply SHAD_transport; [exact SHA | exact MU4 | exact WM4 |]. rewrite cc_gen_length by lia.
      cbn. split; [lia | exact I]. }
    destruct OB as [[E1 E2]|(Hc & HIn & ABb)].
    -
      destruct (Q1Z R3 F fc m3 v (spz - 96) b cap A cap' Q1P E1 E2)
        as (R4 & M4 & Hms & MU4 & WM4 & W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11
            & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & KK).
      pose proof (MSF _ _ Hms HF3) as HF4. cbn [ms_regs] in HF4.
      assert (MI4 : mem_inv asegs M4) by exact (msteps_mem_inv asegs _ _ Hms MI3).
      pose proof (MIDW M4 MU4 WM4 MI4) as MID4.
      pose proof MID4 as (_ & ST4 & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
      assert (XP4' : xpres H LB spz vo_X0 m M4)
        by (eapply (xpres_weaken H); [exact XP4 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (vo_hdr_X0 M4 XP4') as (F0' & F8' & F16' & ADV4 & WV4).
      assert (FS0' : fldA M4 (spz - 96) 8 A) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS0]).
      assert (FS8' : fldA M4 (spz - 96 + 8) 8 (A + 20 * cap)) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS8]).
      assert (FS16' : fldA M4 (spz - 96 + 16) 8 (A + 20 * cap + 20)) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS16]).
      assert (FS24' : fldA M4 (spz - 96 + 24) 8 (A + 20 * cap')) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS24]).
      rewrite G26 in W0. rewrite G25 in W1. rewrite G24 in W2. rewrite G23 in W3. rewrite G22 in W4. rewrite G21 in W5.
      rewrite G20 in W6. rewrite G19 in W7. rewrite G18 in W8. rewrite G9 in W9. rewrite G8 in W10. rewrite G1 in W11.
      assert (H0' : fldA M4 (spz - 96 - 96) 8 (bv_unsigned s10)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (H1' : fldA M4 (spz - 96 - 88) 8 (bv_unsigned s9)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W1).
      assert (H2' : fldA M4 (spz - 96 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W2).
      assert (H3' : fldA M4 (spz - 96 - 72) 8 (bv_unsigned s7)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W3).
      assert (H4' : fldA M4 (spz - 96 - 64) 8 (bv_unsigned s6)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W4).
      assert (H5' : fldA M4 (spz - 96 - 56) 8 src) by exact W5.
      assert (H6' : fldA M4 (spz - 96 - 48) 8 (20 * cap)) by exact W6.
      assert (H7' : fldA M4 (spz - 96 - 40) 8 cap') by exact W7.
      assert (H8' : fldA M4 (spz - 96 - 32) 8 (sh (v + 8))) by exact W8.
      assert (H9' : fldA M4 (spz - 96 - 24) 8 v) by exact W9.
      assert (H10' : fldA M4 (spz - 96 - 16) 8 (v + 8)) by exact W10.
      assert (H11' : fldA M4 (spz - 96 - 8) 8 (VOPND_SLOW_ENTRY + 428)) by exact W11.
      clear W0 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 F0 F8 F16 FS0 FS8 FS16 FS24.
      pose proof (wr_at_transport asegs _ _ _ _ WH WM4) as WH4.
      pose proof (wr_at_transport asegs _ _ _ _ WS WM4) as WS4.
      assert (ZV : LbB_Kit.sh0 M4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV8 : LbB_Kit.sh0 M4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV16 : LbB_Kit.sh0 M4 (v + 16)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZS0 : LbB_Kit.sh0 M4 (spz - 96)) by (eapply sh0_of_stack0; [exact S04 | lia]).
      assert (ZS8' : LbB_Kit.sh0 M4 (spz - 96 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
      assert (ZS16 : LbB_Kit.sh0 M4 (spz - 96 + 16)) by (eapply sh0_of_stack0; [exact S04 | lia]).
      assert (ZS24 : LbB_Kit.sh0 M4 (spz - 96 + 24)) by (eapply sh0_of_stack0; [exact S04 | lia]).
      eapply (sr_blk H HH); [exact KR3 | exact VIS3 | exact HF3 | exact Hms |].
      intros msF4 mo4 KR4 MP4 VIS4. rewrite <- (rfull_eq R4 HF4) in VIS4.
      eapply (vo_sm msF4 mo4 sk3 M4 R4 pid' A jA VIS4 HF4).
      + exact K1.
      + exact K10.
      + exact K11.
      + exact K12.
      + unfold vo_Q3at, voh_Q3_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR4.
      + eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
      + eapply (vo_mid_weaken _ _ _ _ [] vo_X0); [exact MID4 | intros a Ha; destruct Ha].
      + exact ABR.
      + exact NI.
      + exact (CBT M4 MU4 WM4).
      + exact (SHT M4 MU4 WM4).
      + intros Hc. lia.
    -
      pose proof ABb as (O0 & O16 & On & OI & OC & OF & OAP).
      destruct (Q1A R3 F fc m3 v (spz - 96) b cap A cap' Q1P ltac:(lia))
        as (R4 & M4 & Hms & MU4 & WM4 & W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11
            & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K18 & K19 & K22 & K23 & K24 & K25 & KK).
      pose proof (MSF _ _ Hms HF3) as HF4. cbn [ms_regs] in HF4.
      assert (MI4 : mem_inv asegs M4) by exact (msteps_mem_inv asegs _ _ Hms MI3).
      pose proof (MIDW M4 MU4 WM4 MI4) as MID4.
      pose proof MID4 as (_ & ST4 & _ & _ & _ & _ & S04 & _ & _ & XP4 & _ & _).
      assert (XP4' : xpres H LB spz vo_X0 m M4)
        by (eapply (xpres_weaken H); [exact XP4 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
      destruct (vo_hdr_X0 M4 XP4') as (F0' & F8' & F16' & ADV4 & WV4).
      assert (FS0' : fldA M4 (spz - 96) 8 A) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS0]).
      assert (FS8' : fldA M4 (spz - 96 + 8) 8 (A + 20 * cap)) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS8]).
      assert (FS16' : fldA M4 (spz - 96 + 16) 8 (A + 20 * cap + 20)) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS16]).
      assert (FS24' : fldA M4 (spz - 96 + 24) 8 (A + 20 * cap')) by (apply (FLDT M4); [exact MU4 | lia | cbn; lia | exact FS24]).
      rewrite G26 in W0. rewrite G25 in W1. rewrite G24 in W2. rewrite G23 in W3. rewrite G22 in W4. rewrite G21 in W5.
      rewrite G20 in W6. rewrite G19 in W7. rewrite G18 in W8. rewrite G9 in W9. rewrite G8 in W10. rewrite G1 in W11.
      assert (H0' : fldA M4 (spz - 96 - 96) 8 (bv_unsigned s10)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W0).
      assert (H1' : fldA M4 (spz - 96 - 88) 8 (bv_unsigned s9)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W1).
      assert (H2' : fldA M4 (spz - 96 - 80) 8 (bv_unsigned s8)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W2).
      assert (H3' : fldA M4 (spz - 96 - 72) 8 (bv_unsigned s7)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W3).
      assert (H4' : fldA M4 (spz - 96 - 64) 8 (bv_unsigned s6)) by (unfold fldA, fld; rewrite Z_to_bv_bv_unsigned; exact W4).
      assert (H5' : fldA M4 (spz - 96 - 56) 8 src) by exact W5.
      assert (H6' : fldA M4 (spz - 96 - 48) 8 (20 * cap)) by exact W6.
      assert (H7' : fldA M4 (spz - 96 - 40) 8 cap') by exact W7.
      assert (H8' : fldA M4 (spz - 96 - 32) 8 (sh (v + 8))) by exact W8.
      assert (H9' : fldA M4 (spz - 96 - 24) 8 v) by exact W9.
      assert (H10' : fldA M4 (spz - 96 - 16) 8 (v + 8)) by exact W10.
      assert (H11' : fldA M4 (spz - 96 - 8) 8 (VOPND_SLOW_ENTRY + 428)) by exact W11.
      clear W0 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 F0 F8 F16 FS0 FS8 FS16 FS24.
      pose proof (wr_at_transport asegs _ _ _ _ WH WM4) as WH4.
      pose proof (wr_at_transport asegs _ _ _ _ WS WM4) as WS4.
      assert (ZV : LbB_Kit.sh0 M4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZV8 : LbB_Kit.sh0 M4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
      assert (ZS8' : LbB_Kit.sh0 M4 (spz - 96 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
      eapply (sr_blk H HH); [exact KR3 | exact VIS3 | exact HF3 | exact Hms |].
      intros msF4 mo4 KR4 MP4 VIS4. rewrite <- (rfull_eq R4 HF4) in VIS4.
      eapply (vo_sa1 msF4 mo4 sk3 M4 R4 pid' A jA ltac:(lia) VIS4 HF4).
      + exact K1.
      + exact K10.
      + exact K11.
      + exact K12.
      + exact K13.
      + unfold vo_Q2at, voh_Q2_pre.
        repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
      + rewrite (KK 3%bv ltac:(inb)). exact G3.
      + rewrite (KK 4%bv ltac:(inb)). exact G4.
      + rewrite (KK 27%bv ltac:(inb)). exact G27.
      + exact KR4.
      + eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
      + exact MID4.
      + exact ABR.
      + exact NI.
      + exact (CBT M4 MU4 WM4).
      + exact (SHT M4 MU4 WM4).
  Qed.

  Lemma vo_s4 : forall (msF3 : machine_state) (mo3 : Model) (sk3 : as_St H) (m3 : mem) (R3 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jA : list byte),
    as_VIS H sk3 msF3 = MS R3 F (Z_to_bv 64 (VOPND_SLOW_ENTRY + 392)) fc None m3 (seg_rom asegs) -> rfull R3 ->
    vo_B4at R3 m3 A -> getr R3 3 = gp -> getr R3 4 = tp -> getr R3 21 = Z_to_bv 64 src ->
    getr R3 22 = s6 -> getr R3 23 = s7 -> getr R3 24 = s8 -> getr R3 25 = s9 -> getr R3 26 = s10 -> getr R3 27 = s11 ->
    as_AKREL H sk3 (mkCfg msF3 mo3) -> as_MPRES H mo mo3 ->
    vo_mid sk3 m3 pid' A [] -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m3 A [CB (Z.to_nat (20 * cap)) jA] ->
    SHAD m3 A (cc_gen (20 * cap') (20 * cap')) ->
    as_SR H Q (mkCfg msF3 mo3).
  Proof.
    intros msF3 mo3 sk3 m3 R3 pid' A jA VIS3 HF3 B4P G3 G4 G21 G22 G23 G24 G25 G26 G27 KR3 MP3 MID ABR NI CBA SHA.
    pose proof RUNS as (_ & _ & _ & B4 & _).
    pose proof B4P as B4r. unfold vo_B4at, vop_B4_pre in B4r.
    destruct B4r as (G2 & G8 & G9 & G18 & G19 & G20 & F0 & F8 & F16 & FB0 & FB8 & FB16 & FB24 & FB32
                     & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 & P30 & P31
                     & P32 & P33 & P34 & P35).
    pose proof MID as (MI3 & ST3 & _ & _ & AC3 & _ & S03 & RH3 & _ & XP3 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    assert (BM4 : b mod 4 = 0).
    { destruct OB as [[E1 _]|(_ & _ & (_ & B16 & _))]; [rewrite E1; reflexivity | clear - B16; Z.div_mod_to_equations; lia]. }
    pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    destruct (B4 R3 F fc m3 A (spz - 96) v src cap b cap' B4P)
      as (R4 & M4 & Hms & MU4 & WM4 & FS16 & K1 & K2 & K8 & K9 & K10 & K11 & K18 & K19 & K20 & KK).
    pose proof (msteps_full asegs _ _ Hms HF3) as HF4. cbn [ms_regs] in HF4.
    assert (MI4 : mem_inv asegs M4) by exact (msteps_mem_inv asegs _ _ Hms MI3).
    assert (MID4 : vo_mid sk3 M4 pid' A []).
    { eapply vo_mid_munch; [exact MID | exact ABR | exact NI | exact MU4 | exact WM4 | exact MI4 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof MID4 as (_ & ST4 & _ & _ & AC4 & _ & S04 & _ & _ & XP4 & _ & _).
    assert (XP4' : xpres H LB spz vo_X0 m M4)
      by (eapply (xpres_weaken H); [exact XP4 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (vo_hdr_X0 M4 XP4') as (F0' & F8' & F16' & ADV4 & WV4).
    assert (FLDT : forall a k z, 0 <= a -> a + Z.of_nat k <= spz - 96 + 16 \/ spz - 96 + 24 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                    fldA m3 a k z -> fldA M4 a k z).
    { intros a k z Ha Hk Hk' Hf. unfold fldA in *. eapply fld_agree; [lia | lia | exact Hf |].
      intros a' Ha'. hnf in Ha'. apply MU4. rewrite u64_of_Z by lia. cbn [outside]. split; [lia | exact I]. }
    assert (FB0' : fldA M4 (spz - 96) 8 A) by (apply FLDT; [lia | cbn; lia | cbn; lia | exact FB0]).
    assert (FB8' : fldA M4 (spz - 96 + 8) 8 (A + 20 * cap)) by (apply FLDT; [lia | cbn; lia | cbn; lia | exact FB8]).
    assert (FB24' : fldA M4 (spz - 96 + 24) 8 (A + 20 * cap')) by (apply FLDT; [lia | cbn; lia | cbn; lia | exact FB24]).
    clear F0 F8 F16 FB0 FB8 FB16 FB24 FB32.
    assert (WH4 : wr_at asegs M4 (spz - 96 - 96) 96) by (eapply wr_at_of_stk_win; [exact ST4 | lia | lia]).
    assert (WS4 : wr_at asegs M4 (spz - 96) 32) by (eapply wr_at_of_stk_win; [exact ST4 | lia | lia]).
    assert (ZV : LbB_Kit.sh0 M4 v) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV8 : LbB_Kit.sh0 M4 (v + 8)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZV16 : LbB_Kit.sh0 M4 (v + 16)) by (eapply sh0_of_addressable; [exact ADV4 | change (8 * (24 / 8)) with 24; lia]).
    assert (ZS8 : LbB_Kit.sh0 M4 (spz - 96 + 8)) by (eapply sh0_of_stack0; [exact S04 | lia]).
    eapply (sr_blk H HH); [exact KR3 | exact VIS3 | exact HF3 | exact Hms |].
    intros msF4 mo4 KR4 MP4 VIS4. rewrite <- (rfull_eq R4 HF4) in VIS4.
    eapply (vo_sq1 msF4 mo4 sk3 M4 R4 pid' A jA VIS4 HF4).
    - unfold vo_Q1at, voh_Q1_pre.
      split; [exact K10|]. split; [exact K11|]. split; [exact K2|].
      repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
    - exact K1.
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - exact K8.
    - exact K9.
    - exact K18.
    - exact K19.
    - exact K20.
    - rewrite (KK 21%bv ltac:(inb)). exact G21.
    - rewrite (KK 22%bv ltac:(inb)). exact G22.
    - rewrite (KK 23%bv ltac:(inb)). exact G23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR4.
    - eapply (ah_mpres_trans H HH); [exact MP3 | exact MP4].
    - exact MID4.
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact CBA | exact MU4 | exact WM4 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      cbn. split; [lia | exact I].
    - eapply SHAD_transport; [exact SHA | exact MU4 | exact WM4 |]. rewrite cc_gen_length by lia.
      cbn. split; [lia | exact I].
  Qed.

  Lemma vo_s3m : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                        (jA jE : list byte),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 AASAN_MEMCPY) fc None m2 (seg_rom asegs) -> rfull R2 ->
    getr R2 1 = Z_to_bv 64 (VOPND_SLOW_ENTRY + 392) -> getr R2 10 = Z_to_bv 64 (A + 20 * cap) ->
    getr R2 11 = Z_to_bv 64 src -> getr R2 12 = Z_to_bv 64 20 ->
    vo_B4at R2 m2 A -> getr R2 3 = gp -> getr R2 4 = tp -> getr R2 21 = Z_to_bv 64 src ->
    getr R2 22 = s6 -> getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    vo_mid sk2 m2 pid' A [] -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (20 * cap)) jA] -> rw_cells asegs m2 (A + 20 * cap) [CB 20 jE] ->
    SHAD m2 A (cc_gen (20 * cap') (20 * cap')) ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A jA jE VIS2 HF2 G1 G10 G11 G12 B4A G3 G4 G21 G22 G23 G24 G25 G26 G27 KR2 MP2
      MID ABR NI CBA CBE SHA.
    pose proof MID as (MI2 & ST2 & _ & _ & AC2 & _ & _ & RH2 & _ & XP2 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof B4A as (P2 & P8 & P9 & P18 & P19 & P20 & FV0 & FV8 & FV16 & FS0 & FS8 & FS16 & FS24 & FS32
                       & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & WSP & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18
                       & N19 & N20).
    assert (G2 : getr R2 2 = Z_to_bv 64 (spz - 96)) by exact P2.
    destruct (SRC m2 AC2 MI2 (vo_apres_of_xpres_nil m2 XP2)) as (SB & SACC & SSV).
    rewrite SRCL in SACC, SSV.
    assert (SD : src + 20 <= A + 20 * cap \/ A + 20 * cap + 20 <= src).
    { destruct SRCC as [CR|CI]; [|unfold AIMG_TOP in CI; left; lia].
      destruct (Z_le_gt_dec (src + 20) (A + 20 * cap)) as [L1|L1]; [left; exact L1|].
      destruct (Z_le_gt_dec (A + 20 * cap + 20) src) as [L2|L2]; [right; exact L2|]. exfalso.
      assert (PT : exists a, src <= a < src + 20 /\ A <= a < A + 20 * cap').
      { destruct (Z_le_gt_dec src (A + 20 * cap)) as [L3|L3]; [exists (A + 20 * cap) | exists src]; split; lia. }
      destruct PT as (a & Ha1 & Ha2).
      pose proof (aclient_range_addr H _ _ _ _ a CR Ha1) as ACA.
      destruct (vo_cls _ _ _ _ _ spz _ a RH2 NI ltac:(lia) ACA) as [K|(K1 & K2 & K3)]; [lia | apply K2; exact Ha2]. }
    assert (ADA : addressable m2 A (20 * cap')) by (split; [lia | rewrite <- cc_gen_full; exact SHA]).
    rewrite (rfull_eq R2 HF2) in VIS2.
    eapply (ahh_evt_then H HH); [exact KR2 | exact VIS2 | |].
    { eapply (ah_memcpy H HH) with (src := bs) (junk := jE) (lo := lo); rewrite ?G10, ?G11, ?G12, ?G2; rewrite ?u64_of_Z by lia.
      - exact SB.
      - lia.
      - exact CBE.
      - exact SD.
      - exact SACC.
      - eapply addressable_accessible; [exact ADA | lia | lia | unfold AAPP_HI; lia].
      - exact SSV.
      - eapply shvis_sub; [exact (ah_blk_shvis H HH _ _ _ _ _ _ RH2 (or_introl eq_refl)) | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m2 lo (spz - 96) spz ST2 ltac:(lia))).
      - exact LO1.
      - unfold AINTRIN_STACK; lia.
      - exact MI2.
      - exact AC2.
      - lia.
      - exact SRCA.
      - unfold in_app_mem. destruct (vo_band_of_aapp _ _ AAP) as [K|K]; [left | right]; unfold ASHADOW_BASE, AHI_LO, AAPP_HI; lia.
      - eapply aconst_ok_app; [exact AAP | lia | lia].
      - left; lia.
      - destruct SRCD; [left | right]; lia. }
    intros msF3 mo3 KR3 MP3 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3
                      & VIS3 & MU3 & WM3 & MI3 & ST3 & CB3 & SB3 & AC3).
    rewrite G10, G12, G2, ?u64_of_Z in MU3 by lia.
    unfold AINTRIN_STACK in MU3.
    rewrite G1 in VIS3. rewrite (ret_pc_even (VOPND_SLOW_ENTRY + 392) ltac:(unfold VOPND_SLOW_ENTRY; lia) eq_refl) in VIS3.
    assert (W3 : Forall (vo_wk A []) [(A + 20 * cap, A + 20 * cap + 20); (spz - 96 - 4096, spz - 96)]).
    { apply Forall_cons; [right; left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (MID3 : vo_mid sk2 m3 pid' A [])
      by (eapply vo_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 | exact W3]).
    pose proof MID3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XP3 & _ & _).
    assert (XP3' : xpres H LB spz vo_X0 m m3)
      by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (vo_hdr_X0 m3 XP3') as (FV0' & FV8' & FV16' & _ & _).
    assert (FT : forall a z, fldA m2 a 8 z -> spz - 96 <= a -> a + 8 <= spz -> fldA m3 a 8 z).
    { intros a z Hf Ha Hk. unfold fldA in Hf |- *. eapply fld_agree; [lia | change (Z.of_nat 8) with 8; lia | exact Hf |].
      intros y Hy. red in Hy. change (Z.of_nat 8) with 8 in Hy. apply MU3. rewrite u64_of_Z by lia.
      cbn [outside]. split; [lia | split; [lia | exact I]]. }
    eapply (vo_s4 msF3 mo3 sk2 m3 _ pid' A jA VIS3 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold vo_B4at, vop_B4_pre.
      refine (conj P2 (conj P8 (conj P9 (conj P18 (conj P19 (conj P20 (conj FV0' (conj FV8' (conj FV16' _))))))))).
      do 5 (split; [eapply FT; [eassumption | lia | lia] |]).
      refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 _)))))))).
      refine (conj (wr_at_transport asegs _ _ _ _ WSP WM3) _).
      exact (conj N9 (conj N10 (conj N11 (conj N12 (conj N13 (conj N14 (conj N15 (conj N16 (conj N17 (conj N18 (conj N19
        N20))))))))))).
    - exact G3.
    - exact G4.
    - exact G21.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR3.
    - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
    - exact MID3.
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact CBA | exact MU3 | exact WM3 |].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. split; [lia | split; [lia | exact I]].
    - eapply SHAD_transport; [exact SHA | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
      pose proof (v4_app_sh (A + 20 * cap) 20 A (20 * cap') ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(destruct (vo_band_of_aapp _ _ AAP); [left|right]; lia)) as D.
      pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as D2. unfold AHI_LO in D2.
      cbn. split; [lia | split; [lia | exact I]].
  Qed.

  Lemma vo_s3 : forall (msF2 : machine_state) (mo2 : Model) (sk2 : as_St H) (m2 : mem) (R2 : bvmap 5 word) (pid' : bptr) (A : Z)
                       (jall : list byte),
    as_VIS H sk2 msF2 = MS R2 F (Z_to_bv 64 (VOPND_SLOW_ENTRY + 248)) fc None m2 (seg_rom asegs) -> rfull R2 ->
    vo_B3at R2 m2 A -> getr R2 3 = gp -> getr R2 4 = tp ->
    getr R2 22 = s6 -> getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    as_AKREL H sk2 (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
    vo_mid sk2 m2 pid' A [] -> ablock_range H A (20 * cap') -> ~ In pid' (map blk_id LB) ->
    rw_cells asegs m2 A [CB (Z.to_nat (20 * cap')) jall] -> addressable m2 A (20 * cap') ->
    as_SR H Q (mkCfg msF2 mo2).
  Proof.
    intros msF2 mo2 sk2 m2 R2 pid' A jall VIS2 HF2 B3A G3 G4 G22 G23 G24 G25 G26 G27 KR2 MP2 MID ABR NI CBall ADD2.
    pose proof RUNS as (_ & _ & B3 & _).
    pose proof MID as (MI2 & ST2 & _ & _ & AC2 & _ & _ & RH2 & _ & XP2 & _ & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & _).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof B3A as (P10 & P21 & P2 & P8 & P9 & P18 & P19 & P20 & FV0 & FV8 & FV16 & FS32
                       & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & WSP & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18
                       & N19 & N20).
    destruct (B3 R2 F fc m2 A (spz - 96) v src cap b cap' B3A)
      as (R3 & M3 & Hms & MU3 & WM3 & W24 & W16 & W8 & W0 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17
          & K18 & K19 & K20 & K21 & KK).
    pose proof (msteps_full asegs _ _ Hms HF2) as HF3. cbn [ms_regs] in HF3.
    assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms MI2).
    assert (MID3 : vo_mid sk2 M3 pid' A []).
    { eapply vo_mid_munch; [exact MID | exact ABR | exact NI | exact MU3 | exact WM3 | exact MI3 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof MID3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XP3 & _ & _).
    assert (XP3' : xpres H LB spz vo_X0 m M3)
      by (eapply (xpres_weaken H); [exact XP3 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (vo_hdr_X0 M3 XP3') as (FV0' & FV8' & FV16' & _ & _).
    assert (FS32' : fldA M3 (spz - 96 + 32) 8 v).
    { unfold fldA in FS32 |- *. eapply fld_agree; [lia | change (Z.of_nat 8) with 8; lia | exact FS32 |].
      intros y Hy. red in Hy. change (Z.of_nat 8) with 8 in Hy. apply MU3. rewrite u64_of_Z by lia.
      cbn [outside]. split; [lia | exact I]. }
    destruct (rw_cells_CB_split asegs m2 A (Z.to_nat (20 * cap')) (Z.to_nat (20 * cap)) jall CBall ltac:(lia)) as [CBA REST].
    destruct (rw_cells_CB_split asegs m2 (A + Z.of_nat (Z.to_nat (20 * cap))) (Z.to_nat (20 * cap') - Z.to_nat (20 * cap)) 20
                (skipn (Z.to_nat (20 * cap)) jall) REST ltac:(lia)) as [CBE _].
    rewrite Z2Nat.id in CBE by lia.
    assert (SHA0 : SHAD m2 A (cc_gen (20 * cap') (20 * cap'))) by (rewrite cc_gen_full; exact (proj2 ADD2)).
    pose proof (sh_nsh_high A (20 * cap') ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHA2. unfold AHI_LO in SHA2.
    eapply (sr_blk H HH); [exact KR2 | exact VIS2 | exact HF2 | exact Hms |].
    intros msF3 mo3 KR3 MP3 VIS3. rewrite <- (rfull_eq R3 HF3) in VIS3.
    eapply (vo_s3m msF3 mo3 sk2 M3 R3 pid' A _ _ VIS3 HF3).
    - exact K1.
    - exact K10.
    - exact K11.
    - exact K12.
    - unfold vo_B4at, vop_B4_pre.
      refine (conj K2 (conj K8 (conj K9 (conj K18 (conj K19 (conj K20 (conj FV0' (conj FV8' (conj FV16'
        (conj W0 (conj W8 (conj W16 (conj W24 (conj FS32' _)))))))))))))).
      refine (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 _)))))))).
      refine (conj (wr_at_transport asegs _ _ _ _ WSP WM3) _).
      exact (conj N9 (conj N10 (conj N11 (conj N12 (conj N13 (conj N14 (conj N15 (conj N16 (conj N17 (conj N18 (conj N19
        N20))))))))))).
    - rewrite (KK 3%bv ltac:(inb)). exact G3.
    - rewrite (KK 4%bv ltac:(inb)). exact G4.
    - exact K21.
    - rewrite (KK 22%bv ltac:(inb)). exact G22.
    - rewrite (KK 23%bv ltac:(inb)). exact G23.
    - rewrite (KK 24%bv ltac:(inb)). exact G24.
    - rewrite (KK 25%bv ltac:(inb)). exact G25.
    - rewrite (KK 26%bv ltac:(inb)). exact G26.
    - rewrite (KK 27%bv ltac:(inb)). exact G27.
    - exact KR3.
    - eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
    - exact MID3.
    - exact ABR.
    - exact NI.
    - eapply rw_cells_transport; [exact CBA | exact MU3 | exact WM3 |].
      cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. split; [lia | exact I].
    - eapply rw_cells_transport; [exact CBE | exact MU3 | exact WM3 |].
      cbn [cells_size csize]. cbn. split; [lia | exact I].
    - eapply SHAD_transport; [exact SHA0 | exact MU3 | exact WM3 |]. rewrite cc_gen_length by lia.
      cbn. split; [lia | exact I].
  Qed.

  Lemma vo_sn : forall (msF1 : machine_state) (mo1 : Model) (m1 : mem) (R1 : bvmap 5 word) (e1 : word),
    as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AOPNEW) fc None m1 (seg_rom asegs) -> rfull R1 ->
    getr R1 1 = Z_to_bv 64 (VOPND_SLOW_ENTRY + 248) -> getr R1 2 = Z_to_bv 64 (spz - 96) -> getr R1 3 = gp -> getr R1 4 = tp ->
    getr R1 8 = Z_to_bv 64 (v + 8) -> getr R1 9 = Z_to_bv 64 v -> getr R1 10 = Z_to_bv 64 (20 * cap') ->
    getr R1 18 = Z_to_bv 64 (sh (v + 8)) -> getr R1 19 = Z_to_bv 64 cap' -> getr R1 20 = Z_to_bv 64 (20 * cap) ->
    getr R1 21 = Z_to_bv 64 src ->
    getr R1 22 = s6 -> getr R1 23 = s7 -> getr R1 24 = s8 -> getr R1 25 = s9 -> getr R1 26 = s10 -> getr R1 27 = s11 ->
    as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    mem_inv asegs m1 -> stk asegs m1 lo spz -> rw_cells asegs m1 (errno_addr tp) [C4 e1] -> as_rauxv_ok H m1 B ->
    ACONST m1 -> as_RFS H LF m1 -> stack0 m1 lo shi -> as_RHEAP H s LB m1 -> rw_cells asegs m1 (spz - 64) FRAME ->
    xpres H LB spz [] m m1 -> lb_own LB m1 ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 m1 R1 e1 VIS1 HF1 G1 G2 G3 G4 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 KR1 MP1
      MI1 ST1 ERR1 RA1 AC1 RF1 S01 RH1 FR1 XP1 OW1.
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof vo_vec_facts as (_ & _ & _ & _ & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (SP96 : (spz - 96) mod 16 = 0) by exact (v4_mod16_sub96 spz SP16).
    assert (CMB : as_Cm H (20 * cap') <= as_AL H s).
    { pose proof CM as CM'. change (v4_newcap cap) with cap' in CM'.
      assert (CF0 : 0 <= as_Cf H (20 * cap)) by (pose proof (ah_costs H HH) as (_ & _ & CF & _); apply CF; lia). lia. }
    rewrite (rfull_eq R1 HF1) in VIS1.
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := 20 * cap') (LB := LB) (lo := lo) (B := B) (errv := e1);
        [ exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CMB | exact RA1 | rewrite G2, u64_of_Z by lia; lia
        | rewrite G2, u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo (spz - 96) spz ST1 ltac:(lia)))
        | exact LO1 | rewrite G2, u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
        | rewrite G4; exact ERR1 | exact MI1 | rewrite G4; exact TPV | rewrite G2, u64_of_Z by lia; exact SP96
        | exact AC1 | exact G10 | lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p
                      & sk2 & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RAX2 & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2.
    assert (ER1 : 0 <= VOPND_SLOW_ENTRY + 248 < 2 ^ 64) by (unfold VOPND_SLOW_ENTRY; lia).
    assert (ER2 : (VOPND_SLOW_ENTRY + 248) mod 2 = 0) by (unfold VOPND_SLOW_ENTRY; reflexivity).
    rewrite (ret_pc_even (VOPND_SLOW_ENTRY + 248) ER1 ER2) in VIS2.
    rewrite G2, u64_of_Z in AP2, ST2 by lia. rewrite G4 in ERR2.
    pose proof (ah_nodup H HH _ _ _ RH2) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [NI _].
    cbn [blk_id fst] in NI.
    assert (STm : stk asegs m2 lo spz).
    { eapply (stk_merge asegs); [exact ST2 | | lia].
      eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs m1 lo (spz - 96) spz ST1 ltac:(lia))) | lia]. }
    assert (FR2 : rw_cells asegs m2 (spz - 64) FRAME) by (eapply (apres_rw_cells H); [exact AP2 | exact FR1 | left; lia]).
    assert (XP2 : xpres H LB spz [] m m2).
    { eapply (xpres_trans H); [exact XP1 |].
      eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]. }
    assert (MID : vo_mid sk2 m2 p A []).
    { split; [exact MI2|]. split; [exact STm|].
      split; [exists errv2; exact ERR2|].
      split; [exact RAX2|]. split; [exact AC2|].
      split; [exact (RFS_via_apres H HH LF LB _ m1 m2 RF1 AP2)|].
      split; [eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]|].
      split; [exact RH2|]. split; [exact FR2|]. split; [exact XP2|]. split; [exact AL2|].
      apply lb_own_cons; [exact (own_of_rw_cells _ _ _ _ CB2 ltac:(lia)) | exact (lb_own_apres H _ _ _ _ _ OW1 AP2 (fun bb Hb => Hb))]. }
    pose proof ABR as (A0 & A16 & An & AI & ACE & AFS & AAP). unfold AIMG_TOP in AI.
    assert (XP2' : xpres H LB spz vo_X0 m m2)
      by (eapply (xpres_weaken H); [exact XP2 | lia | intros bb Hb; exact Hb | intros a Ha; destruct Ha]).
    destruct (vo_hdr_X0 m2 XP2') as (F0 & F8 & F16 & _ & _).
    assert (FV : fldA m2 (spz - 96 + 32) 8 v).
    { replace (spz - 96 + 32) with (spz - 64) by lia. unfold fldA, fld.
      pose proof (rw_cells_read asegs m2 (spz - 64) _ 0%nat _ FR2 eq_refl) as RD.
      replace (spz - 64 + Z.of_nat 0) with (spz - 64) in RD by lia.
      rewrite <- rdn_of_ov. exact RD. }
    assert (WR : wr_at asegs m2 (spz - 96) 96) by (eapply wr_at_of_stk_win; [exact STm | lia | lia]).
    assert (OB0 : 0 <= b /\ b + 20 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    assert (SRB : 0 <= src /\ src + 20 <= 2 ^ 47) by (unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI in SRCA; lia).
    eapply (vo_s3 msF2 mo2 sk2 m2 _ p A junk VIS2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
    - unfold vo_B3at, vop_B3_pre.
      repeat match goal with |- _ /\ _ => split end; first [ reflexivity | assumption | lia ].
    - exact G3.
    - exact G4.
    - exact G22.
    - exact G23.
    - exact G24.
    - exact G25.
    - exact G26.
    - exact G27.
    - exact KR2.
    - eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2].
    - exact MID.
    - exact ABR.
    - exact NI.
    - exact CB2.
    - exact ADDR.
  Qed.

  Lemma vo_main : forall (msF : machine_state) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 VOPND_SLOW_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros msF t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv VIS KR ERR.
    pose proof RUNS as (B1T & B1F & _).
    pose proof SPR as (SPL & SPH & SP16). pose proof LOR as [LO1 LO2].
    unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LO2.
    pose proof vo_vec_facts as (F0 & F1 & F2 & _ & C0 & OB).
    destruct (vo_capb C0) as [CP1 CP2].
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    assert (OB0 : 0 <= b /\ b + 20 * cap < 2 ^ 47).
    { destruct OB as [[E1 E2]|(Hc & HIn & (O0 & O16 & On & OI & OC & OF & OAP))]; [rewrite E1, E2; lia | lia]. }
    pose proof OBJ as (_ & _ & _ & _ & _ & SD).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) (Z_to_bv 64 src) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R0 eqn:HR0.
    assert (HF0 : rfull R0) by (rewrite HR0; apply rfull_mkR).
    assert (PRE : vop_B1_pre R0 m v src spz b cap).
    { unfold vop_B1_pre. rewrite HR0.
      repeat match goal with |- _ /\ _ => split end;
        first [ reflexivity | exact spz_sp | assumption | lia
              | (eapply wr_at_of_stk_win; [exact ST0 | lia | lia])
              | (eapply sh0_of_addressable; [exact ADV0 | change (8 * (24 / 8)) with 24; lia]) ]. }
    assert (B1 : exists R1 M1,
      CatSim.msteps asegs (MS R0 F (wz VOPND_SLOW_ENTRY) fc None m (seg_rom asegs)) (MS R1 F (wz AOPNEW) fc None M1 (seg_rom asegs))
      /\ munch [((spz - 64), spz)] m M1 /\ wmono asegs m M1
      /\ fldA M1 (spz - 64) 8 v
      /\ LbB_RwSem.fldw asegs M1 (spz - 56) 8 (getr R0 21) /\ LbB_RwSem.fldw asegs M1 (spz - 48) 8 (getr R0 20)
      /\ LbB_RwSem.fldw asegs M1 (spz - 40) 8 (getr R0 19) /\ LbB_RwSem.fldw asegs M1 (spz - 32) 8 (getr R0 18)
      /\ LbB_RwSem.fldw asegs M1 (spz - 24) 8 (getr R0 9) /\ LbB_RwSem.fldw asegs M1 (spz - 16) 8 (getr R0 8)
      /\ LbB_RwSem.fldw asegs M1 (spz - 8) 8 (getr R0 1)
      /\ getr R1 1 = wz (VOPND_SLOW_ENTRY + 248) /\ getr R1 2 = wz (spz - 96)
      /\ getr R1 8 = wz (v + 8) /\ getr R1 9 = wz v /\ getr R1 10 = wz (20 * cap')
      /\ getr R1 18 = wz (sh (v + 8)) /\ getr R1 19 = wz cap' /\ getr R1 20 = wz (20 * cap) /\ getr R1 21 = wz src
      /\ (forall r, In r [3; 4; 5; 6; 7; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv -> getr R1 r = getr R0 r)).
    { destruct (Z_le_gt_dec cap 1) as [CL|CL].
      - destruct (B1F R0 F fc m v src spz b cap PRE CL)
          as (R1 & M1 & Hms & MU & WM & Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14
              & K15 & K16 & K18 & K19 & K20 & K21 & KK).
        exists R1, M1.
        repeat (split; [assumption|]).
        split; [rewrite K10; f_equal; unfold cap', v4_newcap; rewrite vgrow_le1 by lia; Z.div_mod_to_equations; lia|].
        split; [assumption|].
        split; [rewrite K19; f_equal; unfold cap', v4_newcap; rewrite vgrow_le1 by lia; Z.div_mod_to_equations; lia|].
        repeat (split; [assumption|]). exact KK.
      - destruct (B1T R0 F fc m v src spz b cap PRE ltac:(lia))
          as (R1 & M1 & Hms & MU & WM & Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & K1 & K2 & K8 & K9 & K10 & K11 & K12 & K13 & K14
              & K15 & K16 & K18 & K19 & K20 & K21 & KK).
        exists R1, M1.
        repeat (split; [assumption|]).
        split; [rewrite K10; f_equal; unfold cap', v4_newcap; rewrite vgrow_ge2 by lia; Z.div_mod_to_equations; lia|].
        split; [assumption|].
        split; [rewrite K19; f_equal; unfold cap', v4_newcap; rewrite vgrow_ge2 by lia; Z.div_mod_to_equations; lia|].
        repeat (split; [assumption|]). exact KK. }
    destruct B1 as (R1 & M1 & Hms & MU1 & WM1 & Q0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & K1 & K2 & K8 & K9 & K10 & K18 & K19
                    & K20 & K21 & KK).
    rewrite HR0 in Q1, Q2, Q3, Q4, Q5, Q6, Q7.
    pose proof (msteps_full asegs _ _ Hms HF0) as HF1. cbn [ms_regs] in HF1.
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI0).
    pose proof (ah_fsb H HH _ _ _ RH0) as (FS1 & FS2 & FS3 & FS4).
    assert (SWL : aceil <= spz - 64) by lia.
    destruct (stack_window_ok H LB LF (spz - 64) spz SWL FS2) as (SW1 & SW2 & SW3).
    destruct (client_frame H HH s LB LF B [(spz - 64, spz)] m M1 RH0 RF0 AC0 RA0 MU1 WM1
                ltac:(apply Forall_cons; [exact SW1 | apply Forall_nil]) ltac:(apply Forall_cons; [exact SW2 | apply Forall_nil])
                ltac:(apply Forall_cons; [exact SW3 | apply Forall_nil]))
      as (RH1 & RF1 & AC1 & RA1).
    assert (ST1 : stk asegs M1 lo spz) by (apply (stk_high_transport m M1 lo spz ST0 WM1); unfold AIMG_TOP; lia).
    assert (C8F : forall a w, LbB_RwSem.fldw asegs M1 a 8 w -> spz - 64 <= a -> a + 8 <= spz -> rw_cells asegs M1 a [C8 w]).
    { intros a w Hf Ha1 Ha2. split.
      - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_of_rdn; [lia | rewrite length_le8; lia | rewrite length_le8; exact Hf].
      - eapply wr_at_of_stk_win; [exact ST1 | lia | cbn; lia]. }
    assert (FRM : rw_cells asegs M1 (spz - 64) FRAME).
    { unfold FRAME. cbn [map].
      apply rw_cells_cons8; [apply C8F; [exact Q0 | lia | lia]|]. replace (spz - 64 + 8) with (spz - 56) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q1 | lia | lia]|]. replace (spz - 56 + 8) with (spz - 48) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q2 | lia | lia]|]. replace (spz - 48 + 8) with (spz - 40) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q3 | lia | lia]|]. replace (spz - 40 + 8) with (spz - 32) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q4 | lia | lia]|]. replace (spz - 32 + 8) with (spz - 24) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q5 | lia | lia]|]. replace (spz - 24 + 8) with (spz - 16) by lia.
      apply rw_cells_cons8; [apply C8F; [exact Q6 | lia | lia]|]. replace (spz - 16 + 8) with (spz - 8) by lia.
      apply C8F; [exact Q7 | lia | lia]. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. rewrite TPV. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. split; [lia | exact I]. }
    assert (S01 : stack0 M1 lo shi).
    { eapply stack0_transport; [exact S00 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst]; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (XP1 : xpres H LB spz [] m M1).
    { eapply (xpres_of_munch H s LB spz [] [(spz - 64, spz)] m m M1); [exact HH | exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (OW1 : lb_own LB M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact HF0 | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1. rewrite <- (rfull_eq R1 HF1) in VIS1.
    eapply (vo_sn msF1 mo1 M1 R1 errv VIS1 HF1).
    - exact K1.
    - exact K2.
    - rewrite (KK 3%bv ltac:(inb)), HR0. reflexivity.
    - rewrite (KK 4%bv ltac:(inb)), HR0. reflexivity.
    - exact K8.
    - exact K9.
    - exact K10.
    - exact K18.
    - exact K19.
    - exact K20.
    - exact K21.
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
End VoS.

Theorem vopnd_slow_ok {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps H -> vopnd_slow_stmt H.
Proof.
  intros H HH. unfold vopnd_slow_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF
    v b cap src bs pid lo B shi errv.
  intros VIS -> -> VEC V8 ADV OBJ VBAND VWR OWN OLD OLDSH GROW SRC SRCL SRCA SRCD SRCC RH KR AOK CM TRO RA SPB SP16 SP47 ST CE
    LOl ERR MI TPV RA2 AC RF S0 SHI.
  pose proof aceil_facts as ((ACF1 & ACF2) & _ & _).
  unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK in LOl.
  eapply vo_main; try eassumption; try reflexivity.
  all: lazymatch goal with
       | |- vo_runs _ => exact vo_runs_fc400
       | |- _ /\ _ /\ _ mod 16 = 0 => split; [lia|]; split; [exact SP47 | exact SP16]
       | |- aceil <= _ /\ _ => split; [exact CE | unfold VOPND_STACK, AOPNEW_STACK, AMALLOC_STACK; lia]
       end.
Qed.
