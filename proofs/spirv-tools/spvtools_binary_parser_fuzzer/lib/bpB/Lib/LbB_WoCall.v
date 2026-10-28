(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoMs.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma outside_of_forall : forall (W : list (Z * Z)) a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
Proof.
  induction W as [|[x y] W IH]; intros a K; [exact I|]. cbn [outside]. split.
  - pose proof (K (x, y) (or_introl eq_refl)) as X. cbn in X. exact X.
  - apply IH. intros iv Hiv. apply K. right. exact Hiv.
Qed.

Lemma wshvis_nil : forall m, shvis m 0 0.
Proof. intros m. unfold shvis. replace (sh (hull_lo 0)) with 2147450880 by reflexivity. replace (sh (hull_hi 0)) with 2147450880 by reflexivity.
  apply stk_empty. lia. Qed.

Section Call.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition wbw (e : went H) (ff : Z) (P k : Z) (iv : Z * Z) : Prop :=
    (P <= fst iv /\ snd iv <= P + k) \/ (sh P <= fst iv /\ snd iv <= sh P + nsh k) \/ wwin H e ff iv.

  Lemma winv_bw : forall e ff fp XSc sk LBk m1 m2 W pv P k,
    wpre H e -> winv H e ff fp XSc sk LBk m1 -> In (pv, P, k) LBk ->
    (forall b, In b (w_LB e) -> In b LBk /\ blk_id b <> pv) ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 (w_lo e) (wSP e) ->
    Forall (wbw e ff P k) W ->
    winv H e ff fp XSc sk LBk m2.
  Proof.
    intros e ff fp XSc sk LBk m1 m2 W pv P k HP HI INv LBI MU WM MI2 ST2 FW.
    pose proof (wpre_geo H e HP) as (CE & LO & SH1 & SH2 & _ & TP).
    pose proof (winv_ff H _ _ _ _ _ _ _ HI) as FF.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (ah_blocks H HH _ _ _ _ (winv_rh H _ _ _ _ _ _ _ HI) INv) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn in B0, B16, Bn, BI, BC, BF, BAPP.
    pose proof aceil_facts as ACF.
    assert (SHP : sh P + nsh k <= sh aceil) by (unfold sh, nsh; Z.div_mod_to_equations; nia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHL : 0x7fff8000 <= sh P) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (LOs : w_lo e <= wSP e - WO_SAVED) by (unfold WO_SAVED; lia).
    assert (SPH : wSP e <= AAPP_HI) by lia.

    assert (WW : Forall (fun iv => aclient_write_ok H LBk iv /\ afs_write_ok H ((6, ff, fp) :: w_LF e) iv /\ aconst_ok iv /\ stack0_ok iv
                           /\ (snd iv <= wSP e - WO_SAVED \/ wSP e <= fst iv) /\ (snd iv <= ff + WO_FLAGP \/ ff + 4096 <= fst iv)
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
                           /\ ((aceil <= fst iv /\ snd iv <= wSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XSc) a)
                               \/ (P <= fst iv /\ snd iv <= P + k) \/ (sh P <= fst iv /\ snd iv <= sh P + nsh k))) W).
    { eapply Forall_impl; [| exact FW]. intros [x y] Hw. unfold wbw in Hw. cbn [fst snd] in *.
      destruct Hw as [(X1 & X2)|[(X1 & X2)|Hw]].
      - split; [right; right; left; exists (pv, P, k); split; [exact INv | cbn; lia]|].
        split; [left; cbn [fst snd]; split; [destruct BF; [left | right]; unfold AFS_SIZE in *; lia | right; unfold ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia]|].
        split; [eapply (aconst_ok_app P k); [exact BAPP | exact X1 | exact X2]|].
        split; [eapply (stack0_ok_aapp P k); [exact BAPP | exact X1 | exact X2]|].
        unfold WO_SAVED, WO_FLAGP. split; [left; lia|]. split; [destruct BF; unfold AFS_SIZE in *; lia|].
        split; [right; unfold ATP, AIMG_TOP in *; lia|]. right; right; left; lia.
      - split; [right; right; right; left; exists (pv, P, k); split; [exact INv | cbn; lia]|].
        split; [left; cbn [fst snd]; split;
                [destruct (aapp_disjoint_sh (as_FSB H) AFS_SIZE P k F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); [left | right]; lia
                | right; unfold ATLS_PRIV_HI, ATP in *; lia]|].
        split; [apply aconst_ok_high; [assert (sh AIMG_TOP <= sh P) by (apply sh_mono; unfold AIMG_TOP in *; lia); lia | right; left; lia]|].
        split; [right; cbn; lia|].
        unfold WO_SAVED, WO_FLAGP. split; [left; lia|].
        split; [destruct (aapp_disjoint_sh (as_FSB H) AFS_SIZE P k F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)); [left | right]; lia|].
        split; [right; unfold ATP; lia|]. right; right; right; lia.
      - destruct (wwin_ok H e ff fp XSc (x, y) FF CE LOs SPH Hw) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        split; [exact (B2 LBk)|]. split; [exact B1|]. split; [exact B3|]. split; [exact B4|]. split; [exact B6|].
        split; [exact B7|]. split; [exact B8|]. destruct B5 as [B5|B5]; [left; exact B5 | right; left; exact B5]. }
    assert (A1 : Forall (aclient_write_ok H LBk) W) by (eapply Forall_impl; [| exact WW]; intros iv X; apply X).
    assert (A2 : Forall (afs_write_ok H ((6, ff, fp) :: w_LF e)) W) by (eapply Forall_impl; [| exact WW]; intros iv X; apply X).
    assert (A3 : Forall aconst_ok W) by (eapply Forall_impl; [| exact WW]; intros iv X; apply X).
    assert (A4 : Forall stack0_ok W) by (eapply Forall_impl; [| exact WW]; intros iv X; apply X).
    assert (DJ : forall A n, (forall iv, In iv W -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from W A n).
    { intros A n K. clear - K. induction W as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    destruct HI as (RF & FF' & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & WFP & XP & FS & LVI).
    unfold winv. rewrite (werrno_ATP H e TP) in ER |- *.
    split; [eapply (ah_RFS_frame H HH); [exact RF | exact MU | exact WM | exact A2]|].
    split; [exact FF'|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact A1]|].
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact A3]|].
    split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact A4]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU | exact WM | exact A1]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | cbn [cells_size csize]; apply DJ;
              intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WW iv Hiv) as (_ & _ & _ & _ & _ & _ & X & _); lia]|].
    split; [exact ST2|].
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | apply DJ;
              intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WW iv Hiv) as (_ & _ & _ & _ & X & _); unfold WO_SAVED in *; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | apply DJ;
              intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WW iv Hiv) as (_ & _ & _ & _ & _ & X & _); unfold WO_FLAGP in *; cbn; lia]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [exact (wr_at_wmono _ _ _ _ WFP WM)|].
    split; [| split; [exact FS|]].
    2: {
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv HW.
      unfold wbw, wwin in HW. unfold AIMG_TOP in *. destruct HW as [(X1 & _)|[(X1 & _)|[(X1 & _)|[(X1 & _)|(X1 & _)]]]]; lia. }
    eapply xpres_trans; [exact XP|]. intros a Ha [Hc Hx]. split; [| intros X; apply WM; exact X].
    apply MU. unfold wa. rewrite HLib.u64_of_Z by lia.
    apply outside_of_forall. intros [x y] Hiv. pose proof (proj1 (Forall_forall _ _) WW (x, y) Hiv) as W1.
    destruct W1 as (_ & _ & _ & _ & _ & _ & _ & K). cbn [fst snd] in K |- *.
    destruct (aclient_low H HH _ _ _ _ a (wpre_RH0 H e HP) Hc) as [L|L].
    - destruct K as [K|[K|[K|K]]]; [lia | | lia | lia].
      intros Hin. apply Hx. right. apply K. exact Hin.
    - destruct K as [K|[K|[K|K]]]; [lia | intros Hin; apply Hx; right; apply K; exact Hin | |].
      +
        intros Hin. unfold aclient_addr in Hc.
        destruct Hc as [Hc|[Hc|[(b & INb & Hb)|[(b & INb & Hb)|[Hc|[Hc|Hc]]]]]].
        * lia.
        * unfold aimg_client in Hc. unfold AIMG_TOP in BI. lia.
        * destruct (LBI b INb) as (INb' & NE).
          destruct (ah_disj H HH _ _ _ b (pv, P, k) RH INb' INv NE) as [D|D]; cbn in D; lia.
        * destruct (LBI b INb) as (INb' & _).
          pose proof (ah_blocks H HH _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
          pose proof (aapp_disjoint_sh P k (blk_addr b) (blk_size b) BAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) Cn) as D. lia.
        * destruct BF; unfold AFS_SIZE in *; lia.
        * pose proof (aapp_disjoint_sh P k (as_FSB H) AFS_SIZE BAPP ltac:(lia) ltac:(unfold AAPP_HI, AFS_SIZE in *; lia) ltac:(unfold AFS_SIZE; lia)) as D.
          assert (sh (as_FSB H + AFS_SIZE) <= sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh; Z.div_mod_to_equations; lia). lia.
        * unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in BAPP, Hc.
          assert (sh 0x7fff7000 <= sh aceil) by (apply sh_mono; lia). replace (sh 0x7fff7000) with 0x8fff6e00 in * by reflexivity. lia.
      +
        intros Hin. unfold aclient_addr in Hc.
        destruct Hc as [Hc|[Hc|[(b & INb & Hb)|[(b & INb & Hb)|[Hc|[Hc|Hc]]]]]].
        * lia.
        * unfold aimg_client in Hc. lia.
        * destruct (LBI b INb) as (INb' & _).
          pose proof (ah_blocks H HH _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
          pose proof (aapp_disjoint_sh (blk_addr b) (blk_size b) P k CAPP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D. lia.
        * destruct (LBI b INb) as (INb' & NE).
          destruct (ah_disj H HH _ _ _ b (pv, P, k) RH INb' INv NE) as [D|D]; cbn in D.
          -- pose proof (ah_blocks H HH _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
             assert (sh (blk_addr b) + nsh (blk_size b) <= sh P) by (unfold sh, nsh; Z.div_mod_to_equations; nia). lia.
          -- pose proof (ah_blocks H HH _ _ _ _ RH INb') as (C0 & C16 & Cn & CI & CC & CF & CAPP).
             assert (sh P + nsh k <= sh (blk_addr b)) by (unfold sh, nsh; Z.div_mod_to_equations; nia). lia.
        * pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE P k F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D. lia.
        * destruct BF as [BF|BF].
          -- assert (sh P + nsh k <= sh (as_FSB H)) by (unfold sh, nsh; Z.div_mod_to_equations; nia). lia.
          -- assert (sh (as_FSB H + AFS_SIZE) <= sh P) by (apply sh_mono; lia). lia.
        * lia.
  Qed.

  Lemma wmc0 : forall (e : went H) ff fp XSc sk LBk m (Q : machine_state -> Prop)
      (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pv : bptr) (b k : Z) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc sk LBk m -> In (pv, b, k) LBk -> (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> pv) ->
    (forall m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       winv H e ff fp XSc sk LBk m' -> munch [(b, b + 0); (wS1 e - AINTRIN_STACK, wS1 e)] m m' -> wmono asegs m m' ->
       evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 (Z_to_bv 64 b) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AASAN_MEMCPY) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XSc sk LBk m Q ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pv b k F fc HP HI INv LBI K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (ah_blocks H HH _ _ _ _ (winv_rh H _ _ _ _ _ _ _ HI) INv) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn in B0, B16, Bn, BI, BC, BF, BAPP. pose proof aceil_facts as ACF.
    assert (CB0 : rw_cells asegs m b [CB 0 []]).
    { split; [split; [cbn; tauto | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]] | split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]]. }
    eapply evt_cut.
    { eapply (ah_memcpy H HH ra (Z_to_bv 64 (wS1 e))) with (src := []) (junk := []) (lo := w_lo e); rewrite ?HLib.u64_of_Z by lia.
      - split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]].
      - reflexivity.
      - exact CB0.
      - lia.
      - apply accessible_nil; unfold AAPP_HI; lia.
      - apply accessible_nil; unfold AAPP_HI; lia.
      - exact (wshvis_nil m).
      - pose proof (ah_blk_shvis H HH _ _ _ _ _ _ (winv_rh H _ _ _ _ _ _ _ HI) INv) as X. eapply shvis_sub; [exact X | lia | lia | lia | lia | lia].
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - lia.
      - left. unfold ASHADOW_BASE. lia.
      - unfold in_app_mem; unfold aapp, aapp_lo, aapp_hi in BAPP; destruct BAPP as [[X Y]|[X Y]]; [left|right]; unfold ALOWSH_LO, ASHADOW_BASE, AHI_LO, AAPP_HI, AIMG_TOP in *; lia.
      - eapply (aconst_ok_app b k); [exact BAPP | lia | lia].
      - left; lia.
      - left; lia. }
    intros ms' P. destruct P as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & CB' & BA' & AC').
    subst ms'.
    assert (Ed : bv_unsigned (Z_to_bv 64 b) = b) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    assert (En : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Es : bv_unsigned (Z_to_bv 64 (wS1 e)) = wS1 e) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    rewrite Es in ST'.
    assert (MU' : munch [(b, b + 0); (wS1 e - AINTRIN_STACK, wS1 e)] m m') by (eapply munch_eqW; [exact MU | rewrite Ed, En, Es; reflexivity]).
    clear MU. rename MU' into MU.
    apply K; [| exact MU | exact WM].
    eapply (winv_bw e ff fp XSc sk LBk m m' _ pv b k HP HI INv LBI MU WM MI').
    - destruct (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia)) as [_ STu].
      exact (stk_merge asegs m' (w_lo e) (wS1 e) (wSP e) ST' (stk_wmono m m' (wS1 e) (wSP e) STu WM ltac:(lia)) ltac:(lia)).
    - unfold wbw, wwin, WO_SAVED, AINTRIN_STACK. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + left. lia.
      + right; right; left. lia.
  Qed.

  Lemma wann : forall (e : went H) ff fp XSc sk LBk m (Q : machine_state -> Prop)
      (ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (pv : bptr) (b len : Z) (F : bvmap 5 word) (fc : bv 32),
    asan_rt_hyps_bp H ->
    wpre H e -> winv H e ff fp XSc sk LBk m -> In (pv, b, len) LBk -> (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> pv) ->
    SHAD m b (shadow_of len) -> len <= 2 ^ 40 ->
    (forall m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       winv H e ff fp XSc sk LBk m' -> munch [(sh b, sh b + nsh len); (wS1 e - AINTRIN_STACK, wS1 e)] m m' -> wmono asegs m m' ->
       SHAD m' b (cc_gen len 0) ->
       evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 (b + len))
                       (Z_to_bv 64 (b + len)) (Z_to_bv 64 b) a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AANNOTATE_CC) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XSc sk LBk m Q ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 pv b len F fc HHb HP HI INv LBI SB LEN K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (ah_blocks H HH _ _ _ _ (winv_rh H _ _ _ _ _ _ _ HI) INv) as (B0 & B16 & Bn & BI & BC & BF & BAPP).
    cbn in B0, B16, Bn, BI, BC, BF, BAPP. pose proof aceil_facts as ACF.
    eapply evt_cut.
    { eapply (rt_bp_annot H HHb ra (Z_to_bv 64 (wS1 e))) with (beg := b) (len := len) (oldmid := len) (newmid := 0) (lo := w_lo e);
        rewrite ?HLib.u64_of_Z by lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - f_equal; lia.
      - clear - B16. Z.div_mod_to_equations. lia.
      - lia.
      - lia.
      - lia.
      - exact BAPP.
      - unfold AAPP_HI; lia.
      - rewrite cc_gen_full. exact SB.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK; lia.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - unfold in_app_mem; unfold aapp, aapp_lo, aapp_hi in BAPP; destruct BAPP as [[X Y]|[X Y]]; [left|right]; unfold ALOWSH_LO, ASHADOW_BASE, AHI_LO, AAPP_HI, AIMG_TOP in *; lia. }
    intros ms' P. destruct P as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & SB' & AC').
    subst ms'.
    assert (Es : bv_unsigned (Z_to_bv 64 (wS1 e)) = wS1 e) by (rewrite HLib.u64_of_Z by lia; reflexivity).
    rewrite Es in ST', MU.
    apply K; [| exact MU | exact WM | exact SB'].
    eapply (winv_bw e ff fp XSc sk LBk m m' _ pv b len HP HI INv LBI MU WM MI').
    - destruct (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia)) as [_ STu].
      exact (stk_merge asegs m' (w_lo e) (wS1 e) (wSP e) ST' (stk_wmono m m' (wS1 e) (wSP e) STu WM ltac:(lia)) ltac:(lia)).
    - unfold wbw, wwin, WO_SAVED, AINTRIN_STACK. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + right; left. lia.
      + right; right; left. lia.
  Qed.

  Lemma won : forall (e : went H) ff fp XSc s LB m msF mo (Q : config -> Prop)
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (n : Z) (F : bvmap 5 word) (fc : bv 32),
    asan_rt_hyps_bp H ->
    wpre H e -> winv H e ff fp XSc s LB m -> (forall b, In b (w_LB e) -> In b LB) ->
    as_VIS H s msF = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AOPNEW) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    1 <= n <= 64512 ->
    lb_small LB + n <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
    (forall msF' mo' s' (A : Z) (p : bptr) m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk,
       as_VIS H s' msF' = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' s0 s1 (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7'
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp XSc s' ((p, A, n) :: LB) m' -> apres H LB (wS1 e) m m' ->
       ablock_range H A n -> ~ In p (map blk_id LB) ->
       rw_cells asegs m' A [CB (Z.to_nat n) junk] -> addressable m' A n ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB m msF mo Q ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 n F fc HHb
      HP HI INC VIS KR AL0 Hn LS LC LL K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (rt_bp_cost H HHb) as (CF0 & CM0).
    assert (CM : as_Cm H n = 0) by (rewrite CM0; apply ICM_small; lia).
    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH ra (Z_to_bv 64 (wS1 e))) with (s := s) (LB := LB) (n := n) (lo := w_lo e) (B := w_B e) (errv := errv);
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - exact RH.
      - exact KR.
      - apply (rt_bp_live H HHb s LB m n RH); [lia | unfold nsmall; destruct (Z.leb_spec n 64512); lia | exact LC
                                              | unfold nlg; destruct (Z.ltb_spec 64512 n); lia].
      - rewrite CM. exact AL0.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold AOPNEW_STACK, AMALLOC_STACK; lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - clear - S32. Z.div_mod_to_equations. lia.
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - reflexivity.
      - lia. }
    intros [msF' mo'] POST.
    destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & A & junk & p & s'
                      & VIS' & KR' & MP' & MI' & ST' & ER' & RA' & AP & ABR & RH' & CB & AD & AC' & AL').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    rewrite HLib.u64_of_Z in ST', AP by lia.
    assert (NI : ~ In p (map blk_id LB)).
    { pose proof (ah_nodup H HH _ _ _ RH') as ND. cbn [map] in ND. apply NoDup_cons_iff in ND as [ND _]. exact ND. }
    eapply K; [exact VIS' | exact KR' | exact MP' | | exact AP | exact ABR | exact NI | exact CB | exact AD | rewrite CM in AL'; lia].
    rewrite <- (app_nil_r XSc).
    eapply (winv_sr H HH e ff fp XSc [] [] s LB LB s' ((p, A, n) :: LB) m m' HP HI INC (xpres_of_apres H LB (wS1 e) [] m m' AP)
              (Forall_nil _) (Forall_nil _)).
    - exact (RFS_via_apres H HH _ _ _ m m' (winv_rf H _ _ _ _ _ _ _ HI) AP).
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_nil.
  Qed.
End Call.
