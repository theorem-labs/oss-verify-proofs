(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BecLazy.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_DStat LbB_DiagStmt LbB_SR LbB_WoGen LbB_ExDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_Kit LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section XKit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma xframe_facts : forall LF ff fp, fresh_frame H LF 3 ff fp ->
       0x6e8000 + 0x9000 <= ff /\ ff + 512 <= aceil /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= ff /\ ff + 512 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ sh ff + 64 = sh (ff + 512) /\ sh (as_FSB H) <= sh ff /\ sh (ff + 512) <= sh (as_FSB H + AFS_SIZE)
    /\ 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000
    /\ (sh ff + 64 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh ff).
  Proof.
    intros LF ff fp FF. pose proof (fresh_frame_facts H LF 3 ff fp FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    change (fsz 3) with 512 in *. unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *.
    pose proof aceil_facts as ACF.
    assert (S1 : sh ff + 64 = sh (ff + 512)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (S2 : sh (as_FSB H) <= sh ff) by (apply sh_mono; lia).
    assert (S3 : sh (ff + 512) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    assert (S4 : 0x7fff8000 <= sh ff /\ sh ff + 64 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; unfold AFS_SIZE in *; Z.div_mod_to_equations; lia).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 512 P9 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S5.
    change (nsh 512) with 64 in S5.
    repeat split; try assumption; try lia.
  Qed.

  Lemma xpre_all : forall e, xpre H e ->
       as_RHEAP H (x_s e) (x_LB e) (x_m e)
    /\ (xSP e mod 16 = 0 /\ stk asegs (x_m e) (x_lo e) (xSP e) /\ aceil <= x_lo e /\ x_lo e <= xSP e - AEX_STACK)
    /\ x_tp e = Z_to_bv 64 ATP
    /\ (LINV_P5 (x_m e) /\ ACONST (x_m e) /\ mem_inv asegs (x_m e))
    /\ (as_RFS H (x_LF e) (x_m e) /\ (length (x_LF e) + EX_FRAMES <= AFS_MAXLIVE_BP)%nat)
    /\ (stack0 (x_m e) (x_lo e) (x_shi e) /\ xSP e <= x_shi e)
    /\ (as_chain H (x_m e) (bv_unsigned (x_s0 e)) (x_CH e) /\ pf_ok (as_TR H) DS_EXH_PF (bv_unsigned (x_ra e)) (x_CH e)
        /\ (forall fp' ra', In (fp', ra') (x_CH e) -> xSP e + 16 <= fp')).
  Proof.
    intros e HP.
    destruct HP as (_ & RH & _ & _ & _ & _ & _ & _ & SP16 & ST & CE & LO & _ & MI & TP & _ & LV & AC & RF & LFn & S0 & SHI
                    & CHN & PF & CHU & _).
    exact (conj RH (conj (conj SP16 (conj ST (conj CE LO))) (conj TP (conj (conj LV (conj AC MI)) (conj (conj RF LFn) (conj (conj S0 SHI) (conj CHN (conj PF CHU)))))))).
  Qed.
  Lemma xpre_geo : forall e, xpre H e ->
    aceil <= x_lo e /\ x_lo e + 17408 <= xSP e /\ xSP e <= x_shi e /\ x_shi e <= AAPP_HI /\ xSP e mod 16 = 0
    /\ x_tp e = Z_to_bv 64 ATP.
  Proof.
    intros e HP.
    destruct (xpre_all e HP) as (_ & (SP16 & _ & CE & LO) & TP & _ & _ & (S0 & SHI) & _).
    pose proof (stack0_bounds _ _ _ S0). unfold AEX_STACK, ADS_STACK in LO. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact SP16 | exact TP].
  Qed.
  Lemma xpre_RH0 : forall e, xpre H e -> as_RHEAP H (x_s e) (x_LB e) (x_m e).
  Proof. intros e HP. exact (proj1 (xpre_all e HP)). Qed.
  Lemma xerrno_ATP : forall (e : xent H), x_tp e = Z_to_bv 64 ATP -> errno_addr (x_tp e) = ATP - 164.
  Proof. intros e TP. rewrite TP, HLib.u64_of_Z by (unfold ATP; lia). lia. Qed.

  Lemma xS1_facts : forall (e : xent H), xpre H e ->
    xS1 e mod 32 = 0 /\ xS1 e + 128 <= xSP e <= xS1 e + 144 /\ 2 ^ 45 <= xS1 e /\ xSP e <= 2 ^ 47
    /\ x_lo e + 17232 <= xS1 e /\ aceil <= x_lo e.
  Proof.
    intros e HP. pose proof (xpre_geo e HP) as (CE & LO & SH1 & SH2 & SP16 & _).
    pose proof aceil_facts as ACF. unfold xS1, EX_FRAME. unfold AAPP_HI in SH2.
    set (SP := xSP e) in *. clearbody SP.
    assert (R : SP mod 32 = 0 \/ SP mod 32 = 16) by (clear - SP16; Z.div_mod_to_equations; lia).
    assert (R2 : (SP - 128 - SP mod 32) mod 32 = 0) by (clear - R; Z.div_mod_to_equations; lia).
    split; [exact R2|]. destruct R as [R|R]; rewrite R; lia.
  Qed.

  Definition xwin (e : xent H) (ff : Z) (iv : Z * Z) : Prop :=
    (x_lo e <= fst iv /\ snd iv <= xSP e - EX_SAVED) \/ (ff <= fst iv /\ snd iv <= ff + EX_FLAGP)
    \/ (sh ff <= fst iv /\ snd iv <= sh ff + 64).

  Lemma xwin_ok : forall e ff fp XSc iv, fresh_frame H (x_LF e) 3 ff fp ->
    aceil <= x_lo e -> x_lo e <= xSP e - EX_SAVED -> xSP e <= AAPP_HI -> xwin e ff iv ->
       afs_write_ok H ((3, ff, fp) :: x_LF e) iv /\ (forall LBk, aclient_write_ok H LBk iv) /\ aconst_ok iv /\ stack0_ok iv
    /\ ((aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XE H ff fp ++ XSc) a))
    /\ (snd iv <= xSP e - EX_SAVED \/ xSP e <= fst iv)
    /\ (snd iv <= ff + EX_FLAGP \/ ff + 512 <= fst iv)
    /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv).
  Proof.
    intros e ff fp XSc iv FF CE LO SPH HW.
    pose proof (xframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    destruct iv as [a b]. unfold xwin, EX_SAVED, EX_FLAGP in *. cbn [fst snd] in *.
    set (SP := xSP e) in *. set (lo := x_lo e) in *. clearbody SP lo.
    unfold afs_write_ok, aclient_write_ok; cbn [fst snd].
    destruct HW as [(W1 & W2)|[(W1 & W2)|(W1 & W2)]].
    -
      split; [left; split; [right; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      split; [intros LBk; left; cbn; lia|].
      split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]|].
      split; [apply stack0_ok_app; unfold AHI_LO; lia|].
      split; [left; lia|]. split; [left; lia|]. split; [right; lia|]. right; unfold ATP; lia.
    -
      split; [right; exists (3, ff, fp); split; [left; reflexivity | cbn; change (fsz 3) with 512; lia]|].
      split; [intros LBk; right; right; right; right; left; cbn; lia|].
      split; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia]|].
      split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia]|].
      split; [right; intros x Hx; apply rin_ivs_app; left; cbn; right; right; left; change (fsz 3) with 512; lia|].
      split; [left; lia|]. split; [left; lia|]. right; unfold ATP; lia.
    -
      split; [left; split; [destruct F16; [left | right]; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      split; [intros LBk; right; right; right; right; right; left; cbn; lia|].
      split; [apply aconst_ok_high; [assert (sh AIMG_TOP <= sh ff) by (apply sh_mono; unfold AIMG_TOP; lia); lia | right; left; lia]|].
      split; [right; cbn; assert (sh (ff + 512) <= sh aceil) by (apply sh_mono; lia); lia|].
      split; [right; intros x Hx; apply rin_ivs_app; left; cbn; right; right; right; left; change (fshn 3) with 64; lia|].
      split; [left; lia|]. split; [destruct F16; [left | right]; lia|]. right; unfold ATP; lia.
  Qed.

  Lemma xwin_all : forall e ff fp XSc W, fresh_frame H (x_LF e) 3 ff fp ->
    aceil <= x_lo e -> x_lo e <= xSP e - EX_SAVED -> xSP e <= AAPP_HI -> Forall (xwin e ff) W ->
       Forall (afs_write_ok H ((3, ff, fp) :: x_LF e)) W /\ (forall LBk, Forall (aclient_write_ok H LBk) W) /\ Forall aconst_ok W
    /\ Forall stack0_ok W
    /\ Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XE H ff fp ++ XSc) a)) W
    /\ disjoint_from W (xSP e - EX_SAVED) EX_SAVED /\ disjoint_from W (ff + EX_FLAGP) 8 /\ disjoint_from W (ATP - 164) 4.
  Proof.
    intros e ff fp XSc W FF CE LO SPH FW. induction W as [|iv W IH].
    - split; [apply Forall_nil|]. split; [intros; apply Forall_nil|]. do 3 (split; [apply Forall_nil|]). cbn. tauto.
    - apply Forall_cons_iff in FW as [F0 FW]. destruct (IH FW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      destruct (xwin_ok e ff fp XSc iv FF CE LO SPH F0) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
      split; [apply Forall_cons; assumption|]. split; [intros LBk; apply Forall_cons; [apply B2 | apply A2]|].
      split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|].
      destruct iv as [x y]. unfold EX_SAVED, EX_FLAGP in *. cbn [fst snd] in *. cbn [disjoint_from].
      split; [split; [lia | exact A6]|]. split; [split; [lia | exact A7]|]. split; [lia | exact A8].
  Qed.

  Lemma xinv_munch : forall e ff fp XSc sk LBk m1 m2 W,
    xpre H e -> xinv H e ff fp XSc sk LBk m1 ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 (x_lo e) (xSP e) ->
    Forall (xwin e ff) W -> xinv H e ff fp XSc sk LBk m2.
  Proof.
    intros e ff fp XSc sk LBk m1 m2 W HP HI MU WM MI2 ST2 FW.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof (xpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    assert (LO : x_lo e <= xSP e - EX_SAVED) by (unfold EX_SAVED in *; lia).
    assert (SPH : xSP e <= AAPP_HI) by lia. clear LO' SH1 SH2.
    unfold xinv. rewrite (xerrno_ATP e TP) in ER |- *.
    destruct (xwin_all e ff fp XSc W FF CE LO SPH FW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (xpre_RH0 e HP) as RH0.
    split; [eapply (ah_RFS_frame H HH); [exact RF | exact MU | exact WM | exact A1]|].
    split; [exact FF|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact (A2 LBk)]|].
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM | exact A3]|].
    split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact A4]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU | exact WM | exact (A2 LBk)]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | exact A8]|].
    split; [exact ST2|].
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | exact A6]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | exact A7]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [exact (wr_at_wmono _ _ _ _ WFP WM)|].
    split; [| split; [exact FS|]].
    - eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) _ W (x_m e)); [exact HH | exact RH0 | exact MU | exact WM |].
        eapply Forall_impl; [| exact A5]. intros iv [K|K]; [left; exact K | right; intros a Ha; right; exact (K a Ha)].
    -
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv HW.
      pose proof (xframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      pose proof aceil_facts as ACF. unfold xwin in HW. unfold AIMG_TOP. destruct HW as [(W1 & _)|[(W1 & _)|(W1 & _)]]; lia.
  Qed.

  Lemma xfsw_ok : forall (e : xent H) ff fp m iv,
    as_RFS H ((3, ff, fp) :: x_LF e) m -> fresh_frame H (x_LF e) 3 ff fp -> aceil <= x_lo e ->
    fs_scratch H ((3, ff, fp) :: x_LF e) iv ->
       (forall LBk, aclient_write_ok H LBk iv) /\ aconst_ok iv /\ stack0_ok iv
    /\ (snd iv <= ff + EX_FLAGP \/ ff + 512 <= fst iv) /\ (snd iv <= ff \/ ff + 512 <= fst iv)
    /\ (snd iv <= sh ff \/ sh ff + 64 <= fst iv)
    /\ snd iv <= x_lo e /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
    /\ (snd iv <= fp \/ fp + 1 <= fst iv).
  Proof.
    intros e ff fp m iv RF FF CE FS.
    pose proof (xframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF. unfold EX_FLAGP.
    assert (OB : fsobj H ((3, ff, fp) :: x_LF e) ff 512) by (eapply (fsobj_inframe H); [left; reflexivity | cbn; lia | cbn; change (fsz 3) with 512; lia]).
    pose proof (fsobj_scratch H HH _ ff 512 m iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)
                  (aapp_sub _ _ ff 512 F10 ltac:(lia) ltac:(lia)) FS) as D1.
    pose proof (fsobj_scratch_sh H HH _ ff 512 m iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) FS) as D2.
    change (nsh 512) with 64 in D2.

    assert (WH : (as_FSB H <= fst iv /\ snd iv <= as_FSB H + AFS_SIZE) \/ (sh (as_FSB H) <= fst iv /\ snd iv <= sh (as_FSB H + AFS_SIZE))).
    { destruct FS as [->|(k & ff' & fp' & FF' & E)]; [left; cbn; unfold AFS_FLAGS, AFS_SIZE; lia|].
      pose proof (fresh_frame_facts H _ _ _ _ FF') as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)).
      unfold AFS_HDR, AFS_FLAGS in *. destruct E as [E|[E|E]]; rewrite E; cbn [fst snd]; [left; lia | left; unfold AFS_SIZE in *; lia | right].
      assert (sh (as_FSB H) <= sh ff') by (apply sh_mono; lia).
      assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
      assert (sh (ff' + fsz k) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia). lia. }
    assert (SHF : sh (as_FSB H + AFS_SIZE) <= sh aceil) by (apply sh_mono; lia).
    assert (SHA : 0x7fff8000 <= sh (as_FSB H)) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    split; [intros LBk; unfold aclient_write_ok; destruct WH as [W|W]; [right; right; right; right; left | right; right; right; right; right; left]; exact W|].
    split.
    { destruct iv as [x y]. cbn [fst snd] in *. destruct WH as [W|W].
      - eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | lia | lia].
      - apply aconst_ok_high; [| right; left; unfold AFS_SIZE in *; lia].
        replace (sh AIMG_TOP) with 0x800d5000 by reflexivity. assert (sh 0x6e8000 <= sh (as_FSB H)) by (apply sh_mono; lia).
        replace (sh 0x6e8000) with 0x800d5000 in * by reflexivity. lia. }
    split.
    { destruct iv as [x y]. cbn [fst snd] in *. destruct WH as [W|W]; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia] | right; cbn; lia]. }
    split; [destruct D1; [right | left]; lia|]. split; [destruct D1; [right | left]; lia|].
    split; [destruct D2; [right | left]; lia|].
    split; [destruct WH; unfold AFS_SIZE in *; lia|]. split; [right; unfold ATP; destruct WH; unfold AFS_SIZE in *; lia|].

    destruct FS as [->|(k & ff' & fp' & FF' & E)]; [left; cbn; unfold AFS_FLAGS; lia|].
    pose proof (fresh_frame_facts H _ _ _ _ FF') as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    destruct FF' as (_ & _ & FFL).
    destruct (FFL (3, ff, fp) (or_introl eq_refl)) as (_ & NEf). cbn in NEf.
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (as_FSB H) AFS_SIZE F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(unfold AFS_SIZE; lia)) as DS.
    assert (sh (as_FSB H + AFS_SIZE) <= sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
    unfold AFS_HDR, AFS_FLAGS in *.
    destruct E as [E|[E|E]]; rewrite E; cbn [fst snd]; [right; lia | lia |].
    assert (sh (as_FSB H) <= sh ff') by (apply sh_mono; lia).
    assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
    assert (sh (ff' + fsz k) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    destruct DS; [left | right]; lia.
  Qed.

  Definition xcwin (e : xent H) (ff : Z) (XSn : list (Z * Z)) (iv : Z * Z) : Prop :=
    (x_lo e <= fst iv /\ snd iv <= xS1 e) \/ (ff <= fst iv /\ snd iv <= ff + EX_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 64)
    \/ In iv XSn.

  Lemma xinv_callee : forall e ff fp XSc XSn sk LBk sk' LBk' m1 m2 W,
    xpre H e -> xinv H e ff fp XSc sk LBk m1 ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 (x_lo e) (xS1 e) ->
    as_RFS H ((3, ff, fp) :: x_LF e) m2 -> ACONST m2 -> as_RHEAP H sk' LBk' m2 ->
    Forall (fs_scratch H ((3, ff, fp) :: x_LF e)) XSn -> Forall (xcwin e ff XSn) W ->
    xinv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn sk LBk sk' LBk' m1 m2 W HP HI MU WM MI2 ST2 RF2 AC2 RH2 FSn FW.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof (xpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    pose proof (xS1_facts e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof (xpre_RH0 e HP) as RH0.
    assert (LO : x_lo e <= xSP e - EX_SAVED) by (unfold EX_SAVED in *; lia).
    assert (SPH : xSP e <= AAPP_HI) by lia. clear LO' SH1 SH2.

    assert (WOK : Forall (fun iv => (forall LBk0, aclient_write_ok H LBk0 iv) /\ aconst_ok iv /\ stack0_ok iv
                           /\ ((aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XE H ff fp ++ XSc ++ XSn) a))
                          /\ (snd iv <= xSP e - EX_SAVED \/ xSP e <= fst iv) /\ (snd iv <= ff + EX_FLAGP \/ ff + 512 <= fst iv)
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= xS1 e \/ xSP e <= fst iv)) W).
    { eapply Forall_impl; [| exact FW]. intros iv CW. unfold xcwin in CW.
      destruct CW as [CW|[CW|[CW|CW]]].
      - destruct (xwin_ok e ff fp (XSc ++ XSn) iv FF CE LO SPH ltac:(left; unfold EX_SAVED; lia)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        repeat split; try assumption. left; lia.
      - destruct (xwin_ok e ff fp (XSc ++ XSn) iv FF CE LO SPH ltac:(right; left; exact CW)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        pose proof (xframe_facts _ _ _ FF) as (F1 & F2 & _). pose proof aceil_facts.
        repeat split; try assumption. left; unfold EX_FLAGP in *; lia.
      - destruct (xwin_ok e ff fp (XSc ++ XSn) iv FF CE LO SPH ltac:(right; right; exact CW)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        pose proof (xframe_facts _ _ _ FF) as (_ & F2 & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _ & _ & _ & F15 & _).
        pose proof aceil_facts. assert (sh (ff + 512) <= sh aceil) by (apply sh_mono; lia).
        assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        repeat split; try assumption. left; lia.
      - pose proof (proj1 (Forall_forall _ _) FSn iv CW) as FSi.
        destruct (xfsw_ok e ff fp m2 iv RF2 FF CE FSi) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & _).
        repeat split; try assumption; try (left; unfold EX_SAVED; lia).
        right. intros a Ha. apply rin_ivs_app. right. apply rin_ivs_app. right.
        clear - CW Ha. induction XSn as [|iv' XSn IH]; [destruct CW|]. destruct CW as [->|CW]; [left; exact Ha| right; exact (IH CW)]. }
    assert (A1 : forall LBk0, Forall (aclient_write_ok H LBk0) W) by (intros LBk0; eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (A3 : Forall aconst_ok W) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (A4 : Forall stack0_ok W) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (A5 : Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= xSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XE H ff fp ++ XSc ++ XSn) a)) W)
      by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    assert (DJ : forall A n, (forall iv, In iv W -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from W A n).
    { intros A n K. clear - K. induction W as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    assert (DSV : disjoint_from W (xSP e - EX_SAVED) EX_SAVED)
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & X & _); unfold EX_SAVED in *; lia).
    assert (DSF : disjoint_from W (ff + EX_FLAGP) 8)
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & _ & X & _); unfold EX_FLAGP in *; lia).
    assert (DER : disjoint_from W (ATP - 164) 4)
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & _ & _ & X & _); lia).
    assert (DST : disjoint_from W (xS1 e) (xSP e - xS1 e))
      by (apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X; destruct X as (_ & _ & _ & _ & _ & _ & _ & X); lia).
    unfold xinv. rewrite (xerrno_ATP e TP) in ER |- *.
    split; [exact RF2|]. split; [exact FF|]. split; [exact RH2|]. split; [exact AC2|]. split; [exact MI2|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact A4]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RA | exact MU | exact WM | exact (A1 LBk)]|].
    split; [exists errv; eapply rw_cells_transport; [exact ER | exact MU | exact WM | exact DER]|].
    split.
    { destruct (stk_split asegs m1 (x_lo e) (xS1 e) (xSP e) ST ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 (xS1 e) (xSP e)) by (eapply stk_transport_disjoint; [exact STu | exact MU | exact WM | exact DST]).
      exact (stk_merge asegs m2 (x_lo e) (xS1 e) (xSP e) ST2 STu2 ltac:(lia)). }
    split; [eapply rw_cells_transport; [exact SV | exact MU | exact WM | exact DSV]|].
    split; [eapply rw_cells_transport; [exact SF | exact MU | exact WM | exact DSF]|].
    split; [exact (wr_at_wmono _ _ _ _ WF WM)|].
    split; [exact (wr_at_wmono _ _ _ _ WFP WM)|].
    split; [| split].
    - eapply xpres_trans.
      + eapply xpres_weaken; [exact XP | lia | intros b Hb; exact Hb |]. intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
        apply rin_ivs_app in Ha as [Ha|Ha].
        * apply rin_ivs_app. left. exact Ha.
        * apply rin_ivs_app. right. apply rin_ivs_app. left. exact Ha.
      + eapply (xpres_of_munch H (x_s e) (x_LB e) (xSP e) _ W (x_m e)); [exact HH | exact RH0 | exact MU | exact WM |].
        eapply Forall_impl; [| exact A5]. intros iv [K|K]; [left; exact K | right; intros a Ha; right; exact (K a Ha)].
    - apply Forall_app. split; [exact FS|]. eapply Forall_impl; [| exact FSn]. intros iv X. exact (fs_scratch_mono H _ _ _ X).
    -
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv HW.
      pose proof (xframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      pose proof aceil_facts as ACF. unfold xcwin in HW. destruct HW as [(W1 & _)|[(W1 & _)|[(W1 & _)|HW]]]; [unfold AIMG_TOP; lia | unfold AIMG_TOP; lia | unfold AIMG_TOP; lia |].
      exact (LbB_TdKit.fs_scratch_above H HH _ m2 iv RF2 (proj1 (Forall_forall _ _) FSn iv HW)).
  Qed.

  Lemma xkeep : forall e ff fp XSc sk LBk m' a,
    xpre H e -> xinv H e ff fp XSc sk LBk m' -> 0 <= a < 2 ^ 64 ->
    ((exists p A n, In (p, A, n) (x_LB e) /\ ((A <= a < A + n) \/ (sh A <= a < sh A + nsh n))) \/ (aimg_client a /\ ~ (RtB_Td.ATDLOC <= a < RtB_Td.ATDLOC + 8)) \/ xSP e <= a) ->
    m' (wa a) = x_m e (wa a) /\ (wview asegs (x_m e) (wa a) <> None -> wview asegs m' (wa a) <> None).
  Proof.
    intros e ff fp XSc sk LBk m' a HP HI Ha K.
    destruct HI as (_ & FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FS & _).
    pose proof (xpre_RH0 e HP) as RH0.
    pose proof (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (xpre_all e HP))))))) as RF0.
    pose proof (xpre_geo e HP) as (CE & LO & SH1 & SH2 & _ & _).
    pose proof aceil_facts as ACF.
    assert (FSA : Forall (fs_scratch H (x_LF e)) (XE H ff fp ++ XSc))
      by (apply Forall_app; split; [exact (fs_scratch_of_fresh H (x_LF e) 3 ff fp FF) | exact FS]).
    apply XP; [exact Ha|]. split.
    - unfold aclient_addr. destruct K as [(p & A & n & IN & [K|K])|[K|K]].
      + right; right; left. exists (p, A, n). split; [exact IN| cbn; lia].
      + right; right; right; left. exists (p, A, n). split; [exact IN| cbn; lia].
      + right; left. exact (proj1 K).
      + left. exact K.
    - apply rin_ivs_none. apply Forall_cons.
      { cbn [fst snd]. destruct K as [(p & A & n & IN & [K|K])|[[K1 K2]|K]].
        - pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *. right. unfold RtB_Td.ATDLOC, AIMG_TOP in *. lia.
        - right. unfold sh in K. rewrite ASHADOW_BASE_val in K. pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
          unfold RtB_Td.ATDLOC. Z.div_mod_to_equations. lia.
        - lia.
        - right. unfold RtB_Td.ATDLOC. lia. }
      eapply Forall_impl; [| exact FSA]. intros iv FSi.
      destruct K as [(p & A & n & IN & [K|K])|[[K KTD]|K]].
      + pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
        pose proof (fsobj_scratch H HH (x_LF e) A n (x_m e) iv RF0 (fsobj_block H HH _ _ _ _ p A n RH0 IN) ltac:(lia) Bn
                      ltac:(unfold AAPP_HI; lia) BAPP FSi). lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
        pose proof (fsobj_scratch_sh H HH (x_LF e) A n (x_m e) iv RF0 (fsobj_block H HH _ _ _ _ p A n RH0 IN) ltac:(lia) Bn
                      ltac:(unfold AAPP_HI; lia) FSi). lia.
      + destruct FSi as [->|(k & ff' & fp' & FF' & E)].
        * pose proof (proj1 (ah_RFS_range H HH _ _ RF0)) as (Q1 & _). unfold aimg_client, AIMG_TOP in *. cbn. lia.
        * pose proof (fresh_frame_facts H _ _ _ _ FF') as (K0 & R1 & R2 & _ & _ & P1 & _).
          assert (sh AIMG_TOP <= sh ff') by (apply sh_mono; unfold AIMG_TOP, AFS_HDR in *; lia).
          replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity.
          unfold aimg_client, AIMG_TOP, AFS_HDR, AFS_FLAGS in *. destruct E as [->|[->| ->]]; cbn; lia.
      + destruct FSi as [->|(k & ff' & fp' & FF' & E)].
        * pose proof (proj1 (ah_RFS_range H HH _ _ RF0)) as (_ & Q2 & _). unfold AFS_FLAGS, AFS_SIZE in *. cbn. lia.
        * pose proof (fresh_frame_facts H _ _ _ _ FF') as (K0 & R1 & R2 & _ & _ & P1 & P2 & _).
          pose proof (fsz_pos k ltac:(lia)).
          assert (sh (ff' + fsz k) <= sh aceil) by (apply sh_mono; lia).
          assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
          assert (sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
          destruct E as [->|[->| ->]]; cbn; lia.
  Qed.

  Lemma xlinv : forall e ff fp XSc sk LBk m', xpre H e -> xinv H e ff fp XSc sk LBk m' -> LINV_P5 m'.
  Proof using HH.
    intros e ff fp XSc sk LBk m' HP HI.
    apply HI.
  Qed.

  Lemma xchain : forall e ff fp XSc sk LBk m', xpre H e -> xinv H e ff fp XSc sk LBk m' ->
    as_chain H m' (bv_unsigned (x_s0 e)) (x_CH e).
  Proof.
    intros e ff fp XSc sk LBk m' HP HI.
    destruct (xpre_all e HP) as (_ & _ & _ & _ & _ & _ & (CHN & _ & CHU)).
    eapply (ah_chain_ext H HH); [exact CHN|]. intros f r a IN Ha.
    pose proof (ah_chain_range H HH _ _ _ f r CHN IN) as (R1 & R2 & R3). pose proof (CHU f r IN). pose proof aceil_facts.
    assert (X1 : 0 <= a < 2 ^ 64) by lia. assert (X2 : xSP e <= a) by lia.
    exact (proj1 (xkeep e ff fp XSc sk LBk m' a HP HI X1 (or_intror (or_intror X2)))).
  Qed.

  Section Proj.
    Variables (e : xent H) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem).
    Hypothesis HI : xinv H e ff fp XSc sk LBk m.

  End Proj.

  Lemma aclient_low : forall s LB m0 SP a, as_RHEAP H s LB m0 -> aclient_addr H LB SP a -> SP <= a \/ a < aceil.
  Proof.
    intros s LB m0 SP a RH Hc.
    unfold aclient_addr in Hc. destruct Hc as [Hc|Hc]; [left; exact Hc| right].
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3).
    destruct Hc as [Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]].
    - acb; unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATSD0, ATP in *. lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & _ & _ & R & _). lia.
    - pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (_ & _ & R0 & R1 & R & _).
      pose proof (sh_below_aceil (blk_addr b + blk_size b + 8) ltac:(acb; unfold AIMG_TOP, AAPP_HI in *; lia)).
      unfold nsh, sh in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia.
    - lia.
    - pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) ltac:(acb; unfold AIMG_TOP, AAPP_HI, AFS_SIZE in *; lia)).
      acb; unfold AFS_SIZE in *. lia.
    - acb; unfold AHI_LO in *. lia.
  Qed.

  Lemma rin_ivs_dec : forall X a, {rin_ivs X a} + {~ rin_ivs X a}.
  Proof.
    induction X as [|[l h] X IH]; intros a; cbn [rin_ivs fst snd]; [right; tauto|].
    destruct (Z_le_dec l a) as [A1|A1]; [destruct (Z_lt_dec a h) as [A2|A2]|].
    - left. left. lia.
    - destruct (IH a) as [K|K]; [left; right; exact K | right; intros [K'|K']; [lia | exact (K K')]].
    - destruct (IH a) as [K|K]; [left; right; exact K | right; intros [K'|K']; [lia | exact (K K')]].
  Qed.

  Lemma xpres_stk_mix : forall LB SP X m m' lo hi,
    xpres H LB SP X m m' -> stk asegs m lo hi -> SP <= lo ->
    (forall a, lo <= a < hi -> rin_ivs X a -> wview asegs m' (wa a) <> None /\ exists b, mrd asegs m' (wa a) = Some b) ->
    stk asegs m' lo hi.
  Proof.
    intros LB SP X m m' lo hi HP ST HS HX. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (rin_ivs_dec X i) as [K|K]; [exact (HX i Hi K)|].
    assert (XC : xclient H LB SP X i) by (split; [left; lia | exact K]).
    destruct (HP i ltac:(lia) XC) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Lemma xpres_wr_at_mix : forall LB SP X m m' A n,
    xpres H LB SP X m m' -> wr_at asegs m A n -> xclient_range H LB SP [] A n ->
    (forall a, A <= a < A + n -> rin_ivs X a -> wview asegs m' (wa a) <> None) ->
    wr_at asegs m' A n.
  Proof.
    intros LB SP X m m' A n HP (H0 & H1 & HW) [HR _] HX. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (rin_ivs_dec X (A + i)) as [K|K]; [exact (HX (A + i) ltac:(lia) K)|].
    assert (XC : xclient H LB SP X (A + i)) by (split; [eapply aclient_range_addr; [exact HR | lia] | exact K]).
    destruct (HP (A + i) ltac:(lia) XC) as [_ W]. apply W. apply HW. exact Hi.
  Qed.

  Lemma rd_of_wr_hi : forall m a, 0x6e8000 <= a < 2 ^ 64 -> wview asegs m (wa a) <> None -> exists b, mrd asegs m (wa a) = Some b.
  Proof.
    intros m a Ha W. unfold wview in W. unfold wa in W |- *. rewrite HLib.u64_of_Z in W by lia.
    unfold mrd. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
    rewrite BecLazy.asegs_find_segment_none_high in W by lia. congruence.
  Qed.

  Lemma xinv_sr_gen : forall e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2,
    xpre H e -> xinv H e ff fp XSc sk LBk m1 ->
    (forall b, In b (x_LB e) -> In b LBx) ->
    xpres H LBx (xS1 e) Xc m1 m2 ->
    Forall (fs_scratch H ((3, ff, fp) :: x_LF e)) XSn ->
    Forall (fun iv : Z * Z => In iv XSn \/ (ff + 8 <= fst iv /\ snd iv <= ff + EX_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 64)
                              \/ (xS1 e <= fst iv /\ snd iv <= xSP e - EX_SAVED) \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) Xc ->
    as_RFS H ((3, ff, fp) :: x_LF e) m2 -> as_RHEAP H sk' LBk' m2 -> ACONST m2 -> mem_inv asegs m2 ->
    stk asegs m2 (x_lo e) (xS1 e) -> (exists errv', rw_cells asegs m2 (errno_addr (x_tp e)) [C4 errv']) -> as_rauxv_ok H m2 (x_B e) ->

    Forall (fun iv : Z * Z => xS1 e <= fst iv \/ (ff <= fst iv /\ snd iv <= ff + EX_FLAGP) -> wr_at asegs m2 (fst iv) (snd iv - fst iv)) Xc ->
    LINV_P5 m2 ->
    xinv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2 HP HI INC XP FSn FXc RF2 RH2 AC2 MI2 ST2 ER2 RA2 RWX LV2.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & _ & ST & SV & SF & WF & WFP & XP0 & FS & LVI).
    pose proof (xpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    pose proof (xS1_facts e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof (xframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHF : sh (ff + 512) <= sh aceil) by (apply sh_mono; lia).
    unfold EX_FLAGP, EX_SAVED in *.

    assert (XWk : Forall (fun iv : Z * Z => ((snd iv <= x_lo e /\ stack0_ok iv) \/ (xS1 e <= fst iv /\ snd iv <= xSP e - 104))
                          /\ (snd iv <= ff + 8 \/ ff + 512 <= fst iv \/ snd iv <= ff + 504 /\ ff + 8 <= fst iv)
                          /\ (snd iv <= ff \/ ff + 512 <= fst iv \/ (ff + 8 <= fst iv /\ snd iv <= ff + 504))
                           /\ ((forall a, fst iv <= a < snd iv -> rin_ivs ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XE H ff fp ++ XSc ++ XSn) a) \/ (xS1 e <= fst iv /\ snd iv <= xSP e - 104))
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= fp \/ fp + 1 <= fst iv)) Xc).
    { eapply Forall_impl; [| exact FXc]. intros iv K. destruct K as [K|[K|[K|[K|K]]]].
      - pose proof (proj1 (Forall_forall _ _) FSn iv K) as FSi.
        destruct (xfsw_ok e ff fp m2 iv RF2 FF CE FSi) as (_ & _ & B3 & B4 & B5 & B6 & B7 & B8 & B9).
        split; [left; split; [exact B7 | exact B3]|]. split; [destruct B5; [left; lia | right; left; lia]|]. split; [destruct B5; [left | right; left]; lia|].
        split; [|split; [exact B8 | exact B9]].
        left. intros a Ha. right. apply rin_ivs_app. right. apply rin_ivs_app. right.
        clear - K Ha. induction XSn as [|iv' XSn IH]; [destruct K|]. destruct K as [->|K]; [left; exact Ha| right; exact (IH K)].
      - split; [left; split; [lia | destruct iv as [x y]; cbn [fst snd] in *; eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia]]|].
        split; [right; right; lia|]. split; [right; right; lia|].
        split; [left; intros a Ha; right; apply rin_ivs_app; left; cbn; right; right; left; change (fsz 3) with 512; lia|].
        split; [right; unfold ATP; lia | right; lia].
      - split; [left; split; [lia | right; lia]|]. split; [destruct F16; [left | right; left]; lia|]. split; [destruct F16; [left | right; left]; lia|].
        split; [left; intros a Ha; right; apply rin_ivs_app; left; cbn; right; right; right; left; change (fshn 3) with 64; lia|].
        split; [right; unfold ATP; lia | destruct F16; [left | right]; unfold AFS_SIZE in *; lia].
      - split; [right; exact K|]. split; [right; left; lia|]. split; [right; left; lia|]. split; [right; exact K|].
        split; [right; unfold ATP; lia | right; lia].
      -
        subst iv. cbn [fst snd]. split; [left; split; [unfold RtB_Td.ATDLOC; lia | exact RtB_Td.stack0_ok_td]|].
        split; [left; unfold RtB_Td.ATDLOC; lia|]. split; [left; unfold RtB_Td.ATDLOC; lia|].
        split; [left; intros a Ha; left; cbn [fst snd]; exact Ha|].
        split; [right; unfold ATP, RtB_Td.ATDLOC; lia | left; unfold RtB_Td.ATDLOC; lia]. }
    assert (XCL : forall A n, (forall iv, In iv Xc -> A + n <= fst iv \/ snd iv <= A) -> aclient_range H LBx (xS1 e) A n ->
                    xclient_range H LBx (xS1 e) Xc A n).
    { intros A n K CL. split; [exact CL|]. apply Forall_forall. intros iv Hiv. exact (K iv Hiv). }
    assert (LBI : forall b, In b (x_LB e) -> In b LBx) by exact INC.
    unfold xinv, EX_FLAGP, EX_SAVED.
    split; [exact RF2|]. split; [exact FF|]. split; [exact RH2|]. split; [exact AC2|]. split; [exact MI2|].
    split.
    { eapply (stack0_xpres H); [exact XP | exact S0 |]. eapply Forall_impl; [| exact XWk].
      intros iv (K1 & _). destruct K1 as [(_ & K1)|(K1 & K2)]; [exact K1|].
      destruct iv as [l h]. cbn [fst snd] in *. apply stack0_ok_app. unfold AHI_LO. lia. }
    split; [exact RA2|]. split; [exact ER2|].
    split.
    { destruct (stk_split asegs m1 (x_lo e) (xS1 e) (xSP e) ST ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 (xS1 e) (xSP e)).
      { eapply xpres_stk_mix; [exact XP | exact STu | lia |]. intros a Ha Hx.
        assert (EX : exists iv, In iv Xc /\ fst iv <= a < snd iv).
        { clear - Hx. induction Xc as [|iv Xc IH]; [destruct Hx|]. destruct Hx as [Hx|Hx]; [exists iv; split; [left; reflexivity | exact Hx]|].
          destruct (IH Hx) as (iv' & I1 & I2). exists iv'. split; [right; exact I1 | exact I2]. }
        destruct EX as (iv & Iiv & Ia).
        pose proof (proj1 (Forall_forall _ _) XWk iv Iiv) as (K1 & _).
        destruct K1 as [(K1 & _)|(K1 & K2)]; [lia|].
        pose proof (proj1 (Forall_forall _ _) RWX iv Iiv (or_introl K1)) as (W0 & W1 & W).
        assert (WA : wview asegs m2 (wa a) <> None) by (replace a with (fst iv + (a - fst iv)) by lia; apply W; lia).
        split; [exact WA|]. apply rd_of_wr_hi; [unfold AAPP_HI in *; lia | exact WA]. }
      exact (stk_merge asegs m2 (x_lo e) (xS1 e) (xSP e) ST2 STu2 ltac:(lia)). }
    split.
    { eapply xpres_rw_cells; [exact XP | exact SV |]. apply XCL; [| left; lia].
      intros iv Hiv. pose proof (proj1 (Forall_forall _ _) XWk iv Hiv) as (K1 & _). destruct K1 as [(K1 & _)|(K1 & K2)]; [right; lia | right; lia]. }
    split.
    { eapply xpres_rw_cells; [exact XP | exact SF |]. apply XCL.
      - intros iv Hiv. pose proof (proj1 (Forall_forall _ _) XWk iv Hiv) as (_ & K2 & _). cbn [cells_size csize]. lia.
      - right; right; right; right; left. cbn [cells_size csize]. lia. }
    split.
    { eapply xpres_wr_at_mix; [exact XP | exact WF | split; [right; right; right; right; left; lia | apply Forall_nil] |].
      intros a Ha K. assert (EX : exists iv, In iv Xc /\ fst iv <= a < snd iv).
      { clear - K. induction Xc as [|iv Xc IH]; [destruct K|]. destruct K as [K|K]; [exists iv; split; [left; reflexivity | exact K]|].
        destruct (IH K) as (iv' & I1 & I2). exists iv'. split; [right; exact I1 | exact I2]. }
      destruct EX as (iv & Iiv & Ia).
      pose proof (proj1 (Forall_forall _ _) XWk iv Iiv) as (K1 & _ & K3 & _).
      assert (IN : xS1 e <= fst iv \/ (ff <= fst iv /\ snd iv <= ff + 504)).
      { destruct K1 as [(K1 & _)|(K1 & _)]; [|left; exact K1]. destruct K3 as [K3|[K3|K3]]; [lia | lia | right; lia]. }
      pose proof (proj1 (Forall_forall _ _) RWX iv Iiv IN) as (W0 & W1 & W).
      replace a with (fst iv + (a - fst iv)) by lia. apply W. lia. }
    split.
    { eapply xpres_wr_at_mix; [exact XP | exact WFP | split; [right; right; right; right; left; lia | apply Forall_nil] |].
      intros a Ha K. exfalso. assert (EX : exists iv, In iv Xc /\ fst iv <= a < snd iv).
      { clear - K. induction Xc as [|iv Xc IH]; [destruct K|]. destruct K as [K|K]; [exists iv; split; [left; reflexivity | exact K]|].
        destruct (IH K) as (iv' & I1 & I2). exists iv'. split; [right; exact I1 | exact I2]. }
      destruct EX as (iv & Iiv & Ia).
      pose proof (proj1 (Forall_forall _ _) XWk iv Iiv) as (_ & _ & _ & _ & _ & K6). lia. }
    split.
    { eapply xpres_trans; [eapply xpres_weaken; [exact XP0 | lia | intros b Hb; exact Hb |] |].
      - intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
        apply rin_ivs_app in Ha as [Ha|Ha]; [apply rin_ivs_app; left; exact Ha|].
        apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ha.
      -
        pose proof (xpre_RH0 e HP) as RH0.
        intros a Ha [Hc Hx]. apply XP; [exact Ha|]. split; [eapply aclient_addr_weaken; [exact Hc | lia | exact LBI]|].
        intros K. assert (EX : exists iv, In iv Xc /\ fst iv <= a < snd iv).
        { clear - K. induction Xc as [|iv Xc IH]; [destruct K|]. destruct K as [K|K]; [exists iv; split; [left; reflexivity | exact K]|].
          destruct (IH K) as (iv' & I1 & I2). exists iv'. split; [right; exact I1 | exact I2]. }
        destruct EX as (iv & Iiv & Ia).
        pose proof (proj1 (Forall_forall _ _) XWk iv Iiv) as (_ & _ & _ & K4 & _).
        destruct K4 as [K4|(K4 & K5)]; [apply Hx; exact (K4 a Ia)|].
        destruct (aclient_low _ _ _ _ a RH0 Hc) as [L|L]; lia. }
    split; [| exact LV2].
    apply Forall_app. split; [exact FS|]. eapply Forall_impl; [| exact FSn]. intros iv X. exact (fs_scratch_mono H _ _ _ X).
  Qed.

End XKit.
