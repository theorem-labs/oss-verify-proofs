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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_Kit LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WKit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wframe_facts : forall LF ff fp, fresh_frame H LF 6 ff fp ->
       0x6e8000 + 0x9000 <= ff /\ ff + 4096 <= aceil /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ sh ff + 512 = sh (ff + 4096) /\ sh (as_FSB H) <= sh ff /\ sh (ff + 4096) <= sh (as_FSB H + AFS_SIZE)
    /\ 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000
    /\ (sh ff + 512 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh ff).
  Proof.
    intros LF ff fp FF. pose proof (fresh_frame_facts H LF 6 ff fp FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    change (fsz 6) with 4096 in *. unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *.
    pose proof aceil_facts as ACF.
    assert (S1 : sh ff + 512 = sh (ff + 4096)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (S2 : sh (as_FSB H) <= sh ff) by (apply sh_mono; lia).
    assert (S3 : sh (ff + 4096) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    assert (S4 : 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; unfold AFS_SIZE in *; Z.div_mod_to_equations; lia).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 4096 P9 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S5.
    change (nsh 4096) with 512 in S5.
    repeat split; try assumption; try lia.
  Qed.

  Lemma wpre_geo : forall e, wpre H e ->
    aceil <= w_lo e /\ w_lo e + 33280 <= wSP e /\ wSP e <= w_shi e /\ w_shi e <= AAPP_HI /\ wSP e mod 16 = 0
    /\ w_tp e = Z_to_bv 64 ATP.
  Proof.
    intros e HP.
    destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16 & _ & CE & LO & _ & _ & TP & _ & _ & _ & _ & _ & S0 & SHI & _).
    pose proof (stack0_bounds _ _ _ S0). unfold APO_STACK, APM_STACK in LO. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact SP16 | exact TP].
  Qed.
  Lemma wpre_RH0 : forall e, wpre H e -> as_RHEAP H (w_s e) (w_LB e) (w_m e).
  Proof. intros e HP. destruct HP as (_ & _ & _ & _ & X & _). exact X. Qed.
  Lemma werrno_ATP : forall (e : went H), w_tp e = Z_to_bv 64 ATP -> errno_addr (w_tp e) = ATP - 164.
  Proof. intros e TP. rewrite TP, HLib.u64_of_Z by (unfold ATP; lia). lia. Qed.

  Lemma wS1_facts : forall (e : went H), wpre H e ->
    wS1 e mod 32 = 0 /\ wS1 e + 192 <= wSP e <= wS1 e + 208 /\ 2 ^ 45 <= wS1 e /\ wSP e <= 2 ^ 47
    /\ w_lo e + 32768 <= wS1 e /\ aceil <= w_lo e.
  Proof.
    intros e HP. pose proof (wpre_geo e HP) as (CE & LO & SH1 & SH2 & SP16 & _).
    pose proof aceil_facts as ACF. unfold wS1, WO_FRAME. unfold AAPP_HI in SH2.
    set (SP := wSP e) in *. clearbody SP.
    assert (R : SP mod 32 = 0 \/ SP mod 32 = 16) by (clear - SP16; Z.div_mod_to_equations; lia).
    assert (R2 : (SP - 192 - SP mod 32) mod 32 = 0) by (clear - R; Z.div_mod_to_equations; lia).
    split; [exact R2|]. destruct R as [R|R]; rewrite R; lia.
  Qed.

  Definition wwin (e : went H) (ff : Z) (iv : Z * Z) : Prop :=
    (w_lo e <= fst iv /\ snd iv <= wSP e - WO_SAVED) \/ (ff <= fst iv /\ snd iv <= ff + WO_FLAGP)
    \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512).

  Lemma wwin_ok : forall e ff fp XSc iv, fresh_frame H (w_LF e) 6 ff fp ->
    aceil <= w_lo e -> w_lo e <= wSP e - WO_SAVED -> wSP e <= AAPP_HI -> wwin e ff iv ->
       afs_write_ok H ((6, ff, fp) :: w_LF e) iv /\ (forall LBk, aclient_write_ok H LBk iv) /\ aconst_ok iv /\ stack0_ok iv
    /\ ((aceil <= fst iv /\ snd iv <= wSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XSc) a))
    /\ (snd iv <= wSP e - WO_SAVED \/ wSP e <= fst iv)
    /\ (snd iv <= ff + WO_FLAGP \/ ff + 4096 <= fst iv)
    /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv).
  Proof.
    intros e ff fp XSc iv FF CE LO SPH HW.
    pose proof (wframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    destruct iv as [a b]. unfold wwin, WO_SAVED, WO_FLAGP in *. cbn [fst snd] in *.
    set (SP := wSP e) in *. set (lo := w_lo e) in *. clearbody SP lo.
    unfold afs_write_ok, aclient_write_ok; cbn [fst snd].
    destruct HW as [(W1 & W2)|[(W1 & W2)|(W1 & W2)]].
    -
      split; [left; split; [right; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      split; [intros LBk; left; cbn; lia|].
      split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]|].
      split; [apply stack0_ok_app; unfold AHI_LO; lia|].
      split; [left; lia|]. split; [left; lia|]. split; [right; lia|]. right; unfold ATP; lia.
    -
      split; [right; exists (6, ff, fp); split; [left; reflexivity | cbn; change (fsz 6) with 4096; lia]|].
      split; [intros LBk; right; right; right; right; left; cbn; lia|].
      split; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; lia]|].
      split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia]|].
      split; [right; intros x Hx; apply rin_ivs_app; left; cbn; right; right; left; change (fsz 6) with 4096; lia|].
      split; [left; lia|]. split; [left; lia|]. right; unfold ATP; lia.
    -
      split; [left; split; [destruct F16; [left | right]; lia | right; unfold ATLS_PRIV_HI, ATP; lia]|].
      split; [intros LBk; right; right; right; right; right; left; cbn; lia|].
      split; [apply aconst_ok_high; [assert (sh AIMG_TOP <= sh ff) by (apply sh_mono; unfold AIMG_TOP; lia); lia | right; left; lia]|].
      split; [right; cbn; assert (sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia); lia|].
      split; [right; intros x Hx; apply rin_ivs_app; left; cbn; right; right; right; left; change (fshn 6) with 512; lia|].
      split; [left; lia|]. split; [destruct F16; [left | right]; lia|]. right; unfold ATP; lia.
  Qed.

  Lemma wwin_all : forall e ff fp XSc W, fresh_frame H (w_LF e) 6 ff fp ->
    aceil <= w_lo e -> w_lo e <= wSP e - WO_SAVED -> wSP e <= AAPP_HI -> Forall (wwin e ff) W ->
       Forall (afs_write_ok H ((6, ff, fp) :: w_LF e)) W /\ (forall LBk, Forall (aclient_write_ok H LBk) W) /\ Forall aconst_ok W
    /\ Forall stack0_ok W
    /\ Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= wSP e) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XSc) a)) W
    /\ disjoint_from W (wSP e - WO_SAVED) WO_SAVED /\ disjoint_from W (ff + WO_FLAGP) 8 /\ disjoint_from W (ATP - 164) 4.
  Proof.
    intros e ff fp XSc W FF CE LO SPH FW. induction W as [|iv W IH].
    - split; [apply Forall_nil|]. split; [intros; apply Forall_nil|]. do 3 (split; [apply Forall_nil|]). cbn. tauto.
    - apply Forall_cons_iff in FW as [F0 FW]. destruct (IH FW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      destruct (wwin_ok e ff fp XSc iv FF CE LO SPH F0) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
      split; [apply Forall_cons; assumption|]. split; [intros LBk; apply Forall_cons; [apply B2 | apply A2]|].
      split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|]. split; [apply Forall_cons; assumption|].
      destruct iv as [x y]. unfold WO_SAVED, WO_FLAGP in *. cbn [fst snd] in *. cbn [disjoint_from].
      split; [split; [lia | exact A6]|]. split; [split; [lia | exact A7]|]. split; [lia | exact A8].
  Qed.

  Lemma winv_munch : forall e ff fp XSc sk LBk m1 m2 W,
    wpre H e -> winv H e ff fp XSc sk LBk m1 ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 (w_lo e) (wSP e) ->
    Forall (wwin e ff) W -> winv H e ff fp XSc sk LBk m2.
  Proof.
    intros e ff fp XSc sk LBk m1 m2 W HP HI MU WM MI2 ST2 FW.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof (wpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    assert (LO : w_lo e <= wSP e - WO_SAVED) by (unfold WO_SAVED in *; lia).
    assert (SPH : wSP e <= AAPP_HI) by lia. clear LO' SH1 SH2.
    unfold winv. rewrite (werrno_ATP e TP) in ER |- *.
    destruct (wwin_all e ff fp XSc W FF CE LO SPH FW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (wpre_RH0 e HP) as RH0.
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
    - eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch H (w_s e) (w_LB e) (wSP e) _ W (w_m e)); [exact HH | exact RH0 | exact MU | exact WM |].
        eapply Forall_impl; [| exact A5]. intros iv [K|K]; [left; exact K | right; intros a Ha; right; exact (K a Ha)].
    -
      eapply LbB_TdKit.LINV_P5_munch_hi; [exact LVI | exact MU |]. eapply Forall_impl; [| exact FW]. intros iv HW.
      pose proof (wframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      pose proof aceil_facts as ACF. unfold wwin in HW. unfold AIMG_TOP. destruct HW as [(W1 & _)|[(W1 & _)|(W1 & _)]]; lia.
  Qed.

  Lemma wfsw_ok : forall (e : went H) ff fp m iv,
    as_RFS H ((6, ff, fp) :: w_LF e) m -> fresh_frame H (w_LF e) 6 ff fp -> aceil <= w_lo e ->
    fs_scratch H ((6, ff, fp) :: w_LF e) iv ->
       (forall LBk, aclient_write_ok H LBk iv) /\ aconst_ok iv /\ stack0_ok iv
    /\ (snd iv <= ff + WO_FLAGP \/ ff + 4096 <= fst iv) /\ (snd iv <= ff \/ ff + 4096 <= fst iv)
    /\ (snd iv <= sh ff \/ sh ff + 512 <= fst iv)
    /\ snd iv <= w_lo e /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
    /\ (snd iv <= fp \/ fp + 1 <= fst iv).
  Proof.
    intros e ff fp m iv RF FF CE FS.
    pose proof (wframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF. unfold WO_FLAGP.
    assert (OB : fsobj H ((6, ff, fp) :: w_LF e) ff 4096) by (eapply (fsobj_inframe H); [left; reflexivity | cbn; lia | cbn; change (fsz 6) with 4096; lia]).
    pose proof (fsobj_scratch H HH _ ff 4096 m iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)
                  (aapp_sub _ _ ff 4096 F10 ltac:(lia) ltac:(lia)) FS) as D1.
    pose proof (fsobj_scratch_sh H HH _ ff 4096 m iv RF OB ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia) FS) as D2.
    change (nsh 4096) with 512 in D2.

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
    destruct (FFL (6, ff, fp) (or_introl eq_refl)) as (_ & NEf). cbn in NEf.
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (as_FSB H) AFS_SIZE F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(unfold AFS_SIZE; lia)) as DS.
    assert (sh (as_FSB H + AFS_SIZE) <= sh (as_FSB H) + nsh AFS_SIZE) by (unfold sh, nsh; Z.div_mod_to_equations; lia).
    unfold AFS_HDR, AFS_FLAGS in *.
    destruct E as [E|[E|E]]; rewrite E; cbn [fst snd]; [right; lia | lia |].
    assert (sh (as_FSB H) <= sh ff') by (apply sh_mono; lia).
    assert (sh ff' + fshn k = sh (ff' + fsz k)) by (unfold sh, fshn, fsz; Z.div_mod_to_equations; nia).
    assert (sh (ff' + fsz k) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    destruct DS; [left | right]; lia.
  Qed.

  Definition wcwin (e : went H) (ff : Z) (XSn : list (Z * Z)) (iv : Z * Z) : Prop :=
    (w_lo e <= fst iv /\ snd iv <= wS1 e) \/ (ff <= fst iv /\ snd iv <= ff + WO_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
    \/ In iv XSn.

  Lemma wkeep : forall e ff fp XSc sk LBk m' a,
    wpre H e -> winv H e ff fp XSc sk LBk m' -> 0 <= a < 2 ^ 64 ->
    ((exists p A n, In (p, A, n) (w_LB e) /\ ((A <= a < A + n) \/ (sh A <= a < sh A + nsh n))) \/ (aimg_client a /\ ~ (RtB_Td.ATDLOC <= a < RtB_Td.ATDLOC + 8)) \/ wSP e <= a) ->
    m' (wa a) = w_m e (wa a) /\ (wview asegs (w_m e) (wa a) <> None -> wview asegs m' (wa a) <> None).
  Proof.
    intros e ff fp XSc sk LBk m' a HP HI Ha K.
    destruct HI as (_ & FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & FS & _).
    pose proof (wpre_RH0 e HP) as RH0.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RF0 & _).
    pose proof (wpre_geo e HP) as (CE & LO & SH1 & SH2 & _ & _).
    pose proof aceil_facts as ACF.
    assert (FSA : Forall (fs_scratch H (w_LF e)) (XW H ff fp ++ XSc))
      by (apply Forall_app; split; [exact (fs_scratch_of_fresh H (w_LF e) 6 ff fp FF) | exact FS]).
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
        pose proof (fsobj_scratch H HH (w_LF e) A n (w_m e) iv RF0 (fsobj_block H HH _ _ _ _ p A n RH0 IN) ltac:(lia) Bn
                      ltac:(unfold AAPP_HI; lia) BAPP FSi). lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH0 IN) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in *.
        pose proof (fsobj_scratch_sh H HH (w_LF e) A n (w_m e) iv RF0 (fsobj_block H HH _ _ _ _ p A n RH0 IN) ltac:(lia) Bn
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

  Lemma wbytes : forall e ff fp XSc sk LBk m' p A n a bs, wpre H e -> winv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (w_LB e) -> A <= a -> a + Z.of_nat (length bs) <= A + n -> bytes_at asegs (w_m e) a bs -> bytes_at asegs m' a bs.
  Proof.
    intros e ff fp XSc sk LBk m' p A n a bs HP HI IN H1 H2 (B0 & B1 & B).
    split; [lia|]. split; [lia|]. intros i Hi.
    unfold mrd. rewrite (proj1 (wkeep e ff fp XSc sk LBk m' (a + Z.of_nat i) HP HI ltac:(lia) ltac:(left; exists p, A, n; split; [exact IN| left; lia]))).
    exact (B i Hi).
  Qed.

  Lemma wlinv : forall e ff fp XSc sk LBk m', wpre H e -> winv H e ff fp XSc sk LBk m' -> LINV_P5 m'.
  Proof using HH.
    intros e ff fp XSc sk LBk m' HP HI.
    apply HI.
  Qed.

  Lemma wchain : forall e ff fp XSc sk LBk m', wpre H e -> winv H e ff fp XSc sk LBk m' ->
    as_chain H m' (bv_unsigned (w_s0 e)) (w_CH e).
  Proof.
    intros e ff fp XSc sk LBk m' HP HI.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & CHN & _ & CHU & _).
    eapply (ah_chain_ext H HH); [exact CHN|]. intros f r a IN Ha.
    pose proof (ah_chain_range H HH _ _ _ f r CHN IN) as (R1 & R2 & R3). pose proof (CHU f r IN). pose proof aceil_facts.
    assert (X1 : 0 <= a < 2 ^ 64) by lia. assert (X2 : wSP e <= a) by lia.
    exact (proj1 (wkeep e ff fp XSc sk LBk m' a HP HI X1 (or_intror (or_intror X2)))).
  Qed.

  Lemma wcells_keep : forall e ff fp XSc sk LBk m' p A n a cs, wpre H e -> winv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (w_LB e) -> A <= a -> a + Z.of_nat (cells_size cs) <= A + n -> rw_cells asegs (w_m e) a cs -> rw_cells asegs m' a cs.
  Proof.
    intros e ff fp XSc sk LBk m' p A n a cs HP HI IN H1 H2 [[WF B] W]. split; [split; [exact WF|]|].
    - eapply wbytes; [exact HP | exact HI | exact IN | exact H1 | rewrite cells_bytes_length by exact WF; exact H2 | exact B].
    - destruct W as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      apply (proj2 (wkeep e ff fp XSc sk LBk m' (a + i) HP HI ltac:(lia) ltac:(left; exists p, A, n; split; [exact IN | left; lia]))).
      apply W. exact Hi.
  Qed.

  Lemma waddr_keep : forall e ff fp XSc sk LBk m' p A n, wpre H e -> winv H e ff fp XSc sk LBk m' ->
    In (p, A, n) (w_LB e) -> addressable (w_m e) A n -> addressable m' A n.
  Proof.
    intros e ff fp XSc sk LBk m' p A n HP HI IN (Hn & HA & HA8 & (B0 & B1 & B) & (W0 & W1 & W)).
    rewrite shadow_of_length in B1, W1, W by lia.
    pose proof (ah_blocks H HH _ _ _ _ (wpre_RH0 e HP) IN) as (C0 & C16 & Cn & CI & CC & CF & CAPP). cbn in C0, C16, Cn, CI, CC, CF, CAPP.
    pose proof aceil_facts as ACF.
    assert (X1 : A + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    assert (SB : sh A + nsh n <= 0x10007fff8000) by (pose proof (sh_nsh_high A n ltac:(lia) ltac:(lia) X1); unfold AHI_LO in *; lia).
    assert (KP : forall a, sh A <= a < sh A + nsh n -> m' (wa a) = w_m e (wa a) /\ (wview asegs (w_m e) (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha. apply (wkeep e ff fp XSc sk LBk m' a HP HI); [unfold sh in *; rewrite ASHADOW_BASE_val in *; lia|].
      left. exists p, A, n. split; [exact IN | right; exact Ha]. }
    split; [exact Hn|]. split; [exact HA|]. split; [exact HA8|]. split.
    - split; [exact B0|]. split; [rewrite shadow_of_length by lia; exact B1|]. intros i Hi. unfold mrd.
      assert (Hi' : Z.of_nat i < nsh n) by (rewrite <- shadow_of_length by lia; lia).
      rewrite (proj1 (KP (sh A + Z.of_nat i) ltac:(lia))). exact (B i Hi).
    - split; [exact W0|]. split; [rewrite shadow_of_length by lia; exact W1|]. intros i Hi. rewrite shadow_of_length in Hi by lia.
      apply (proj2 (KP (sh A + i) ltac:(lia))). apply W. exact Hi.
  Qed.

  Section Proj.
    Variables (e : went H) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem).
    Hypothesis HI : winv H e ff fp XSc sk LBk m.
    Lemma winv_rf : as_RFS H ((6, ff, fp) :: w_LF e) m.             Proof. apply HI. Qed.
    Lemma winv_ff : fresh_frame H (w_LF e) 6 ff fp.                  Proof. apply HI. Qed.
    Lemma winv_rh : as_RHEAP H sk LBk m.                             Proof. apply HI. Qed.
    Lemma winv_ac : ACONST m.                                        Proof. apply HI. Qed.
    Lemma winv_mi : mem_inv asegs m.                                 Proof. apply HI. Qed.
    Lemma winv_s0 : stack0 m (w_lo e) (w_shi e).                     Proof. apply HI. Qed.
    Lemma winv_stk : stk asegs m (w_lo e) (wSP e).                   Proof. apply HI. Qed.
    Lemma winv_sf : rw_cells asegs m (ff + WO_FLAGP) [C8 (Z_to_bv 64 fp)]. Proof. apply HI. Qed.
    Lemma winv_wf : wr_at asegs m ff WO_FLAGP.                       Proof. apply HI. Qed.
    Lemma winv_wfp : wr_at asegs m fp 1.                             Proof. apply HI. Qed.
    Lemma winv_sv : rw_cells asegs m (wSP e - WO_SAVED) (wsaved e).   Proof. apply HI. Qed.
    Lemma winv_ra : as_rauxv_ok H m (w_B e).                         Proof. apply HI. Qed.
    Lemma winv_er : exists errv, rw_cells asegs m (errno_addr (w_tp e)) [C4 errv]. Proof. apply HI. Qed.

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

  Lemma winv_sr_gen : forall e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2,
    wpre H e -> winv H e ff fp XSc sk LBk m1 ->
    (forall b, In b (w_LB e) -> In b LBx) ->
    xpres H LBx (wS1 e) Xc m1 m2 ->
    Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XSn ->
    Forall (fun iv : Z * Z => In iv XSn \/ (ff + 8 <= fst iv /\ snd iv <= ff + WO_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
                              \/ (wS1 e <= fst iv /\ snd iv <= wSP e - WO_SAVED) \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) Xc ->
    as_RFS H ((6, ff, fp) :: w_LF e) m2 -> as_RHEAP H sk' LBk' m2 -> ACONST m2 -> mem_inv asegs m2 ->
    stk asegs m2 (w_lo e) (wS1 e) -> (exists errv', rw_cells asegs m2 (errno_addr (w_tp e)) [C4 errv']) -> as_rauxv_ok H m2 (w_B e) ->

    Forall (fun iv : Z * Z => wS1 e <= fst iv \/ (ff <= fst iv /\ snd iv <= ff + WO_FLAGP) -> wr_at asegs m2 (fst iv) (snd iv - fst iv)) Xc ->
    LINV_P5 m2 ->
    winv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2 HP HI INC XP FSn FXc RF2 RH2 AC2 MI2 ST2 ER2 RA2 RWX LV2.
    destruct HI as (RF & FF & RH & AC & MI & S0 & RA & _ & ST & SV & SF & WF & WFP & XP0 & FS & LVI).
    pose proof (wpre_geo e HP) as (CE & LO' & SH1 & SH2 & _ & TP).
    pose proof (wS1_facts e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof (wframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHF : sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia).
    unfold WO_FLAGP, WO_SAVED in *.

    assert (XWk : Forall (fun iv : Z * Z => ((snd iv <= w_lo e /\ stack0_ok iv) \/ (wS1 e <= fst iv /\ snd iv <= wSP e - 104))
                           /\ (snd iv <= ff + 8 \/ ff + 4096 <= fst iv \/ snd iv <= ff + 4088 /\ ff + 8 <= fst iv)
                           /\ (snd iv <= ff \/ ff + 4096 <= fst iv \/ (ff + 8 <= fst iv /\ snd iv <= ff + 4088))
                           /\ ((forall a, fst iv <= a < snd iv -> rin_ivs ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XW H ff fp ++ XSc ++ XSn) a) \/ (wS1 e <= fst iv /\ snd iv <= wSP e - 104))
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= fp \/ fp + 1 <= fst iv)) Xc).
    { eapply Forall_impl; [| exact FXc]. intros iv K. destruct K as [K|[K|[K|[K|K]]]].
      - pose proof (proj1 (Forall_forall _ _) FSn iv K) as FSi.
        destruct (wfsw_ok e ff fp m2 iv RF2 FF CE FSi) as (_ & _ & B3 & B4 & B5 & B6 & B7 & B8 & B9).
        split; [left; split; [exact B7 | exact B3]|]. split; [destruct B5; [left; lia | right; left; lia]|]. split; [destruct B5; [left | right; left]; lia|].
        split; [|split; [exact B8 | exact B9]].
        left. intros a Ha. right. apply rin_ivs_app. right. apply rin_ivs_app. right.
        clear - K Ha. induction XSn as [|iv' XSn IH]; [destruct K|]. destruct K as [->|K]; [left; exact Ha| right; exact (IH K)].
      - split; [left; split; [lia | destruct iv as [x y]; cbn [fst snd] in *; eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia]]|].
        split; [right; right; lia|]. split; [right; right; lia|].
        split; [left; intros a Ha; right; apply rin_ivs_app; left; cbn; right; right; left; change (fsz 6) with 4096; lia|].
        split; [right; unfold ATP; lia | right; lia].
      - split; [left; split; [lia | right; lia]|]. split; [destruct F16; [left | right; left]; lia|]. split; [destruct F16; [left | right; left]; lia|].
        split; [left; intros a Ha; right; apply rin_ivs_app; left; cbn; right; right; right; left; change (fshn 6) with 512; lia|].
        split; [right; unfold ATP; lia | destruct F16; [left | right]; unfold AFS_SIZE in *; lia].
      - split; [right; exact K|]. split; [right; left; lia|]. split; [right; left; lia|]. split; [right; exact K|].
        split; [right; unfold ATP; lia | right; lia].
      -
        subst iv. cbn [fst snd]. split; [left; split; [unfold RtB_Td.ATDLOC; lia | exact RtB_Td.stack0_ok_td]|].
        split; [left; unfold RtB_Td.ATDLOC; lia|]. split; [left; unfold RtB_Td.ATDLOC; lia|].
        split; [left; intros a Ha; left; cbn [fst snd]; exact Ha|].
        split; [right; unfold ATP, RtB_Td.ATDLOC; lia | left; unfold RtB_Td.ATDLOC; lia]. }
    assert (XCL : forall A n, (forall iv, In iv Xc -> A + n <= fst iv \/ snd iv <= A) -> aclient_range H LBx (wS1 e) A n ->
                    xclient_range H LBx (wS1 e) Xc A n).
    { intros A n K CL. split; [exact CL|]. apply Forall_forall. intros iv Hiv. exact (K iv Hiv). }
    assert (LBI : forall b, In b (w_LB e) -> In b LBx) by exact INC.
    unfold winv, WO_FLAGP, WO_SAVED.
    split; [exact RF2|]. split; [exact FF|]. split; [exact RH2|]. split; [exact AC2|]. split; [exact MI2|].
    split.
    { eapply (stack0_xpres H); [exact XP | exact S0 |]. eapply Forall_impl; [| exact XWk].
      intros iv (K1 & _). destruct K1 as [(_ & K1)|(K1 & K2)]; [exact K1|].
      destruct iv as [l h]. cbn [fst snd] in *. apply stack0_ok_app. unfold AHI_LO. lia. }
    split; [exact RA2|]. split; [exact ER2|].
    split.
    { destruct (stk_split asegs m1 (w_lo e) (wS1 e) (wSP e) ST ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 (wS1 e) (wSP e)).
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
      exact (stk_merge asegs m2 (w_lo e) (wS1 e) (wSP e) ST2 STu2 ltac:(lia)). }
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
      assert (IN : wS1 e <= fst iv \/ (ff <= fst iv /\ snd iv <= ff + 4088)).
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
        pose proof (wpre_RH0 e HP) as RH0.
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

  Lemma winv_sr : forall e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2,
    wpre H e -> winv H e ff fp XSc sk LBk m1 ->
    (forall b, In b (w_LB e) -> In b LBx) ->
    xpres H LBx (wS1 e) Xc m1 m2 ->
    Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XSn ->
    Forall (fun iv : Z * Z => In iv XSn \/ (ff + 8 <= fst iv /\ snd iv <= ff + WO_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
                              \/ (wS1 e <= fst iv /\ snd iv <= wSP e - WO_SAVED)) Xc ->
    as_RFS H ((6, ff, fp) :: w_LF e) m2 -> as_RHEAP H sk' LBk' m2 -> ACONST m2 -> mem_inv asegs m2 ->
    stk asegs m2 (w_lo e) (wS1 e) -> (exists errv', rw_cells asegs m2 (errno_addr (w_tp e)) [C4 errv']) -> as_rauxv_ok H m2 (w_B e) ->

    Forall (fun iv : Z * Z => wS1 e <= fst iv \/ (ff <= fst iv /\ snd iv <= ff + WO_FLAGP) -> wr_at asegs m2 (fst iv) (snd iv - fst iv)) Xc ->
    winv H e ff fp (XSc ++ XSn) sk' LBk' m2.
  Proof.
    intros e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2 HP HI INC XP FSn FXc RF2 RH2 AC2 MI2 ST2 ER2 RA2 RWX.
    eapply (winv_sr_gen e ff fp XSc XSn Xc sk LBk LBx sk' LBk' m1 m2); try eassumption.
    - eapply Forall_impl; [| exact FXc]. intros iv [K|[K|[K|K]]]; [left | right; left | right; right; left | right; right; right; left]; exact K.
    - pose proof HI as (_ & FF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LVI).
      pose proof (wframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      pose proof (wS1_facts e HP) as (_ & _ & S45 & _). pose proof aceil_facts as ACF.
      eapply (LbB_TdKit.LINV_P5_xpres_hi H); [exact LVI | exact XP |].
      eapply Forall_impl; [| exact FXc]. intros iv [K|[K|[K|K]]].
      + exact (LbB_TdKit.fs_scratch_above H HH _ m2 iv RF2 (proj1 (Forall_forall _ _) FSn iv K)).
      + unfold AIMG_TOP. lia.
      + unfold AIMG_TOP. lia.
      + unfold AIMG_TOP. lia.
  Qed.

  Lemma wframe_bounds : forall e ff fp XSc sk LBk m, wpre H e -> winv H e ff fp XSc sk LBk m ->
    0 <= ff /\ ff mod 64 = 0 /\ AIMG_TOP + AFS_HDR <= ff /\ ff + WO_FLAGP <= 2 ^ 47 /\ 3808 <= WO_FLAGP
    /\ ff + WO_FLAGP <= wS1 e - AINTRIN_STACK /\ (sh ff + 512 <= ff \/ ff + 4096 <= sh ff)
    /\ sh ff + 512 <= wS1 e - AINTRIN_STACK /\ 2 ^ 45 <= wS1 e /\ wS1 e + 192 <= wSP e /\ wSP e <= 2 ^ 47
    /\ w_lo e <= wS1 e.
  Proof.
    intros e ff fp XSc sk LBk m HP HI.
    pose proof HI as (_ & FF & _).
    pose proof (wframe_facts _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CE).
    unfold WO_FLAGP, AINTRIN_STACK, AIMG_TOP, AFS_HDR in *.
    clear - F1 F2 F3 F6 F7 F15 F16 S1SP S1L SPH LOS1 CE.
    repeat split; lia.
  Qed.
End WKit.
