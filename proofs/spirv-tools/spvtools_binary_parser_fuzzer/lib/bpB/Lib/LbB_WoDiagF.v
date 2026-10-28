From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own LbB_DiagStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_DStat LbB_PrsStmt LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit2.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoDiagF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wd_pre : forall (e : went H) ff fp XSc sk LBk m msF mo (entry : Z)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (DB : list block) (cost : Z),
    ds_tr_ok H -> wpre H e -> winv H e ff fp XSc sk LBk m -> as_AKREL H sk (mkCfg msF mo) ->
    as_VIS H sk msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
    frm_zero fc -> sp = Z_to_bv 64 (wS1 e) -> s0 = w_sp e -> tp = w_tp e -> bv_unsigned ra mod 2 = 0 ->
    lb_own DB m -> lb_small LBk + 64512 <= RT_SMALL_MAX -> Z.of_nat (length LBk) + 2 <= RT_CNT_MAX ->
    nlarge LBk + 1 <= RT_LARGE_MAX -> cost <= as_AL H sk ->
    exists errv, ds_pre H LINV_P5 entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                   t3 t4 t5 t6 F fc msF m mo sk LBk DB ((6, ff, fp) :: w_LF e) ((wSP e, bv_unsigned (w_ra e)) :: w_CH e) cost
                   (w_lo e) (w_B e) (w_shi e) errv.
  Proof.
    intros e ff fp XSc sk LBk m msF mo entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc DB cost TR HP HI KR VIS FZ ESP ES0 ETP RA2 OWN LS LC LL AL.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof HI as (RF & FF' & RH & AC & MI & S0 & RAX & (errv & ER) & ST & SV & SF & WF & WFP & XP & FS & LVI).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BB & B64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NLF & _).
    destruct (wchain_call H HH e ff fp XSc sk LBk m HP HI) as (CH & CHB).
    pose proof aceil_facts as ACF.
    assert (Esp : bv_unsigned sp = wS1 e) by (rewrite ESP, HLib.u64_of_Z by lia; reflexivity).
    exists errv. unfold ds_pre. subst tp s0. rewrite Esp.
    split; [exact VIS|]. split; [exact FZ|]. split; [exact RH|]. split; [exact KR|]. split; [exact OWN|].
    split; [exact LS|]. split; [exact LC|]. split; [exact LL|]. split; [exact RAX|]. split; [lia|]. split; [exact B64|].
    split; [clear - S32; Z.div_mod_to_equations; lia|].
    split; [exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) ST ltac:(lia)))|].
    split; [exact CE|]. split; [unfold ADS_STACK; lia|]. split; [exact ER|]. split; [exact MI|]. split; [exact TP|].
    split; [exact RA2|]. split; [exact LVI|]. split; [exact AC|]. split; [exact RF|].
    split; [cbn [length]; unfold PO_FRAMES, DS_FRAMES, AFS_MAXLIVE_BP in *; lia|].
    split; [exact S0|]. split; [lia|]. split; [exact CH|]. split; [unfold pf_ok, DS_PF; apply Forall_nil|].
    split; [exact CHB|]. split; [exact TR | exact AL].
  Qed.

  Lemma wd_dtor_pf : forall (e : went H) (r : Z), wpre H e -> In (APC0_FREE, [0xfd148; r]) PO_PF ->
    pf_ok (as_TR H) DS_DTOR_PF r ((wSP e, bv_unsigned (w_ra e)) :: w_CH e).
  Proof.
    intros e r HP IN.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PF & _).
    pose proof (pf_ok_site (as_TR H) PO_PF (bv_unsigned (w_ra e)) (w_CH e) APC0_FREE [0xfd148; r] PF IN) as T.
    unfold pf_ok, DS_DTOR_PF. apply Forall_cons; [| apply Forall_nil]. exact T.
  Qed.

  Lemma wd_back : forall (e : went H) ff fp XSc sk LBk m (LBX : list block) (X XS : list (Z * Z)) sk' LB' m' (errv' : word),
    wpre H e -> winv H e ff fp XSc sk LBk m -> (forall b, In b (w_LB e) -> In b LBX) ->
    xpres H LBX (wS1 e) (X ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => (ff + 8 <= fst iv /\ snd iv <= ff + WO_FLAGP /\ wr_at asegs m' (fst iv) (snd iv - fst iv))
                              \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) X ->
    as_RFS H ((6, ff, fp) :: w_LF e) m' -> as_RHEAP H sk' LB' m' -> ACONST m' -> mem_inv asegs m' ->
    stk asegs m' (w_lo e) (wS1 e) -> rw_cells asegs m' (errno_addr (w_tp e)) [C4 errv'] -> as_rauxv_ok H m' (w_B e) ->
    LINV_P5 m' -> winv H e ff fp (XSc ++ XS) sk' LB' m'.
  Proof.
    intros e ff fp XSc sk LBk m LBX X XS sk' LB' m' errv' HP HI INC XP FS FX RF RH AC MI ST ER RA LV.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof aceil_facts as ACF.
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI))
      as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    eapply (winv_sr_gen H HH e ff fp XSc XS (X ++ XS) sk LBk LBX sk' LB' m m' HP HI INC XP FS).
    - apply Forall_app. split.
      + eapply Forall_impl; [| exact FX]. intros iv [(X1 & X2 & _)|EQ].
        * right; left. split; [exact X1 | exact X2].
        * right; right; right; right. exact EQ.
      + apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF.
    - exact RH.
    - exact AC.
    - exact MI.
    - exact ST.
    - exists errv'. exact ER.
    - exact RA.
    - apply Forall_app. split.
      + eapply Forall_impl; [| exact FX]. intros iv [(_ & _ & W)|EQ] K; [exact W|].
        exfalso. subst iv. cbn [fst snd] in K. unfold RtB_Td.ATDLOC in K. lia.
      + eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
        destruct (wfsw_ok H HH e ff fp m' iv RF (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
        destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
          (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASDW_BASE_val in *; lia|]; split;
           [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
    - exact LV.
  Qed.
End WoDiagF.
