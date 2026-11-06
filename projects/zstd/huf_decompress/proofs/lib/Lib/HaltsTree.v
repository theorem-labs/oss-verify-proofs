(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_HaltsTree () := "C47Corelib7Classes?RelationClasses9ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib5ITree9ns_nolazyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib3Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at00C59OSSVerify5KrLib3Lib4Exec5mstepC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C59OSSVerify5KrLib3Lib5ITree;mstep_sstepC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5ITree?sstep_mstep_invC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at02C59OSSVerify5KrLib3Lib4Exec:msteps_indC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeHleaves_unreachable_m_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree7tree_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree<tree_at_stepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib5ITree;ns_progressC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5ITree8ns_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree7ns_exitC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib5ITree;ns_completeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at01c59OSSVerify5KrLib3Lib9HaltsTreeCmsteps_must_exit_inC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv7cfg_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib3Lib9RegsEquiv6ms_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv=sstep_cfg_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv6to_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv;cfg_eqv_symC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitCmust_exit_in_at_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions6bv_andC4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedC4ELinuxProcessSemantics?LinuxProcessSem5StateDm_killed_with_haltedK59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition<HaltsAllowed?any_exit_coversC5ELinuxProcessSemanticsEEquivalenceDefinition<HaltsAllowed7AnyExit5codesc59OSSVerify5KrLib3Lib9HaltsTreeDtree_at_must_exit_inC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC59OSSVerify5KrLib3Lib9RegsEquiv7init_msC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitAmust_exit_in_scfgK4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit<must_exit_inC4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitJmust_exit_in_scfg_may_failC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC4ELinuxProcessSemantics?LinuxProcessSem3Run@valid_entry_sv48C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib5Nodes9minv_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes;nodes_soundC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC59OSSVerify5KrLib3Lib9RegsEquivFinit_machine_state_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv:ms_eqv_symC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9HaltsTreeCmust_exit_in_at_eqvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib3Lib9HaltsTreeChx_nexit_not_killedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib9HaltsTree<hx_nexit_anyC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02C4ELinuxProcessSemantics?LinuxProcessSem3Run<may_fail_cfgI4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bridge.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> machine_state -> Prop.
  Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
  Variable nexit : node -> Model -> word -> Model -> Prop.
  Variable minv : Model -> Prop.
  Variable nsafe : node -> Model -> Prop.
  Hypothesis NS : node_sound node segs at_node nstep nexit minv nsafe.
  (* [comment removed for export] *)
  Hypothesis NK : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
  (* [comment removed for export] *)
  Variable S : list word.
  Hypothesis NC : forall n mo code mo', nexit n mo code mo' -> In code S.

  (* [comment removed for export] *)
  Lemma msteps_must_exit_in : forall ms ms1 mo,
    msteps segs ms ms1 ->
    m_halted mo = None -> minv mo ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms1 mo) ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms mo).
Proof using NS S.
  intros ms ms1 mo Hm Hh Hinv Hend.
  induction Hm as [ms | ms msa ms1 H1 H2 IH].
  - exact Hend.
  - apply must_exit_in_at_cfg_running.
    + exact Hh.
    + exists [], (SNext (mkCfg msa mo)). exact (mstep_sstep_cfg segs ms msa mo Hh (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) H1).
    + intros evs Hss. destruct (sstep_cfg_mstep_inv segs ms mo msa evs SError (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) H1 Hss) as [_ E].
      discriminate E.
    + intros evs c' Hss. destruct (sstep_cfg_mstep_inv segs ms mo msa evs (SNext c') (ns_nolazy _ _ _ _ _ _ _ NS mo Hinv) H1 Hss) as [_ E].
      injection E as ->. exact (IH Hend).
Qed.

  Theorem tree_at_must_exit_in : forall {R} (t : itree node R) Q ms mo,
    tree_at segs at_node nstep minv nsafe t Q ms mo ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms mo).
Proof using NS NK S NC.
  intros R t. induction t as [r | n k IH]; intros Q ms mo HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - pose proof HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    apply (msteps_must_exit_in ms ms1 mo Hm Hh Hinv).
    apply must_exit_in_at_cfg_running.
    + exact Hh.
    + destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
      * destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss). eauto.
      * destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss). eauto.
    + intros evs Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Hss)
        as [(rsp & mo' & E & _) | (code & mo' & E & _)]; discriminate E.
    + intros evs c' Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
        as [(rsp & mo' & E & Hst) | (code & mo' & E & Hex & _)].
      * injection E as ->.
        destruct (tree_at_step node segs at_node nstep nexit minv nsafe NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
        exact (IH rsp Q (nret ms1 rsp) mo' HT').
      * injection E as ->.
        destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
        apply (must_exit_in_at_cfg_halted ACFG segs S _ code); cbn [cfg_model];
          [exact Hh' | exact (NC n mo code mo' Hex) | exact (NK n mo code mo' Hex)].
Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma must_exit_in_at_eqv : forall segs S c,
  must_exit_in_at_cfg ACFG segs S c -> forall c', cfg_eqv c c' -> must_exit_in_at_cfg ACFG segs S c'.
Proof.
  intros segs S c H. induction H as [c code Hh Hin Hk | c Hnone Hprog Hnoerr Hnext IH]; intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [_ Hmo]. cbn in *. subst.
    apply (must_exit_in_at_cfg_halted ACFG segs S _ code); cbn; assumption.
  - apply must_exit_in_at_cfg_running.
    + destruct c as [ms mo], c' as [ms' mo']. destruct Heqv as [_ Hmo]. cbn in *. subst. exact Hnone.
    + destruct Hprog as (evs & st & Hst).
      destruct (sstep_cfg_eqv_scfg segs ACFG c c' evs st Heqv Hst) as (X' & Hst' & _). eauto.
    + intros evs Hst'.
      destruct (sstep_cfg_eqv_scfg segs ACFG c' c evs SError (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
      destruct X as [c2|]; simpl in HX; [contradiction|]. exact (Hnoerr evs Hst).
    + intros evs c2' Hst'.
      destruct (sstep_cfg_eqv_scfg segs ACFG c' c evs (SNext c2') (cfg_eqv_sym _ _ Heqv) Hst') as (X & Hst & HX).
      destruct X as [c2|]; simpl in HX; [|contradiction].
      apply (IH evs c2 Hst). apply cfg_eqv_sym. exact HX.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma hx_nexit_not_killed : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTree ()) [] "p'0h01Hh12fdi002fdh24addri014addrh33leni023lenh43mo'h54proti034proth63reqi043reqh72_Hh82bsi052bsh93bufi063bufh:4bufsi074bufsh;4codei084codeh<5code0h=5counti095counth>5flagsi0:5flagsh?2moh@1ni0;1nhA4pathi0<4pathp;1p;4p;2p;3p;6g006aj13Tg007Fj1;Tg007dj1:Tg00jbj40Tg008Gj1MTg009`j1DTg00=Mj19Tg00kVj2@Tg00C>j24Tg00lKj2>Tg00m@j1=Tg00n5j3<Tg00njj1LTg00o_j2KTg010Tj1JTg011Ij26Tg011oj12Tg012Tj1CTg0132j38Tg00:Bj35Tg013Wj27Tg014Qj2BTg002Ej6ATg015Tj1ETg016Ij4FTg017>j2GTg0183j3HTg018hj2?Tg00]lj1ITf2R0f1R1#If0R235p=1g019]R3g00HjR4g00I`R5#3#3#3R6#3#3#3#;R7#:R8f3R9P0P1P2C0P3P2f4R3P9P0C0%M8R:%D8R;719]0P3g01:RR<%;6#:#9R61@12f7R=f6R>f5R?C0A1:>;/42R@W0W8W1P1P2O2%961>12P=P>P?C0P@W0W:X1<P1P2O2%=2P?P3P9C0A1:3;/42RAW0XA6P2O1A<012f9R6f8RBP=C0A1:B;/42RCW0X=<X9<X1<P0P1P2O3%L2P?P3P9C0PAW0X1<P2O11K12P=P>P?C0P@W0X6<X1<P1P2O2g01;0P9P0P1C0A1:0;/42W0%J2P?P3P9C0g00Bc1671%25#2#2#2#2#2#2#C,67R5587958?17?>9543A1:?;P21679=875958=17B6954=P4f:R8,76A1:2;X441B68PBP2EAW0W7P1P2O2n2001000000120000000W0X<<P2O1%E2P?P3P9C0PAW0X6<P2O1P9P0P1P2CFf;P8P6C0A1:8;/42W0X><X5<X3<X2<P9P0P1P2O41G12P=P>P?C0P@W0X3<X2<P1P2O2AH012P6PBP=C0PCW0X5<X3<X2<P0P1P2O31?12P=P>P?C0P@W0X3<X2<P1P2O2n0110;000=20100105201001071010<3010010610910100201001040011108101044010110210310:201011023010110210320101102P2O1W0X44W;W?W@o"). Qed.

(* [comment removed for export] *)
Lemma hx_nexit_any : forall n mo code mo', nexit n mo code mo' -> In code AnyExit.codes.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTree ()) [] "p'0h01Hh12fdi002fdh24addri014addrh33leni023lenh44codei034codeh54proti044proth63reqi053reqh72_Hh82bsi062bsh93bufi073bufh:4bufsi084bufsh;5code0h<5counti095counth=5flagsi0:5flagsh>2moh?3mo'h@1ni0;1nhA4pathi0<4pathp;1p;4p;2p;3p;6g006aj13Tg007Fj1;Tg007dj19Tg00jbj40Tg00=Mj1:Tg00kVj2ITg00C>j24Tg00lKj2@Tg00m@j1?Tg00n5j3>Tg00njj1=Tg00o_j2<Tg010Tj1KTg011Ij26Tg011oj12Tg012Tj1JTg0132j37Tg00:Bj35Tg013Wj28Tg01;ej1HTg002Ej6CTg015Tj1BTg016Ij4ATg017>j2DTg0183j3ETg018hj2FTg00]Uj3GTf1R0f0R1g01=03Gp=1g019]R2g00HjR3g00I`R4#3#3#3R5#3#3#3#;R6#9R7f3R8f2R9P0P1C0P2P1f4R2P8P9C01172]0P2g01:RR:%;5#9#:R51I01f7R;f6R<f5R=C0117;/41R>W0W8W1P0P1O2%:51@01P;P<P=C0P>W0W:X1:P0P1O2%?1P=P2P8C0117=/41R?W0XA5P1O1A>901f9R5f8R@P;C01175/41RAW0X<:X9:X1:P9P0P1O3%=1P=P2P8C0P?W0X1:P1O11<01P;P<P=C0P>W0X6:X1:P0P1O2g01;0P8P9P0C01178/41W0%K1P=P2P8C0g00Bc1660%24#2#2#2#2#2#2#J,66R4576957=18=<9532117<P11668=764957;P71662=764R4f:RB,81953@1170[X471845953;166=#HW7P@P1ECW0P0P1O2n2001000000121000000W0X;:P1O1%B1P=P2P8C0P?W0X6:P1O1P8P9P0P1CAf;R?PBP5C0117?/41W0X=:X5:X3:X2:P8P9P0P1O41D01P;P<P=C0P>W0X3:X2:P0P1O2AE901P5P@P;C0PAW0X5:X3:X2:P9P0P1O31F01P;P<P=C0P>W0X3:X2:P0P1O2n0110;000=20100106201001081010<3010010710910100201001050011103101054010110210410:201011023010110210420101102P1O1W0X?3W4W>W@o"). Qed.

(* [comment removed for export] *)
Theorem halts_of_impl_tree : forall segs pc ph lim {R} (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  impl segs (at_node segs) t Q
       (init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) ->
  leaves_unreachable_m nstep t (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ->
  tsafe nstep nsafe t (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ->
  must_exit_in_scfg ACFG AnyExit.codes (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim R t Q [sp brk0 mbase rnd] inp Hve Hsv48 Himpl Hleaves Hsafe.
  cbn [en_sp en_brk en_mmap_base en_draw] in Himpl, Hleaves, Hsafe.
  cbn [must_exit_in_scfg]. unfold init_config.
  set (mo := init_model (segments_reserved segs) brk0 mbase sp lim inp) in *.
  assert (Hminv : minv mo).
  { rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & _ & _).
    apply minv_init. destruct Vsp as (L & H & _). lia. }
  apply (must_exit_in_at_eqv segs AnyExit.codes
           (mkCfg (init_ms segs pc ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd) mo)).
  - apply (tree_at_must_exit_in node segs (at_node segs) nstep nexit minv nsafe (nodes_sound segs)
             hx_nexit_not_killed AnyExit.codes hx_nexit_any t Q).
    split; [exact Himpl | split; [exact Hleaves | split; [reflexivity | split; [exact Hminv | exact Hsafe]]]].
  - split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.
