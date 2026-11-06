(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_add_abs_W () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.Rep.limbs_val"; "OSSVerify.KrLib.Lib.Arr.upd"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.MpiCoreAux.limb32"; "OSSVerify.KrLib.P.P_mpi_addsub.mpi_binop_post"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.P.P_mpi_addsub.add_abs_R"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "W.AA_FRAME"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Frame.wmono"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Spec.MpiJourney.XJ"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "W.AA_VAL"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "W.AA_POST"; "OSSVerify.KrLib.Spec.MpiJourney.BJ"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiJourney.JB"; "W.K1_stmt"; "Stdlib.ZArith.BinInt.Z.lt"].


Definition P_CALLOC : Z := 0x3c268.
Definition P_MEMCPY : Z := 0x43348.

(* [comment removed for export] *)
Definition add_frame (j0 : list byte) (ra s0 s1 s2 s3 s4 s5 : word) : list cell :=
  [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma limb32_app_r : forall (a b : list word) k, (length a <= k)%nat -> limb32 (a ++ b) k = limb32 b (k - length a).
Proof. intros. unfold limb32. rewrite app_nth2 by assumption. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39167884333.3000007S1m1k1H". (* [comment removed for export] *)
Lemma limb32_repeat0 : forall m k, limb32 (repeat (Z_to_bv 64 0) m) k = 0.
Proof.
  intros m k. unfold limb32. destruct (Nat.lt_ge_cases k m).
  - rewrite nth_repeat_lt by assumption. reflexivity.
  - rewrite nth_overflow by (rewrite repeat_length; lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39879861825.2000004S2xs". (* [comment removed for export] *)
Lemma limbs_val_app_zeros : forall xs k, limbs_val (xs ++ repeat (Z_to_bv 64 0) k) = limbs_val xs.
Proof. intros. rewrite limbs_val_app, limbs_val_repeat0. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma skipn_repeat : forall {T} (x : T) i k, skipn i (repeat x k) = repeat x (k - i).
Proof. intros T x i. induction i as [|i IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L1586849863.2 L1586849863.3 L29066016505.6L44015172725.6L47708349136.6L49026514663.6L7688242505.5 L7688242505.6 00000600>00G00P00Y00b00m01:S1v2HiS1i1v2HiS2xs1i2HiS2xs1i2HiS2xs1i2HiS2xs1i2HiS1w2xs1v2HiS1w2xs1i1v2Hi". (* [comment removed for export] *)
Lemma limbs_val_upd : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pxs,(0.(1.&40.))Pi,$2.Pv,(1.&40.)P,(3.R2.(4.(1.&40.)R3.))(5.$6.(7.(8.(1.&40.)R4.R3.R2.))(9.(7.R4.)(:.(;.+2.(:.+20.(<.R3.)))(=.(>.(?.&40.R2.)(;.+2.+20.))(10.R4.R3.)))))")
(* [comment removed for export] *).
Proof.
  induction xs as [|w xs IH]; intros [|i] v Hi; cbn [upd limbs_val length] in *; try lia.
  - unfold limb32. cbn. lia.
  - rewrite IH by lia. unfold limb32. cbn [nth].
    replace (32 * Z.of_nat (S i)) with (32 + 32 * Z.of_nat i) by lia. rewrite Z.pow_add_r by lia. unfold limb32. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section W.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk) (dA dB : mpd) (lo : Z) (MSF : Z) (j0 : list byte)
            (X sX nX pX : Z) (xs0 : list word) (padX : word) (ownX : limb_own).
  (* [comment removed for export] *)
  Local Notation dX := (mkMPD X sX nX pX xs0 padX ownX).
  Hypothesis MSFE : MSF = P_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SLO2 : lo <= bv_unsigned sp - 176 - hl_stack L.
  Definition AA_FRAME := add_frame j0 ra s0 s1 s2 s3 s4 s5.
  Hypothesis JCX : JC psegs L HI h LB m mo dX sp lo 64 AA_FRAME.

  Definition AA_POST := ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "(11.$12.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)(14.VLB,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)VdA,VdB,)Vlo,Vm,Vmo,)")
(* [comment removed for export] *).
  Definition AA_VAL := mpd_abs dA + mpd_abs dB.

  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L36100449086.89000004S2sp". (* [comment removed for export] *)
  #[using="L HI m mo h LB lo X sX nX pX xs0 padX ownX JCX"] Lemma add_epilogue : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Px20,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pm1,P,(1.&40.)(15.(1.&8.))P,(16.$12.R1.(=.(?.&40.Vsp,)+40.)$17.)P,(18.$12.R2.)(19.$12.Lms',$1:.(1;.(5.$1:.R1.(1<.(1=.Vra,Vsp,Vgp,Vtp,R1:.R19.R18.Vs0,Vs1,R14.R13.R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(1>.Vra,)Vfc,(1?.(1.&40.))R4.(20.$12.)))(1;.(21.(22.$23.)R4.R4.)(1;.(24.$12.R4.R4.)(18.$12.R4.))))(1<.(1=.R16.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R19.R18.R17.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(25.&40.+1?;48.)Vfc,(1?.(1.&40.))R3.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. intros until m1. intros FR MI. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    unfold AA_FRAME, add_frame in FR.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl psegs m1) as WM.
    do 9 zstep.
    replace (Z_to_bv 64 (bv_unsigned sp - 64 + 64)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; lia). rewrite Z_to_bv_bv_unsigned.
    finish.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="JCX"] Lemma add_ret : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Px20,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.PdXc,$29.Pr,$6.P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R6.R5.R4.R3.R2.)P,(2;.(1;.(5.$6.R2.=)(1;.(5.$6.(2<.R3.)$2=.)(5.$6.(2>.R3.)+1.)))(5.$6.R2.$2?.))(30.$12.R5.$31.(1<.(1=.R1:.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1=.R1<.R1;.R19.R18.(25.&40.R3.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.+1?;48.)Vfc,(1?.(1.&40.))R6.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros J HR. pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    eapply aevtM_cut_evt; [exact MK| eapply add_epilogue; [exact (xj_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)]|].
    cbv beta. intros ms' (-> & _). apply aevtM_done. unfold AA_POST. eapply xj_post; [exact JCX| exact J|].
    split; [exact HR|]. split; [exact (xj_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)|]. split; [exact (xj_pad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)|]. split; [exact (xj_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact (xj_nmono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)].
  Qed.

  #[using="JCX"] Lemma add_ret0 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Px20,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.PdXc,$29.P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R5.R4.R3.R2.R1.)P,(5.$6.(2<.R2.)$2=.)P,(5.$6.(2>.R3.)+1.)(30.$12.R5.$31.(1<.(1=.R1;.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1>.R1=.R1<.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.+1?;30.)Vfc,(1?.(1.&40.))R6.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J HV HS. pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. eapply add_ret; [exact J|]. left. split; [reflexivity|]. split; assumption.
  Qed.

  #[using="JCX"] Lemma add_retm16 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Px8,(1.&40.)Px9,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px18,(1.&40.)Px19,(1.&40.)Px20,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.PdXc,$29.P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R5.R4.R3.R2.R1.)(30.$12.R3.$31.(1<.(1=.R19.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1<.R1;.R1:.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+1?;44.)Vfc,(1?.(1.&40.))R4.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros J. pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (_ & _ & _ & MK & _).
    pose proof (xj_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as MI.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. eapply add_ret; [exact J|]. right. reflexivity.
  Qed.
  Local Notation XJ0 := (XJ psegs L HI h LB m mo dX sp lo 64 AA_FRAME []).
  Local Notation XJ1 An cnt := (XJ psegs L HI h LB m mo dX sp lo 64 AA_FRAME [(An, 4 * cnt)]).
  Local Notation FB0 := (FB psegs L LB dX).
  Local Notation JBE dE := (JB psegs L LB m dX sp lo dE).
  Local Notation BJE dE := (BJ psegs sp dE).
  Local Ltac xj_open J := pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]; cbn [app] in HH1.

  (* [comment removed for export] *)
  Definition K1_stmt (dE : mpd) (j : Z) (v : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.PdXc,$29.P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R5.R4.R3.R2.R1.)P,(32.$12.Vsp,O3.R5.R4.R2.)P,(5.$33.(34.R3.)$35.)P,(36.O2.(37.R4.))P,(5.$6.(2>.R5.)+1.)P,(5.$6.(7.(38.R6.))O1.)(30.$12.R8.$31.(1<.(1=.R18.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1;.R1:.R19.(25.&40.(39.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))(25.&40.O2.)R17.R16.(25.&40.(3:.O3.))R15.R14.R13.R12.R11.(25.&40.(39.O3.))(25.&40.(3:.R7.))(25.&40.(9.(:.+4.O2.)+4.))R10.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R?.R>.R=.R<.)VF,(25.&40.+1?;<4.)Vfc,(1?.(1.&40.))R9.(20.$12.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L15649680808.1  L2213969368.17  L22796454209.4  L23100341967.170L23100341967.178L23100341967.209L23100341967.211L25033945976.180L25044352195.208L25486643629.6  L2606027435.4   L27177789875.17 L28330171465.1  L35697396760.3  L37369374369.0  L39172636981.0  L39443110026.7  L41117966897.171L41117966897.212L44266429985.17 L45080762910.2  L45270661735.17 L46754389927.9  L46756382136.177L48154966246.178L48155112051.7  L49578233423.170L49578233423.211L49939585185.0  L52707865424.1  L5285175918.1   L5287573646.9   L5337555984.175 L5337555984.176 L5337555984.217 L5337555984.218 L58980668962.8  L59308633593.10 L59308743508.177L59308972243.3  L63588923042.7  L64932176453.4  L65258828961.0  L67601363691.1  L8695580055.5   00000300@00N00`01201]02H03203a04604F04]04b04m04n04o05G05Y06D06O06W06f07F08?08@08X08j09U09V09Y09Z0:;0:c0;M0<N0=O0=l0>70>b0>m0?C0?Q0?R0?W0?gS1jS1L2sp2lo3SLOS1j3nXc3CNT2N1S2sp1X2Ea2zs2xs2AnS2sp1X2Ea2zs2xs2AnS2sp1X2Ea2zs1j3nXc3pXc2xs2An4SLEN4DLEN4ZLENS2sp1X2Ea2zs1j3nXc3pXc2xs2An4SLEN4DLEN4ZLENS2sp1X2Ea2zs1j3nXc3pXc2xs3NR12An4SLEN4DLENS2sp1X2Ea2zs1j3nXc3pXc2xs3NR12An4SLEN4DLEN4ZLENS2Ea1j3nXc3CNT2An3ESAS3nXc3pXc2An3SEPS1L2HI2sp1h2hc4HTOP3HT1S3nXcS1j3nXc3CNTSSS1L3nXc3pXc3ACV2N12P02PCS2sp1X2Ea2zs2xs2AnS2sp1X2Ea2zs1j3nXc3pXc2xs2An4SLEN4DLEN4ZLENS1j3nXc3CNTS3nXc2AnS1j3nXc3CNT3NR1S1L1j3nXc3CNT3ACV3NR12An3An03AnCS1L2sp1X2Ea2zs1j3nXc2xs3CNT3SPB3ACV2X04LEN12E02An3An03AnCFS1L3nXc3pXc3ACV2N12P02PCS2sp1X2Ea2zs2xs2AnS2sp1X2Ea2zs1j3nXc3pXc2xs2An4SLEN4DLEN4ZLENSS1jFS1L2sp2lo3SPA3HLS3ACL3SLO3SPB3ACPS2sp1X2Ea2pE2zs2xs3SXB2An2HB5Ha_st5Hl_stS2sp1X2Ea2pE2zs1j2xs3SXB2An2HB5Ha_st5Hl_stS2sp1X2Ea2pE2zs1j3nXc3pXc2xs3SXB2An4SLEN4DLEN4ZLEN2HB5Ha_st5Hl_stS2sp1X2Ea2pE2zs1j3nXc3pXc2xs3SXB2An4SLEN4DLEN4ZLEN2HB5Ha_st5Hl_stS1L2sp2lo3HLS3ACL3SLO3SPB3ACPS2An3An02KZS2sp1X2nX2Ea2zs1j2xs3CNT3NR18xj_nmono2An2ENS3pXc2KP2P0S2nE2pE1j3nXc3CNT2An1HS1j3nXc3CNT2N1SS3nXcS1L2HI2sp1h4HTOP". (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA JCX"] Lemma add_G1 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "PdE,$29.Pj,$6.Pv,$6.Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px19,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.PdXc,$29.P,(3;.$12.VL,VLB,Vm,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,R1:.)P,(3<.R1;.R1:.R19.)P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R7.R6.R5.R4.R3.)P,(32.$12.Vsp,R1=.R7.R6.R4.)P,(1;.(3=.(37.R5.)R1=.)(36.R1=.+2710.))P,(5.$6.(2>.R6.)+1.)P,(5.$6.(7.(38.R7.))R1>.)(30.$12.R9.$31.(1<.(1=.R1;.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1>.R1=.R1<.(25.&40.(39.(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)))(25.&40.R20.)R1:.R19.R18.R17.R16.R15.R14.R13.(25.&40.(39.R21.))R12.(25.&40.(9.(:.+4.R20.)+4.))R11.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(25.&40.+1?;74.)Vfc,(1?.(1.&40.))R:.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until dXc. intros DBJ K1 J B CNT SG1 HV. jc_open. unfold K1_stmt in K1.
    destruct dE as [Ea sE nE pE zs padE ownE].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1). cbn [app] in HBR1, HAP1, ND1.
    pose proof DBJ as [MB0 OB CRB CRBL SXB].
    xj_open J.
    destruct dXc as [X' sg nXc pXc xs pad' own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. subst X' pad' sg.
    pose proof (bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1). cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := j) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
      clear - SLO HLS ACL ACP HTOP HT1 CNT NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
    replace (ret_pc (Z_to_bv 64 129920)) with (Z_to_bv 64 129920) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply add_retm16. exact J2. }
    (* [comment removed for export] *)
    replace (j * 4) with (4 * j) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ J MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - CNT; lia)) as [J2 F2].
    pose proof (bj_heap_pres _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ J B HPc MI2) as B2.
    dpose HBA as (An0 & An16 & _ & AnC & AnI). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc J B MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1.
    xj_open J2. pose proof MX1 as [(CX2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV CNT NR1; lia|].
    zstep. zstep. zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      assert (EO : own = LNull).
      { destruct own; [reflexivity| | exfalso; exact (NS1 eq_refl)]. exfalso. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & _ & _ & _ & P0 & PC & _). rewrite Z.mod_small in KP by (clear - N1 P0 PC ACV; lia). clear - KP P0. lia. }
      subst own. pose proof (xg_null _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as D2.
      destruct (OWN0 eq_refl) as [EP EN]. cbn [md_p md_n] in EP, EN. subst pXc nXc.
      pose proof (opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ B2)) as [(CE2 & _) _]. unfold mpi_cells in CE2. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE2.
      clear MU WM. pose proof (munch_refl [(X, X + 16)] m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      clear HH1 HH2 HNEW SOK1 ST2 FR1 HPX1 MI1.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D2 MU WM MI2 CX2) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
      pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ D2 B2 MU WM) as B5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5.
      eapply K1 with (dXc := mkMPD X 1 j An ([] ++ skipn (Z.to_nat 0) (repeat (Z_to_bv 64 0) (Z.to_nat j))) padX LHeap);
        [exact J5| exact B5| reflexivity| cbn [md_n]; clear; lia| reflexivity|].
      cbn [md_limbs]. rewrite skipn_repeat. destruct xs; [| exfalso; cbn [length] in *; lia].
      cbn [app]. rewrite limbs_val_repeat0. cbn [limbs_val] in HV. exact HV. }
    (* [comment removed for export] *)
    assert (EO : own = LHeap).
    { destruct own; [| reflexivity| exfalso; exact (NS1 eq_refl)]. exfalso. destruct (OWN0 eq_refl) as [EP _]. cbn [md_p] in EP. apply KP. rewrite EP. reflexivity. }
    subst own. ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & _ & P0 & PC & PI). cbn [md_p md_n] in N1, XIN, XPAL, P0, PC, PI.
    destruct (xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
    clear HH1 HH2 HNEW SOK1 FR1 HPX1.
    zstep. rewrite ?zx16_small by (clear - N1 CNT; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof P_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV CNT NR1; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (nXc * 4)) = nXc * 4) by (apply unsigned_lit; clear - N1 CNT; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (nXc * 4)) with (4 * length (firstn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat j))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 129952)) with (Z_to_bv 64 129952) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + nXc * 4) with (An + 4 * nXc) in MUd by (clear; lia). replace (Z.to_nat (nXc * 4)) with (Z.to_nat (4 * nXc)) in PA3 by (clear; lia).
    destruct (xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3) as [J3 F3]. cbn [md_limbs md_n] in F3.
    pose proof (bj_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ J2 F2 B2) as [ESA ELA]. cbn [md_addr md_own md_p md_n] in ESA, ELA.
    pose proof (bj_munch _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ B2 MUd WMd ltac:(cbn; clear - ESA CNT; lia) ltac:(intros BN; cbn; pose proof (ELA BN); clear - H CNT; lia)) as B3.
    clear J2 F2 B2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    xj_open J3. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    destruct (xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB). cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    pose proof MX1 as [(CX3 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite ?zx16_small by (clear - N1 CNT; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    clear CX3.
    eapply aevtM_cut.
    { eapply (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * nXc) (lo := lo) (junk := u32s xs);
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
      all: try exact ZB.
      all: try (rewrite HT1; clear - HTOP; lia).
      all: try (rewrite <- MSFE; exact CA).
      all: try (f_equal; clear; lia).
      all: clear - SLO SPA SPB HLS ACL ACP; lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & mo4 & h4 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & PX4 & SOK4).
    replace (ret_pc (Z_to_bv 64 129968)) with (Z_to_bv 64 129968) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ST4 MF4 HT4 HH4 PX4 SOK4) as D4.
    pose proof (bj_zfree _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ J3 F3 B3 eq_refl PX4 MI4) as B4. cbn [md_p] in B4.
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 B3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (opnd_view _ _ _ _ _ (bj_at _ _ _ _ _ _ B4)) as [(CE4 & _) _]. unfold mpi_cells in CE4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CE4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    pose proof (bj_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ _ _ _ _ _ _ D4 B4 MU WM) as B5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in B5.
    eapply K1 with (dXc := mkMPD X 1 j An (xs ++ skipn (Z.to_nat nXc) (repeat (Z_to_bv 64 0) (Z.to_nat j))) padX LHeap);
      [exact J5| exact B5| reflexivity| cbn [md_n]; clear; lia| reflexivity|].
    cbn [md_limbs]. rewrite skipn_repeat, limbs_val_app_zeros. exact HV.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@D12531787527.211D61813135019.211D6764644418.211 L11656196980.1  L12918245879.3  L14186142497.0  L14948330784.206L15015395550.2  L1597150190.10  L17830241467.2  L21297056158.4  L2213969368.16  L22479503797.3  L22538470188.1  L22641008756.208L22642964918.209L22642964918.211L23100341967.160L23100341967.186L23100341967.187L24799912036.4  L2606027435.4   L26228513507.2  L26662969968.16 L27177789875.16 L27749114960.5  L27835483287.185L27850050348.158L28659165194.3  L28671776394.4  L34663205127.211L39172636981.0  L4403968507.4   L44617445775.4  L46754389927.8  L46756382136.159L48154966246.160L48155112051.7  L49304323974.209L49306541636.211L49578233423.187L5285175918.1   L5287573646.9   L53280969732.16 L53342260001.0  L54817154178.3  L5562114849.0   L56211743567.208L58980668962.8  L59308630497.1  L59308632307.3  L59308633593.9  L63654471873.2  L67723135505.3  L68608730939.211L8695580055.5   L8890516472.1   00000100S01801<01H01I01J01Q02002702F02S02^02b03\04V05P05c06E06g07607E07L07T07k08508_09D09P09_0:h0:i0;40;?0;X0<F0=30=J0>G0>o0?Q0?R0@30@;0@<0@D0@E0@j0AG0AK0AV0Aa0Ah0B30C90CI0CMFS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLEN2ZBS2jnS2xs2jn4LEN1SFS2jn2AnS1L2sp2lo2jn3HLS3ACL3SLO2An3AnCS2jn2N1S2xs2jn4LEN12N1S1L2sp2lo3SLOS2jn3CNT2N1S2jnS1L2sp1X2xs3pXc2jn3SPB3ACV2X02P02An3An03AnC4SLEN4DLEN4ZLENS1L2sp1X2xs3pXc2jn3SPB3ACV2X02P02An3An03AnC4SLEN4DLEN4ZLENS1L2sp1X2xs3pXc2jn3SPB3ACV2X02P02An3An03AnC4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn2AnS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS2xs2jn4LEN12N1S3pXc2jn2An3SEPS2jn2N1S2jn3NR1S1L2HI2sp1h2hc4HTOP3HT1S2xs2jn2HVS2sp1X2xs3pXc2jn3CNT3NR12An4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn3CNT3NR12An4SLEN4DLENS2xs2jn4LEN1S2xs2jn4LEN12N1S1L2sp1X2xs3pXc2jn4DIMG3SPB2X04LEN12N12P02An3An03AnI2KZ2KP4SLEN4DLEN4ZLENSS1X2jn2An1HS2jn2An1a1OS1L2jn3ACV3NR12An3An03AnCS1L2sp1X2xs3pXc2jn3SPB3ACV2X02N12P02An3An03AnCS1L2sp1X2xs3pXc2jn3SPB3ACV2X02N12P02PC2An3An0S1L3pXc2jn3ACV2N12P02PCS2sp1X2xs3pXc2jn3SPB2X04LEN12N12P02An3An04SLEN4DLEN4ZLEN4LEN5S2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLEN5Ha_stS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENFS1L2sp2lo3SPA3HLS3ACL3SLO3SPB3ACPS2jn3CNTSS2jn3CNTSS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLEN2ZBS1L2sp2lo3HLS3ACL3SLO3SPB3ACPS2KBS3pXc2P02KPS2An3An02KZS2jn2N1S2jn3CNT2N1S1L2sp2lo1X4SLO22xs3pXc2jn3HLS3ACL3SPB2X02P02An3An03AnC4SLEN4DLEN4ZLENS1L2HI2sp1h4HTOPS2jn". (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_G2 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px19,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.Pxs,(0.(1.&40.))PpXc,$6.Pjn,$6.P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R7.R6.R5.R4.(13.VX,+1.R1.R2.R3.VpadX,$35.))P,(36.(9.R2.+1.)+2710.)P,(5.$6.(9.(7.R5.)(;.+2.(:.+20.R3.)))$2=.)(30.$12.R7.$31.(1<.(1=.R19.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1<.R1;.R1:.(25.&40.VX,)(25.&40.(9.R4.+1.))R18.R17.R16.R15.R14.R13.R12.R11.(25.&40.R4.)R10.(25.&40.(:.+4.R4.))R?.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(25.&40.+1?<38.)Vfc,(1?.(1.&40.))R8.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until jn. intros J0 CNT HV. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1). cbn [app] in HBR1, HAP1, ND1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & _ & P0 & PC & PI).
    pose proof J0 as JX. xj_open JX.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := jn + 1) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
      clear - SLO HLS ACL ACP HTOP HT1 CNT NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
    replace (ret_pc (Z_to_bv 64 130116)) with (Z_to_bv 64 130116) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ JX MI2 ST2 MF2 HPc HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply add_retm16. exact J2. }
    (* [comment removed for export] *)
    replace ((jn + 1) * 4) with (4 * (jn + 1)) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ JX MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - CNT NR1; lia)) as [J2 F2].
    dpose HBA as (An0 & An16 & _ & AnC & AnI). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1.
    xj_open J2. pose proof MX1 as [(CX2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV CNT NR1; lia|].
    zstep. zstep. zstep. if_cases KP; zify_cond KP; [exfalso; rewrite ?Z.mod_small in KP by (clear - N1 P0 PC ACV; lia); clear - KP P0; lia|].
    destruct (xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
    clear HH1 HH2 HNEW SOK1 FR1 HPX1.
    zstep. rewrite ?zx16_small by (clear - N1 CNT; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof P_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV CNT NR1; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (jn * 4)) = jn * 4) by (apply unsigned_lit; clear - N1 CNT; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (jn * 4)) with (4 * length (firstn (Z.to_nat jn) (repeat (Z_to_bv 64 0) (Z.to_nat (jn + 1)))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 130148)) with (Z_to_bv 64 130148) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + jn * 4) with (An + 4 * jn) in MUd by (clear; lia). replace (Z.to_nat (jn * 4)) with (Z.to_nat (4 * jn)) in PA3 by (clear; lia).
    destruct (xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3) as [J3 F3]. cbn [md_limbs md_n] in F3.
    clear J2 F2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    xj_open J3. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    destruct (xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB). cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    pose proof MX1 as [(CX3 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite ?zx16_small by (clear - N1 CNT; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    clear CX3.
    eapply aevtM_cut.
    { eapply (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * jn) (lo := lo) (junk := u32s xs);
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
      all: try exact ZB.
      all: try (rewrite HT1; clear - HTOP; lia).
      all: try (rewrite <- MSFE; exact CA).
      all: try (f_equal; clear; lia).
      all: clear - SLO SPA SPB HLS ACL ACP; lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & mo4 & h4 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & PX4 & SOK4).
    replace (ret_pc (Z_to_bv 64 130164)) with (Z_to_bv 64 130164) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ST4 MF4 HT4 HH4 PX4 SOK4) as D4.
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    rewrite skipn_repeat in J5. replace (Z.to_nat (jn + 1) - Z.to_nat jn)%nat with 1%nat in J5 by (clear - N1; lia). cbn [repeat] in J5.
    clear D4 CX4 MU WM ST4.
    (* [comment removed for export] *)
    xj_open J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    dpose MX1 as [(_ & _ & _ & LEN5 & _ & (_ & _ & _ & ARR5)) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ARR5, LEN5.
    pose proof (munch_refl [(An, An + 4 * (jn + 1))] m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    zstep. zstep. zstep.
    assert (NTH : nth_error (xs ++ [Z_to_bv 64 0]) (Z.to_nat jn) = Some (Z_to_bv 64 0)).
    { rewrite nth_error_app2 by (clear - LEN1; lia). replace (Z.to_nat jn - length xs)%nat with 0%nat by (clear - LEN1; lia). reflexivity. }
    pose proof (u32arr_read psegs m5 An (xs ++ [Z_to_bv 64 0]) jn (Z_to_bv 64 0) _ ARR5 NTH ltac:(clear - N1; lia) eq_refl) as RD.
    zstep. clear RD. zstep. zstep.
    pose proof (u32arr_store_ok psegs m5 An (xs ++ [Z_to_bv 64 0]) jn _ ARR5 ltac:(rewrite app_length; cbn [length]; clear - N1 LEN1; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write psegs m5 An (xs ++ [Z_to_bv 64 0]) jn v ARR5 ltac:(rewrite app_length; cbn [length]; clear - N1 LEN1; lia)) as ARR6 end.
    clear ARR5. store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    zstep. zstep. if_cases KB; zify_cond KB; [| exfalso; vm_compute in KB; clear - KB; first [lia | discriminate]].
    match goal with ST6 : stk psegs m6 _ _, MI6 : mem_inv psegs m6 |- _ =>
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J5 MU WM MI6 ST6
                    ltac:(intros a NO; left; destruct (outside_dec [(An, An + 4 * (jn + 1))] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                    ltac:(cbn; clear - AnC ACL SLO HLS CNT; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR6
                    ltac:(rewrite upd_length; reflexivity)) as J6 end.
    eapply add_ret; [exact J6|]. left. split; [reflexivity|]. split; [| reflexivity].
    unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite app_length; cbn [length]; clear - N1 LEN1; lia).
    change [Z_to_bv 64 0] with (repeat (Z_to_bv 64 0) 1). rewrite limbs_val_app_zeros.
    rewrite limb32_app_r by (clear - LEN1 N1; lia). rewrite limb32_repeat0.
    replace (Z.of_nat (Z.to_nat jn)) with jn by (clear - N1; lia).
    lazymatch goal with |- context [bv_unsigned ?v mod _] => let e := eval vm_compute in (bv_unsigned v mod 2 ^ 32) in change (bv_unsigned v mod 2^32) with e end.
    clear - HV. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00j0@D12531787527.210D61813135019.210D6764644418.210 L11656196980.1  L12918245879.3  L14948330784.205L15015395550.2  L1597150190.10  L17830241467.2  L21297056158.4  L2213969368.16  L22479503797.3  L22538470188.1  L22641008756.207L22642964918.208L22642964918.210L23100341967.159L23100341967.185L23100341967.186L24799912036.4  L2606027435.4   L2606547745.0   L26228513507.2  L26662969968.16 L27177789875.16 L27749114960.5  L27835483287.184L27850050348.157L28659165194.3  L28671776394.4  L32879090465.0  L34663205127.210L39172636981.0  L4079999236.209 L4403968507.4   L44617445775.4  L46754389927.8  L46756382136.158L48154966246.159L48155112051.7  L49304323974.208L49306541636.210L49578233423.186L5285175918.1   L5287573646.9   L53280969732.16 L54817154178.3  L56211743567.207L58980668962.8  L59308630497.1  L59308632307.3  L59308633593.9  L61522160417.0  L63654471873.2  L67723135505.3  L68608730939.210L8695580055.5   L8890516472.1   00000100S01801<01H01I01P01o02602E02R02]02a03[04U05O05b06D06f07507D07E07L07T07k08508_09D09P09_09`0:i0:j0;L0;W0;b0<;0<i0=V0=m0>j0?R0@40@50@V0@^0@f0AK0Ah0Ai0B40B?0B@0BG0BR0CX0Ch0ClFS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLEN2ZBS2jnS2xs2jn4LEN1FS2jn2AnS1L2sp2lo2jn3HLS3ACL3SLO2An3AnCS2jn2N1S2xs2jn4LEN12N1S1L2sp2lo3SLOS2jn3CNT2N1S2jnS1L2sp1X2xs3pXc2jn3SPB3ACV2X02P02An3An03AnC4SLEN4DLEN4ZLENS1L2sp1X2xs3pXc2jn3SPB3ACV2X02P02An3An03AnC4SLEN4DLEN4ZLENS1L2sp1X2xs3pXc2jn3SPB3ACV2X02P02An3An03AnC4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn2AnS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS2xs2jn4LEN12N1S3pXc2jn2An3SEPSS2jn2N1S2jn3NR1S1L2HI2sp1h2hc4HTOP3HT1S2xs2jn2HVS2sp1X2xs3pXc2jn3CNT3NR12An4SLEN4DLEN4ZLENS2sp1X2xs3pXc2jn3CNT3NR12An4SLEN4DLENS2xs2jn4LEN1S2xs2jn4LEN12N1SS1L2sp1X2xs3pXc2jn4DIMG3SPB2X04LEN12N12P02An3An03AnI2KZ2KP4SLEN4DLEN4ZLENSS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENS1X2jn2An1HS2jn2An1a1OS1L2jn3ACV3NR12An3An03AnCS1L2sp1X2xs3pXc2jn3SPB3ACV2X02N12P02An3An03AnCS1L2sp1X2xs3pXc2jn3SPB3ACV2X02N12P02PC2An3An0S1L3pXc2jn3ACV2N12P02PCS2sp1X2xs3pXc2jn3SPB2X04LEN12N12P02An3An04SLEN4DLEN4ZLEN4LEN5S2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLEN5Ha_stS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLENFS1L2sp2lo3SPA3HLS3ACL3SLO3SPB3ACPS2jn3CNTS2jn3CNTS2sp1X2xs3pXc2jn2An4SLEN4DLEN4ZLEN2ZBS1L2sp2lo3HLS3ACL3SLO3SPB3ACPFS3pXc2P02KPS2An3An02KZSS2jn2N1S2jn3CNT2N1S1L2sp2lo1X4SLO22xs3pXc2jn3HLS3ACL3SPB2X02P02An3An03AnC4SLEN4DLEN4ZLENS1L2HI2sp1h4HTOPS2jn". (* [comment removed for export] *)
  #[using="HFREE HCALLOC MSF MSFE CA TP SPA SLO2 JCX"] Lemma add_G3 : ltac2:(CDefT.buildp (gd_tbl_P_mpi_add_abs_W ()) "Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Praj,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Px19,(1.&40.)Px21,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Phc,(26.$12.VL,VHI,)PLBc,(0.$27.)Pmc,P,(1.&40.)(15.(1.&8.))Pmoc,$28.Pxs,(0.(1.&40.))PpXc,$6.Pjn,$6.P,(2:.$12.VL,VHI,Vh,VLB,Vm,Vmo,(13.VX,VsX,VnX,VpX,Vxs0,VpadX,VownX,)Vsp,Vlo,+40.$17.(22.$27.)R7.R6.R5.R4.(13.VX,+1.R1.R2.R3.VpadX,$35.))P,(36.(9.R2.+1.)+2710.)P,(5.$6.(9.(7.R5.)(;.+2.(:.+20.R3.)))$2=.)(30.$12.R7.$31.(1<.(1=.R18.(25.&40.(=.(?.&40.Vsp,)+40.))Vgp,Vtp,R1;.R1:.R19.(25.&40.VX,)(25.&40.R4.)(25.&40.+1.)R17.R16.R15.R14.R13.R12.R11.(25.&40.R4.)R10.(25.&40.(9.(:.+4.R4.)+4.))R?.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(25.&40.+1?<;0.)Vfc,(1?.(1.&40.))R8.(20.$12.)))")
(* [comment removed for export] *).
  Proof.
    intros until jn. intros J0 CNT HV. jc_open.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    pose proof alloc_ceiling_bounds as ACV.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J0) as (HBR1 & HAP1 & ND1 & MK1 & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1). cbn [app] in HBR1, HAP1, ND1.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    ddestruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & _ & P0 & PC & PI).
    pose proof J0 as JX. xj_open JX.
    pose proof (munch_refl ([] : list ivl) mc) as MU. pose proof (wmono_refl psegs mc) as WM.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 0x3c268) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc psegs L HI) with (cnt := jn + 1) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity;
      clear - SLO HLS ACL ACP HTOP HT1 CNT NR1 SPB; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI2 & ST2 & MF2 & HPc & h2 & HT2 & RES2).
    replace (ret_pc (Z_to_bv 64 130244)) with (Z_to_bv 64 130244) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    clear MU WM.
    destruct RES2 as [[-> HH2] | (An & -> & HBA & HH2 & HNEW)].
    { (* [comment removed for export] *)
      pose proof (xj_calloc_fail _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ JX MI2 ST2 MF2 HPc HT2 HH2) as J2.
      pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
      pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
      zstep. if_cases KZ; zify_cond KZ; [| exfalso; apply KZ; reflexivity].
      eapply add_retm16. exact J2. }
    (* [comment removed for export] *)
    replace ((jn + 1) * 4) with (4 * (jn + 1)) in * by (clear; lia).
    destruct (xj_calloc_ok _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ JX MI2 ST2 MF2 HPc HT2 HH2 HBA HNEW ltac:(cbn [md_n]; clear - CNT NR1; lia)) as [J2 F2].
    dpose HBA as (An0 & An16 & _ & AnC & AnI). pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    clear HPc JX MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1.
    xj_open J2. pose proof MX1 as [(CX2 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX2. unfold mpi_cells in CX2.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl psegs m2) as WM.
    zstep. if_cases KZ; zify_cond KZ; [exfalso; clear - KZ An0 AnC ACV CNT NR1; lia|].
    zstep. zstep. zstep. if_cases KP; zify_cond KP; [exfalso; rewrite ?Z.mod_small in KP by (clear - N1 P0 PC ACV; lia); clear - KP P0; lia|].
    destruct (xg_memcpy_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J2 F2 eq_refl) as (SBY & SLEN & DST & DLEN & SEP & _ & _ & _ & _).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in SBY, SLEN, DST, DLEN, SEP.
    clear HH1 HH2 HNEW SOK1 FR1 HPX1.
    zstep. rewrite ?zx16_small by (clear - N1 CNT; lia). zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    pose proof P_memcpy_spec as SPc. unfold memcpy_stmt in SPc.
    assert (U1 : bv_unsigned (Z_to_bv 64 An) = An) by (apply unsigned_lit; clear - An0 AnC ACV CNT NR1; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 pXc) = pXc) by (apply unsigned_lit; clear - P0 PC ACV N1; lia).
    assert (U3 : bv_unsigned (Z_to_bv 64 (jn * 4)) = jn * 4) by (apply unsigned_lit; clear - N1 CNT; lia).
    eapply aevtM_cut_evt; [ exact MK2 | eapply SPc with (src := u32s xs); rewrite ?U1, ?U2, ?U3;
      [ exact SBY | rewrite SLEN; clear; lia | replace (Z.to_nat (jn * 4)) with (4 * length (firstn (Z.to_nat jn) (repeat (Z_to_bv 64 0) (Z.to_nat (jn + 1)))))%nat by (rewrite DLEN; clear; lia); exact DST
      | clear - SEP; lia | exact MI2 ] | ].
    clear SPc. unfold memcpy_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & za1 & za2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & m3 & E & MUd & WMd & MI3 & PA3 & _). subst ms'.
    rewrite ?U1, ?U2, ?U3 in MUd. rewrite ?U1, ?U2, ?U3 in PA3.
    replace (ret_pc (Z_to_bv 64 130276)) with (Z_to_bv 64 130276) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    replace (An + jn * 4) with (An + 4 * jn) in MUd by (clear; lia). replace (Z.to_nat (jn * 4)) with (Z.to_nat (4 * jn)) in PA3 by (clear; lia).
    destruct (xg_memcpy_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ J2 F2 eq_refl MUd WMd MI3 PA3) as [J3 F3]. cbn [md_limbs md_n] in F3.
    clear J2 F2 MU WM DST SBY CX2 ST2 MI2 MK2 MI1 ST1 HT1 MF1 MX1 NS1 OUT1 FRS1 XP1 AD1 PD1.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl psegs m3) as WM.
    xj_open J3. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK3.
    destruct (xg_zfree_pre _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ J3 F3 eq_refl) as (ZIN & ZCH & ZLEN & ZB). cbn [md_p md_n md_limbs] in ZIN, ZCH, ZLEN, ZB.
    (* [comment removed for export] *)
    pose proof MX1 as [(CX3 & _) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX3. unfold mpi_cells in CX3.
    zstep. rewrite ?zx16_small by (clear - N1 CNT; lia). zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep.
    clear CX3.
    eapply aevtM_cut.
    { eapply (P_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := pXc) (len := 4 * jn) (lo := lo) (junk := u32s xs);
        rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by (clear - SPB SLO HLS ACL ACP; lia); try eassumption; try reflexivity.
      all: try (right; split; [exact ZIN|]; rewrite <- ZLEN; exact ZCH).
      all: try exact ZB.
      all: try (rewrite HT1; clear - HTOP; lia).
      all: try (rewrite <- MSFE; exact CA).
      all: try (f_equal; clear; lia).
      all: clear - SLO SPA SPB HLS ACL ACP; lia. }
    cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m4 & mo4 & h4 & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in PO by (clear - SPB SLO HLS ACL ACP; lia).
    ddestruct PO as (MI4 & ST4 & MF4 & HT4 & HH4 & PX4 & SOK4).
    replace (ret_pc (Z_to_bv 64 130292)) with (Z_to_bv 64 130292) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    pose proof (xg_zfree_post _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ J3 F3 eq_refl MI4 ST4 MF4 HT4 HH4 PX4 SOK4) as D4.
    pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
    clear J3 F3 MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NS1 OUT1 FRS1 HPX1 XP1 AD1 PD1 MU WM MK3 HH4 PX4 ZCH PA3 MUd WMd MI3 SOK4.
    pose proof (xd_struct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D4) as CX4. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CX4. unfold mpi_cells in CX4.
    pose proof (munch_refl [(X, X + 16)] m4) as MU. pose proof (wmono_refl psegs m4) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    pose proof (xd_finish _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ D4 MU WM MI4 CX4) as J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in J5.
    rewrite skipn_repeat in J5. replace (Z.to_nat (jn + 1) - Z.to_nat jn)%nat with 1%nat in J5 by (clear - N1; lia). cbn [repeat] in J5.
    clear D4 CX4 MU WM ST4.
    (* [comment removed for export] *)
    xj_open J5. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    dpose MX1 as [(_ & _ & _ & LEN5 & _ & (_ & _ & _ & ARR5)) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in ARR5, LEN5.
    pose proof (munch_refl [(An, An + 4 * (jn + 1))] m5) as MU. pose proof (wmono_refl psegs m5) as WM.
    zstep.
    assert (NTH : nth_error (xs ++ [Z_to_bv 64 0]) (Z.to_nat jn) = Some (Z_to_bv 64 0)).
    { rewrite nth_error_app2 by (clear - LEN1; lia). replace (Z.to_nat jn - length xs)%nat with 0%nat by (clear - LEN1; lia). reflexivity. }
    pose proof (u32arr_read psegs m5 An (xs ++ [Z_to_bv 64 0]) jn (Z_to_bv 64 0) _ ARR5 NTH ltac:(clear - N1; lia) eq_refl) as RD.
    zstep. clear RD. zstep.
    pose proof (u32arr_store_ok psegs m5 An (xs ++ [Z_to_bv 64 0]) jn _ ARR5 ltac:(rewrite app_length; cbn [length]; clear - N1 LEN1; lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write psegs m5 An (xs ++ [Z_to_bv 64 0]) jn v ARR5 ltac:(rewrite app_length; cbn [length]; clear - N1 LEN1; lia)) as ARR6 end.
    clear ARR5. store_done.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    zstep. if_cases KB; zify_cond KB; [| exfalso; vm_compute in KB; clear - KB; first [lia | discriminate]].
    match goal with ST6 : stk psegs m6 _ _, MI6 : mem_inv psegs m6 |- _ =>
      pose proof (xj_limbs _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ _ _ _ _ _ _ _ J5 MU WM MI6 ST6
                    ltac:(intros a NO; left; destruct (outside_dec [(An, An + 4 * (jn + 1))] a) as [O|O]; [exfalso; exact (NO O)| cbn in O; clear - O; lia])
                    ltac:(cbn; clear - AnC ACL SLO HLS CNT; lia) ltac:(cbn; pose proof (XP1 eq_refl); clear - H; lia) ARR6
                    ltac:(rewrite upd_length; reflexivity)) as J6 end.
    eapply add_ret0; [exact J6| | reflexivity].
    unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_upd by (rewrite app_length; cbn [length]; clear - N1 LEN1; lia).
    change [Z_to_bv 64 0] with (repeat (Z_to_bv 64 0) 1). rewrite limbs_val_app_zeros.
    rewrite limb32_app_r by (clear - LEN1 N1; lia). rewrite limb32_repeat0.
    replace (Z.of_nat (Z.to_nat jn)) with jn by (clear - N1; lia).
    lazymatch goal with |- context [bv_unsigned ?v mod _] => let e := eval vm_compute in (bv_unsigned v mod 2 ^ 32) in change (bv_unsigned v mod 2^32) with e end.
    clear - HV. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End W.
