(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_addsub U_mpi_free U_mpi_core_sub U_mpi_cmp U_mpi_core_sub_int.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_checks.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_sub_abs_C () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_sub.U_MPI_CORE_SUB"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lseg"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "stdpp.bitvector.definitions.bv_unsigned"; "sub_frame"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_NEGATIVE_VALUE"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_cmp.SIGF"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.USpec.MpiOpnd.opnd_at"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"].


(* [comment removed for export] *)
Definition sub_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell :=
  [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma U_core_sub_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  mem_inv usegs m -> stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> a3 = Z_to_bv 64 0 ->
  evt usegs
    (fun ms' : machine_state => exists (a4' : word) (m' : mem),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
       /\ stk usegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 U_MPI_CORE_SUB) fc None m (seg_rom usegs))
(* [comment removed for export] *).
Proof.
  intros until lo. intros MI ST SLO ->. unfold U_MPI_CORE_SUB.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  pose proof (proj1 ST) as LO0.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  do 8 zstep.
  zstep. try (if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]).
  do 9 zstep.
  release_frame FR ST (bv_unsigned sp).
  repeat match goal with |- context [Z_to_bv 64 (bv_unsigned sp + ?a + ?b)] =>
    replace (bv_unsigned sp + a + b) with (bv_unsigned sp) by lia end.
  rewrite ?Z_to_bv_bv_unsigned.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L1231189785.9  L26153468717.12L27601770837.7 L27847865865.9 L35878332091.9 L43191333535.9 L44674750285.9 L58023740499.1200000>00T00`00j01401B01P01bS1j1d1i3Hij2HdS1j1d1i3Hij2Hd1k2H12H2S1j1i3Hij2HdS1j1d1i2HdS1j1d1i2HdS1j1d1i3Hij2HdS1j1d1i3Hij2HdS1j1d1i2Hd1k2H12H2". (* [comment removed for export] *)
Lemma lseg_ext : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pxs,(15.(0.&40.))Pys,(15.(0.&40.))Pi,$16.Pj,$16.P,(:.(17.=R2.)(17.R2.R1.))P,Pk,$18.P,(19.(1:.R4.)R1.)P,(1;.R2.(1:.R4.))(5.$16.(1<.R8.R3.)(1<.R7.R3.))(5.$16.(1=.R6.R4.R3.)(1=.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros xs ys i j Hij HE.
  remember (Z.to_nat (j - i)) as d eqn:Hd. revert i Hij HE Hd. induction d as [|d IH]; intros i Hij HE Hd.
  - assert (j = i) as -> by lia. rewrite !lseg_empty. reflexivity.
  - rewrite (lseg_cons xs i j), (lseg_cons ys i j) by lia. rewrite (HE (Z.to_nat i)) by lia.
    rewrite (IH (i + 1)); [reflexivity| lia| | lia]. intros k H1 H2. apply HE; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L1231189785.8  L26153468717.11L27601770837.6 L27847865865.8 L35878332091.8 L43191333535.8 L44674750285.8 L58023740499.11L61021986978.8 00000>00T00`00j01401B01P01b01lS1j1d1i3Hij2HdS1j1d1i3Hij2Hd1k2H12H2S1j1i3Hij2HdS1j1d1i2HdS1j1d1i2HdS1j1d1i3Hij2HdS1j1d1i3Hij2HdS1j1d1i2Hd1k2H12H2S1j1d1i2Hd". (* [comment removed for export] *)
Lemma lseg_zero : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pxs,(15.(0.&40.))Pi,$16.Pj,$16.P,(:.(17.=R2.)(17.R2.R1.))P,Pk,$18.P,(19.(1:.R4.)R1.)P,(1;.R2.(1:.R4.))(5.$16.(1<.R7.R3.)=)(5.$16.(1=.R5.R4.R3.)=)")
(* [comment removed for export] *).
Proof.
  intros xs i j Hij HE.
  remember (Z.to_nat (j - i)) as d eqn:Hd. revert i Hij HE Hd. induction d as [|d IH]; intros i Hij HE Hd.
  - assert (j = i) as -> by lia. apply lseg_empty.
  - rewrite (lseg_cons xs i j) by lia. rewrite (HE (Z.to_nat i)) by lia. rewrite (IH (i + 1)); [lia| lia| | lia]. intros k H1 H2. apply HE; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L21677587979.6L24141441379.6L28550249749.600000700C00JS1i1j1HS1i1j1k1H2H'S1i1j1k". (* [comment removed for export] *)
Lemma lseg_mid : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pxs,(15.(0.&40.))Pi,$16.Pj,$16.Pk,$16.P,(:.(17.=R3.)(17.R3.R2.))P,(17.R3.R2.)(5.$16.(1=.R6.R5.R3.)(1>.(1=.R6.R5.R4.)(1?.(20.+2.(1?.+20.(21.R4.R5.)))(1=.R6.R4.R3.))))")
(* [comment removed for export] *).
Proof.
  intros xs i j k H H'. unfold lseg at 1 2. rewrite (lval_split (skipn (Z.to_nat i) xs) (j - i) (k - i)) by lia. f_equal. f_equal.
  unfold lseg. rewrite skipn_skipn. replace (Z.to_nat (j - i) + Z.to_nat i)%nat with (Z.to_nat j) by lia. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma lval_lseg0 : forall xs n, lval xs n = lseg xs 0 n.
Proof. intros. unfold lseg. cbn [Z.to_nat skipn]. rewrite Z.sub_0_r. reflexivity. Qed.

Lemma limbs_val_lval : forall l, limbs_val l = lval l (Z.of_nat (length l)).
Proof. intros l. unfold lval. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L21007901678.5000006S1n2Hn". (* [comment removed for export] *)
Lemma lval_ext_limb : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pxs,(15.(0.&40.))Pys,(15.(0.&40.))Pn,$16.P,(17.=R1.)P,Pk,$18.P,(1;.R1.(1:.R3.))(5.$16.(1<.R6.R2.)(1<.R5.R2.))(5.$16.(22.R5.R3.)(22.R4.R3.))")
(* [comment removed for export] *).
Proof. intros xs ys n Hn HE. rewrite !lval_lseg0. apply lseg_ext; [lia|]. intros k _ Hk. apply HE. exact Hk. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L22954391803.6000008S1n1k2Hk". (* [comment removed for export] *)
Lemma limb32_skipn_eq : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pxs,(15.(0.&40.))Pys,(15.(0.&40.))Pn,$18.Pk,$18.P,(5.(15.(0.&40.))(23.(0.&40.)R2.R4.)(23.(0.&40.)R2.R3.))P,(19.R3.R2.)(5.$16.(1<.R6.R3.)(1<.R5.R3.))")
(* [comment removed for export] *).
Proof.
  intros xs ys n k E Hk. unfold limb32. replace k with (n + (k - n))%nat by lia.
  rewrite <- (nth_skipn n xs), <- (nth_skipn n ys), E. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma limb32_skipn : forall (xs : list word) n k, limb32 (skipn n xs) k = limb32 xs (n + k).
Proof. intros. unfold limb32. rewrite nth_skipn. reflexivity. Qed.


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L26836206051.49L36100449086.48000004008S2spS2sp". (* [comment removed for export] *)
Lemma sub_epilogue : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Praj,(0.&40.)Px8,(0.&40.)Px9,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Px18,(0.&40.)Px19,(0.&40.)Px20,(0.&40.)Px21,(0.&40.)Px22,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))P,(24.$4.R1.(21.(25.&40.R29.)+40.)(26.R2:.R23.R22.R21.R20.R1?.R1>.R1=.))P,(3.$4.R2.)P,(17.=(21.(25.&40.R2;.)+40.))(7.$4.Lms',$8.(:.(5.$8.R1.(;.(<.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R14.R13.R12.R11.R10.R?.R>.R=.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R7.(=.R2>.)R6.(>.(0.&40.))R5.(?.$4.)))(:.(10.(11.$12.)R5.R5.)(:.(13.$4.R5.R5.)(3.$4.R5.))))(;.(<.R16.(6.&40.(21.(25.&40.R2<.)+40.))R2;.R2:.R29.R28.R27.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R6.(6.&40.+209=0.)R5.(>.(0.&40.))R4.(?.$4.)))")
(* [comment removed for export] *).
Proof.
  intros until m. intros FR MI SP0. unfold sub_frame in FR.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 10 zstep.
  replace (Z_to_bv 64 (bv_unsigned sp - 64 + 64)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; lia). rewrite Z_to_bv_bv_unsigned.
  finish.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L36502023484.9L39145098449.900000<00HS2xs1n2Hn2HlS2xs1n2Hn2Hl". (* [comment removed for export] *)
Lemma u32arr_split_at : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Psegs,(15.$27.)Pm,P,(0.&40.)(2.(0.&8.))PA,$16.Pxs,(15.(0.&40.))Pn,$16.P,(28.R5.R4.R3.R2.)P,(17.=R2.)P,(17.R3.(29.(2:.(0.&40.)R4.)))(:.(28.R8.R7.R6.(2;.(0.&40.)(1:.R4.)R5.))(:.(28.R8.R7.(1>.R6.(1?.+4.R4.))(23.(0.&40.)(1:.R4.)R5.))(:.(5.$16.(29.(2:.(0.&40.)(2;.(0.&40.)(1:.R4.)R5.)))R4.)(5.$16.(29.(2:.(0.&40.)(23.(0.&40.)(1:.R4.)R5.)))(21.(29.(2:.(0.&40.)R5.))R4.)))))")
(* [comment removed for export] *).
Proof.
  intros segs m A xs n H Hn Hl. rewrite <- (firstn_skipn (Z.to_nat n) xs) in H. apply u32arr_app in H. destruct H as [H1 H2].
  rewrite length_firstn in H2. replace (Z.of_nat (Nat.min (Z.to_nat n) (length xs))) with n in H2 by lia.
  split; [exact H1|]. split; [exact H2|]. rewrite length_firstn, length_skipn. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L3370403632.13L37997145123.8L49735219075.8L51826142604.8L66760982176.7L955972261.8  00000D00R00l01@01T01bS3xs23xs31n2n12Hn2LFS3xs23xs31n2LFS3xs23xs31n2n12Hn2L22L32LFS3xs23xs31n2n12Hn2LFS3xs23xs31n2n12L22L3S3xs23xs31n2LF". (* [comment removed for export] *)
Lemma splice_facts : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Pxs2,(15.(0.&40.))Pxs3,(15.(0.&40.))Pn,$16.Pn1,$16.P,(:.(17.=R2.)(17.R2.R1.))P,(5.$16.(29.(2:.(0.&40.)R5.))R2.)P,(5.$16.(29.(2:.(0.&40.)R5.))(21.R3.R4.))(:.(5.$18.(2:.(0.&40.)(2<.(0.&40.)(2;.(0.&40.)(1:.R5.)R7.)R6.))(2:.(0.&40.)R7.))(:.(5.$16.(22.(2<.(0.&40.)(2;.(0.&40.)(1:.R5.)R7.)R6.)R4.)(1>.(22.R7.R5.)(1?.(20.+2.(1?.+20.R5.))(22.R6.(21.R4.R5.)))))Psegs,(15.$27.)Pm,P,(0.&40.)(2.(0.&8.))PA,$16.P,(28.R3.R2.R1.(2;.(0.&40.)(1:.R8.)R:.))P,(28.R4.R3.(1>.R2.(1?.+4.R9.))R:.)(28.R5.R4.R3.(2<.(0.&40.)(2;.(0.&40.)(1:.R:.)R<.)R;.))))")
(* [comment removed for export] *).
Proof.
  intros xs2 xs3 n n1 Hn L2 L3.
  assert (LF : length (firstn (Z.to_nat n) xs2) = Z.to_nat n) by (rewrite length_firstn; lia).
  split; [rewrite length_app, LF; lia|]. split.
  - rewrite (lval_split (firstn (Z.to_nat n) xs2 ++ xs3) n n1) by lia. f_equal.
    + unfold lval. rewrite firstn_app, LF, Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn by lia. f_equal. f_equal. lia.
    + f_equal. unfold lseg. rewrite skipn_app, LF, Nat.sub_diag, skipn_O, skipn_all2 by lia. reflexivity.
  - intros segs m A H1 H2. apply u32arr_app. split; [exact H1|]. rewrite LF. replace (4 * Z.of_nat (Z.to_nat n)) with (4 * n) by lia. exact H2.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m1 : mem) (X p1 n1 n lo : Z) (padX : word) (sX : Z) (xs1 ysv zsv : list word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Lms',$8.(9.(0.&40.)Lt0,(0.&40.)(9.(0.&40.)Lt1,(0.&40.)(9.(0.&40.)Lt2,(0.&40.)(9.(0.&40.)La1,(0.&40.)(9.(0.&40.)La2,(0.&40.)(9.(0.&40.)La3,(0.&40.)(9.(0.&40.)La4,(0.&40.)(9.(0.&40.)La5,(0.&40.)(9.(0.&40.)La6,(0.&40.)(9.(0.&40.)La7,(0.&40.)(9.(0.&40.)Lt3,(0.&40.)(9.(0.&40.)Lt4,(0.&40.)(9.(0.&40.)Lt5,(0.&40.)(9.(0.&40.)Lt6,(0.&40.)(9.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(9.$16.Lr,$16.(9.$16.Lsg',$16.(9.(15.(0.&40.))Lxs',(15.(0.&40.))(:.(5.$8.R13.(;.(<.O1=.O1<.O1;.O1:.R12.R11.R10.O19.O18.(6.&40.R3.)R?.R>.R=.R<.R;.R:.R9.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R8.R7.R6.R5.)O=.(=.O1=.)O<.(>.(0.&40.))R4.(?.$4.)))(:.(10.(2=.(2>.$16.$16.)(2?.$16.$16.O9.(1>.O9.(1?.+4.O8.)))(2=.(2>.$16.$16.)(2?.$16.$16.O:.(1>.O:.+10.))(2=.(2>.$16.$16.)(2?.$16.$16.(21.(25.&40.O1<.)+:0.)(25.&40.O1<.))(11.(2>.$16.$16.)))))O;.R4.)(:.(13.$4.O;.R4.)(:.(3.$4.R4.)(:.(30.$4.R4.O6.(25.&40.O1<.))(:.(24.$4.R4.O:.(2=.$31.(32.(6.&40.O9.))(2=.$31.(33.(6.&40.R2.))(2=.$31.(33.(6.&40.O8.))(2=.$31.(34.O5.)(11.$31.))))))(:.P,(17.+1.O8.)(28.$4.R5.O9.R2.)(:.(5.$18.(2:.(0.&40.)R1.)(2:.(0.&40.)O3.))(35.(:.(5.$16.R3.=)(:.(5.$16.R2.+1.)(5.$16.(1>.(22.R1.O8.)(22.O1.O7.))(1>.(22.O2.O7.)(1?.(20.+2.(1?.+20.O7.))(1=.O3.O7.O8.))))))(:.(5.$16.R3.$36.)(:.(5.$16.R2.O4.)(37.(1>.(22.O2.O7.)(1?.(20.+2.(1?.+20.O7.))(1=.O3.O7.O8.)))(22.O1.O7.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Section TailWalk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem).
  Variables (X p1 n1 n lo sX : Z) (padX : word) (xs1 : list word).
  Variables (Aa pA' nA' : Z) (sA' pdA' : word) (ysv : list word).
  Variables (Ba pB' nB' : Z) (sB' pdB' : word) (zsv : list word).
  Hypothesis CX1 : rw_cells usegs m1 X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX].
  Hypothesis CA1 : rw_cells usegs m1 Aa [C8 (Z_to_bv 64 pA'); C2 sA'; C2 (Z_to_bv 64 nA'); C4 pdA'].
  Hypothesis CB1 : rw_cells usegs m1 Ba [C8 (Z_to_bv 64 pB'); C2 sB'; C2 (Z_to_bv 64 nB'); C4 pdB'].
  Hypothesis FR1 : rw_cells usegs m1 (bv_unsigned sp - 64) (sub_frame ra s0 s1 s2 s3 s4 s5 s6).
  Hypothesis ST1 : stk usegs m1 lo (bv_unsigned sp - 64).
  Hypothesis MI1 : mem_inv usegs m1.
  Hypothesis XB : 0 < X /\ X + 16 <= 2^64 /\ X mod 8 = 0.
  Hypothesis AB : 0 <= Aa /\ Aa + 16 <= 2^64.
  Hypothesis BB : 0 <= Ba /\ Ba + 16 <= 2^64.
  Hypothesis XS : X + 16 <= lo \/ bv_unsigned sp <= X.
  Hypothesis Hn : 0 <= n <= n1 /\ n1 <= 10000.
  Hypothesis LEN1 : Z.of_nat (length xs1) = n1.
  Hypothesis SLO : lo <= bv_unsigned sp - 160.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis XV : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "P,(17.+1.Vn1,)(:.(28.$4.Vm1,Vp1,Vxs1,)(:.(37.=Vp1,)(:.(5.$16.(38.Vp1,+10.)=)(:.(17.(1>.Vp1,(1?.+4.Vn1,))Vlo,)(35.(17.(1>.VX,+10.)Vp1,)(17.(1>.Vp1,(1?.+4.Vn1,))VX,))))))")
(* [comment removed for export] *).
  Hypothesis AV : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "P,(17.+1.Vn,)(:.(39.$4.Vm1,VpA',(3:.Vysv,))(:.(17.Vn,(29.(2:.(0.&40.)Vysv,)))(:.(35.(:.(5.$16.VpA',Vp1,)(5.(15.(0.&40.))Vysv,Vxs1,))(35.(17.(1>.VpA',(1?.+4.(29.(2:.(0.&40.)Vysv,))))Vp1,)(17.(1>.Vp1,(1?.+4.(29.(2:.(0.&40.)Vxs1,))))VpA',)))(:.(37.=VpA',)(:.(5.$16.(38.VpA',+4.)=)(35.(17.(1>.VpA',(1?.+4.(29.(2:.(0.&40.)Vysv,))))Vlo,)(17.(25.&40.Vsp,)VpA',)))))))")
(* [comment removed for export] *).
  Hypothesis BV : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "P,(17.+1.Vn,)(:.(39.$4.Vm1,VpB',(3:.Vzsv,))(:.(17.Vn,(29.(2:.(0.&40.)Vzsv,)))(:.(35.(:.(5.$16.VpB',Vp1,)(5.(15.(0.&40.))Vzsv,Vxs1,))(35.(17.(1>.VpB',(1?.+4.(29.(2:.(0.&40.)Vzsv,))))Vp1,)(17.(1>.Vp1,(1?.+4.(29.(2:.(0.&40.)Vxs1,))))VpB',)))(:.(37.=VpB',)(:.(5.$16.(38.VpB',+4.)=)(35.(17.(1>.VpB',(1?.+4.(29.(2:.(0.&40.)Vzsv,))))Vlo,)(17.(25.&40.Vsp,)VpB',)))))))")
(* [comment removed for export] *).

  Let TPOST := sub_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 X p1 n1 n lo padX sX xs1 ysv zsv.

  Local Ltac2 Set LiaOrc.tbl := fun () => "01A0@L10067647165.10 L10509129601.3  L11803680532.9  L11813812081.0  L13515622303.5  L13543837870.3  L13768857241.7  L14735152929.98 L1519907469.133 L1519907469.90  L1519907469.95  L1521876082.144 L16256852529.83 L22550422114.115L23100341967.115L2416455492.112 L2424960062.3   L24364998578.116L24897143244.3  L24897143244.4  L29969751007.86 L29975665505.92 L32584855577.142L32692044090.98 L34563290702.98 L34694833314.6  L35435638487.8  L35925021705.136L35925021705.93 L35925021705.98 L36953018935.2  L36953018935.3  L37984538148.9  L38037054623.5  L38042866488.133L38042866488.90 L38042866488.95 L38045097415.144L38770676052.98 L39165210342.112L39637022374.9  L40231054904.132L40231054904.89 L40231054904.94 L40231054967.143L40616120490.10 L43164748215.142L44482837595.8  L44631303542.3  L45493589040.136L45493589040.98 L46266856490.4  L49931595771.5  L50127901390.98 L51826211300.3  L51828156728.112L51834577566.113L52257865806.98 L5287801372.5   L53513324069.116L55345850227.113L57069973797.114L58925199741.82 L58978557631.98 L58980376192.116L59227895449.7  L59310676298.3  L59435147825.83 L60376076319.3  L60435344950.98 L61145405211.142L61931785385.114L62459982354.3  L63102239738.90 L63102239738.95 L63105734064.116L64529515421.9  L65510276341.3  L811966425.6    L8928379077.90  L8928379077.95  00000O00X00o01001D01Q01d03904H04d05@06W07708008X09F09O0;60;:0;>0;f0<N0=B0=f0?D0?[0@70AT0B>0Bh0Bi0Bj0CO0Cc0D[0Dl0E=0F=0F^0HE0Hh0IY0Ic0Im0Jf0K80Kl0L?0LK0NV0OW0Ob0P80PY0Pb0QP0R>0R_0Rk0TL0U90VR0Wd0X_0Ye0Z80ZC0Zc0Zl0\@0]A0^i0_20_<0_F0_n0`H0`Q0`b0`o0a<S2sp1X2p12n11n2lo2XS2Hn3SLO3XS1S2n11n2HnS2sp2p12n11n2lo3SLO3P1CSS2sp2lo3pA'3ysv4ASTKS2c'4Hc'03Hc'S2sp1X2p12n11n2Hn1xS2sp1X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn4LEN13SLO3SPB3P103P1C4ALEN3AP04BLEN3BP0S2sp1X2p11n2lo3xs13pA'3ysv3pB'3zsv2XB3SLO3LO03SPB3P103AP03BP03xs24LEN23xsf4LENzS2sp1X2lo3xs12XB3SLO3LO03SPBS2sp1X2lo3xs12XB3SLO3LO03SPBS2sp1X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB3SLO3LO03SPB3P103AP03BP03xs24LEN23xs34LEN34LENFS2sp1X2p13xs13pA'3ysv2Ba3pB'3zsvS2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv2Hn2N01c3xs22Hc4LEN22KCS2sp1X2p11n3xs13pA'3ysv3pB'3zsv3xs24LEN2S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv2Hn3xs24LEN2S2n11n2HnS2sp1X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS4LEN13SLO3LO03SPB3P103P1C4ALEN3AP04BLEN3BP03xs24LEN23LLO3LHIS2p1S2p1S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv2Hn2N0S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv2Hn2N0S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv3xs24LEN23xs34LEN3S2sp1X2p12lo3xs13pA'3ysv3pB'3zsv3SLOS2sp2m11X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn4LEN13SLO2AV2BV3SPB3P103P1C4ALEN3AP04BLEN3BP0S1n3ysv3zsv3xs24VAL22R2S2n11n3xs14LEN13xs24LEN23LHIS2sp1X2p11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS3SLO3SPB3P103AP03BP03xs24LEN23xsf4LENz2HB5Ha_st5Hl_stS2sp1X2lo3xs12XB2XS3SLO3SPB2HB5Ha_st5Hl_stS2sp1X2lo3xs12XB2XS3SLO3SPB2HB5Ha_st5Hl_stSSS2n11n3xs14LEN13xs24LEN23LHI3xs34LEN3S2sp2lo3pB'3zsv4BSTKS2sp1X2p11n2lo3xs13pA'3ysv3pB'3zsv3SLO3xs24LEN23xsf4LENzS2sp1X2lo3xs13SLOS2sp1X2lo3xs13SLOS2sp1X2p12n11n2lo3xs13pA'3ysv3pB'3zsv3SLO3xs24LEN23xs34LEN34LENFS2sp1X2p13xs13pA'3ysv3pB'3zsv3P10S2sp2m11X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn4LEN13SLO2AV2BV3SPB3P103P1C4ALEN3AP04BLEN3BP03xs24LEN2S2n11n3xs13xs23xs34VAL35LSEG32R32RLS2sp1X2p11n3xs13pA'3ysv3pB'3zsv3xs24LEN23xsf4LENzS2sp1X3xs1S2sp1X3xs1S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv3xs24LEN23xs34LEN34LENFS1X2p12n11n2Hn3XS1S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv3xs24LEN23xs34LEN3S2sp2p12n11n2lo3P1CS2c'4Hc'12KCS2sp2m11X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn4LEN13SLO2XV3SPB3P104PAL13P1C4ALEN3AP04APAL4BLEN3BP04BPAL3xs24LEN23xsf4LENz2HB5Ha_st5Hl_stS2sp1X2p12n12lo3xs12XB4LEN13SLO3SPB3XVF2N13P1C3XS12HB5Ha_st5Hl_stS2p11n1q2HqS2n13xs14LEN13xs24LEN2S2sp1X2p13xs13pA'3ysv3pB'3zsv3AP0S2n11n2HnS2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv2Hn3xs24LEN2S2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv2Hn3xs24LEN2S2sp1X2p13xs13pA'3ysv3pB'3zsv3BP0S2sp3SPA3SPBS2sp1X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn4LEN13SLO3SPB3P103P1C4ALEN3AP03BP03xs24LEN23LLO3LHIS2sp1X2p11n3xs13pA'3ysv3pB'3zsv1c3xs22Hc4LEN2S2sp1X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2Hn4LEN13SLO3SPB3P103P1C3AP03BP03xs24LEN23LLO3LHIS2sp2m11X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn4LEN13SLO3LO02XV2AV2BV3SPB3XVF2N0S2sp1X2p12lo3xs13pA'3ysv3pB'3zsv2XB3SLO3LO03SPB3P103AP03BP0S2sp1X2p11n2lo3xs13pA'3ysv3pB'3zsv2XB3SLO3LO03SPB3P103AP03BP03xs24LEN2S2sp1X2p12n11n2Hn1xS2n12N13H1'S2sp1X2p13xs12Aa3pA'3ysv3pB'3zsvS2p11q2HqS2sp2m11X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2XS2Hn3SLO2XV2AV2BV3SPB3P103P1C4ALEN4BLENS2sp1X2p12n11n3xs13pA'3ysv3pB'3zsv3xs24LEN22c'3xs34LEN34LENF4Hc'1S2sp2m11X2p12n11n2lo3xs13pA'3ysv3pB'3zsv2XB2Hn4LEN13SLO2AV2BV3SPB3P103P1C4ALEN3AP04BLEN3BP03xs24LEN23LHIS2n11n2HnS2sp1X3xs1S2sp1X3xs1S2sp1X2p11n3xs13pA'3ysv3pB'3zsv3xs24LEN2S2sp2p12n11n2lo2Hn3SLO3P1CS2n11n2HnS2p12n11n3xs23LLOS2sp1X2n13xs1S2sp1X2n13xs1". (* [comment removed for export] *)
  #[using="pA' nA' sA' pdA' pB' nB' sB' pdB' CX1 CA1 CB1 FR1 ST1 MI1 XB XS Hn LEN1 SLO LO0 SPA XV AV BV"] Lemma sub_tail_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Ps3j,(0.&40.)Ps2j,(0.&40.)Praj,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5j,(0.&40.)Ps6j,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)(7.$4.VTPOST,(;.(<.R11.(6.&40.(21.(25.&40.Vsp,)+40.))Vgp,Vtp,R10.R?.R>.(6.&40.VX,)(6.&40.Vn,)(6.&40.Vp1,)(6.&40.VAa,)(6.&40.VBa,)R;.R:.R9.R8.R7.R12.R13.(6.&40.(1?.+4.Vn,))R6.R5.Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(6.&40.+20974.)Vfc,(>.(0.&40.))Vm1,(?.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (munch_refl [(p1, p1 + 4 * n1); (X, X + 16); (bv_unsigned sp - 160, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold sub_frame in FR1.
    (* [comment removed for export] *)
    assert (XV' : exists xv, (1 <= n1 -> u32arr usegs m1 p1 xv) /\ xv = xs1 /\ (1 <= n1 -> 0 < p1 /\ p1 mod 16 = 0 /\ p1 + 4 * n1 <= lo /\ (X + 16 <= p1 \/ p1 + 4 * n1 <= X))).
    { exists xs1. split; [intros H1; exact (proj1 (XV H1))|]. split; [reflexivity|]. intros H1; exact (proj2 (XV H1)). }
    ddestruct XV' as (xv & PARR1 & EXV & XVF).
    (* [comment removed for export] *)
    assert (ZERO : forall mz (xv' : list word) (c1 c2 c3 : cell) (ya1 ya2 : word), n = 0 -> xv' = xs1 ->
      rw_cells usegs mz X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX] ->
      rw_cells usegs mz (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk usegs mz lo (bv_unsigned sp - 64) -> mem_inv usegs mz -> (1 <= n1 -> u32arr usegs mz p1 xv') ->
      (1 <= n1 -> 0 < p1 /\ p1 + 4 * n1 <= lo /\ (X + 16 <= p1 \/ p1 + 4 * n1 <= X)) ->
      munch [(p1, p1 + 4 * n1); (X, X + 16); (bv_unsigned sp - 160, bv_unsigned sp)] m1 mz -> wmono usegs m1 mz ->
      evt usegs TPOST
        (MS (mkR raj (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 n)
                (Z_to_bv 64 p1) ya1 ya2 (Z_to_bv 64 n) a4 a5 a6 a7 s2j s3j (Z_to_bv 64 (4 * n))
                s5j s6j s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20980) fc None mz (seg_rom usegs))).
    { intros mz xv' c1 c2 c3 ya1 ya2 N0 EXV' CXz FRz STz MIz XAz XFz MU' WM'. subst n. subst xv'.
      clear MU WM XV AV BV. rename MU' into MU. rename WM' into WM.
      destruct (Z.le_gt_cases 1 n1) as [N1|N1]; [specialize (XAz N1); ddestruct (XFz N1) as (P10 & P1C & XS1)| clear XAz XFz].
      all: zstep; pose proof (unsigned_lit (bv_unsigned sp - 64) ltac:(clear - SPB SLO LO0; lia)) as SPE.
      all: call U_core_sub_null; [exact MIz| rewrite SPE; exact STz| rewrite SPE; clear - SLO; lia| reflexivity|].
      all: match goal with H : stk usegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ =>
             rewrite SPE in H; try clear STz; rename H into STz end.
      all: zstep; if_true; zstep; zstep; zstep.
      all: call sub_epilogue; [exact FRz| assumption| lia|].
      all: apply evt_done; unfold TPOST, sub_tail_post; deexists 15; dexists 0, 1, xs1.
      all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
      all: split; [release_frame FRz STz (bv_unsigned sp); exact STz|].
      all: split. 1,3: exact CXz. all: split. 1: intros _; exact XAz. 2:{ intros H1'. exfalso. clear - H1' N1. lia. }
      all: split; [reflexivity|].
      all: left; split; [reflexivity|]; split; [reflexivity|]; rewrite !lval_0, lval_lseg0; change (2 ^ (32 * 0)) with 1; lia. }
    zstep. zstep. zstep.
    destruct (Z.eq_dec n 0) as [N0|N0].
    { eapply ZERO; try eassumption; try reflexivity; try exact (C1 (Z_to_bv 8 0)). intros H1. ddestruct (XVF H1) as (Q1 & _ & Q2 & Q3). auto. }
    (* [comment removed for export] *)
    subst xv. specialize (PARR1 ltac:(lia)). ddestruct (XVF ltac:(lia)) as (P10 & PAL1 & P1C & XS1). zstep.
    ddestruct (AV ltac:(lia)) as (ABY & ALEN & ADJ & AP0 & APAL & ASTK).
    ddestruct (BV ltac:(lia)) as (BBY & BLEN & BDJ & BP0 & BPAL & BSTK).
    pose proof U_mpi_core_sub_spec as SPs. unfold mpi_core_sub_stmt, U_MPI_CORE_SUB in SPs.
    eapply evt_cut; [eapply SPs with (X := p1) (xs := xs1) (A := pA') (ys := ysv) (B := pB') (zs := zsv) (n := n) (lo := lo); clear SPs | clear SPs].
    all: rewrite ?(unsigned_lit (bv_unsigned sp - 64)) by lia.
    { exact PARR1. } { exact ABY. } { exact BBY. } { lia. } { lia. } { exact ALEN. } { exact BLEN. }
    { destruct ADJ as [[-> ->]|D]; [left; split; reflexivity| right; exact D]. }
    { destruct BDJ as [[-> ->]|D]; [left; split; reflexivity| right; exact D]. }
    { clear - PAL1; apply Z.mod_divide in PAL1; [|lia]; apply Z.mod_divide; [lia|]; destruct PAL1 as [q Hq]; exists (4 * q); lia. }
    { exact APAL. } { exact BPAL. } { lia. } { lia. } { lia. } { exact ST1. } { unfold MPI_CORE_SUB_STACK. lia. }
    { clear - SPA SPB SLO; lia. } { left. lia. } { clear - ASTK; lia. } { clear - BSTK; lia. } { exact MI1. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    clear ABY BBY CA1 CB1 ADJ BDJ ASTK BSTK.
    unfold mpi_core_sub_post, MPI_CORE_SUB_STACK. cbv beta. intros ms' PO.
    ddestruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & c & xs2 & E & MUc & WMc & MI2 & Ey3 & Hc & XA2 & LEN2 & SK2 & VAL2 & ST2).
    subst ms' y3. rewrite ?(unsigned_lit (bv_unsigned sp - 64)) in ST2, MUc by lia.
    replace (ret_pc (Z_to_bv 64 133508)) with (Z_to_bv 64 133508) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (CX2 : rw_cells usegs m2 X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX]).
    { eapply rw_cells_transport; [exact CX1| exact MUc| exact WMc|]. cbn. clear - XS XS1 Hn SLO. lia. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR1| exact MUc| exact WMc|]. cbn. clear - P1C Hn SLO SPB. lia. }
    assert (MU2 : munch [(p1, p1 + 4 * n1); (X, X + 16); (bv_unsigned sp - 160, bv_unsigned sp)] m1 m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. intros x. cbn. clear - Hn. lia. }
    assert (WM2 : wmono usegs m1 m2) by (eapply wmono_trans; [exact WM| exact WMc]).
    clear CX1 FR1 ST1 MU WM MUc WMc MI1.
    assert (LSEG2 : lseg xs2 n n1 = lseg xs1 n n1).
    { apply lseg_ext; [lia|]. intros k Hk _. eapply limb32_skipn_eq; [exact SK2| exact Hk]. }
    (* [comment removed for export] *)
    assert (OKEXIT : forall mz (xsf : list word) (za0 za2 : word) (za1 za3 zra q0 q1 q2 q7 q8 q9 q10 q11 q12 q13 q14 : word),
      rw_cells usegs mz X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX] ->
      rw_cells usegs mz (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk usegs mz lo (bv_unsigned sp - 64) -> mem_inv usegs mz -> u32arr usegs mz p1 xsf -> length xsf = length xs1 ->
      munch [(p1, p1 + 4 * n1); (X, X + 16); (bv_unsigned sp - 160, bv_unsigned sp)] m1 mz -> wmono usegs m1 mz ->
      lval xsf n1 + lval zsv n = lval ysv n + 2 ^ (32 * n) * lseg xs1 n n1 ->
      evt usegs TPOST
        (MS (mkR zra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp q0 q1 q2 (Z_to_bv 64 X) (Z_to_bv 64 n)
                za0 za1 za2 za3 q7 q8 q9 q10 s2j s3j (Z_to_bv 64 (4 * n))
                s5j s6j s7 s8 s9 s10 s11 q11 q12 q13 q14)
            F (Z_to_bv 64 0x209c4) fc None mz (seg_rom usegs))).
    { intros mz xsf za0 za2 za1 za3 zra q0 q1 q2 q7 q8 q9 q10 q11 q12 q13 q14 CXz FRz STz MIz XAz LENz MUz WMz VALz. clear MU2 WM2 CX2 FR2 ST2 XA2 PARR1.
      rename MUz into MU. rename WMz into WM.
      zstep. zstep. zstep.
      call sub_epilogue; [exact FRz| assumption| lia|].
      apply evt_done; unfold TPOST, sub_tail_post; deexists 15; dexists 0, 1, xsf.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split; [release_frame FRz STz (bv_unsigned sp); exact STz|].
      split; [assumption|]. split; [intros _; assumption|]. split; [exact LENz|].
      left. split; [reflexivity|]. split; [reflexivity|]. exact VALz. }
    zstep. if_cases KC; zify_cond KC.
    { (* [comment removed for export] *) subst c. eapply OKEXIT; try eassumption.
      rewrite (lval_split xs2 n n1), <- LSEG2 by lia. clear - VAL2. nia. }
    (* [comment removed for export] *)
    assert (c = 1) as -> by lia. clear KC Hc.
    destruct (u32arr_split_at _ _ _ _ n XA2 ltac:(lia) ltac:(lia)) as (XLO & XHI & LLO & LHI).
    zstep. zstep. zstep.
    zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|].
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; [rewrite ?unsigned_lit in K2 by lia; lxu_pnull K2|].
    zstep. rewrite zx16_small by lia. zstep. zstep. zstep.
    pose proof U_mpi_core_sub_int_spec as SPi. unfold mpi_core_sub_int_stmt, U_MPI_CORE_SUB_INT in SPi.
    eapply evt_cut; [eapply SPi with (X := p1 + 4 * n) (xs := skipn (Z.to_nat n) xs2) (A := p1 + 4 * n) (ys := skipn (Z.to_nat n) xs2) (n := n1 - n) (c := 1); clear SPi | clear SPi].
    { exact XHI. } { apply u32arr_ro. exact XHI. } { clear - Hn; lia. } { clear; lia. } { clear - LHI LEN2 LEN1 Hn; lia. } { clear - LHI LEN2 LEN1 Hn; lia. }
    { left. split; reflexivity. } { clear - PAL1; apply Z.mod_divide in PAL1; [|lia]; apply Z.mod_divide; [lia|]; destruct PAL1 as [q Hq]; exists (4 * q + n); lia. }
    { clear - PAL1; apply Z.mod_divide in PAL1; [|lia]; apply Z.mod_divide; [lia|]; destruct PAL1 as [q Hq]; exists (4 * q + n); lia. }
    { lia. } { lia. } { exact MI2. } { f_equal; lia. } { f_equal; lia. } { reflexivity. } { f_equal; lia. }
    unfold mpi_core_sub_int_post. cbv beta. intros ms' PO.
    ddestruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & c' & xs3 & E & MUd & WMd & MI3 & Ez3 & Hc'0 & Hc' & XA3 & LEN3 & SK3 & VAL3).
    subst ms' z3.
    replace (ret_pc (Z_to_bv 64 133560)) with (Z_to_bv 64 133560) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (p1 + 4 * n + 4 * (n1 - n)) with (p1 + 4 * n1) in MUd by lia.
    assert (CX3 : rw_cells usegs m3 X [C8 (Z_to_bv 64 p1); C2 (Z_to_bv 64 sX); C2 (Z_to_bv 64 n1); C4 padX]).
    { eapply rw_cells_transport; [exact CX2| exact MUd| exact WMd|]. cbn. clear - XS XS1 Hn SLO. lia. }
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR2| exact MUd| exact WMd|]. cbn. clear - P1C Hn SLO SPB. lia. }
    assert (ST3 : stk usegs m3 lo (bv_unsigned sp - 64)).
    { eapply stk_transport_disjoint; [| exact MUd| exact WMd|]; [exact ST2|]. cbn. clear - P1C Hn SLO. lia. }
    assert (XLO3 : u32arr usegs m3 p1 (firstn (Z.to_nat n) xs2)).
    { eapply u32arr_transport; [exact XLO| exact MUd| exact WMd|]. cbn. clear - Hn LLO. lia. }
    assert (LEN3' : Z.of_nat (length xs3) = n1 - n) by (clear - LEN3 LHI LEN2 LEN1; lia).
    ddestruct (splice_facts xs2 xs3 n n1 ltac:(clear - Hn; lia) ltac:(clear - LEN2 LEN1; lia) LEN3') as (LENF & VALF & JOIN).
    pose proof (JOIN _ _ _ XLO3 XA3) as XA3'. clear JOIN. rewrite LEN2 in LENF.
    assert (MU3 : munch [(p1, p1 + 4 * n1); (X, X + 16); (bv_unsigned sp - 160, bv_unsigned sp)] m1 m3).
    { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [| exact MUd]. intros x. cbn. clear - Hn. lia. }
    assert (WM3 : wmono usegs m1 m3) by (eapply wmono_trans; [exact WM2| exact WMd]).
    assert (LSEG3 : lval (skipn (Z.to_nat n) xs2) (n1 - n) = lseg xs1 n n1) by (rewrite <- LSEG2; reflexivity).
    clear CX2 FR2 ST2 XLO XHI MU2 WM2 MUd WMd MI2 XLO3.
    pose proof (lval_range xs3 (n1 - n) ltac:(clear - Hn; lia)) as R3. pose proof (lval_range xs2 n ltac:(clear - Hn; lia)) as R2.
    assert (Hc'1 : 0 <= c' <= 1) by (clear - Hc' Hc'0; lia). clear Hc' Hc'0.
    zstep. zstep. zstep. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by lia.
    all: try (assert (c' = 0) as -> by (clear - KC Hc'1; lia); eapply OKEXIT; try eassumption; rewrite VALF; clear - VAL2 VAL3 LSEG3; nia).
    (* [comment removed for export] *)
    rename MU3 into MU. rename WM3 into WM.
    call sub_epilogue; [exact FR3| assumption| lia|].
    apply evt_done; unfold TPOST, sub_tail_post; deexists 15; dexists MBEDTLS_ERR_MPI_NEGATIVE_VALUE, sX, (firstn (Z.to_nat n) xs2 ++ xs3).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [release_frame FR3 ST3 (bv_unsigned sp); exact ST3|].
    split; [assumption|]. split; [intros _; assumption|]. split; [exact LENF|].
    right. split; [reflexivity|]. split; [reflexivity|].
    pose proof (lseg_range xs1 n n1 ltac:(clear - Hn; lia)) as RL.
    assert (c' = 1) as -> by (clear - Hc'1 KC; lia).
    assert (Z0 : lseg xs1 n n1 = 0) by (clear - VAL3 LSEG3 R3 RL; lia).
    rewrite Z0, Z.mul_0_r, Z.add_0_r. clear - VAL2 R2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End TailWalk.

Section Tail.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr usegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (dX dA dB : mpd) (lo : Z).
  Hypothesis HH : HEAP usegs L HI h LB m mo.
  Hypothesis MX : mpd_at usegs m LB dX.
  Hypothesis MA : opnd_at usegs m LB (bv_unsigned sp) dA.
  Hypothesis MB : opnd_at usegs m LB (bv_unsigned sp) dB.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis SAB : mpd_sep dA dB.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis CRA : client_range L LB lo (md_addr dA) 16.
  Hypothesis CRAL : md_own dA = LHeap -> client_range L LB lo (md_p dA) (4 * md_n dA).
  Hypothesis CRB : client_range L LB lo (md_addr dB) 16.
  Hypothesis CRBL : md_own dB = LHeap -> client_range L LB lo (md_p dB) (4 * md_n dB).
  Hypothesis XW : mpd_writable L LB (bv_unsigned sp) (heap_top usegs L HI h) dX.
  Hypothesis XLS : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis SLO : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).

  Let POST := mpi_binop_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB dX (sub_abs_R LB dX dA dB) lo m mo.
  Let FRAME := sub_frame ra s0 s1 s2 s3 s4 s5 s6.

  (* [comment removed for export] *)
  Definition sub_C1_stmt (n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs_C ()) "Ps5j,(0.&40.)Ps3j,(0.&40.)Ps2j,(0.&40.)Pm1,P,(0.&40.)(2.(0.&8.))Pmo1,$3;.Ph1,(3<.$4.VL,VHI,)PLB1,(15.$3=.)Pxs1,(15.(0.&40.))Pp1,$16.Pn1,$16.Pown1,$3>.Praj,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps6j,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)ZdX1,$3?.(40.(41.VdX,)(42.VdX,)R12.R13.R14.(43.VdX,)R11.)P,(44.(45.VdB,)(46.VdB,)O1.)P,(17.O1.(46.VdA,))P,(3.$4.R1;.)P,(30.$4.R1<.Vlo,(21.(25.&40.Vsp,)+40.))P,(24.$4.R1=.(21.(25.&40.Vsp,)+40.)VFRAME,)P,(47.$4.VL,VHI,R1<.R1;.R1>.R1=.)P,(5.$16.(48.$4.VL,VHI,R1=.)(48.$4.VL,VHI,Vh,))P,(49.Vmo,R1?.)P,(4:.$4.VL,R21.)P,(4;.$4.R22.R1?.R:.)P,(4<.(5.$3>.R1<.$4=.))P,(4>.VLB,VdX,R21.R<.)P,Pb,$3=.P,(4?.$3=.R1.(50.R>.))(35.(4?.$3=.R2.(50.VdX,))(4<.(4?.$3=.R2.VLB,)))P,(51.$4.VL,VLB,(25.&40.Vsp,)(52.VdX,)Vm,R26.)P,P,(4<.(5.$3?.VdX,VdA,))(53.$4.R28.R25.(25.&40.Vsp,)VdA,)P,P,(4<.(5.$3?.VdX,VdB,))(53.$4.R29.R26.(25.&40.Vsp,)VdB,)P,(5.$16.R23.(54.(46.VdX,)(46.VdA,)))P,Pk,$18.P,(19.(1:.O1.)R1.)P,(1;.R2.(1:.(46.VdA,)))(5.$16.(1<.R29.R3.)(1<.(45.VdA,)R3.))P,P,(5.$3?.VdX,VdA,)Pk,$18.P,(1;.R1.(1:.O1.))(5.$16.(1<.R2:.R2.)(1<.(45.VdA,)R2.))P,P,(5.$3?.VdX,VdB,)Pk,$18.P,(1;.R1.(1:.O1.))(5.$16.(1<.R2;.R2.)(1<.(45.VdB,)R2.))P,Pk,$18.P,(19.(1:.(46.VdA,))R1.)P,(1;.R2.(1:.R29.))(5.$16.(1<.R2<.R3.)=)(55.$4.R2=.VPOST,(;.(<.R26.(6.&40.(21.(25.&40.Vsp,)+40.))Vgp,Vtp,R25.R24.R23.(6.&40.(41.VdX,))(6.&40.O1.)(6.&40.R29.)(6.&40.(41.VdA,))(6.&40.(41.VdB,))R20.R1?.R1>.R1=.R1<.R2?.R30.(6.&40.(1?.+4.O1.))R31.R1;.Vs7,Vs8,Vs9,Vs10,Vs11,R1:.R19.R18.R17.)VF,(6.&40.+20974.)Vfc,(>.(0.&40.))R2>.(?.$4.)))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01D0@L11351096470.14 L11351197600.13 L11357518363.9  L11483215692.2  L11732592900.6  L13296942291.186L13299025639.2  L13969895251.5  L14739578793.8  L159781158.2    L16391240856.3  L17045064434.5  L19028989642.174L19617510420.15 L21682153356.4  L217313293.9    L23188028534.5  L23709070179.9  L23917438199.2  L2426952441.2   L24897143244.3  L27839572960.5  L28082072438.6  L29428324939.4  L29971684470.4  L3228313176.10  L33099413492.2  L34067280200.6  L34566920600.6  L34573829616.10 L34573829616.8  L36352558489.4  L36950922632.2  L36953265544.2  L36953314696.2  L38479858882.5  L38538305444.6  L44451007663.3  L46238161847.9  L46244439564.13 L46244584762.14 L47115871883.10 L51794547071.3  L51794627208.186L52101694457.9  L52101765134.11 L52101785646.9  L52108071704.3  L52616107219.177L53297280983.2  L54392012715.10 L54398102733.9  L5524831100.2   L5527026534.6   L5527026534.7   L5711078758.5   L57355402471.2  L57801194132.8  L58007148250.7  L58806496252.6  L59308661201.9  L59308874064.5  L59308874064.8  L59310643530.6  L59314873579.11 L59314873579.16 L60376076319.3  L61310881898.5  L64081407397.6  L64822708246.2  L65500220205.174L65502163868.169L65575152201.5  L65575152201.9  L66963266466.5  L7552954281.8   L772750287.169  L8096778074.5   L8097008716.7   L8102950907.4   L8103103427.7   L8103103427.8   L8103103693.11  L8103327610.8   00000a01J01j02202I03<03D03U04104904B04T05Q06_06l07=07S07`07h07o08908F08]08k09809909A09T09k0:G0:`0:l0:m0:n0:o0;A0;X0;a0<A0<j0=[0>90>B0>f0?D0?d0@B0@J0A40A<0A\0B60B=0BQ0Bh0C70C?0CZ0D40DF0D^0Dm0EG0El0FH0FX0Fa0G70GH0GP0Go0HN0H_0I30IB0I]0JV0Jc0K40K@0KV0Kl0LN0LfS1L3HLS2sp2lo2pA2ys3SLO3ACL3xs12p12n14LEN13ASP2PCS1L2nA2pA2ys3xs12p12n14LEN14LENA2PI2I02I1S2nA2pA2ys3xs12p14LENA1H2n14LEN1S2nB3NB1S2nB2pB2zs4LENB3NB13BB2S2sp1X2nX2Aa2nA2ys2Ba2zs3xs12n13SPB2X02A02B02XB3N11S2n13N11S1L3HLS2sp2lo3SLOS1L2lo3ACL3xs12p12n14LEN12PCS2nA3NA1S2pB1q2HqS2nA2ys1n3NLE4LENAS1L3HLS2sp2lo1X2nX2Aa2nA2ys2Ba2zs3SLO3ACL3xs13SPB2X02A02B02XBS1X2sX2nX2pX3xs04padX4ownX2Aa2sA2nA2pA2ys4padA4ownA1D2Ba2sB2nB2pB2zs4padB4ownBS1X3XAL2X02XBS2nX2nA2n12N13NRAS3xs12n14LEN13xs'4LENfS2nX2nA2n12N1S2nA3NA1S1n3N1'S2p12pA2pBS2p12n11q1k1DS2nA2pA2ys4LENA3NA13AB2S1L2lo3ACL3ACPS2nB1n3SB12NZFS2n13NR1S1L2lo3ACL2p12n12PCS2nA2pA2ys4LENA3NA13AB2S2nX2nA1n3xs12n12N14LEN13SB1S2nX1n3xs12n13NLE2N14LEN1S2p12n11a2WaSSSS2nB2zs1n4LENB3SB1S2nB2pB2zs4LENB3NB13BB2S2pA1q2HqS2nB2pB2zs3xs12p14LENB1H2n14LEN1S1L2nB2pB2zs3xs12p12n14LEN14LENB2PI2I02I1S1L3HLS2sp2lo2pB2zs3SLO3ACL3xs12p12n14LEN13BSP2PCS2nX2nA2nB1n2n13NLE2N13NR13SB1S1k2K02KpS2sp1X2nX2Aa2nA2ys2Ba2zs3xs12XB1k2HkS1L3HLS2sp2lo3SLO3ACL3DHI1a2HdS1L3HLS2sp2lo3SLO3ACL1a1q1k1R2LQS1L3HLS2sp2lo3SLO3ACL3DHI1a2C1S2sp1a1CS1L2HI2sp1h1X2nX2Aa2nA2ys2Ba2zs3xs12XB1a1CS2nB3NB1S1L2HI3HLS2sp1h2lo3SLO4HTOP1a2WaS1L2HI3HLS2sp1h2lo3SLO1a1CS2n12H1S2nX1n2n13NLE2N13N1'S2nX2nA1n2n13NLE2N13N1'S2nX2pX2nA2pA1CS2nB3NB1S1L2lo2nB2pB2zs3ACL4LENB2R3S1n3xs12n13ysv3zsv3xs'3VALS1L2p12n12R02R32R4S2nX2pX1a1q1k1R2O22E12E2S2p12n11a2Wa2Z1S2nX2nA1n2n13NLE2N13N1'2Z1S2nA2pA1n3NLE4OWNA3N1'2nB2pB4OWNB3SB1S1X2pX1a2Ha1q1k1R2E11H2nX2E2S2nX2pX3xs12Hk1HS2p11q2HqS3xs12n14LEN13xs'4LENfS2sp1X2p12n11a2NOS2nA3NA1S2sp1X2nX2Aa2nA2ys2Ba2zs3xs12XBS2sp1X2nX2Aa2nA2ys2Ba2zs3xs12XBS2nA2nB1n3NLE3SB1S2nX2nA2nB1n3NLE3SB1S2nX2pX2nB2pB1CS1L2lo2nA2pA2ys3ACL4LENA2R3S1L3HLS2sp2lo1X2nX2Aa2nA2ys2Ba2zs3SLO3xs13SPB2X02A02B02XBS2p12n11a1q1RS2p12n11a1q1k1R1DS2p12n11a2Z1S1L4DIMG2p12n11a2Hd2PIS1L4DIMG2p12n11a2C12PIS1L3HLS2sp2lo3SLO3ACL2p12n11a1C2PCS2nX2pX2p12n11a2O22E12E2". (* [comment removed for export] *)
  #[using="HLS DIMG HND ROIMG HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS SLO ACL HTOP SPA DHI"] Lemma sub_C1_proof : forall n, sub_C1_stmt n.
  Proof.
    intros n. unfold sub_C1_stmt. intros until t6. cbv zeta.
    intros SB NLE MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 NST1 OUT1 FRESH1 HPX1 MA1 MB1 N1 LA LAX LBX LZ.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 HAP1]. pose proof (HND _ _ _ _ HH1) as ND1.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP]. pose proof (HND _ _ _ _ HH) as ND.
    (* [comment removed for export] *)
    destruct dX as [X sX nX pX xs0 padX ownX]. destruct dA as [Aa sA nA pA ys padA ownA]. destruct dB as [Ba sB nB pB zs padB ownB].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof MX1 as [(CX1 & XAL & X0 & LEN1 & NR1 & OWN1) SGX]. unfold mpi_cells in CX1. unfold MPI_MAX_LIMBS in NR1.
    pose proof (opnd_view _ _ _ _ _ MA) as [(_ & AAL & A0 & LENA & NRA & OWNA) SGA]. unfold MPI_MAX_LIMBS in NRA.
    pose proof (opnd_view _ _ _ _ _ MB) as [(_ & BAL & B0 & LENB & NRB & OWNB) SGB]. unfold MPI_MAX_LIMBS in NRB.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    dpose SB as (SB1 & SB2 & SB3).
    ddestruct XW as (XCW & XD & XP). dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    pose proof (rw_cells_bound _ _ _ _ CX1) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    subst FRAME. unfold sub_frame in FR1.
    (* [comment removed for export] *)
    assert (P1F : n1 <> 0 -> own1 = LHeap /\ 1 <= n1 /\ In (p1, 4 * n1) LB1 /\ p1 mod 16 = 0 /\ u32arr usegs m1 p1 xs1
                             /\ 0 < p1 /\ p1 + 4 * n1 <= alloc_ceiling /\ (p1 + 4 * n1 <= hl_img_lo L \/ hl_img_hi L <= p1)).
    { intros NZ. destruct own1; [| | exfalso; exact (NST1 eq_refl)].
      { exfalso. destruct OWN1 as [E1 E2]. apply NZ. exact E2. }
      ddestruct OWN1 as (O1 & O2 & O3 & O4). pose proof (proj1 (Forall_forall _ _) HBR1 _ O2) as (R0 & R1 & R2 & R3 & R4). cbn in R0, R1, R2, R3, R4.
      split; [reflexivity|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. clear - R0 R3 R4. lia. }
    (* [comment removed for export] *)
    assert (OLDBLK : forall q k, In (q, k) LB -> 0 < k -> (ownX = LHeap -> q + k <= pX \/ pX + 4 * nX <= q) ->
                     In (q, k) LB1 /\ (n1 <> 0 -> q + k <= p1 \/ p1 + 4 * n1 <= q)).
    { intros q k Hq Hk Hapart. dpose OUT1 as (_ & _ & K1 & K2 & K3).
      assert (HqX : ~ In (q, k) (mpd_blk (mkMPD X sX nX pX xs0 padX ownX))).
      { unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail). intros [E|[]]. injection E as <- <-.
        destruct (Hapart eq_refl); clear - H Hk NR1 LEN1 OWNB; lia. }
      pose proof (K2 _ Hq HqX) as Hq1. split; [exact Hq1|]. intros NZ. ddestruct (P1F NZ) as (EO & N11 & PIN & _ & _ & P0 & _).
      assert (NE : (q, k) <> (p1, 4 * n1)).
      { intros E. destruct (FRESH1 (p1, 4 * n1) ltac:(unfold mpd_blk; cbn [md_own md_p md_n]; rewrite EO; left; reflexivity)) as [Hold|Hnew].
        - apply HqX. rewrite E. exact Hold.
        - apply Hnew. rewrite <- E. exact Hq. }
      destruct (blocks_apart_neq _ _ _ HAP1 Hq1 PIN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; clear - D; lia. }
    (* [comment removed for export] *)
    assert (XS1 : n1 <> 0 -> X + 16 <= p1 \/ p1 + 4 * n1 <= X).
    { intros NZ. ddestruct (P1F NZ) as (EO & N11 & _).
      eapply (new_limbs_apart_range usegs L HI h1 LB LB1 m1 m1 mo1 (bv_unsigned sp)
                (mkMPD X sX nX pX xs0 padX ownX) (mkMPD X sX n1 p1 xs1 padX own1) X 16);
        [exact HH1| exact MX1| exact OUT1| exact FRESH1| lia| exact (proj1 DIMG)| exact (proj2 DIMG)| | lia| | rewrite EO; reflexivity].
      - intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
      - exact XP. }
    assert (AF : exists pA' (sA' : word) nA' pdA' ysv, rw_cells usegs m1 Aa [C8 (Z_to_bv 64 pA'); C2 sA'; C2 (Z_to_bv 64 nA'); C4 pdA']
              /\ (1 <= n -> lval ysv n = lval ys n)
              /\ (1 <= n -> bytes_at usegs m1 pA' (u32s ysv) /\ n <= Z.of_nat (length ysv)
                    /\ ((pA' = p1 /\ ysv = xs1) \/ pA' + 4 * Z.of_nat (length ysv) <= p1 \/ p1 + 4 * Z.of_nat (length xs1) <= pA')
                    /\ 0 < pA' /\ pA' mod 4 = 0 /\ (pA' + 4 * Z.of_nat (length ysv) <= lo \/ bv_unsigned sp <= pA'))).
    { destruct SXA as [E|D].
      - injection E as <- <- <- <- <- <- <-. dexists p1, (Z_to_bv 64 sX), n1, padX, xs1. split; [exact CX1|].
        split; [intros N1'; apply lval_ext_limb; [clear - N1'; lia|]; intros k Hk; apply (LAX eq_refl); exact Hk|].
        intros N1'. ddestruct (P1F ltac:(clear - N1' NLE N1; lia)) as (EO & N11 & PIN & PAL & PARR & P0 & PC & PI).
        split; [apply u32arr_ro; exact PARR|]. split; [clear - N11 NLE N1 LEN1; lia|].
        split; [left; split; reflexivity|]. split; [exact P0|]. split; [clear - PAL; apply Z.mod_divide in PAL; [|lia]; apply Z.mod_divide; [lia|]; destruct PAL as [q Hq]; exists (4 * q); lia|].
        left. clear - PC ACL LEN1. lia.
      - cbn [md_addr] in D. assert (NEQ : mkMPD X sX nX pX xs0 padX ownX <> mkMPD Aa sA nA pA ys padA ownA) by (intros E; injection E; clear - D; lia).
        pose proof (opnd_view _ _ _ _ _ (MA1 NEQ)) as [(CA1 & _ & _ & _ & _ & OWNA1) _]. unfold mpi_cells in CA1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CA1, OWNA1.
        dexists pA, (Z_to_bv 64 sA), nA, padA, ys. split; [exact CA1|]. split; [intros _; reflexivity|]. intros N1'.
        destruct ownA as [| |].
        + exfalso. clear - OWNA N1' NLE. lia.
        + ddestruct OWNA1 as (NA1 & AIN1 & APAL & AARR). ddestruct OWNA as (_ & AIN & _ & _).
          pose proof (proj1 (Forall_forall _ _) HBR1 _ AIN1) as (R0 & R1 & R2 & R3 & R4). cbn in R0, R1, R2, R3, R4.
          destruct (OLDBLK pA (4 * nA) AIN ltac:(clear - NA1; lia) ltac:(intros HO; destruct OA3 as [C|[C|[C|C]]]; [exfalso; exact (NEQ C)| exfalso; exact (C HO)| discriminate| clear - C; lia])) as [_ APART].
          split; [apply u32arr_ro; exact AARR|]. split; [clear - NLE LENA; lia|].
          split; [right; destruct (Z.eq_dec n1 0) as [Z1|NZ]; [exfalso; clear - Z1 N1' NLE N1; lia|]; destruct (APART NZ); clear - H LENA LEN1; lia|].
          split; [exact R0|]. split; [clear - APAL; apply Z.mod_divide in APAL; [|lia]; apply Z.mod_divide; [lia|]; destruct APAL as [q Hq]; exists (4 * q); lia|].
          left. clear - R3 ACL LENA. lia.
        + ddestruct OWNA1 as (NA1 & APAL & AP0 & ABY & AW).
          split; [exact ABY|]. split; [clear - NLE LENA; lia|].
          split. { right. destruct (Z.eq_dec n1 0) as [Z1|NZ]; [exfalso; clear - Z1 N1' NLE N1; lia|]. ddestruct (P1F NZ) as (_ & _ & _ & _ & _ & P0 & PC & PI).
                   destruct AW as [ARO|[ASP _]]; [| clear - ASP PC ACL SLO HLS LEN1; lia].
                   pose proof (u32ro_bound _ _ _ _ ABY) as AB2.
                   pose proof (ROIMG (pA + 0) (ARO 0 ltac:(clear - NA1; lia)) ltac:(clear - AB2 LENA NA1; lia)) as I0.
                   pose proof (ROIMG (pA + (4 * nA - 1)) (ARO (4 * nA - 1) ltac:(clear - NA1; lia)) ltac:(clear - AB2 LENA NA1; lia)) as I1. clear - I0 I1 PI LENA LEN1 NA1. lia. }
          split; [exact AP0|]. split; [exact APAL|]. rewrite LENA. apply OA5. discriminate. }
    assert (BF : exists pB' (sB' : word) nB' pdB' zsv, rw_cells usegs m1 Ba [C8 (Z_to_bv 64 pB'); C2 sB'; C2 (Z_to_bv 64 nB'); C4 pdB']
              /\ (1 <= n -> lval zsv n = lval zs n)
              /\ (1 <= n -> bytes_at usegs m1 pB' (u32s zsv) /\ n <= Z.of_nat (length zsv)
                    /\ ((pB' = p1 /\ zsv = xs1) \/ pB' + 4 * Z.of_nat (length zsv) <= p1 \/ p1 + 4 * Z.of_nat (length xs1) <= pB')
                    /\ 0 < pB' /\ pB' mod 4 = 0 /\ (pB' + 4 * Z.of_nat (length zsv) <= lo \/ bv_unsigned sp <= pB'))).
    { destruct SXB as [E|D].
      - injection E as <- <- <- <- <- <- <-. dexists p1, (Z_to_bv 64 sX), n1, padX, xs1. split; [exact CX1|].
        split; [intros N1'; apply lval_ext_limb; [clear - N1'; lia|]; intros k Hk; apply (LBX eq_refl); exact Hk|].
        intros N1'. ddestruct (P1F ltac:(clear - N1' NLE N1; lia)) as (EO & N11 & PIN & PAL & PARR & P0 & PC & PI).
        split; [apply u32arr_ro; exact PARR|]. split; [clear - N11 SB1 N1 LEN1 NLE; lia|].
        split; [left; split; reflexivity|]. split; [exact P0|]. split; [clear - PAL; apply Z.mod_divide in PAL; [|lia]; apply Z.mod_divide; [lia|]; destruct PAL as [q Hq]; exists (4 * q); lia|].
        left. clear - PC ACL LEN1. lia.
      - cbn [md_addr] in D. assert (NEQ : mkMPD X sX nX pX xs0 padX ownX <> mkMPD Ba sB nB pB zs padB ownB) by (intros E; injection E; clear - D; lia).
        pose proof (opnd_view _ _ _ _ _ (MB1 NEQ)) as [(CB1 & _ & _ & _ & _ & OWNB1) _]. unfold mpi_cells in CB1. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in CB1, OWNB1.
        dexists pB, (Z_to_bv 64 sB), nB, padB, zs. split; [exact CB1|]. split; [intros _; reflexivity|]. intros N1'.
        destruct ownB as [| |].
        + exfalso. clear - OWNB N1' SB1. lia.
        + ddestruct OWNB1 as (NB1 & BIN1 & BPAL & BARR). ddestruct OWNB as (_ & BIN & _ & _).
          pose proof (proj1 (Forall_forall _ _) HBR1 _ BIN1) as (R0 & R1 & R2 & R3 & R4). cbn in R0, R1, R2, R3, R4.
          destruct (OLDBLK pB (4 * nB) BIN ltac:(clear - NB1; lia) ltac:(intros HO; destruct OB3 as [C|[C|[C|C]]]; [exfalso; exact (NEQ C)| exfalso; exact (C HO)| discriminate| clear - C; lia])) as [_ APART].
          split; [apply u32arr_ro; exact BARR|]. split; [clear - SB1 LENB; lia|].
          split; [right; destruct (Z.eq_dec n1 0) as [Z1|NZ]; [exfalso; clear - Z1 N1' NLE N1; lia|]; destruct (APART NZ); clear - H LENB LEN1; lia|].
          split; [exact R0|]. split; [clear - BPAL; apply Z.mod_divide in BPAL; [|lia]; apply Z.mod_divide; [lia|]; destruct BPAL as [q Hq]; exists (4 * q); lia|].
          left. clear - R3 ACL LENB. lia.
        + ddestruct OWNB1 as (NB1 & BPAL & BP0 & BBY & BW).
          split; [exact BBY|]. split; [clear - SB1 LENB; lia|].
          split. { right. destruct (Z.eq_dec n1 0) as [Z1|NZ]; [exfalso; clear - Z1 N1' NLE N1; lia|]. ddestruct (P1F NZ) as (_ & _ & _ & _ & _ & P0 & PC & PI).
                   destruct BW as [BRO|[BSP _]]; [| clear - BSP PC ACL SLO HLS LEN1; lia].
                   pose proof (u32ro_bound _ _ _ _ BBY) as BB2.
                   pose proof (ROIMG (pB + 0) (BRO 0 ltac:(clear - NB1; lia)) ltac:(clear - BB2 LENB NB1; lia)) as I0.
                   pose proof (ROIMG (pB + (4 * nB - 1)) (BRO (4 * nB - 1) ltac:(clear - NB1; lia)) ltac:(clear - BB2 LENB NB1; lia)) as I1. clear - I0 I1 PI LENB LEN1 NB1. lia. }
          split; [exact BP0|]. split; [exact BPAL|]. rewrite LENB. apply OB5. discriminate. }
    ddestruct AF as (pA' & sA' & nA' & pdA' & ysv & CA1 & AVAL & AV). ddestruct BF as (pB' & sB' & nB' & pdB' & zsv & CB1 & BVAL & BV).
    pose proof (rw_cells_bound _ _ _ _ CA1) as ABND. pose proof (rw_cells_bound _ _ _ _ CB1) as BBND. cbn [cells_size csize Nat.add] in ABND, BBND.
    (* [comment removed for export] *)
    eapply aevtM_cut_evt; [exact MK1 | |].
    { eapply (sub_tail_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 X p1 n1 n lo sX padX xs1
                Aa pA' nA' sA' pdA' ysv Ba pB' nB' sB' pdB' zsv); try eassumption.
      - clear - X0 XB XAL. lia.
      - clear - SB1 NLE N1 NR1 NRA. lia.
      - clear - SLO HLS. lia.
      - clear - ACL ACP. lia.
      - intros H1. ddestruct (P1F ltac:(clear - H1; lia)) as (EO & N11 & PIN & PAL & PARR & P0 & PC & PI).
        split; [exact PARR|]. split; [exact P0|]. split; [exact PAL|]. split; [clear - PC ACL; lia|]. apply XS1. clear - H1; lia. }
    (* [comment removed for export] *)
    cbv beta. intros ms' TQ. unfold sub_tail_post in TQ.
    ddestruct TQ as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m' & r & sg' & xs' & -> & MUf & WMf & MIf & STf & CXf & XAf & LENf & RES).
    apply aevtM_done. subst POST. unfold mpi_binop_post. deexists 14. dexists m', mo1, h1, LB1, (mkMPD X sg' n1 p1 xs' padX own1), r.
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    split; [reflexivity|]. split; [exact MIf|]. split; [exact STf|]. split; [exact MF1|]. split; [exact HT1|].
    (* [comment removed for export] *)
    assert (XCW1 : forall a, X <= a < X + 16 -> client_waddr L LB1 lo (heap_top usegs L HI h) a).
    { intros a Ha. destruct (XCW a Ha) as [C|[C|([q k] & Hq & R)]]; [left; clear - C SLO HLS; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. cbn in R. apply (proj1 (proj2 (proj2 (proj2 OUT1)))); [exact Hq|].
      unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail). intros [E|[]]. injection E as E1 E2.
      destruct (XP eq_refl); clear - H Ha R E1 E2; lia. }
    split.
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH1| exact ACL| exact MUf| exact WMf|].
      intros a Ha NO. rewrite HT1.
      assert (W3 : p1 <= a < p1 + 4 * n1 \/ X <= a < X + 16 \/ bv_unsigned sp - 160 <= a < bv_unsigned sp) by (cbn in NO; clear - NO; lia).
      clear NO. destruct W3 as [Wa|[Wa|Wa]].
      - destruct (Z.eq_dec n1 0) as [Z1|NZ]; [exfalso; clear - Wa Z1; lia|]. ddestruct (P1F NZ) as (_ & _ & PIN & _).
        right; right; exists (p1, 4 * n1); split; [exact PIN| cbn; clear - Wa; lia].
      - apply XCW1; exact Wa.
      - left. clear - Wa HTOP SLO HLS. lia. }
    split.
    { split; [| cbn [md_sg]; destruct RES as [(_ & -> & _)|(_ & -> & _)]; [left; reflexivity| exact SGX]].
      cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CXf|]. split; [exact XAL|]. split; [exact X0|]. split; [clear - LENf LEN1; lia|]. split; [unfold MPI_MAX_LIMBS; clear - NR1; lia|].
      destruct own1; [exact OWN1| | exfalso; exact (NST1 eq_refl)].
      ddestruct OWN1 as (O1 & O2 & O3 & O4). split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. apply XAf. exact O1. }
    split.
    { eapply mpd_out_ext; [exact OUT1| reflexivity| cbn; exact NST1| reflexivity]. }
    split.
    { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MUf| exact WMf|].
      intros a Ha Hc Ho. cbn in Ho. cbn. destruct Ho as (O1 & O2).
      assert (LOW : forall q k, In (q, k) LB -> q + k <= alloc_ceiling).
      { intros q k Hq. pose proof (proj1 (Forall_forall _ _) HBR _ Hq) as (_ & _ & _ & B4 & _). exact B4. }
      split; [| split; [exact O1| split; [| exact I]]].
      - (* [comment removed for export] *)
        destruct (Z.eq_dec n1 0) as [Z1|NZ]; [clear - Z1; lia|]. ddestruct (P1F NZ) as (EO & N11 & PIN & _ & _ & P0 & PC & PI).
        dpose OUT1 as (_ & _ & _ & K2 & _).
        destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C PC ACL SLO HLS; lia| clear - C2 PI DIMG C1; lia|]. cbn in R.
        destruct (FRESH1 (p1, 4 * n1) ltac:(unfold mpd_blk; cbn [md_own md_p md_n]; rewrite EO; left; reflexivity)) as [Hold|Hnew].
        + unfold mpd_blk in Hold; cbn [md_own md_p md_n] in Hold. destruct ownX; try (destruct Hold; fail). destruct Hold as [E|[]]. injection E as E1 E2.
          cbn in O2. destruct O2 as [O2 _]. clear - O2 E1 E2. lia.
        + assert (Hq1 : In (q, k) LB1).
          { apply K2; [exact Hq|]. unfold mpd_blk; cbn [md_own md_p md_n]. destruct ownX; try (intros []; fail).
            intros [E|[]]. injection E as E1 E2. cbn in O2. destruct O2 as [O2 _]. clear - O2 R E1 E2. lia. }
          pose proof (proj1 (Forall_forall _ _) HBR _ Hq) as (_ & _ & K0 & _ & _). cbn in K0.
          assert (NE : (q, k) <> (p1, 4 * n1)) by (intros E; apply Hnew; rewrite <- E; exact Hq).
          destruct (Z.eq_dec k 0) as [->|Kp]; [clear - R; lia|].
          destruct (blocks_apart_neq _ _ _ HAP1 Hq1 PIN NE ltac:(cbn; clear - Kp K0; lia) ltac:(cbn; clear - N11; lia)) as [D|D]; cbn in D; clear - D R; lia.
      - (* [comment removed for export] *) destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]].
        + clear - C. lia.
        + clear - C1 DHI ACL SLO HLS. lia.
        + cbn in R. pose proof (LOW q k Hq) as LQ. clear - LQ R ACL SLO HLS. lia. }
    split.
    { eapply statics_ok_munch; [exact SOK1| exact MUf|]. intros a Hd NW. cbn.
      split; [| split; [intros C; exact (NW (XD a C Hd))| split; [clear - Hd DHI ACL SLO HLS; lia| exact I]]].
      destruct (Z.eq_dec n1 0) as [Z1|NZ]; [clear - Z1; lia|]. ddestruct (P1F NZ) as (_ & _ & _ & _ & _ & _ & _ & PI). clear - PI Hd DIMG. lia. }
    (* [comment removed for export] *)
    assert (EA : lval ysv n = lval ys n) by (destruct (Z.eq_dec n 0) as [->|NZ]; [rewrite !lval_0; reflexivity| apply AVAL; clear - NZ SB1; lia]).
    assert (EB : lval zsv n = lval zs n) by (destruct (Z.eq_dec n 0) as [->|NZ]; [rewrite !lval_0; reflexivity| apply BVAL; clear - NZ SB1; lia]).
    assert (KEYA : lval ys n + 2 ^ (32 * n) * lseg xs1 n n1 = limbs_val ys).
    { rewrite limbs_val_lval, LENA. rewrite (lval_split ys n nA) by (clear - SB1 NLE; lia). f_equal. f_equal.
      rewrite (lseg_mid xs1 n nA n1) by (clear - SB1 NLE N1 NR1; lia).
      rewrite (lseg_zero xs1 nA n1) by (first [clear - NRA NLE N1 SB1; lia | intros k H1 H2; apply LZ; assumption]).
      rewrite Z.mul_0_r, Z.add_0_r. apply lseg_ext; [clear - SB1 NLE; lia|]. intros k H1 H2. apply LA; assumption. }
    assert (KEYB : limbs_val zs = lval zs n) by (rewrite limbs_val_lval, LENB; exact SB2).
    split.
    - destruct RES as [(-> & -> & VAL)|(-> & -> & VAL)].
      + left. split; [reflexivity|]. split; [| reflexivity]. unfold mpd_val, mpd_abs; cbn [md_sg md_limbs].
        rewrite Z.mul_1_l, limbs_val_lval, KEYB, <- KEYA, <- EA, <- EB. replace (Z.of_nat (length xs')) with n1 by (clear - LENf LEN1; lia). clear - VAL. lia.
      + right; right. split; [reflexivity|]. unfold mpd_abs; cbn [md_limbs]. rewrite KEYB, <- KEYA, <- EA, <- EB. exact VAL.
    - split; [reflexivity|]. split; [reflexivity|]. split; [exact FRESH1|]. cbn [md_n]. rewrite N1. apply Z.le_max_l.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Tail.
