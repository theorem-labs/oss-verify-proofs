(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame LibTail MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_unreg_globals A_exit A_stdio_defs A_stdio_write A_stdio_call A_rip A_amem_lib A_imemcpy A_fwrite_oom A_oomtail A_printf1 A_refused.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SymDriveH4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AHeapL0.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2 A_splice A_imz A_icpt_str A_icpt_strnlen A_icpt_strnlenJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tail_lib A_tail_openfail_defs A_tail_openfail_defs2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxADrvKit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnDS.

Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_tail_openfail_S8 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.outzone"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "OF.VF"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.blobs_ev"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.B.A_refused.SHW"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Nat.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "OF.EnvV"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.AGR"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OF.FD2"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "OF.TT"; "OF.XL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "OF.TT64"; "Corelib.Init.Datatypes.None"].

#[local] Existing Instance Lib.PropExec.fx0.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition PRE17 : list byte := s2b "cli: cannot open "%string.
Lemma PRE17_len : length PRE17 = 17%nat. Proof. reflexivity. Qed.
Lemma msg_cannot_open_eq : forall p, msg_cannot_open p = PRE17 ++ p ++ [Z_to_bv 8 10].
Proof. intros p. unfold msg_cannot_open, PRE17. reflexivity. Qed.

Lemma mo_mat_fds' : forall mo mo', mo_mat mo mo' -> m_fds mo' = m_fds mo.
Proof. unfold mo_mat, m_fds; intros mo mo' H; intuition congruence. Qed.

Section OF.  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable KI : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000%Z.
  Hypothesis GSB : al_gsb AL = 0x1099f8%Z.
  Hypothesis IMGCS : A_unreg_globals.img_cs AL CS.
  Hypothesis K_halted : forall mo, KI mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VKI,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VKI,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Pmo,$0.Pmo',$0.P,A1.VKI,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis SPlo : (0x7fff7f000000 + 16384 <= bv_unsigned sp0)%Z.      (* [comment removed for export] *)
  Hypothesis SPhi : (bv_unsigned sp0 + 128 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis HKI : KI model.
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  (* [comment removed for export] *)
  Variable lo : Z.
  Hypothesis LOlo : (0x10007fff7fff < lo)%Z.
  Hypothesis LOhi : (lo + 16384 <= bv_unsigned sp0)%Z.
  Hypothesis LOdeep : (bv_unsigned sp0 - 8388608 <= lo)%Z.
  (* [comment removed for export] *)
  Variable STKHI : Z.
  Hypothesis STKHIlo : (bv_unsigned sp0 + 128 <= STKHI)%Z.
  Hypothesis STKHIhi : (STKHI <= 0x800000000000)%Z.
  Hypothesis STKHI64 : (STKHI mod 64 = 0)%Z.
  Hypothesis SCS : crange CS lo (STKHI - lo).
  (* [comment removed for export] *)
  Hypothesis FCS : crange CS 0x208c0 64.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G8 : getr R 8 = Z_to_bv 64 2.
  Hypothesis G9 : getr R 9 = Z_to_bv 64 2.
  Hypothesis G20 : getr R 20 = Z_to_bv 64 0.
  Hypothesis G21 : getr R 21 = Z_to_bv 64 0.
  Hypothesis G22 : getr R 22 = Z_to_bv 64 0.
  Hypothesis G23 : getr R 23 = Z_to_bv 64 0.
  Hypothesis G24 : getr R 24 = Z_to_bv 64 0.
  Hypothesis G25 : getr R 25 = Z_to_bv 64 0.
  Hypothesis G26 : getr R 26 = Z_to_bv 64 0.
  Hypothesis G27 : getr R 27 = Z_to_bv 64 0.
  Hypothesis TM : tail_memA sp0 M can tid wp0 rp0 wp1 rp1.
  Hypothesis MAPD : mapped M lo (bv_unsigned sp0).
  (* [comment removed for export] *)
  Hypothesis ZSH : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Ps,$12.P,(7.(13.(14.+7???8000.(15.Vlo,+8.))R1.)(16.R1.(14.+7???8000.(15.VSTKHI,+8.))))(8.(9.(3.&8.))A1.VM,(17.&40.R2.)(;.(3.&8.)(17.&8.=)))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Variables (P : word) (path extra : list byte).
  Let L : Z := Z.of_nat (length path).
  Let buf : list byte := path ++ Z_to_bv 8 0 :: extra.
  Hypothesis G18 : getr R 18 = P.
  Hypothesis BY : bytes_at asegs M (bv_unsigned P) buf.
  Hypothesis NZ : ~ In (Z_to_bv 8 0) path.
  Hypothesis WIN8 : ((bv_unsigned P + L) / 8 * 8 + 8 <= bv_unsigned P + Z.of_nat (length buf))%Z.
  Hypothesis Plo : (bv_unsigned sp0 + 128 <= bv_unsigned P)%Z.
  Hypothesis Phi : (bv_unsigned P + Z.of_nat (length buf) <= STKHI)%Z.          (* [comment removed for export] *)
  Hypothesis PL16 : (bv_unsigned P + L + 16 <= STKHI)%Z.                        (* [comment removed for export] *)
  Hypothesis LMAX : (L <= 131071)%Z.                                            (* [comment removed for export] *)
  Hypothesis L63E : (L = 63)%Z.         (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30247682266.71L35495549846.7000000k01CS3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E1z2Hz1H2H0S3sp05STKHI1P4path1L3buf". (* [comment removed for export] *)
  Lemma PCS : crange CS (bv_unsigned P - bv_unsigned P mod 64) (STKHI - (bv_unsigned P - bv_unsigned P mod 64)).
  Proof. intros z Hz. apply SCS. pose proof LOhi. pose proof (Z.mod_pos_bound (bv_unsigned P) 64 ltac:(lia)). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SHRD : forall c, CS c -> exists b, bytes_at asegs M (shadow_of AL c) [b].
  Hypothesis CSTOP : forall c, CS c -> (c < 2^47)%Z.

  Let WINLO := (bv_unsigned sp0 - 4096)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (0x7fffc118, 0x7fffc120)%Z; (SSH_LO sp0, SSH_HI sp0)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32276418883.71L57167447340.71L57657395591.7200000N01601lS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H". (* [comment removed for export] *)
  Lemma SSH_facts : (0x7fff8000 <= SSH_LO sp0)%Z /\ (SSH_HI sp0 <= 2^46)%Z /\ (SSH_LO sp0 < SSH_HI sp0)%Z.
  Proof. pose proof (SHW_range sp0 (-64) ltac:(lia) SPal ltac:(lia)). unfold SSH_LO, SSH_HI in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.73000011S3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma D_Dseg : forall a : word, segcov asegs (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.7300000PS3sp05STKHI1P4path1L3buf5WINLO1c". (* [comment removed for export] *)
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L51355856640.75L5268879960.75 L57161095762.75L60694983881.77L61028787006.75L67812584585.7500000i01I02102T03203US3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1zS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2A1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply FCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. destruct (ssh_app sp0 z ltac:(lia) SPal Hz) as [A1 A2]. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply WCS; lia| exact A2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L15567212646.73L44851315118.73L60924558599.7300000P00n01QS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. pose proof SSH_facts. pose proof SPlo. unfold D. apply Dimg_D0. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition RRUN := rz_runA asegs D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L30901545954.77L46534914516.77L60924549197.7700001301V029S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1a1b2Ha2Hb1z2HzS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_frame : forall a b, (bv_unsigned sp0 - 4096 <= a)%Z -> (b <= bv_unsigned sp0)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.77000013S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1a1b2Ha2Hb1z2Hz". (* [comment removed for export] *)
  Lemma D_img : forall a b, (0x10000 <= a)%Z -> (b <= 0x65f000)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L43185048941.73L44851324132.73L58554083103.7300000S01101OS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_fsh : DcovZ D 0x7fffc118 0x7fffc120.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z; (0x7fffc118, 0x7fffc120)%Z].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L51855127614.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | exact D_fsh | apply Forall_nil]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18267881737.75L5599869189.75 00000V01<S3sp05STKHI1P4path1L3buf5WINLO3qhi3HhiS3sp05STKHI1P4path1L3buf5WINLO3qlo3Hlo". (* [comment removed for export] *)
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Pqlo,$12.Pqhi,$12.P,(13.(14.(18.&40.Vsp0,)-1000.)R2.)P,(13.R2.(14.(18.&40.Vsp0,)=))(19.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13440388671.74L15567222060.74L52039345437.7400000S01301SS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLO1H". (* [comment removed for export] *)
  Lemma D_ssh : DcovZ D (SSH_LO sp0) (SSH_HI sp0).
  Proof. pose proof SSH_facts. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5287174892.7500001<S3sp02lo5STKHI1P4path1L3buf5WINLO1x2Hr2O24SPlo4LOhi7STKHI643Plo4PL164L63E2O1". (* [comment removed for export] *)
  Lemma D_out_zone : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Px,(3.&40.)P,(8.$1:.A1.VD,R1.$1;.)P,(1<.Vlo,(18.&40.Vsp0,)R2.)(1=.(7.(7.(13.+10000.(18.&40.R3.))(16.(18.&40.R3.)+65?000.))(1>.(7.(13.+?:488.(18.&40.R3.))(16.(18.&40.R3.)+?:570.))))(1=.(7.(13.+7???<118.(18.&40.R3.))(16.(18.&40.R3.)+7???<120.))(7.(13.(1?.Vsp0,)(18.&40.R3.))(16.(18.&40.R3.)(20.Vsp0,)))))")
(* [comment removed for export] *).
  Proof.
    intros x Dx [O1 O2]. unfold D, Dimg in Dx. apply Dof_true in Dx as (iv & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold AIMG_LO, AIMG_HI in *; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition V0 : list word := [sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8.
  Lemma V0_len : length V0 = 42%nat.
  Proof. unfold V0. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma V0_0 : vals_ev V0 0 = sp0. Proof. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_33 : vals_ev V0 33 = can.
  Proof. unfold V0, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ repeat (Z_to_bv 64 0) 8) with (([sp0] ++ junk_vals R) ++ ([can] ++ repeat (Z_to_bv 64 0) 8)).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia]. rewrite length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma V0_junk : forall i, (i < 32)%nat -> vals_ev V0 (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold V0, vals_ev. cbn [app length Nat.add].
    change (sp0 :: junk_vals R ++ can :: repeat (Z_to_bv 64 0) 8) with ([sp0] ++ (junk_vals R ++ (can :: repeat (Z_to_bv 64 0) 8))).
    change (S i) with (length [sp0] + i)%nat. rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_19 : vals_ev V0 19 = P. Proof. change 19%nat with (1 + 18)%nat. rewrite (V0_junk 18) by lia. exact G18. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VF (V : list word) : Prop :=
    (forall n, (n < 42)%nat -> vals_ev V n = vals_ev V0 n) /\ (42 <= length V)%nat.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25269778915.7100000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma VF0 : VF V0. Proof. split; [intros; reflexivity | rewrite V0_len; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L21188810707.77L9784235213.75 00000n01kS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2P21n2HnS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V3ext2P2". (* [comment removed for export] *)
  Lemma VF_app : forall V ext, VF V -> VF (V ++ ext).
  Proof. intros V ext [P1 P2]. split; [| rewrite length_app; lia]. intros n Hn. rewrite vals_ev_app_l by lia. apply P1. exact Hn. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30227048842.7300000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf0 : forall V, VF V -> vals_ev V 0 = sp0. Proof. intros V [P1 _]. rewrite (P1 0%nat) by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.7300000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf19 : forall V, VF V -> vals_ev V 19 = P. Proof. intros V [P1 _]. rewrite (P1 19%nat) by lia. apply V0_19. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.7300000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf33 : forall V, VF V -> vals_ev V 33 = can. Proof. intros V [P1 _]. rewrite (P1 33%nat) by lia. apply V0_33. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55760870395.7500000US3sp05STKHI1R1P4path1L3buf5WINLO1i2Hi". (* [comment removed for export] *)
  Lemma regs_okV0 : regs_ok (Env (vals_ev V0) (blobs_ev [])) sr_OF R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_OF all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G3 | exact G4 | exact G8 | exact G9 | exact G20 | exact G21 | exact G22 | exact G23
                                   | exact G24 | exact G25 | exact G26 | exact G27 | (cbn [ev]; rewrite V0_0; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot (Env (vals_ev V0) (blobs_ev [])) (EVar n)) with (vals_ev V0 n); rewrite (V0_junk (n - 1)) by lia; reflexivity end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01;0?L13042945941.85L13484217602.85L14054083309.89L14499496082.85L15439463048.85L16774753289.85L17543312104.87L1756166345.85 L18928696722.85L2183569985.85 L21927717721.85L21986899558.85L22604873481.85L2431328725.89 L24690173574.85L24992216082.85L25271909867.85L2564951689.85 L25940753974.85L27134698386.85L27315410273.85L27352604565.85L28434372873.85L29762371858.85L31327315070.89L31396711570.85L32648418366.91L32873232769.89L33148392579.85L33669037980.85L34577004134.85L34774111081.85L3506990866.85 L3829630897.89 L39213365269.85L39510883410.85L40253358217.85L43030311433.85L44353219849.85L44510486418.85L44751598473.85L44851494802.85L4504975677.89 L46809767186.85L48461698953.85L5004984661.85 L51238950418.85L52457697417.85L52875384210.85L53519161933.89L53519190958.85L54226205864.85L54967497737.85L55007380242.85L55149030888.87L55662616861.89L55849630025.85L5641132690.85 L58560891017.85L58961367305.85L5926593349.85 L61064399881.85L62675677899.85L6275277449.85 L64037435666.85L64202541330.85L64791502857.85L65502196882.85L65732472201.85L66336703634.85L67631326282.89L68058909735.85L68075363561.85L7781517330.85 L9911486354.85 00000k01I02L02j03H03f04I04g05E05c06A06d07B07d08B08`09>09\0::0:X0;;0;^0<<0<Z0=W0>50?:0?_0?`0@>0@\0A:0AX0B>0B?0B]0C;0CY0D70DU0E30EQ0F50FS0G10GY0H70HU0I30IS0J10J20JP0Jn0KQ0LQ0Lo0MM0Mk0NI0Ng0OE0OF0Od0PB0P`0Q>0Q\0R:0RX0S=0S[0T90TW0U5S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL164L63E5WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H2H01d1m2Hd2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1n1BS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf3Plo4PL164L63E5WINLO1H3off1n1B1CS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H1d1m2Hd2Hm1x2HxS3sp05STKHI1P4path1L3buf5WINLO1d1m2HdFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1n1CFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1AS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1mS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL164L63E5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma know_okV0 : know_ok asegs (Env (vals_ev V0) (blobs_ev [])) M kn_OF.
  Proof.
    pose proof SPlo. pose proof SPhi. pose proof SPal. pose proof (u64_range P) as PR.
    pose proof TM as TM'. destruct TM' as [WIN RO ERR CAN RTC ZI ZS _ _ _ _ _ _ _ _ _ _ _ _].
    assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat (Env (vals_ev V0) (blobs_ev [])) (SA (ELit 0) off) n).
    { intros off n A B C. apply flat_abs0; lia. }
    unfold know_ok, kn_OF.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    all: try (split; [lia|]; split; [apply FL; lia|]; rewrite adenot_lit0; cbn [edenot];
              first [ exact CAN
                    | (apply (rtc_rdn1 _ _ _ RTC); rtc_in)
                    | (apply (rtc_rdn8 _ _ _ RTC); rtc_in)
                    | (eapply (zrun_rdn8 _ _ _ _ ZI); cbv -[Z.le]; lia) ]).
    all: first
      [ (* [comment removed for export] *) split; [lia|]; cbn [edenot ev]; rewrite V0_0; assumption
      | (* [comment removed for export] *) cbn [edenot ev]; rewrite V0_0; lia
      | (* [comment removed for export] *) cbn [edenot ev]; rewrite V0_19; lia
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot ev]; rewrite ?V0_0; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off]; cbn [edenot ev]; rewrite ?V0_0;
        apply store_ok_of_all; rewrite u_small by lia; [lia|]; intros x Hx; apply WIN; lia
      | (* [comment removed for export] *) split; [lia|]; split; [lia|]; intros i Hi; first [apply RO; lia | apply ERR; lia]
      | (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
        intros d m Hd Hm; unfold estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia;
        apply store_ok_data; rewrite u_small by lia; lia
      | match goal with |- ?g => idtac "KNOWN-GOAL-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac covtac :=
    try (unfold estart, elenZ; cbn [a_base a_off]);
    first [ exact I
          | cbn [edenot ev];
            lazymatch goal with VFV : VF ?V |- _ => rewrite ?(vf0 V VFV) | _ => idtac end;
            rewrite ?u_small by lia; intros z Hz;
            first [ apply (D_img z (z + 1)); lia | apply (D_frame z (z + 1)); lia | apply D_fsh; lia ] ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L17034448047.78L29784460291.77L3479498253.77 L43935895424.79L47803405696.79L55715225071.77L59576963504.79L63368316460.79L63368316589.78L63368325619.77L64266648997.77L66561261592.79L8929201831.80 00000n01L02T03:03`04>04^05>05^06<07707W08[S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL164L63E5WINLO1k2HkS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL164L63E5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1kS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H1k2Hk2H12H22H3". (* [comment removed for export] *)
  Lemma shw_denotV : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "PV,(1.(3.&40.))Pk,$12.P,(21.R2.)P,(7.(13.-1000.R2.)(13.R2.=))(8.$12.(18.&40.(22.(23.(24.R4.)(25.(26.(1.(3.&8.)))))(27.$28.(27.$29.(27.$2:.(27.$29.(2;.#0.)(2<.R3.))(2<.+3.))(2<.+7???8000.))(2<.-8.))))(2=.Vsp0,R3.))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros V k VFV Hk. cbn [edenot ev]. rewrite (vf0 V VFV).
    rewrite alu_and. rewrite alu_add. rewrite alu_srl. rewrite (alu_add sp0).
    unfold v_and, v_add, v_srl.
    replace (bv_unsigned (Z_to_bv 64 (bv_unsigned sp0 + bv_unsigned (Z_to_bv 64 k))))%Z with (bv_unsigned sp0 + k)%Z.
    2:{ rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
        rewrite Zplus_mod_idemp_r. symmetry. apply Z.mod_small. lia. }
    rewrite (unsigned_lit 3) by lia. change (3 mod 64)%Z with 3%Z. rewrite Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
    pose proof (Z.div_pos (bv_unsigned sp0 + k) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound (bv_unsigned sp0 + k) 8 (2^45) ltac:(lia) ltac:(lia)).
    rewrite (unsigned_lit ((bv_unsigned sp0 + k) / 8)) by lia. rewrite (unsigned_lit 2147450880) by lia.
    rewrite (unsigned_lit ((bv_unsigned sp0 + k) / 8 + 2147450880)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (-8))) with 18446744073709551608%Z by reflexivity.
    rewrite A_rip.land_m8 by lia. rewrite unsigned_lit.
    2:{ pose proof (Z.mod_pos_bound ((bv_unsigned sp0 + k) / 8 + 2147450880) 8 ltac:(lia)). lia. }
    unfold SHW. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L3479498253.75 L35907637249.76L40825277235.75L53519168529.76L55715225071.75L64266638075.76L64266648997.7500001801[02902Y03704204mS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL164L63E5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H1k2HkS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H1k2Hk". (* [comment removed for export] *)
  Lemma and3_lit : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Pk,$12.P,(7.(13.-1000.R1.)(13.R1.=))(8.$1:.(2>.&40.(2?.$28.(17.&40.(14.(18.&40.Vsp0,)R2.))(17.&40.+3.))(17.&40.=))(30.(31.R2.+4.)=))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros k Hk. rewrite alu_and. unfold v_and. rewrite (unsigned_lit 3), (unsigned_lit (bv_unsigned sp0 + k)) by lia.
    rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned sp0 + k) 4 ltac:(lia)).
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply (mod4_of_sp (bv_unsigned sp0) k); [exact SPal | lia | reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L37106200957.75L5744834796.75 L61929758668.75L8443611008.75 00000]01@01c02FS3sp04SPlo5STKHI1P4path1L3buf5WINLO1x1n2Hx2HnS3sp05STKHI1P4path1L3buf5WINLO1x2HxS3sp05STKHI1P4path1L3buf5WINLO1n2HnS3sp05STKHI1P4path1L3buf5WINLO1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu_small : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Px,$12.Pn,$12.P,(7.(13.=R2.)(16.R2.(32.+2.+30.)))P,(7.(13.=R2.)(16.R2.(32.+2.+10.)))(8.$1:.(33.&40.(17.&40.(34.(18.&40.(17.&40.R4.))(18.&40.(17.&40.-1.))))(17.&40.R3.))$35.)")
(* [comment removed for export] *).
  Proof.
    intros x n Hx Hn. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "Px,(3.&40.)Pk,$12.P,(7.(13.=(14.(18.&40.R2.)R1.))(16.(14.(18.&40.R2.)R1.)(32.+2.+40.)))(8.(3.&40.)(2?.$29.R3.(17.&40.R2.))(17.&40.(14.(18.&40.R3.)R2.)))")
(* [comment removed for export] *).
  Proof.
    intros x k Hk. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac evs :=
    cbn [ev eb];
    lazymatch goal with VFV : VF ?V |- _ => rewrite ?(vf0 V VFV), ?(vf19 V VFV), ?(vf33 V VFV) | _ => idtac end;
    repeat match goal with H : vals_ev ?V ?n = _ |- context [vals_ev ?V ?n] => rewrite H end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21188810707.7500000US3sp05STKHI1P4path1L3buf5WINLO1V1n2Hn". (* [comment removed for export] *)
  Lemma vals_ev_app_ge : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "PV,(1.(3.&40.))Pext,(1.(3.&40.))Pn,$4.P,(36.(37.(3.&40.)R3.)R1.)(8.(3.&40.)(24.(38.(3.&40.)R4.R3.)R2.)(24.R3.(39.R2.(37.(3.&40.)R4.))))")
(* [comment removed for export] *).
  Proof. intros V ext n Hn. unfold vals_ev. rewrite app_nth2 by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Ltac solve_sc :=
    cbn [sc_denot branch_taken];
    first
      [ (* [comment removed for export] *)
        lazymatch goal with VFV : VF ?V |- flat _ _ _ /\ _ =>
          unfold flat, estart, elenZ; cbn [a_base a_off];
          rewrite !(shw_denotV V) by (first [exact VFV | lia]);
          lazymatch goal with |- context [SHW sp0 ?k] =>
            pose proof (SHW_range sp0 k ltac:(lia) SPal ltac:(lia)); pose proof SSH_facts end;
          cbn [edenot]; rewrite ?(u_small 8), ?(u_small 4), ?(u_small 0) by lia; lia end
      | (* [comment removed for export] *)
        lazymatch goal with VFV : VF ?V, AGk : AGR M lo (bv_unsigned sp0) ?Mk |- exists bs, rdn _ (restrict _ ?Mk) _ _ = Some bs /\ _ =>
          exists (word_to_le_bytes 8 (Z_to_bv 64 0)); split;
          [ lazymatch goal with |- rdn _ _ (adenot _ (SA ?e 0)) 8 = _ =>
              unfold adenot, v_addi; cbn [a_base a_off]; rewrite Z.add_0_r;
              lazymatch e with context [ELit ?k] =>
                rewrite (shw_denotV V k VFV) by lia;
                pose proof (SHW_range sp0 k ltac:(lia) SPal ltac:(lia)); pose proof SSH_facts;
                apply (RestrictRun.rdn_restrictD asegs D);
                [ eapply (AGR_rdn M lo (bv_unsigned sp0) LOlo Mk); [exact AGk | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | lia |];
                  eapply (zrun_rdn8 _ _ _ _ (tm_zstk _ _ _ _ _ _ _ _ TM)); lia
                | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | rewrite u_small by lia; intros z Hz; apply D_ssh; cbn in Hz; lia ] end end
          | cbn [edenot]; evs; vm_compute; reflexivity ] end
      | cbn [edenot]; evs; rewrite ?alu_add_zlit by lia;
        first
          [ (* [comment removed for export] *) apply Bool.negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia
          | (* [comment removed for export] *)
            unfold bv_eqb, bv_ltu; rewrite !unsigned_lit by lia; first [apply Z.eqb_neq | apply Z.ltb_ge | apply Bool.negb_false_iff; apply Z.ltb_lt]; lia
          | (* [comment removed for export] *) rewrite and3_lit by lia; reflexivity
          | (* [comment removed for export] *) rewrite alu_or; unfold v_or; rewrite !unsigned_lit by lia; reflexivity
          | (* [comment removed for export] *) rewrite alu_and, alu_or; unfold v_and, v_or; apply rf_memset_align_false'; lia
          | (* [comment removed for export] *) rewrite alu_xor; unfold v_xor; apply not_ltu_small; lia ]
      | match goal with |- ?g => idtac "SC-LEFT:" g end ].

(* [comment removed for export] *)
  Lemma regs_ok_tree : forall E sr Rx, regs_ok E sr Rx -> regs_ok E sr (regs_tree Rx).
  Proof. intros E sr Rx HR r. rewrite getr_regs_tree. apply HR. Qed.

  (* [comment removed for export] *)
  Ltac to_tree HR :=
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rx _ _ _) _) _ =>
      apply (srzJ_getr_ext asegs (regs_tree Rx) Rx); [intros r; apply getr_regs_tree|];
      apply regs_ok_tree in HR; unfold regs_tree in HR |- * end.
  (* [comment removed for export] *)
  Ltac regvV HR r :=
    lazymatch type of HR with regs_ok ?E ?sr ?Rx =>
      let e := eval vm_compute in (sr_get sr r) in
      rewrite (reg_val E sr Rx r HR); change (sr_get sr r) with e; cbn [edenot]; evs; rewrite ?alu_add_zlit by lia
    end.


  (* [comment removed for export] *)
  Record FK (Mk : mem) : Prop := MKFK {
    fk_mi : mem_inv asegs Mk;
    fk_mapped : mapped Mk lo (bv_unsigned sp0);
    fk_stk : stk asegs Mk lo (bv_unsigned sp0);
    fk_buf : bytes_at asegs Mk (bv_unsigned P) buf;
    fk_shrd : forall c, CS c -> exists b, bytes_at asegs Mk (shadow_of AL c) [b];
    fk_rip : rip_consts Mk;
    fk_sn : sn_consts Mk;
    fk_amem : amem_consts Mk;
    fk_zstr : forall s : Z, (0x7fff8000 + lo / 8 <= s < 0x7fff8000 + STKHI / 8)%Z -> Mk (Z_to_bv 64 s) = Some (Z_to_bv 8 0);
    fk_zstk : forall a : Z, SSH_LO sp0 <= a < SSH_HI sp0 -> Mk (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
    fk_aobj : aobj asegs AL CS Mk (bv_unsigned P) (L + 1)
  }.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L17743517653.92 L18614817987.92 L2008272931.101 L24498169710.92 L27076589246.94 L29443216221.92 L29731801447.94 L30247691664.94 L37492600210.101L42153134065.92 L46058870405.92 L46530783016.92 L56457790905.92 L56765667309.94 L58965540039.89 L65604097635.92 L8120965920.94  L8564305960.92  00000[01e02k03n05D06007>08L09:09f0:M0;60<@0=D0=b0>^0?b0@[S3sp02lo5STKHI1P4path5extra1L3buf3Plo5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo4L63E5WINLO1H1s2HsS3sp04SPlo2lo6LOdeep5STKHI1P4path5extra1L3buf3Plo4L63E5WINLO1H1c2Q02H3S3sp04SPlo2lo4LOlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1H1s2HsS3sp04SPlo2lo4LOlo4LOhi5STKHI7STKHI641P4path5extra1L3buf3Plo4PL164L63E5WINLO1H2H11s2HsS3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path5extra1L3buf3Plo4L63E5WINLO1H2H21a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path5extra1L3buf3Plo4PL164L63E5WINLO1H1z2HzS3sp04SPlo5STKHI1P4path5extra1L3buf5WINLO1c2Q0S3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp05STKHI1P4path5extra1L3buf5WINLO2H1S3sp04SPhi5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo4L63E5WINLO1H1s2HsS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo4L63E5WINLO1H2H21a2HaS3sp05STKHI1P4path5extra5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo4L63E5WINLO1HS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo4L63E5WINLO1H2H21a2HaS3sp04SPlo5STKHI1P4path5extra1L3buf3Plo4PL164L63E5WINLO1H". (* [comment removed for export] *)
  Lemma facts : forall Mk, AGR M lo (bv_unsigned sp0) Mk -> FK Mk.
  Proof.
    intros Mk AG. pose proof SPlo. pose proof SPhi. pose proof (u64_range P). pose proof SSH_facts.
    pose proof TM as TM'. destruct TM' as [WIN RO ERR CAN RTC ZI ZS STKW MI _ _ _ _ _ _ _ _ _ _].
    pose proof (cs_ok_sb _ _ CSOK) as SB64.
    assert (MP : mapped Mk lo (bv_unsigned sp0)) by (eapply (AGR_mapped M lo (bv_unsigned sp0)); [exact AG | exact MAPD]).
    assert (ZSTR' : forall s : Z, (0x7fff8000 + lo / 8 <= s < 0x7fff8000 + STKHI / 8)%Z -> Mk (Z_to_bv 64 s) = Some (Z_to_bv 8 0)).
    { intros s Hs. eapply (AGR_byte M lo (bv_unsigned sp0) Mk s); [exact AG | lia | lia | lia | apply ZSH; exact Hs]. }
    assert (LBUF : Z.of_nat (length buf) = L + 1 + Z.of_nat (length extra)) by (subst buf L; rewrite length_app; cbn [length]; lia).
    split.
    - eapply (AGR_mem_inv M lo (bv_unsigned sp0) LOlo MI Mk AG ERR).
    - exact MP.
    - apply mapped_stk; [exact MP | lia | lia].
    - eapply (AGR_bytes_at M lo (bv_unsigned sp0) Mk); [exact AG | rewrite LBUF; lia | rewrite LBUF; lia | exact BY].
    - intros c Hc. destruct (SHRD c Hc) as [b Hb]. exists b.
      destruct CSOK as (C1 & _). destruct (C1 c Hc) as (Q0 & Q1 & Q2 & _). pose proof (CSTOP c Hc).
      eapply (AGR_bytes_at M lo (bv_unsigned sp0) Mk); [exact AG | cbn [length]; unfold shadow_of; rewrite ASB; lia | cbn [length]; unfold shadow_of; rewrite ASB; lia | exact Hb].
    - apply rtc_rip_consts. eapply asan_rtc_munch_fw; [apply (AGR_munch2 M lo (bv_unsigned sp0) Mk AG) | lia | exact RTC].
    - apply rtc_sn_consts. eapply asan_rtc_munch_fw; [apply (AGR_munch2 M lo (bv_unsigned sp0) Mk AG) | lia | exact RTC].
    - apply rtc_amem_consts. eapply asan_rtc_munch_fw; [apply (AGR_munch2 M lo (bv_unsigned sp0) Mk AG) | lia | exact RTC].
    - exact ZSTR'.
    - intros a Ha. eapply (AGR_byte M lo (bv_unsigned sp0) Mk a); [exact AG | lia | lia | lia | apply ZS; exact Ha].
    - apply (aobj_of_zero_range AL CS Mk (bv_unsigned P) (L + 1) CSOK ASB); [| lia | lia | intros s Hs; apply ZSTR'; lia].
      intros z Hz. apply SCS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac awp Ls := (repeat (first [ rewrite (edenot_addw0_r _ _) by (exact Ls) | rewrite (edenot_addw0_l _ _) by (exact Ls) | rewrite (edenot_exts4 _ _) by (exact Ls) ])); exact Ls.
  Ltac awn Ls := repeat (first [ rewrite (edenot_addw0_r _ _) by (awp Ls) | rewrite (edenot_addw0_l _ _) by (awp Ls) | rewrite (edenot_exts4 _ _) by (awp Ls) ]).
  (* [comment removed for export] *)
  Ltac swnorm := repeat match goal with
    | |- context [bv_swrap 32 ?z] =>
        lazymatch z with context [bv_swrap 32 _] => fail | context [bv_unsigned (Z_to_bv 64 _)] => fail | _ => rewrite (swrap32_small z) by lia end end.
  Ltac cmpL :=
    cbn [edenot ev]; repeat match goal with H : vals_ev ?V ?n = _ |- context [vals_ev ?V ?n] => rewrite H end;
    rewrite ?w_addw, ?w_subw; unfold v_addw, v_subw;
    rewrite ?alu_add, ?alu_sub, ?m_mul;
    repeat (progress (unorm; swnorm; rewrite ?vadd_ZZ, ?vsub_ZZ, ?vmul_ZZ));
    rewrite ?lts_ZZ, ?ltu_ZZ, ?eqb_ZZ by lia; cbn [negb];
    first [ reflexivity
          | apply Z.ltb_ge; lia | apply Z.ltb_lt; lia | apply Z.eqb_neq; lia | apply Z.eqb_eq; lia
          | apply Bool.negb_true_iff; first [apply Z.ltb_ge; lia | apply Z.eqb_neq; lia | apply Z.leb_gt; lia]
          | apply Bool.negb_false_iff; first [apply Z.ltb_lt; lia | apply Z.eqb_eq; lia | apply Z.leb_le; lia] ].


  (* [comment removed for export] *)
  Ltac azl := repeat match goal with
    | |- context [alu64 ALU_ADD ?x (Z_to_bv 64 ?k)] =>
        lazymatch x with context [alu64 ALU_ADD _ _] => fail | _ => rewrite (alu_add_zlit x k) by (unorm; lia) end
    end; unorm.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EnvV (V : list word) : env := Env (vals_ev V) (blobs_ev []).
  Definition TT : TSet := t_emit (W 2 (msg_cannot_open path)) (t_exit (exit_code 2) (m_fs model)).
  Definition FD2 (mo : Model) : Prop := fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Definition STG (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "PRk,(3:.&5.(3.&40.))PMk,P,(3.&40.)(9.(3.&8.))Pmok,$0.P,(21.O6.)P,(8.$4.(37.(3.&40.)O6.)O5.)P,(3;.(3<.O6.)O4.R5.)P,(3=.$3>.(3<.O6.)R5.O3.)P,(3?.VM,Vlo,(18.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(8.$40.(41.R7.)(41.Vmodel,))P,(42.R8.)P,A2.O1.O6.R:.(43.$3>.(44.(45.$46.R<.(17.&40.O2.)R;.(47.$3>.))R:.)$48.)")
(* [comment removed for export] *).
  Definition XL (V : list word) : Prop := vals_ev V 150 = Z_to_bv 64 L.
  Definition X0 (V : list word) (Mk : mem) : Prop := True.
  Definition XC (V : list word) (Mk : mem) : Prop := XL V.
  Definition XD (V : list word) (Mk : mem) : Prop := XL V /\ bytes_at asegs Mk (bv_unsigned sp0 - 447) path.
  Definition XE (V : list word) (Mk : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "(7.(49.O2.)(7.(4:.$3>.O1.(4;.(18.&40.Vsp0,)+1;?.)Vpath,)(4:.$3>.O1.(14.(4;.(18.&40.Vsp0,)+1;?.)VL,)(4<.(3.&8.)(17.&8.+:.)(26.(3.&8.))))))")
(* [comment removed for export] *).
  Definition S_A2 : Prop := forall V, STG V 74 srA2 knA2 0x5b1b4 X0.
  Definition S_B1 : Prop := forall V, STG V 106 srB1 knB1 0x5b504 X0.
  Definition S_B2 : Prop := forall V, STG V 138 srB2 knB2 0x5b1b4 X0.
  Definition S_C1 : Prop := forall V, STG V 172 srC1 knC1 0x0e79c4 XC.
  Definition S_D : Prop := forall V, STG V 205 srD knD 0x0e6f40 XD.
  Definition S_E : Prop := forall V, STG V 237 srE knE 0x0e6f40 XE.
  (* [comment removed for export] *)
  Definition TT64 : TSet := t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model)).
  Definition STG64 (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "PRk,(3:.&5.(3.&40.))PMk,P,(3.&40.)(9.(3.&8.))Pmok,$0.P,(21.O6.)P,(8.$4.(37.(3.&40.)O6.)O5.)P,(3;.(3<.O6.)O4.R5.)P,(3=.$3>.(3<.O6.)R5.O3.)P,(3?.VM,Vlo,(18.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(8.$40.(41.R7.)(41.Vmodel,))P,(42.R8.)P,A2.O1.O6.R:.(43.$3>.(44.(45.$46.R<.(17.&40.O2.)R;.(47.$3>.))R:.)$4=.)")
(* [comment removed for export] *).
  Definition S_D64 : Prop := forall V, STG64 V 205 (sc_sr resC2X) (sc_kn resC2X) (sc_ret resC2X) XC.

  (* [comment removed for export] *)
  Ltac block_AG AGk EQM OUT :=
    first [ eapply (AGR_blockb D _ M lo (bv_unsigned sp0) _ _ _ 0%nat (-16384) 0 sp0 AGk EQM OUT);
            [ cbv [ev EnvV]; apply vf0; assumption
            | vm_compute; reflexivity
            | clear -LOhi; lia
            | clear; lia
            | clear -LOlo; lia
            | pose proof (u64_range sp0) as XAG; clear -XAG; lia ]
          | idtac "block_AG: slow path";
            eapply (AGR_block D); [exact AGk | exact EQM | exact OUT |];
            intros x Dx Ox; destruct (D_out_zone x Dx Ox) as [Z1|[Z1|Z1]]; cbn [log_out]; unfold adenot, v_addi; cbn [a_base a_off edenot]; evs;
            rewrite ?(u_small 0) by lia; repeat split; rewrite ?u_small by lia; first [lia | exact I] ].

  (* [comment removed for export] *)
  Definition preZ : list Z := Eval vm_compute in match kread_bytes knD63e (EVar 0) (-464) 17 with Some vs => vs | None => [] end.
  Lemma preZ_eq : kread_bytes knD63e (EVar 0) (-464) 17 = Some preZ.
  Proof. vm_compute. reflexivity. Qed.
  Lemma preZ_msg : map (fun v => Z_to_bv 8 v) preZ = PRE17.
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L1157467871.71 L22990087647.71L2740393567.71 L27805217375.71L28651882079.71L29200756447.71L42861428319.71L47645164127.71L64277815263.71L64478848479.71L7532534367.71 00000N00l01J01h02F02d03B03`04>04\05:S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma preZ_range : Forall (fun v => 0 <= v < 256)%Z preZ.
  Proof. unfold preZ. repeat (constructor; [lia|]). constructor. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma nl_img : rdn asegs (fun _ => None) (Z_to_bv 64 0x208da) 1%nat = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19494940884.73L27606714393.76L39096254020.75L43785672655.7300000N01101T022S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma nl_bytes_at : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S8 ()) "PMk,Px,(3.&40.)(9.(3.&8.))P,Pa,$12.P,(7.(13.+10000.R1.)(16.R1.+?1000.))(8.(9.(3.&8.))A1.R3.(17.&40.R2.)(4>.(3.&8.)))(4:.$3>.R2.+208=:.(4<.(3.&8.)(17.&8.+:.)(26.(3.&8.))))")
(* [comment removed for export] *).
  Proof.
    intros Mk RO. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
    pose proof nl_img as RN. rewrite rdn_unfold in RN. unfold mrd in RN |- *. unfold wa. rewrite (RO 0x208da) by lia.
    destruct (seg_rom asegs (Z_to_bv 64 133338)); [|discriminate RN]. cbn [rdn] in RN. congruence.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac regs_ext RC V' VFV HR :=
      apply (srzJ_getr_ext asegs
               (mkR (getr RC (Z_to_bv 5 1)) sp0 (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90)
                    (getr RC (Z_to_bv 5 5)) (getr RC (Z_to_bv 5 6)) (getr RC (Z_to_bv 5 7)) (getr RC (Z_to_bv 5 8)) (getr RC (Z_to_bv 5 9))
                    (getr RC (Z_to_bv 5 10)) (getr RC (Z_to_bv 5 11)) (getr RC (Z_to_bv 5 12)) (getr RC (Z_to_bv 5 13))
                    (getr RC (Z_to_bv 5 14)) (getr RC (Z_to_bv 5 15)) (getr RC (Z_to_bv 5 16)) (getr RC (Z_to_bv 5 17))
                    (getr RC (Z_to_bv 5 18)) (getr RC (Z_to_bv 5 19)) (getr RC (Z_to_bv 5 20)) (getr RC (Z_to_bv 5 21))
                    (getr RC (Z_to_bv 5 22)) (getr RC (Z_to_bv 5 23)) (getr RC (Z_to_bv 5 24)) (getr RC (Z_to_bv 5 25))
                    (getr RC (Z_to_bv 5 26)) (getr RC (Z_to_bv 5 27))
                    (getr RC (Z_to_bv 5 28)) (getr RC (Z_to_bv 5 29)) (getr RC (Z_to_bv 5 30)) (getr RC (Z_to_bv 5 31))) RC);
      [ intros r; pose proof (ridx_range r) as Hi;
        rewrite <- (ridx_roundtrip r); set (i := ridx r) in *; clearbody i;
        destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
          [ .. | lia];
          lazymatch goal with |- _ = getr RC (Z_to_bv 5 (Z.of_nat ?k)) =>
            first
              [ (transitivity (getr RC (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
              | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
                lazymatch goal with |- _ = edenot _ (sr_get ?Ls ?rr) =>
                  let e := eval vm_compute in (sr_get Ls rr) in change (sr_get Ls rr) with e end;
                cbn [edenot];
                first [ reflexivity
                      | (lazymatch goal with |- _ = ev _ ?n =>
                           change (ev _ n) with (vals_ev V' n); rewrite (vf0 V' VFV); reflexivity end) ] ]
          end
      | ].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0380@L10522145838.117L10522145838.95 L10769333283.105L10799694563.126L10804238365.143L10804272427.125L11037419697.117L11037419697.95 L11580455375.106L11581664421.105L11586752988.106L11592156342.105L11938850325.140L12162701095.105L12352482293.117L12352482293.95 L12381576378.117L12381576378.95 L12773901487.146L13960147734.105L13966730876.106L13970631343.119L14309645649.117L14309645649.95 L14564977834.117L14564977834.95 L14949938610.105L15043846984.126L15047244086.117L15047244086.95 L15047376000.125L16252466602.117L16252466602.95 L17915679977.105L18381454536.105L18452601618.1  L19458343858.105L20567396662.95 L20921304178.125L21980766659.119L21987063930.105L21993516304.106L22084037116.105L22383075205.125L22494550619.105L22836635619.106L22836635619.126L22838081693.106L22838440585.105L22840162347.125L23018909934.90 L23027502411.115L23763115550.104L24671356340.125L24673046294.105L24675965564.106L24675965564.126L25271896031.147L25273991249.146L25273991639.145L25274020488.143L25276088791.144L25325349558.95 L26725352500.105L27242632186.105L27298204868.105L27304139182.106L27350566115.106L27352116571.105L27352437129.105L27362920496.119L27598234713.105L27834789085.125L29443215018.2  L29731801447.106L30135717720.105L30135878988.106L30829919541.105L30835910751.106L31003767474.105L31388510616.125L31563690188.95 L32012096746.105L32032333883.3  L32679584054.117L32679584054.95 L33355456082.117L33355456082.95 L33748443578.117L33748443578.95 L34301841077.123L34301841077.147L34634032557.90 L34642466824.115L35083152984.117L35083152984.95 L35894239326.125L36714795227.105L36782180292.117L36782180292.95 L37179020373.105L37185077567.106L37769436838.117L37769436838.95 L38557618280.105L38950490845.117L38950490845.95 L38950885227.125L38955452579.126L39015870258.105L39055317628.105L40044123314.105L40863868540.126L40867265666.143L40867690932.125L41531727740.105L42720804476.105L43784225316.106L43785639758.105L44024123370.95 L44072741110.146L44220201975.105L44492042876.105L45874800581.143L46533078311.2  L46952839184.106L46952839184.126L46956357592.125L46958833018.105L46965831548.105L48283514159.105L49938019708.105L50615126198.95 L50774715085.117L50774715085.95 L50863770329.106L50961132635.105L52416194011.105L52516241414.95 L52726078230.117L52726078230.95 L5316274158.140 L53172326615.105L53519159512.105L53992051850.117L53992051850.95 L54385772041.106L54388101987.105L54439012977.114L55069172786.105L55810752186.117L55810752186.95 L55888914490.106L55890197840.105L56739572530.127L56765667309.106L56840607695.125L58965918048.105L5926590833.147 L5928689407.146 L5928689529.145 L5928709158.143 L5930786681.144 L5967283506.105 L5968498776.106 L60820242395.105L61014438335.117L61014438335.95 L61453166143.125L62241966870.95 L62940874996.117L62940874996.95 L63334892984.105L63606425980.105L64111889970.105L64830566235.105L6602603065.117 L6602603065.95  L66167766678.117L66167766678.95 L66599922634.105L6755849374.105 L6757253620.106 L67812584585.107L67812584585.127L67818668628.147L67820762883.143L67820766300.145L67820766682.146L67822863452.144L6939957600.105 L7276823820.117 L7276823820.95  L8120965920.106 L8625402099.95  L9154751704.125 L9154980334.143 L9158275856.126 L9553928542.125 L9776606788.107 00001402102Y03H04704f05P06306V07908:09;09j0:l0;[0<C0=<0=n0>`0?M0@:0@n0AX0B;0B<0B=0Be0CO0D90D\0EF0F00FS0GP0H50H:0Hb0IE0Io0J^0KF0Kn0LQ0M@0Mh0NP0O?0Og0PO0Q>0R@0SI0Sl0T`0UM0V:0Vn0WX0XB0Xl0YV0Z@0[B0[e0\g0]d0^a0_I0`10`Y0aH0ak0bU0b^0cj0dR0e:0e]0f@0fh0gR0hO0i20i?0ii0jL0kU0lW0m`0nb10;11T12<12k12l12m13W14?15C16@17=18:19C1:E1;T1<>1<a1=K1>51>]1?J1@21@f1AZ1BN1C;1Ch1DK1Dn1EV1FH1G01G]1HO1HX1I@1Io1J^1KF1L31LV1MC1NE1OI1PF1Pi1QQ1R91R\1R]1R^1SM1T01TS1U=1U`1V]1WZ1XD1Xl1Z51[71\41]11]f1^N1_=1_e1`O1a91ac1bM1c71d81e91ea1fP1g81gb1hO1iS1jP1k31k`1lH1m01m_1nG1o61o^20[21>21a22c23R24<24f25P26:26d27G28628^29F29G2:62:e2;T2<>2<fS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo3HhiS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo3HhiS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf4LMAX4L63E5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI1P4path1L3buf4LMAX4L63E5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'1x2O2S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVFFS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1zS3sp0S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S2lo4LOloS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo1a2HaS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp02lo4LOhiS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp04SPlo2lo4LOhi5STKHI7STKHI641P4path1L3buf3Plo4PL164L63E5WINLO1V2LV3Hlo2V'3LV'1x2O12O2S3sp04SPlo2lo4LOhi5STKHI7STKHI641P4path1L3buf3Plo4PL164L63E5WINLO1V2LV3Hlo2V'3LV'1x2O12O2S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV2V'3LV'FFS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HhiS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HhiS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL164L63E5WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'1x2O1S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'2RC1i2HiS3sp03XAGS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVFFS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV2Rm3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX4L63E5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HhiS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HhiS2AL2CS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV1a2HaS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo3HhiS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo3HhiS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPlo5STKHI1P4path1L3buf4L63E5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3Hlo2V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4L63E5WINLO1V2LV3HhiS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2Hz4SPlo7STKHIlo3Plo4L63E3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1a2HaFS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2Hz". (* [comment removed for export] *)
  Theorem stage_D63 : S_D.
  Proof.
    intros V Rk Mk mok VFV LV HR HK AGk HKk FS FD XD1.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSH_facts as SSF. pose proof (u64_range P) as PR.
    unfold EnvV in HR, HK. destruct XD1 as [XL1 BYP1]. unfold XL in XL1. rename XL1 into EV150.
    assert (HL : L = Z.of_nat (length path)) by reflexivity.
    assert (Lsmall : (bv_unsigned (edenot {| ev := vals_ev V; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
    { cbn [edenot ev]. rewrite EV150, u_small by lia. lia. }
    pose proof TM as TM'. destruct TM' as [_ RO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrD63 205%nat true covtac).
    all: try solve_sc.
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall; cmpL end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "D63-SC-LEFT" g end.
    rename EQM into EQMA. rename OUT into OUTA. rename R0 into RA. rename M0 into MA0. rename HKmo into HKA. rename MM into MMA.
    assert (AGA : AGR M lo (bv_unsigned sp0) MA0) by (block_AG AGk EQMA OUTA).
    (* [comment removed for export] *)
    assert (BYPA : bytes_at asegs MA0 (bv_unsigned sp0 - 447) path).
    { eapply (bytes_at_block D _ Mk MA0 _ _ _ BYP1 EQMA). intros z Hz. split.
      - apply (D_frame z (z + 1)); unfold L in *; lia.
      - cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
        rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [unfold L in *; lia | exact I]. }
    assert (NLA : bytes_at asegs MA0 0x208da [Z_to_bv 8 10]).
    { apply nl_bytes_at. intros a Ha. eapply (AGR_byte M lo (bv_unsigned sp0) MA0 a); [exact AGA | lia | lia | lia | apply RO; exact Ha]. }
    clear AGk EQMA OUTA.
    (* [comment removed for export] *)
    unfold TT. rewrite msg_cannot_open_eq. unfold W.
    replace (PRE17 ++ path ++ [Z_to_bv 8 10]) with ((PRE17 ++ path) ++ [Z_to_bv 8 10]) by (rewrite ?app_assoc; reflexivity).
    change (Z_to_bv 64 2) with (Z_to_bv 64 (sc_fd resD63)).
    assert (FdA : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { unfold FD2 in FD. unfold m_fds in *. destruct MMA as (E1 & _). rewrite E1. exact FD. }
    assert (SC1 : stdio_call 205%nat srD63e knD63e = Some resD63) by (vm_compute; reflexivity).
    assert (LP : Z.of_nat (length (PRE17 ++ path)) = 17 + L).
    { rewrite length_app, PRE17_len. unfold L. lia. }
    eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly V (blobs_ev []) srD63e knD63e RA MA0 mo resD63 (PRE17 ++ path) [Z_to_bv 8 10]
              (t_exit (exit_code 2) (m_fs model)) HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resD63 edenot];
      rewrite ?LP; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    + rewrite LV. exact SC1.
    + evs. azl. unorm. lia.
    + evs. azl. unorm. lia.
    + unorm. reflexivity.
    + lia.
    + right. evs. azl. unorm. lia.
    + left. evs. azl. unorm. lia.
    + unorm. lia.
    + evs. azl. unorm. lia.
    + unorm. lia.
    + (* [comment removed for export] *)
      evs. rewrite alu_add_zlit by lia. rewrite u_small by lia.
      rewrite <- preZ_msg. rewrite length_app, length_map. change (length preZ) with 17%nat.
      apply rdn_app_Z; [ | | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
      * pose proof (kread_bytes_rdn _ MA0 knD63e (EVar 0) 17 (-464) preZ HK preZ_eq preZ_range) as RD.
        cbn [edenot ev] in RD. rewrite (vf0 V VFV) in RD. apply RD; lia.
      * change (Z.of_nat 17) with 17.
        pose proof (bytes_at_rdn asegs MA0 _ path 0 (length path) BYPA ltac:(lia)) as RD. rewrite Z.add_0_r in RD. cbn [skipn] in RD. rewrite firstn_all in RD.
        unfold wa in RD. replace (bv_unsigned sp0 + -464 + 17) with (bv_unsigned sp0 - 447) by lia. exact RD.
    + (* [comment removed for export] *)
      unorm. pose proof (bytes_at_rdn asegs MA0 _ [Z_to_bv 8 10] 0 1 NLA ltac:(cbn; lia)) as RD. rewrite Z.add_0_r in RD. cbn [skipn firstn] in RD.
      unfold wa in RD. exact RD.
    + exact FdA.
    + exact HKA.
    + intros z Hz. revert Hz. evs. azl. intros Hz. apply WCS. lia.
    + intros z Hz. revert Hz. evs. azl. unorm. intros Hz. left. apply WCS. lia.
    + intros z Hz. revert Hz; unorm; intros Hz. left. apply FCS. lia.
    + unfold t_exit. apply t_emit_has_nil.
    + (* [comment removed for export] *)
      intros Rm MB moB HPOSTB HRm HKm HKB MMB. clear HR HK. rename HRm into HR. rename HKm into HK.
      pose proof (vf0 V VFV) as V0eq.
      pose proof (VF_app V (junk_vals Rm) VFV) as VFV'. set (V' := V ++ junk_vals Rm) in *.
      assert (LV' : length V' = 237%nat) by (subst V'; rewrite length_app, junk_vals_length, LV; reflexivity).
      assert (EV150' : vals_ev V' 150 = Z_to_bv 64 L) by (subst V'; rewrite vals_ev_app_l by (rewrite LV; lia); exact EV150).
      clearbody V'. clear VFV. rename VFV' into VFV.
      assert (Lsmall' : (bv_unsigned (edenot {| ev := vals_ev V'; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
      { cbn [edenot ev]. rewrite EV150', u_small by lia. lia. }
      assert (AGB : AGR M lo (bv_unsigned sp0) MB).
      { eapply AGR_trans; [exact AGA|]. destruct HPOSTB as [Pagree Pgrows Pwend Pwpos Pwbase].
        cbn [sc_sp sc_f sc_bufp sc_bufsz resD63 edenot ev] in Pagree. rewrite V0eq in Pagree. revert Pagree. azl. intros Pagree.
        split; [| exact Pgrows]. intros x [O1 O2]. apply Pagree; lia. }
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
      time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrE63 237%nat true covtac).
      all: try solve_sc.
      all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall'; cmpL end).
      all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "E63-SC-LEFT" g end.
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) ?mon) _ => rename Rn into RB'; rename Mn into MB'; rename mon into moB' end.
      rename EQM into EQMB. rename OUT into OUTB. rename HKmo into HKB'. rename MM into MMB'.
      assert (AGB' : AGR M lo (bv_unsigned sp0) MB') by (block_AG AGB EQMB OUTB).
      clear EQMB OUTB.
      (* [comment removed for export] *)
      apply (srzJ_conseq asegs _ (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd resE63))) ([] ++ [])) (t_exit (exit_code 2) (m_fs model))));
        [| cbn [map app]; apply t_emit_nil_eq; unfold t_exit; apply t_emit_has_nil].
      assert (FdB : fd_lookup (m_fds moB') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
      { rewrite (mo_mat_fds' _ _ MMB'), (mo_mat_fds' _ _ MMB). exact FdA. }
      assert (SC2 : stdio_call 237%nat srE63e knE63e = Some resE63) by (vm_compute; reflexivity).
      eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly V' (blobs_ev []) srE63e knE63e RB' MB' moB' resE63 [] []
                (t_exit (exit_code 2) (m_fs model)) HR HK);
        cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resE63 edenot length Z.of_nat].
      * rewrite LV'. exact SC2.
      * evs. azl. unorm. lia.
      * evs. azl. unorm. lia.
      * unorm. reflexivity.
      * lia.
      * right. evs. azl. unorm. lia.
      * left. evs. azl. unorm. lia.
      * unorm. lia.
      * evs. azl. unorm. lia.
      * unorm. lia.
      * reflexivity.
      * reflexivity.
      * exact FdB.
      * exact HKB'.
      * intros z Hz. revert Hz. evs. azl. intros Hz. apply WCS. lia.
      * intros z Hz. revert Hz. evs. azl. unorm. intros Hz. lia.
      * intros z Hz. revert Hz; unorm; intros Hz. lia.
      * unfold t_exit. apply t_emit_has_nil.
      * (* [comment removed for export] *)
        intros Rm2 MC moC HPOST HRm2 HKm2 HKC MMC. clear HR HK. rename HRm2 into HR. rename HKm2 into HK.
        pose proof (vf0 V' VFV) as V0eq'.
        pose proof (VF_app V' (junk_vals Rm2) VFV) as VFV''. set (V'' := V' ++ junk_vals Rm2) in *. clearbody V''. clear VFV. rename VFV'' into VFV.
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
        time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrF 269%nat true covtac).
        all: try solve_sc.
        lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
        rename EQM into EQMC. rename OUT into OUTC. rename HKmo into HKD. rename MM into MMD.
        regs_ext RC V'' VFV HR.
        change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
        lazymatch goal with |- srealizesJ _ (mkCfg _ ?mox) _ => replace (m_fs model) with (m_fs mox) end.
        2:{ rewrite (mo_mat_fs _ _ MMD), (mo_mat_fs _ _ MMC), (mo_mat_fs _ _ MMB'), (mo_mat_fs _ _ MMB), (mo_mat_fs _ _ MMA). exact FS. }
        apply (die2_at_96e04_deep AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly sp0 ltac:(lia) ltac:(lia) SPal WCS lo LOlo
                 M can tid wp0 rp0 wp1 rp1 TM); [| exact HKD].
        (* [comment removed for export] *)
        assert (AGC : AGR M lo (bv_unsigned sp0) MC).
        { eapply AGR_trans; [exact AGB'|]. destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
          cbn [sc_sp sc_f sc_bufp sc_bufsz resE63 edenot ev] in Pagree. rewrite V0eq' in Pagree. revert Pagree. azl. intros Pagree.
          split; [| exact Pgrows]. intros x [O1 O2]. apply Pagree; lia. }
        assert (AGD : AGR M lo (bv_unsigned sp0) MD) by (block_AG AGC EQMC OUTC).
        destruct AGD as [AGm GRm].
        split.
        -- intros x O1 O2. apply AGm. split; [exact O1 | exact O2].
        -- intros x Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & _). apply AGm. split; lia.
        -- exact GRm.
        -- apply mem_grows_wmono. exact GRm.
        -- krd HK (0x0fa488 + 140)%Z 4%nat F140. krd HK (0x0fa488 + 40)%Z 8%nat F40. krd HK (0x0fa488 + 56)%Z 8%nat F56.
           krd HK (0x0fa488 + 8)%Z 8%nat F8. krd HK (0x0fa488 + 16)%Z 8%nat F16.
           eexists. eexists. unfold file_clean. fold asegs. repeat split.
           ++ exact F140.
           ++ rewrite F40. reflexivity.
           ++ rewrite F56. reflexivity.
           ++ rewrite F8. reflexivity.
           ++ rewrite F16. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End OF.
