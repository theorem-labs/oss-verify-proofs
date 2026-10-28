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
Ltac2 gd_tbl_A_tail_openfail_S10 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.outzone"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "OF.VF"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.blobs_ev"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.B.A_refused.SHW"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Nat.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "OF.EnvV"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.AGR"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OF.FD2"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "OF.TT"; "OF.XL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "OF.TT64"; "Corelib.Init.Datatypes.None"].

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
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VKI,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VKI,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Pmo,$0.Pmo',$0.P,A1.VKI,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VKI,R6.")
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
  Hypothesis ZSH : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Ps,$12.P,(7.(13.(14.+7???8000.(15.Vlo,+8.))R1.)(16.R1.(14.+7???8000.(15.VSTKHI,+8.))))(8.(9.(3.&8.))A1.VM,(17.&40.R2.)(;.(3.&8.)(17.&8.=)))")
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
  Hypothesis L64 : (64 <= L)%Z.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30247682266.71L35495549846.7000000j01BS3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo3L641z2Hz1H2H0S3sp05STKHI1P4path1L3buf". (* [comment removed for export] *)
  Lemma PCS : crange CS (bv_unsigned P - bv_unsigned P mod 64) (STKHI - (bv_unsigned P - bv_unsigned P mod 64)).
  Proof. intros z Hz. apply SCS. pose proof LOhi. pose proof (Z.mod_pos_bound (bv_unsigned P) 64 ltac:(lia)). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SHRD : forall c, CS c -> exists b, bytes_at asegs M (shadow_of AL c) [b].
  Hypothesis CSTOP : forall c, CS c -> (c < 2^47)%Z.

  Let WINLO := (bv_unsigned sp0 - 4096)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0)%Z; (0x7fffc118, 0x7fffc120)%Z; (SSH_LO sp0, SSH_HI sp0)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32276418883.71L57167447340.71L57657395591.7200000N01601kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H". (* [comment removed for export] *)
  Lemma SSH_facts : (0x7fff8000 <= SSH_LO sp0)%Z /\ (SSH_HI sp0 <= 2^46)%Z /\ (SSH_LO sp0 < SSH_HI sp0)%Z.
  Proof. pose proof (SHW_range sp0 (-64) ltac:(lia) SPal ltac:(lia)). unfold SSH_LO, SSH_HI in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.73000010S3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma D_Dseg : forall a : word, segcov asegs (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.7300000PS3sp05STKHI1P4path1L3buf5WINLO1c". (* [comment removed for export] *)
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L51355856640.75L5268879960.75 L57161095762.75L60694983881.77L61028787006.75L67812584585.7500000h01H02002S03103TS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1zS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2A1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2Hz". (* [comment removed for export] *)
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L30901545954.77L46534914516.77L60924549197.7700001201U028S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1a1b2Ha2Hb1z2HzS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_frame : forall a b, (bv_unsigned sp0 - 4096 <= a)%Z -> (b <= bv_unsigned sp0)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.77000012S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1a1b2Ha2Hb1z2Hz". (* [comment removed for export] *)
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
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Pqlo,$12.Pqhi,$12.P,(13.(14.(18.&40.Vsp0,)-1000.)R2.)P,(13.R2.(14.(18.&40.Vsp0,)=))(19.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13440388671.74L15567222060.74L52039345437.7400000S01301SS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLO1H". (* [comment removed for export] *)
  Lemma D_ssh : DcovZ D (SSH_LO sp0) (SSH_HI sp0).
  Proof. pose proof SSH_facts. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L5287174892.7500001;S3sp02lo5STKHI1P4path1L3buf5WINLO1x2Hr2O24SPlo4LOhi7STKHI643Plo4PL163L642O1". (* [comment removed for export] *)
  Lemma D_out_zone : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Px,(3.&40.)P,(8.$1:.A1.VD,R1.$1;.)P,(1<.Vlo,(18.&40.Vsp0,)R2.)(1=.(7.(7.(13.+10000.(18.&40.R3.))(16.(18.&40.R3.)+65?000.))(1>.(7.(13.+?:488.(18.&40.R3.))(16.(18.&40.R3.)+?:570.))))(1=.(7.(13.+7???<118.(18.&40.R3.))(16.(18.&40.R3.)+7???<120.))(7.(13.(1?.Vsp0,)(18.&40.R3.))(16.(18.&40.R3.)(20.Vsp0,)))))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L21188810707.77L9784235213.75 00000m01iS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1V2P21n2HnS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1V3ext2P2". (* [comment removed for export] *)
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "01;0?L13042945941.85L13484217602.85L14054083309.89L14499496082.85L15439463048.85L16774753289.85L17543312104.87L1756166345.85 L18928696722.85L2183569985.85 L21927717721.85L21986899558.85L22604873481.85L2431328725.89 L24690173574.85L24992216082.85L25271909867.85L2564951689.85 L25940753974.85L27134698386.85L27315410273.85L27352604565.85L28434372873.85L29762371858.85L31327315070.89L31396711570.85L32648418366.91L32873232769.89L33148392579.85L33669037980.85L34577004134.85L34774111081.85L3506990866.85 L3829630897.89 L39213365269.85L39510883410.85L40253358217.85L43030311433.85L44353219849.85L44510486418.85L44751598473.85L44851494802.85L4504975677.89 L46809767186.85L48461698953.85L5004984661.85 L51238950418.85L52457697417.85L52875384210.85L53519161933.89L53519190958.85L54226205864.85L54967497737.85L55007380242.85L55149030888.87L55662616861.89L55849630025.85L5641132690.85 L58560891017.85L58961367305.85L5926593349.85 L61064399881.85L62675677899.85L6275277449.85 L64037435666.85L64202541330.85L64791502857.85L65502196882.85L65732472201.85L66336703634.85L67631326282.89L68058909735.85L68075363561.85L7781517330.85 L9911486354.85 00000j01H02J02h03F03d04G04e05C05a06?06b07@07b08@08^09<09Z0:80:V0;90;\0<:0<X0=T0>20?60?[0?\0@:0@X0A60AT0B:0B;0BY0C70CU0D30DQ0Do0EM0F10FO0Fm0GU0H30HQ0Ho0IO0Im0In0JL0Jj0KM0LL0Lj0MH0Mf0ND0Nb0O@0OA0O_0P=0P[0Q90QW0R50RS0S80SV0T40TR0U0S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL163L645WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H2H01d1m2Hd2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1n1BS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf3Plo4PL163L645WINLO1H3off1n1B1CS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H1d1m2Hd2Hm1x2HxS3sp05STKHI1P4path1L3buf5WINLO1d1m2HdFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1n1CFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1AS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1mS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL163L645WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L17034448047.78L29784460291.77L3479498253.77 L43935895424.79L47803405696.79L55715225071.77L59576963504.79L63368316460.79L63368316589.78L63368325619.77L64266648997.77L66561261592.79L8929201831.80 00000m01K02R03803^04<04\05<05\06:07407T08WS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL163L645WINLO1k2HkS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL163L645WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1kS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H1k2Hk2H12H22H3". (* [comment removed for export] *)
  Lemma shw_denotV : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "PV,(1.(3.&40.))Pk,$12.P,(21.R2.)P,(7.(13.-1000.R2.)(13.R2.=))(8.$12.(18.&40.(22.(23.(24.R4.)(25.(26.(1.(3.&8.)))))(27.$28.(27.$29.(27.$2:.(27.$29.(2;.#0.)(2<.R3.))(2<.+3.))(2<.+7???8000.))(2<.-8.))))(2=.Vsp0,R3.))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L3479498253.75 L35907637249.76L40825277235.75L53519168529.76L55715225071.75L64266638075.76L64266648997.7500001701Z02802X03604004jS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL163L645WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H1k2HkS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H1k2Hk". (* [comment removed for export] *)
  Lemma and3_lit : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Pk,$12.P,(7.(13.-1000.R1.)(13.R1.=))(8.$1:.(2>.&40.(2?.$28.(17.&40.(14.(18.&40.Vsp0,)R2.))(17.&40.+3.))(17.&40.=))(30.(31.R2.+4.)=))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros k Hk. rewrite alu_and. unfold v_and. rewrite (unsigned_lit 3), (unsigned_lit (bv_unsigned sp0 + k)) by lia.
    rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned sp0 + k) 4 ltac:(lia)).
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply (mod4_of_sp (bv_unsigned sp0) k); [exact SPal | lia | reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L37106200957.75L5744834796.75 L61929758668.75L8443611008.75 00000]01@01c02FS3sp04SPlo5STKHI1P4path1L3buf5WINLO1x1n2Hx2HnS3sp05STKHI1P4path1L3buf5WINLO1x2HxS3sp05STKHI1P4path1L3buf5WINLO1n2HnS3sp05STKHI1P4path1L3buf5WINLO1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu_small : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Px,$12.Pn,$12.P,(7.(13.=R2.)(16.R2.(32.+2.+30.)))P,(7.(13.=R2.)(16.R2.(32.+2.+10.)))(8.$1:.(33.&40.(17.&40.(34.(18.&40.(17.&40.R4.))(18.&40.(17.&40.-1.))))(17.&40.R3.))$35.)")
(* [comment removed for export] *).
  Proof.
    intros x n Hx Hn. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "Px,(3.&40.)Pk,$12.P,(7.(13.=(14.(18.&40.R2.)R1.))(16.(14.(18.&40.R2.)R1.)(32.+2.+40.)))(8.(3.&40.)(2?.$29.R3.(17.&40.R2.))(17.&40.(14.(18.&40.R3.)R2.)))")
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
  Lemma vals_ev_app_ge : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "PV,(1.(3.&40.))Pext,(1.(3.&40.))Pn,$4.P,(36.(37.(3.&40.)R3.)R1.)(8.(3.&40.)(24.(38.(3.&40.)R4.R3.)R2.)(24.R3.(39.R2.(37.(3.&40.)R4.))))")
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L17743517653.92 L18614817987.92 L2008272931.101 L24498169710.92 L27076589246.94 L29443216221.92 L29731801447.94 L30247691664.94 L37492600210.101L42153134065.92 L46058870405.92 L46530783016.92 L56457790905.92 L56765667309.94 L58965540039.89 L65604097635.92 L8120965920.94  L8564305960.92  00000[01d02i03k05@05l07908F09409`0:G0;00<90=<0=Z0>B0?E0@=S3sp02lo5STKHI1P4path5extra1L3buf3Plo5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo3L645WINLO1H1s2HsS3sp04SPlo2lo6LOdeep5STKHI1P4path5extra1L3buf3Plo3L645WINLO1H1c2Q02H3S3sp04SPlo2lo4LOlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1H1s2HsS3sp04SPlo2lo4LOlo4LOhi5STKHI7STKHI641P4path5extra1L3buf3Plo4PL163L645WINLO1H2H11s2HsS3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path5extra1L3buf3Plo3L645WINLO1H2H21a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path5extra1L3buf3Plo4PL163L645WINLO1H1z2HzS3sp04SPlo5STKHI1P4path5extra1L3buf5WINLO1c2Q0S3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp05STKHI1P4path5extra1L3buf5WINLO2H1S3sp04SPhi5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo3L645WINLO1H1s2HsS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo3L645WINLO1H2H21a2HaS3sp05STKHI1P4path5extra5WINLOS3sp05STKHI1P4path5extra1L3buf3L645WINLOS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo3L645WINLO1H2H21a2HaS3sp04SPlo5STKHI1P4path5extra1L3buf3Plo4PL163L645WINLO1H". (* [comment removed for export] *)
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
  Definition STG (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "PRk,(3:.&5.(3.&40.))PMk,P,(3.&40.)(9.(3.&8.))Pmok,$0.P,(21.O6.)P,(8.$4.(37.(3.&40.)O6.)O5.)P,(3;.(3<.O6.)O4.R5.)P,(3=.$3>.(3<.O6.)R5.O3.)P,(3?.VM,Vlo,(18.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(8.$40.(41.R7.)(41.Vmodel,))P,(42.R8.)P,A2.O1.O6.R:.(43.$3>.(44.(45.$46.R<.(17.&40.O2.)R;.(47.$3>.))R:.)$48.)")
(* [comment removed for export] *).
  Definition XL (V : list word) : Prop := vals_ev V 150 = Z_to_bv 64 L.
  Definition X0 (V : list word) (Mk : mem) : Prop := True.
  Definition XC (V : list word) (Mk : mem) : Prop := XL V.
  Definition XD (V : list word) (Mk : mem) : Prop := XL V /\ bytes_at asegs Mk (bv_unsigned sp0 - 447) path.
  Definition XE (V : list word) (Mk : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "(7.(49.O2.)(7.(4:.$3>.O1.(4;.(18.&40.Vsp0,)+1;?.)Vpath,)(4:.$3>.O1.(14.(4;.(18.&40.Vsp0,)+1;?.)VL,)(4<.(3.&8.)(17.&8.+:.)(26.(3.&8.))))))")
(* [comment removed for export] *).
  Definition S_A2 : Prop := forall V, STG V 74 srA2 knA2 0x5b1b4 X0.
  Definition S_B1 : Prop := forall V, STG V 106 srB1 knB1 0x5b504 X0.
  Definition S_B2 : Prop := forall V, STG V 138 srB2 knB2 0x5b1b4 X0.
  Definition S_C1 : Prop := forall V, STG V 172 srC1 knC1 0x0e79c4 XC.
  Definition S_D : Prop := forall V, STG V 205 srD knD 0x0e6f40 XD.
  Definition S_E : Prop := forall V, STG V 237 srE knE 0x0e6f40 XE.
  (* [comment removed for export] *)
  Definition TT64 : TSet := t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model)).
  Definition STG64 (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "PRk,(3:.&5.(3.&40.))PMk,P,(3.&40.)(9.(3.&8.))Pmok,$0.P,(21.O6.)P,(8.$4.(37.(3.&40.)O6.)O5.)P,(3;.(3<.O6.)O4.R5.)P,(3=.$3>.(3<.O6.)R5.O3.)P,(3?.VM,Vlo,(18.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(8.$40.(41.R7.)(41.Vmodel,))P,(42.R8.)P,A2.O1.O6.R:.(43.$3>.(44.(45.$46.R<.(17.&40.O2.)R;.(47.$3>.))R:.)$4=.)")
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
  Lemma nl_img : rdn asegs (fun _ => None) (Z_to_bv 64 0x208da) 1%nat = Some [Z_to_bv 8 10].
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L19494940884.73L27606714393.76L39096254020.75L43785672655.7300000N01101T022S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma nl_bytes_at : ltac2:(CDefT.buildp (gd_tbl_A_tail_openfail_S10 ()) "PMk,Px,(3.&40.)(9.(3.&8.))P,Pa,$12.P,(7.(13.+10000.R1.)(16.R1.+?1000.))(8.(9.(3.&8.))A1.R3.(17.&40.R2.)(4>.(3.&8.)))(4:.$3>.R2.+208=:.(4<.(3.&8.)(17.&8.+:.)(26.(3.&8.))))")
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "02[0@L10224213514.128L10522145838.106L10522145838.142L10769333283.152L10799694563.152L10804238365.169L10804272427.151L10828472560.128L11037419697.106L11037419697.142L11853314448.128L11938850325.166L12162701095.152L12352482293.106L12352482293.142L12381576378.106L12381576378.142L12773901487.172L13720533833.151L14098852785.125L14309645649.106L14309645649.142L14334882987.149L14564977834.106L14564977834.142L14773974451.125L14960291423.151L15043846984.152L15047244086.106L15047244086.142L15047376000.151L1555929440.151 L16252466602.106L16252466602.142L18381454536.152L18452601618.1  L18883718650.128L20567396662.106L20921304178.151L21114452482.128L22383075205.151L22836635619.152L22840162347.151L23018909934.89 L23027502411.141L23894205492.124L24623709742.141L24625795186.141L24669031985.128L24671356340.151L24675965564.152L25271896031.173L25273991249.172L25273991639.171L25274020488.169L25276088791.170L25325349558.106L25343251584.152L25347820360.151L25733274633.128L26284087056.128L26507518861.128L26529290239.128L26725352500.152L27076589246.130L27242632186.152L27769815572.151L27774655964.152L27834789085.151L27905951373.128L28492528645.128L29443215018.2  L29731801447.125L30247691664.130L30426774554.128L32012096746.152L32032333883.3  L32679584054.106L32679584054.142L33355456082.106L33355456082.142L33748443578.106L33748443578.142L34301841077.173L34634032557.89 L34642466824.141L35083152984.106L35083152984.142L35223706973.128L36782180292.106L36782180292.142L37155417985.125L37622523289.151L37769436838.106L37769436838.142L38557618280.152L38950490845.106L38950490845.142L38950885227.151L38955452579.152L40237970414.151L40863868540.152L40867265666.169L40867690932.151L42151021506.136L42333743922.151L42567548243.152L42571358875.151L43772843625.128L44024123370.106L44072741110.172L44930239921.124L45874800581.169L46533078311.2  L46952839184.152L46956357592.151L50615126198.106L50774715085.106L50774715085.142L52726078230.106L52726078230.142L5305592157.128 L5316274158.166 L53174770293.151L53519159512.152L53992051850.106L53992051850.142L54439012977.140L55810752186.106L55810752186.142L56408548612.125L56418692864.128L56739572530.153L56765667309.125L57131020424.130L58695151760.149L5926590833.173 L59281996761.128L5928689407.172 L5928689529.171 L5928709158.169 L5930786681.170 L60669077807.149L60679793201.128L61014438335.106L61014438335.142L61345436741.128L62940874996.106L62940874996.142L63556147876.124L6602603065.106 L6602603065.142 L66167766678.106L66167766678.142L66538926532.152L6751606201.128 L67812584585.153L67818668628.173L67820762883.169L67820766300.171L67820766682.172L67822863452.170L7276823820.106 L7276823820.142 L8120965920.125 L8321648537.124 L9154751704.151 L9154980334.169 L9158275856.152 L9553928542.151 L9776606788.130 00000a01H02?03703o04g05_06N07107d08Z09R0:c0;K0<C0<o0=k0>f0?Y0@D0@g0AZ0BF0BG0BH0Bk0Cc0DV0E90El0F_0GR0H50Hh0I`0Ie0JV0K90Kl0LX0MP0NH0O@0Ol0Ph0QK0RD0Sd0TZ0UW0VT0WG0X:0Xm0Y`0ZS0[?0\70\o0]c0^W0_C0_o0`g0b>0c60d30e00ec0fO0g@0gI0hT0j80jl0kd0l10lT0mG0n30no0o[10W12812`13X13Y13Z14K15215i16Q17E18118m1:K1:n1;a1<T1=G1>:1?71@41A11Ae1BY1CQ1DI1E51E]1FX1G;1H61H?1I71Io1J[1KB1L91L:1L;1Ll1Md1NW1OO1P21Pe1QX1RD1S@1Sh1TY1UW1V?1WQ1X^1YQ1ZG1[:1[m1\`1]S1^I1_?1_g1`_1aS1b:1c11cT1d<1e41e\1fT1gG1h31hk1i^1jQ1kD1l71lj1mR1nJ1o21o]20U21M22E23824JS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1V2LV3Hlo3ds54LEN52V'3LV'1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1x2O2S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5FFS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp0S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51x1l2l02HxS3sp04SPlo2lo5STKHI7STKHI641P4path1L3buf3Plo4PL163L645WINLO1V2LV3Hlo3ds54LEN51H1x2Hx1g7STKHIlo1lS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp04SPlo4SPal2lo5STKHI7STKHI641P4path1L3buf3Plo4PL163L645WINLO1V2LV3Hlo3ds54LEN51s2HsS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S2lo4LOloS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1V2LV3Hlo1a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo3L645WINLO1V2LV3Hlo3ds54LEN51z2Hz4SPal7STKHI644PL16S3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp02lo4LOhiS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo2lo4LOhi5STKHI7STKHI641P4path1L3buf3Plo4PL163L645WINLO1V2LV3Hlo3ds54LEN52V'3LV'1x2O12O2S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds54LEN52V'3LV'FFS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51x2HxS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL163L645WINLO1V2LV3Hlo3ds54LEN52V'3LV'1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51x2HxS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1x2O1S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'2RC1i2HiS3sp03XAGS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf3L645WINLO1V2LV3ds54LEN52V'3LV'FFS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52R33LV'S3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S2AL2CS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV1a2HaS3sp04SPlo2lo5STKHI7STKHI641P4path1L3buf3Plo4PL163L645WINLO1V2LV3Hlo3ds54LEN51s2HsS3sp04SPlo2lo5STKHI7STKHI641P4path1L3buf3Plo4PL163L645WINLO1V2LV3Hlo3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo6LOdeep5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds54LEN52V'3LV'S3sp02lo4LOhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf3L645WINLO1V2LVS3sp05STKHI1P4path1L3buf3L645WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN5S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV1a2HaS3sp02lo4LOlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN52V'3LV'S3sp05STKHI1P4path1L3buf5WINLO1V2LV3ds54LEN51z2Hz4SPlo2lo7STKHI643Plo4PL163L643Hlo". (* [comment removed for export] *)
  Theorem stage_D64 : S_D64.
  Proof.
    intros V Rk Mk mok VFV LV HR HK AGk HKk FS FD XC1.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSH_facts as SSF. pose proof (u64_range P) as PR.
    unfold EnvV in HR, HK. unfold XC, XL in XC1. rename XC1 into EV150.
    assert (HL : L = Z.of_nat (length path)) by reflexivity.
    assert (Lsmall : (bv_unsigned (edenot {| ev := vals_ev V; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
    { cbn [edenot ev]. rewrite EV150, u_small by lia. lia. }
    pose proof TM as TM'. destruct TM' as [_ RO _ _ _ ZI _ _ _ _ _ _ _ _ _ _ _ _ _].
    destruct (facts Mk AGk) as [MIk MPk STk BUFk SHRDk RIPk SNk AMk ZSTRk ZSTKk OBJk].
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrD64 205%nat true covtac).
    all: try solve_sc.
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall; cmpL end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "D64-SC-LEFT" g end.
    rename EQM into EQM1. rename OUT into OUT1. rename R0 into R1. rename M0 into M1. rename mo into mo1. rename HKmo into HK1. rename MM into MM1.
    assert (AG1 : AGR M lo (bv_unsigned sp0) M1) by (block_AG AGk EQM1 OUT1).
    clear AGk EQM1 OUT1. rename AG1 into AGk.
    (* [comment removed for export] *)
    pose proof HR as HR0. to_tree HR.
    destruct (facts M1 AGk) as [MI1 MP1 ST1 BUF1 SHRD1 RIP1 SN1 AM1 ZSTR1 ZSTK1 OBJ1].
    assert (NL1 : bytes_at asegs M1 0x208da [Z_to_bv 8 10]).
    { apply nl_bytes_at. intros a Ha. eapply (AGR_byte M lo (bv_unsigned sp0) M1 a); [exact AGk | lia | lia | lia | apply RO; exact Ha]. }
    assert (ZF1 : M1 (Z_to_bv 64 0x7fffc11b) = Some (Z_to_bv 8 0)).
    { eapply (AGR_byte M lo (bv_unsigned sp0) M1); [exact AGk | lia | lia | lia | apply ZI; unfold ZIMG_LO, ZIMG_HI; lia]. }
    destruct (u8arr_of_mapped M1 (bv_unsigned sp0 - 464) 1
                ltac:(eapply mapped_sub; [exact MP1 | lia | cbn; lia]) ltac:(lia) ltac:(cbn; lia)) as (ds5 & LEN5 & ARR5).
    time (eapply (splice_evtA2 AL CS KI K_halted K_mat V (blobs_ev []) _ _ _ M1 mo1 KEPT_CR (-1088) (-464) 1 lo
              (fun R' M' => bytes_at asegs M' (bv_unsigned sp0 - 464) [Z_to_bv 8 10] /\ mem_inv asegs M')
              0x67db8 0x0e6f40);
      [ exact HR | exact HK | exact HK1
      | rewrite LV; vm_compute; reflexivity | rewrite LV; vm_compute; reflexivity | cbn; intuition discriminate
      | rewrite (vf0 V VFV); unfold AIMG_HI; lia | rewrite (vf0 V VFV); lia | lia | lia | lia | rewrite (vf0 V VFV); lia | rewrite (vf0 V VFV); lia
      | | ]).
    { (* [comment removed for export] *)
      regvV HR0 (1%bv : reg). regvV HR0 (2%bv : reg). regvV HR0 (10%bv : reg). regvV HR0 (11%bv : reg). regvV HR0 (12%bv : reg).
      eapply (evtA_cut asegs AL CS); [apply (jstep_walk_memcpy AL IMG ALWF); exact CSOK|].
      cbn beta. intros ms1 ->.
      eapply evtA_mono.
      - time (eapply (imemcpy_spec AL IMG ALWF CS CSOK ASB) with (DST := bv_unsigned sp0 - 464) (SRC := 0x208da) (n := 1) (lo := lo) (ds := ds5) (ss := [Z_to_bv 8 10]);
          rewrite ?(unsigned_lit (bv_unsigned sp0 + -1088)) by lia;
          first [ exact ARR5 | exact NL1 | exact SHRD1 | exact AM1 | exact MI1
                | lazymatch goal with |- aobj _ _ _ _ 0x208da _ =>
                    apply (aobj_of_zero_range AL CS M1 _ _ CSOK ASB); [intros z Hz; apply FCS; lia | lia | lia | intros s Hs; replace s with 0x7fffc11b by lia; exact ZF1] end
                | lazymatch goal with |- aobj _ _ _ _ _ _ => apply (aobj_of_zero_range AL CS M1 _ _ CSOK ASB); [intros z Hz; apply SCS; lia | lia | lia | intros s Hs; apply ZSTK1; unfold SSH_LO, SSH_HI; lia] end
                | lazymatch goal with |- app_range 0x208da _ => unfold app_range; left; lia end
                | lazymatch goal with |- app_range _ _ => unfold app_range; right; lia end
                | lazymatch goal with |- amem_apart _ _ => unfold amem_apart; lia end
                | lazymatch goal with |- (1 <= _)%Z -> crange CS (0x208da - _) _ /\ _ => intros _; split; intros z Hz; apply FCS; lia end
                | lazymatch goal with |- (1 <= _)%Z -> _ /\ _ => intros _; split; intros z Hz; apply SCS; lia end
                | lazymatch goal with |- crange CS lo _ => intros z Hz; apply SCS; lia end
                | lazymatch goal with |- stk _ _ lo ?hi => apply (proj1 (stk_split asegs M1 lo hi (bv_unsigned sp0) ST1 ltac:(lia))) end
                | lazymatch goal with |- @eq word (Z_to_bv 64 _) (Z_to_bv 64 _) => f_equal; lia end
                | lazymatch goal with |- @eq word (alu64 _ _ _) _ => rewrite (alu_add_zlit sp0) by lia; rewrite ?alu_add_zlit by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia; f_equal; lia end
                | lazymatch goal with |- @eq nat _ _ => exact LEN5 end
                | lazymatch goal with |- _ \/ _ => lia end
                | lazymatch goal with |- Z.of_nat _ = _ => first [rewrite LEN5; reflexivity | reflexivity] end
                | lia
                | match goal with |- ?g => idtac "IMC-LEFT:" g end ]).
      - cbn beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ARR' & SRC' & ST').
        eexists _, m'. split; [rewrite ret_pc_even by (first [lia | reflexivity]); reflexivity|].
        split; [intros r Hr; cbn [In KEPT_CR] in Hr; repeat (destruct Hr as [<-|Hr]; [reflexivity|]); destruct Hr|].
        rewrite ?(unsigned_lit (bv_unsigned sp0 + -1088)) in MU by lia. rewrite ?(vf0 V VFV).
        split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [Frame.outside]; intros x Hx; repeat split; try exact I; lia|].
        split; [exact WM|]. split; [exact (proj1 ARR') | exact MI']. }
    (* [comment removed for export] *)
    intros R3 M3 mo3 (NL3 & MI3) MU3 WM3 HR3 HK3 HKmo3 MM3.
    rewrite LV in HR3. clear HR HK HR0. rename HR3 into HR. rename HK3 into HK.
    assert (AG3 : AGR M lo (bv_unsigned sp0) M3).
    { eapply (AGR_munch _ M lo (bv_unsigned sp0) M1 M3); [exact AGk | exact MU3 | exact WM3 | | unfold AIMG_HI; lia].
      cbn [Frame.outside]. rewrite !(vf0 V VFV). pose proof LOhi. intros x Hx.
      destruct (Z_le_gt_dec lo x); destruct (Z_lt_le_dec x (bv_unsigned sp0)); try lia; exfalso; apply Hx; repeat split; lia. }
    pose proof (vf0 V VFV) as V0eq.
    pose proof (VF_app V (junk_vals R3) VFV) as VFV'. set (V' := V ++ junk_vals R3) in *.
    assert (LV' : length V' = 237%nat) by (subst V'; rewrite length_app, junk_vals_length, LV; reflexivity).
    assert (EV150' : vals_ev V' 150 = Z_to_bv 64 L) by (subst V'; rewrite vals_ev_app_l by (rewrite LV; lia); exact EV150).
    clearbody V'. clear VFV. rename VFV' into VFV.
    assert (Lsmall' : (bv_unsigned (edenot {| ev := vals_ev V'; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
    { cbn [edenot ev]. rewrite EV150', u_small by lia. lia. }
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 0 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrE 237%nat true covtac).
    all: try solve_sc.
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall'; cmpL end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "E64-SC-LEFT" g end.
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) ?mon) _ => rename Rn into RA; rename Mn into MA0; rename mon into moA end.
    rename EQM into EQMA. rename OUT into OUTA. rename HKmo into HKA. rename MM into MMA.
    assert (AGA : AGR M lo (bv_unsigned sp0) MA0) by (block_AG AG3 EQMA OUTA).
    (* [comment removed for export] *)
    assert (NLA : bytes_at asegs MA0 (bv_unsigned sp0 - 464) [Z_to_bv 8 10]).
    { eapply (bytes_at_block D _ M3 MA0 _ _ _ NL3 EQMA). intros z Hz. cbn [length] in Hz. split.
      - apply (D_frame z (z + 1)); lia.
      - cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
        rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [lia | exact I]. }
    clear EQMA OUTA.
    (* [comment removed for export] *)
    unfold TT64, W.
    replace (map (WriteEv (Z_to_bv 64 2)) [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 (sc_fd resE64))) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    assert (FdA : fd_lookup (m_fds moA) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { unfold FD2 in FD. rewrite (mo_mat_fds' _ _ MMA), (mo_mat_fds' _ _ MM3), (mo_mat_fds' _ _ MM1). exact FD. }
    assert (SC2 : stdio_call 237%nat srE64e knE64e = Some resE64) by (vm_compute; reflexivity).
    eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly V' (blobs_ev []) srE64e knE64e RA MA0 moA resE64 [Z_to_bv 8 10] []
              (t_exit (exit_code 2) (m_fs model)) HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resE64 edenot length Z.of_nat Pos.of_succ_nat Pos.succ].
    + rewrite LV'. exact SC2.
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
      pose proof (bytes_at_rdn asegs MA0 _ [Z_to_bv 8 10] 0 1 NLA ltac:(cbn; lia)) as RD. rewrite Z.add_0_r in RD. cbn [skipn firstn] in RD.
      unfold wa in RD. replace (bv_unsigned sp0 + -464) with (bv_unsigned sp0 - 464) by lia. exact RD.
    + reflexivity.
    + exact FdA.
    + exact HKA.
    + intros z Hz. revert Hz. evs. azl. intros Hz. apply WCS. lia.
    + intros z Hz. revert Hz. evs. azl. unorm. intros Hz. left. apply WCS. lia.
    + intros z Hz. revert Hz; unorm; intros Hz. lia.
    + unfold t_exit. apply t_emit_has_nil.
    + (* [comment removed for export] *)
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
      2:{ rewrite (mo_mat_fs _ _ MMD), (mo_mat_fs _ _ MMC), (mo_mat_fs _ _ MMA), (mo_mat_fs _ _ MM3), (mo_mat_fs _ _ MM1). exact FS. }
      apply (die2_at_96e04_deep AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly sp0 ltac:(lia) ltac:(lia) SPal WCS lo LOlo
               M can tid wp0 rp0 wp1 rp1 TM); [| exact HKD].
      (* [comment removed for export] *)
      assert (AGC : AGR M lo (bv_unsigned sp0) MC).
      { eapply AGR_trans; [exact AGA|]. destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
        cbn [sc_sp sc_f sc_bufp sc_bufsz resE64 edenot ev] in Pagree. rewrite V0eq' in Pagree. revert Pagree. azl. intros Pagree.
        split; [| exact Pgrows]. intros x [O1 O2]. apply Pagree; lia. }
      assert (AGD : AGR M lo (bv_unsigned sp0) MD) by (block_AG AGC EQMC OUTC).
      destruct AGD as [AGm GRm].
      split.
      * intros x O1 O2. apply AGm. split; [exact O1 | exact O2].
      * intros x Hout. cbn [outside] in Hout. destruct Hout as (O1 & O2 & _). apply AGm. split; lia.
      * exact GRm.
      * apply mem_grows_wmono. exact GRm.
      * krd HK (0x0fa488 + 140)%Z 4%nat F140. krd HK (0x0fa488 + 40)%Z 8%nat F40. krd HK (0x0fa488 + 56)%Z 8%nat F56.
        krd HK (0x0fa488 + 8)%Z 8%nat F8. krd HK (0x0fa488 + 16)%Z 8%nat F16.
        eexists. eexists. unfold file_clean. fold asegs. repeat split.
        -- exact F140.
        -- rewrite F40. reflexivity.
        -- rewrite F56. reflexivity.
        -- rewrite F8. reflexivity.
        -- rewrite F16. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End OF.
