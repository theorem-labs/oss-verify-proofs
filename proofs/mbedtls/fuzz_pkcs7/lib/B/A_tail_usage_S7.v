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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tailkit_defs A_tailkit_exit2 A_tailkit_exit3 A_splice A_imz A_icpt_str A_icpt_strnlen A_icpt_strnlenJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_tail_lib A_tail_usage_defs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxADrvKit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxAKnDS.

Import ListNotations.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_tail_usage_S7 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.LibA.SymDriveA.DcovZ"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.outzone"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_LO"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.SSH_HI"; "OF.VF"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.blobs_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_AND"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.B.A_refused.SHW"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bv_ltu"; "Stdlib.ZArith.BinInt.Z.lxor"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Nat.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "OF.EnvV"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.AgentSubmission.B.A_tail_lib.AGR"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "OF.FD2"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "OF.TT"; "OF.XL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.sub"; "SUF7"; "OF.TT64"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Lists.ListDef.nth"].

#[local] Existing Instance Lib.PropExec.fx0.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition PRE17 : list byte := s2b "usage: "%string.            (* [comment removed for export] *)
Lemma PRE17_len : length PRE17 = 7%nat. Proof. reflexivity. Qed.
Definition SUF7 : list byte := (s2b " INPUT"%string) ++ [Z_to_bv 8 10].   (* [comment removed for export] *)
Lemma SUF7_len : length SUF7 = 7%nat. Proof. reflexivity. Qed.
Lemma msg_cannot_open_eq : forall p, msg_usage p = PRE17 ++ p ++ SUF7.
Proof. intros p. unfold msg_usage, PRE17, SUF7. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stk_agree : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.Phi,$2.P,Pa,$2.P,(3.(4.R3.R1.)(5.R1.R2.))(6.(1.(0.&8.))A1.R5.(7.R2.)A1.R6.(7.R2.))P,(8.$9.R5.R3.R2.)(8.$9.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' lo hi AG (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  unfold wview, mrd in *. rewrite (AG a Ha). exact (H a Ha).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47745453783.6000007S1w3LEN". (* [comment removed for export] *)
Lemma rw_C8_rdn : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "PMk,P,(0.&40.)(1.(0.&8.))PA,$2.Pw,(0.&40.)P,(:.$9.R3.R2.(;.$<.(=.R1.)(>.$<.)))(6.(1.(?.(0.&8.)))(10.$9.R4.(11.&40.R3.)#8.)(12.(?.(0.&8.))(13.#8.R2.)))")
(* [comment removed for export] *).
Proof.
  intros Mk A w [[WF B] _].
  pose proof (cells_bytes_length [C8 w] WF) as LEN. cbn [cells_size csize Nat.add] in LEN.
  pose proof (bytes_at_rdn asegs Mk A _ 0 8 B ltac:(rewrite LEN; lia)) as RD.
  rewrite Z.add_0_r in RD. unfold wa in RD. rewrite RD. cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

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
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Pmo,$14.Pacc,(?.(15.(0.&40.)$16.))P,A1.VKI,R2.P,(17.VAL,VCS,R2.)(18.$14.Lmo',$14.(3.(6.(1.$14.)(19.R5.R4.)(12.$14.R1.))(3.A1.VKI,R1.(1:.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Pmo,$14.Pmo',$14.P,A1.VKI,R2.P,(6.$1;.(1<.R2.)(1<.R3.))P,(6.(?.(15.(0.&40.)(0.&40.)))(1=.R3.)(1=.R4.))P,(6.(?.(0.&40.))(1>.R4.)(1>.R5.))P,(6.(1.(0.&40.))(1?.R5.)(1?.R6.))A1.VKI,R6.")
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
  Hypothesis STKHIlo : (bv_unsigned sp0 + 144 <= STKHI)%Z.
  Hypothesis STKHIhi : (STKHI <= 0x800000000000)%Z.
  Hypothesis STKHI64 : (STKHI mod 64 = 0)%Z.
  Hypothesis SCS : crange CS lo (STKHI - lo).
  (* [comment removed for export] *)
  Hypothesis FCS : crange CS 0x16bc0 64.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x0e0aa8.
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G8 : getr R 8 = Z_to_bv 64 2.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 (bv_unsigned sp0 + 136).     (* [comment removed for export] *)
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
  Hypothesis UFR : stk asegs M (bv_unsigned sp0) (bv_unsigned sp0 + 80).      (* [comment removed for export] *)
  Variables (w8 w16 w24 w32 w40 w48 w56 w64 : word).                             (* [comment removed for export] *)
  Hypothesis FRW : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "(:.$9.VM,(20.(21.&40.Vsp0,)+8.)(;.$<.(=.Vw8,)(;.$<.(=.Vw16,)(;.$<.(=.Vw24,)(;.$<.(=.Vw32,)(;.$<.(=.Vw40,)(;.$<.(=.Vw48,)(;.$<.(=.Vw56,)(;.$<.(=.Vw64,)(>.$<.))))))))))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis ZSH : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Ps,$2.P,(3.(4.(20.+7???8000.(22.Vlo,+8.))R1.)(5.R1.(20.+7???8000.(22.VSTKHI,+8.))))(6.(1.(0.&8.))A1.VM,(11.&40.R2.)(12.(0.&8.)(11.&8.=)))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Variables (P : word) (path extra : list byte).      (* [comment removed for export] *)
  Let L : Z := Z.of_nat (length path).
  Let buf : list byte := path ++ Z_to_bv 8 0 :: extra.
  Hypothesis G18 : getr R 18 = Z_to_bv 64 0x0970e0.
  Hypothesis AV0 : rw_cells asegs M (bv_unsigned sp0 + 136) [C8 P].                       (* [comment removed for export] *)
  Hypothesis FRA : rw_cells asegs M (bv_unsigned sp0 + 72) [C8 (Z_to_bv 64 0x0e0aa8)].    (* [comment removed for export] *)
  Hypothesis BY : bytes_at asegs M (bv_unsigned P) buf.
  Hypothesis NZ : ~ In (Z_to_bv 8 0) path.
  Hypothesis WIN8 : ((bv_unsigned P + L) / 8 * 8 + 8 <= bv_unsigned P + Z.of_nat (length buf))%Z.
  Hypothesis Plo : (bv_unsigned sp0 + 128 <= bv_unsigned P)%Z.
  Hypothesis Phi : (bv_unsigned P + Z.of_nat (length buf) <= STKHI)%Z.          (* [comment removed for export] *)
  Hypothesis PL16 : (bv_unsigned P + L + 16 <= STKHI)%Z.                        (* [comment removed for export] *)
  Hypothesis LMAX : (L <= 131071)%Z.                                            (* [comment removed for export] *)
  Hypothesis L62 : (L <= 66)%Z.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30247682266.84L35495549846.8300000f01>S3sp04SPlo2lo5STKHI7STKHIlo1P4path1L3buf3Plo1z2Hz1H2H0S3sp05STKHI1P4path1L3buf". (* [comment removed for export] *)
  Lemma PCS : crange CS (bv_unsigned P - bv_unsigned P mod 64) (STKHI - (bv_unsigned P - bv_unsigned P mod 64)).
  Proof. intros z Hz. apply SCS. pose proof LOhi. pose proof (Z.mod_pos_bound (bv_unsigned P) 64 ltac:(lia)). lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SHRD : forall c, CS c -> exists b, bytes_at asegs M (shadow_of AL c) [b].
  Hypothesis CSTOP : forall c, CS c -> (c < 2^47)%Z.

  Let WINLO := (bv_unsigned sp0 - 4096)%Z.

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(bv_unsigned sp0 - 4096, bv_unsigned sp0 + 144)%Z; (0x7fffad78, 0x7fffad80)%Z; (SSH_LO sp0, SSH_HI sp0)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32276418883.84L57167447340.84L57657395591.8500000N01601gS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H". (* [comment removed for export] *)
  Lemma SSH_facts : (0x7fff8000 <= SSH_LO sp0)%Z /\ (SSH_HI sp0 <= 2^46)%Z /\ (SSH_LO sp0 < SSH_HI sp0)%Z.
  Proof. pose proof (SHW_range sp0 (-64) ltac:(lia) SPal ltac:(lia)). unfold SSH_LO, SSH_HI in *. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.8600000lS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30247691664.8600000lS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2Hz". (* [comment removed for export] *)
  Lemma WCS' : crange CS (bv_unsigned sp0 - 4096) (4096 + 144).
  Proof. intros z Hz. apply SCS. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma D_Dseg : forall a : word, segcov asegs (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6097392651.8600000PS3sp05STKHI1P4path1L3buf5WINLO1c". (* [comment removed for export] *)
  Lemma shadow_aok : forall c x, CS c -> (x = 0x7fff8000 + c / 8)%Z -> aok_addr AL CS x.
  Proof. intros c x Hc ->. right; left. exists c. split; [exact Hc|]. unfold shadow_of. rewrite ASB. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11408572375.88L37650509568.88L5268879960.88 L57161095762.88L60694983881.90L61028787006.8800000S01G01g02O03203PS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1zS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1z2A1S3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK_aok AL CS IMG); [|exact H].
    repeat (apply Forall_cons; [cbn [fst snd]|]); [ .. | apply Forall_nil].
    - intros z Hz. left. apply WCS'. lia.
    - intros z Hz. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply FCS; lia|]. rewrite Z.mul_comm, Z.div_mul by lia. lia.
    - intros z Hz. destruct (ssh_app sp0 z ltac:(lia) SPal Hz) as [A1 A2]. apply (shadow_aok (8 * (z - 0x7fff8000))); [apply WCS; lia| exact A2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L15567212646.86L40578935982.86L60924558599.8600000P00n01QS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. pose proof SSH_facts. pose proof SPlo. unfold D. apply Dimg_D0. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition RRUN := rz_runA asegs D AL CS KI K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13601108214.90L4172514697.90 L60924549197.9000000S01Q024S3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1a1b2Ha2Hb1z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_frame : forall a b, (bv_unsigned sp0 - 4096 <= a)%Z -> (b <= bv_unsigned sp0 + 144)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply (Dimg_cov _ (bv_unsigned sp0 - 4096) (bv_unsigned sp0 + 144)); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.9000000nS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1a1b2Ha2Hb1z2Hz". (* [comment removed for export] *)
  Lemma D_img : forall a b, (0x10000 <= a)%Z -> (b <= 0x65f000)%Z -> DcovZ D a b.
  Proof. intros a b Ha Hb z Hz. unfold D. apply Dimg_img. unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L32683096429.86L40578927076.86L55842434079.8600000S01101OS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma D_fsh : DcovZ D 0x7fffad78 0x7fffad80.
  Proof. intros z Hz. unfold D. eapply Dimg_cov; [right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LITS_KND : list (Z * Z) := [(0x10000, 0x65f000)%Z; (0x7fffad78, 0x7fffad80)%Z].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L51855127614.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma HLITS_KND : Forall (fun iv => DcovZ D (fst iv) (snd iv)) LITS_KND.
  Proof. repeat (apply Forall_cons; [cbn [fst snd] |]); [apply D_img; lia | exact D_fsh | apply Forall_nil]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18362884487.88L5599869189.88 00000V01<S3sp05STKHI1P4path1L3buf5WINLO3qhi3HhiS3sp05STKHI1P4path1L3buf5WINLO3qlo3Hlo". (* [comment removed for export] *)
  Lemma D_frameS : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Pqlo,$2.Pqhi,$2.P,(4.(20.(21.&40.Vsp0,)-1000.)R2.)P,(4.R2.(20.(21.&40.Vsp0,)+90.))(23.VD,R4.R3.)")
(* [comment removed for export] *).
  Proof. intros qlo qhi Hlo Hhi. apply D_frame; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L13440388671.87L15567222060.87L52039345437.8700000S01301SS3sp05STKHI1P4path1L3buf5WINLO1z2HzS3sp05STKHI1P4path1L3buf5WINLO1HS3sp05STKHI1P4path1L3buf5WINLO1H". (* [comment removed for export] *)
  Lemma D_ssh : DcovZ D (SSH_LO sp0) (SSH_HI sp0).
  Proof. pose proof SSH_facts. intros z Hz. unfold D. eapply Dimg_cov; [right; right; left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L53694884100.8800001:S3sp02lo5STKHI1P4path1L3buf5WINLO1x2Hr2O24SPlo4LOhi7STKHIlo7STKHI643Plo2O1". (* [comment removed for export] *)
  Lemma D_out_zone : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Px,(0.&40.)P,(6.$24.A1.VD,R1.$25.)P,(26.Vlo,(21.&40.Vsp0,)R2.)(27.(3.(3.(4.+10000.(21.&40.R3.))(5.(21.&40.R3.)+65?000.))(28.(3.(4.+?:488.(21.&40.R3.))(5.(21.&40.R3.)+?:570.))))(27.(3.(4.+7???:=78.(21.&40.R3.))(5.(21.&40.R3.)+7???:=80.))(27.(3.(4.(29.Vsp0,)(21.&40.R3.))(5.(21.&40.R3.)(2:.Vsp0,)))(3.(4.(21.&40.Vsp0,)(21.&40.R3.))(5.(21.&40.R3.)(20.(21.&40.Vsp0,)+90.))))))")
(* [comment removed for export] *).
  Proof.
    intros x Dx [O1 O2]. unfold D, Dimg in Dx. apply Dof_true in Dx as (iv & Hin & Hr).
    cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; unfold AIMG_LO, AIMG_HI in *; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition V0 : list word := [sp0] ++ junk_vals R ++ [can] ++ [P] ++ repeat (Z_to_bv 64 0) 7.
  Lemma V0_len : length V0 = 42%nat.
  Proof. unfold V0. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Lemma V0_0 : vals_ev V0 0 = sp0. Proof. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_33 : vals_ev V0 33 = can.
  Proof. unfold V0, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ [P] ++ repeat (Z_to_bv 64 0) 7) with (([sp0] ++ junk_vals R) ++ ([can] ++ [P] ++ repeat (Z_to_bv 64 0) 7)).
    rewrite app_nth2; [|rewrite length_app, junk_vals_length; cbn; lia]. rewrite length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma V0_junk : forall i, (i < 32)%nat -> vals_ev V0 (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold V0, vals_ev. cbn [app length Nat.add].
    change (sp0 :: junk_vals R ++ can :: P :: repeat (Z_to_bv 64 0) 7) with ([sp0] ++ (junk_vals R ++ (can :: P :: repeat (Z_to_bv 64 0) 7))).
    change (S i) with (length [sp0] + i)%nat. rewrite app_nth2_plus. rewrite app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54434947932.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma V0_19 : vals_ev V0 34 = P.   (* [comment removed for export] *)
  Proof. unfold V0, vals_ev. change ([sp0] ++ junk_vals R ++ [can] ++ [P] ++ repeat (Z_to_bv 64 0) 7) with (([sp0] ++ junk_vals R ++ [can]) ++ ([P] ++ repeat (Z_to_bv 64 0) 7)).
    rewrite app_nth2; [|rewrite !length_app, junk_vals_length; cbn; lia]. rewrite !length_app, junk_vals_length. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VF (V : list word) : Prop :=
    (forall n, (n < 42)%nat -> vals_ev V n = vals_ev V0 n) /\ (42 <= length V)%nat.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25269778915.8400000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma VF0 : VF V0. Proof. split; [intros; reflexivity | rewrite V0_len; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L21188810707.90L9784235213.88 00000i01aS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2P21n2HnS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V3ext2P2". (* [comment removed for export] *)
  Lemma VF_app : forall V ext, VF V -> VF (V ++ ext).
  Proof. intros V ext [P1 P2]. split; [| rewrite length_app; lia]. intros n Hn. rewrite vals_ev_app_l by lia. apply P1. exact Hn. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30227048842.8600000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf0 : forall V, VF V -> vals_ev V 0 = sp0. Proof. intros V [P1 _]. rewrite (P1 0%nat) by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.8600000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf19 : forall V, VF V -> vals_ev V 34 = P. Proof. intros V [P1 _]. rewrite (P1 34%nat) by lia. apply V0_19. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L54441433323.8600000NS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma vf33 : forall V, VF V -> vals_ev V 33 = can. Proof. intros V [P1 _]. rewrite (P1 33%nat) by lia. apply V0_33. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L45321507673.87L55760870395.8800000[01@S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO2HiS3sp05STKHI1R1P4path1L3buf5WINLO1i2Hi". (* [comment removed for export] *)
  Lemma regs_okV0 : regs_ok (Env (vals_ev V0) (blobs_ev [])) sr_OF R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_OF all_regs];
      first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G8 | exact G18 | (cbn [ev]; rewrite V0_0, (alu_add_zlit sp0 136) by (unorm; lia); exact G11) | exact G20 | exact G21 | exact G22 | exact G23
                                   | exact G24 | exact G25 | exact G26 | exact G27 | (cbn [ev]; rewrite V0_0; exact G2) ])
            | (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                 change (edenot (Env (vals_ev V0) (blobs_ev [])) (EVar n)) with (vals_ev V0 n); rewrite (V0_junk (n - 1)) by lia; reflexivity end) ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01C0@L11615743984.98 L13042945941.98 L13484217602.98 L14054083309.102L14499496082.98 L15439463048.98 L17543312104.100L1756166345.98  L18928696722.98 L21294246587.98 L21683230006.98 L2183569985.98  L21927717721.98 L21986899558.98 L22163189566.98 L22604873481.98 L2431328725.102 L24992216082.98 L25271909867.98 L25484198400.98 L2564951689.98  L27134698386.98 L27315410273.98 L27352604565.98 L28325820091.98 L28434372873.98 L29762371858.98 L31327315070.102L31396711570.98 L32648418366.104L32873232769.102L33148392579.98 L33669037980.98 L34577004134.98 L34774111081.98 L3506990866.98  L38114121216.98 L3829630897.102 L39213365269.98 L39510883410.98 L40253358217.98 L40579027602.98 L43030311433.98 L44353219849.98 L44510486418.98 L44751598473.98 L4504975677.102 L46809767186.98 L48461698953.98 L48555263348.98 L5004984661.98  L51238950418.98 L52457697417.98 L52875384210.98 L53129770761.98 L53519161933.102L53519190958.98 L54226205864.98 L54292390718.98 L54967497737.98 L55007380242.98 L55149030888.100L55662616861.102L55849630025.98 L5641132690.98  L57481666438.98 L58560891017.98 L58961367305.98 L5926593349.98  L61064399881.98 L62675677899.98 L6275277449.98  L64037435666.98 L64202541330.98 L64791502857.98 L65502196882.98 L65732472201.98 L66336703634.98 L67631326282.102L68058909735.98 L68075363561.98 L7781517330.98  L9911486354.98  00000100o01M02P02n03L03o04M04k05N05l06J06h07K07n08L08n09L09j0:M0:k0;I0;l0<O0=20=P0=n0>i0?G0@G0@l0@m0AK0Ai0BG0Be0CH0Cn0Co0DM0Dk0EI0Eg0FE0Fc0GA0Ge0HC0Ha0Hb0IJ0Ih0JF0Jd0KB0Kb0L@0LA0Ld0MB0M`0NC0OA0O_0P=0P[0Q90QW0R50RS0RT0S20SP0Sn0TL0Tj0UH0Uf0VK0Vi0WG0We0XCFS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1HS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1H1d1m2Hd2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1n1BS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H3off1n1B1CS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1d1m2Hd2Hm1x2HxS3sp05STKHI1P4path1L3buf5WINLO1d1m2HdFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1n1CFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO3off1AS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1mS3sp05STKHI1P4path1L3buf5WINLOFS3sp04SPhi5STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1i2HiS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOFS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1d1m2HmS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
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
      | (* [comment removed for export] *) split; [lia|]; split; [apply flat_intro; cbn [edenot ev]; rewrite ?V0_0; lia|];
        unfold adenot, v_addi; cbn [a_base a_off edenot ev]; rewrite ?V0_0, ?V0_19; rewrite ?alu_add_zlit by (unorm; lia);
        first [exact (rw_C8_rdn _ _ _ AV0) | exact (rw_C8_rdn _ _ _ FRA)]
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L17034448047.91L29784460291.90L3479498253.90 L43935895424.92L47803405696.92L55715225071.90L59576963504.92L63368316460.92L63368316589.91L63368325619.90L64266648997.90L66561261592.92L8929201831.93 00000l01J02H02n03T04204R05205R06006f07F08ES3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1k2HkS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLO1k2H12H2S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1kS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2Hk2H12H22H3". (* [comment removed for export] *)
  Lemma shw_denotV : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "PV,(?.(0.&40.))Pk,$2.P,(2;.R2.)P,(3.(4.-1000.R2.)(4.R2.=))(6.$2.(21.&40.(2<.(2=.(2>.R4.)(2?.(>.(?.(0.&8.)))))(30.$31.(30.$32.(30.$33.(30.$32.(34.#0.)(35.R3.))(35.+3.))(35.+7???8000.))(35.-8.))))(36.Vsp0,R3.))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L3479498253.88 L35907637249.89L40825277235.88L53519168529.89L55715225071.88L64266638075.89L64266648997.8800000n01Q01o02O02m03c04YS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1H1k2HkS3sp05STKHI1P4path1L3buf5WINLO1k2H1S3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO1kS3sp05STKHI1P4path1L3buf5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2HkS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1k2Hk". (* [comment removed for export] *)
  Lemma and3_lit : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Pk,$2.P,(3.(4.-1000.R1.)(4.R1.=))(6.$24.(37.&40.(38.$31.(11.&40.(20.(21.&40.Vsp0,)R2.))(11.&40.+3.))(11.&40.=))(39.(3:.R2.+4.)=))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo. pose proof SPhi.
    intros k Hk. rewrite alu_and. unfold v_and. rewrite (unsigned_lit 3), (unsigned_lit (bv_unsigned sp0 + k)) by lia.
    rewrite land3_mod4 by lia. pose proof (Z.mod_pos_bound (bv_unsigned sp0 + k) 4 ltac:(lia)).
    unfold bv_eqb. rewrite !unsigned_lit by lia. apply (mod4_of_sp (bv_unsigned sp0) k); [exact SPal | lia | reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L37106200957.88L5744834796.88 L61929758668.88L8443611008.88 00000]01@01c02FS3sp04SPlo5STKHI1P4path1L3buf5WINLO1x1n2Hx2HnS3sp05STKHI1P4path1L3buf5WINLO1x2HxS3sp05STKHI1P4path1L3buf5WINLO1n2HnS3sp05STKHI1P4path1L3buf5WINLO1x2Hx". (* [comment removed for export] *)
  Lemma not_ltu_small : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Px,$2.Pn,$2.P,(3.(4.=R2.)(5.R2.(3;.+2.+30.)))P,(3.(4.=R2.)(5.R2.(3;.+2.+10.)))(6.$24.(3<.&40.(11.&40.(3=.(21.&40.(11.&40.R4.))(21.&40.(11.&40.-1.))))(11.&40.R3.))$3>.)")
(* [comment removed for export] *).
  Proof.
    intros x n Hx Hn. rewrite (unsigned_lit x) by lia. replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615%Z by reflexivity.
    rewrite zb_lxor_ones by lia. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma alu_add_zlit : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "Px,(0.&40.)Pk,$2.P,(3.(4.=(20.(21.&40.R2.)R1.))(5.(20.(21.&40.R2.)R1.)(3;.+2.+40.)))(6.(0.&40.)(38.$32.R3.(11.&40.R2.))(11.&40.(20.(21.&40.R3.)R2.)))")
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L21188810707.8800000US3sp05STKHI1P4path1L3buf5WINLO1V1n2Hn". (* [comment removed for export] *)
  Lemma vals_ev_app_ge : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "PV,(?.(0.&40.))Pext,(?.(0.&40.))Pn,$16.P,(3?.(40.(0.&40.)R3.)R1.)(6.(0.&40.)(2>.(41.(0.&40.)R4.R3.)R2.)(2>.R3.(42.R2.(40.(0.&40.)R4.))))")
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

  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L17743517653.105L18614817987.105L2008272931.114 L24498169710.105L27076589246.107L29443216221.105L29731801447.107L30247691664.107L37492600210.114L42153134065.105L46058870405.105L46530783016.105L56457790905.105L56765667309.107L58965540039.102L65604097635.105L8120965920.107 L8564305960.105 00000[01`02a03_05805d06m08608d09P0:70:`0;e0<d0=B0>90?80?oS3sp02lo5STKHI1P4path5extra1L3buf3Plo5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo2lo6LOdeep5STKHI1P4path5extra1L3buf3Plo5WINLO1H1c2Q02H3S3sp04SPlo2lo4LOlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo2lo4LOlo4LOhi5STKHI7STKHIlo7STKHI641P4path5extra1L3buf3Plo4PL165WINLO1H2H11s2HsS3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo6LOdeep5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path5extra1L3buf3Plo4PL165WINLO1H1z2HzS3sp04SPlo5STKHI1P4path5extra1L3buf5WINLO1c2Q0S3sp02lo4LOlo5STKHI1P4path5extra1L3buf5WINLOS3sp05STKHI1P4path5extra1L3buf5WINLO2H1S3sp04SPhi5STKHI1P4path5extra1L3buf5WINLOS3sp04SPlo2lo4LOlo6LOdeep5STKHI7STKHIhi1P4path1L3buf3Plo5WINLO1H1s2HsS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp05STKHI1P4path5extra5WINLOS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1HS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H2H21a2HaS3sp04SPlo5STKHI7STKHIlo1P4path5extra1L3buf3Plo5WINLO1H". (* [comment removed for export] *)
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
  Definition TT : TSet := t_emit (W 2 (msg_usage path)) (t_exit (exit_code 2) (m_fs model)).
  Definition FD2 (mo : Model) : Prop := fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Definition STG (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "PRk,(43.&5.(0.&40.))PMk,P,(0.&40.)(1.(0.&8.))Pmok,$14.P,(2;.O6.)P,(6.$16.(40.(0.&40.)O6.)O5.)P,(44.(45.O6.)O4.R5.)P,(46.$9.(45.O6.)R5.O3.)P,(47.VM,Vlo,(21.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(6.$48.(49.R7.)(49.Vmodel,))P,(4:.R8.)P,A2.O1.O6.R:.(4;.$9.(4<.(4=.$4>.R<.(11.&40.O2.)R;.(4?.$9.))R:.)$50.)")
(* [comment removed for export] *).
  Definition XL (V : list word) : Prop := vals_ev V 150 = Z_to_bv 64 L.
  Definition X0 (V : list word) (Mk : mem) : Prop := True.
  Definition XC (V : list word) (Mk : mem) : Prop := XL V.
  Definition XD (V : list word) (Mk : mem) : Prop := XL V /\ bytes_at asegs Mk (bv_unsigned sp0 - 457) path.
  Definition XE (V : list word) (Mk : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "(3.(51.O2.)(3.(52.$9.O1.(53.(21.&40.Vsp0,)+1<9.)Vpath,)(52.$9.O1.(20.(53.(21.&40.Vsp0,)+1<9.)VL,)$54.)))")
(* [comment removed for export] *).
  Definition S_A2 : Prop := forall V, STG V 74 srA2 knA2 0x5b1b4 X0.
  Definition S_B1 : Prop := forall V, STG V 106 srB1 knB1 0x5b504 X0.
  Definition S_B2 : Prop := forall V, STG V 138 srB2 knB2 0x5b1b4 X0.
  Definition S_C1 : Prop := forall V, STG V 172 srC1 knC1 0x0e79c4 XC.
  Definition S_D : Prop := forall V, STG V 205 srD knD 0x0e6f40 XD.
  Definition S_E : Prop := forall V, STG V 237 srE knE 0x0e6f40 XE.
  (* [comment removed for export] *)
  Definition TT64 : TSet := t_emit (W 2 SUF7) (t_exit (exit_code 2) (m_fs model)).
  Definition STG64 (V : list word) (nx : nat) (sr : list expr) (kn : list kentry) (pc : Z) (X : list word -> mem -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "PRk,(43.&5.(0.&40.))PMk,P,(0.&40.)(1.(0.&8.))Pmok,$14.P,(2;.O6.)P,(6.$16.(40.(0.&40.)O6.)O5.)P,(44.(45.O6.)O4.R5.)P,(46.$9.(45.O6.)R5.O3.)P,(47.VM,Vlo,(21.&40.Vsp0,)R6.)P,A1.VKI,R6.P,(6.$48.(49.R7.)(49.Vmodel,))P,(4:.R8.)P,A2.O1.O6.R:.(4;.$9.(4<.(4=.$4>.R<.(11.&40.O2.)R;.(4?.$9.))R:.)$55.)")
(* [comment removed for export] *).
  Definition S_D64 : Prop := forall V, STG64 V 205 (sc_sr resC2X) (sc_kn resC2X) (sc_ret resC2X) XC.
  (* [comment removed for export] *)

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
            intros x Dx Ox; destruct (D_out_zone x Dx Ox) as [Z1|[Z1|[Z1|Z1]]]; cbn [log_out]; unfold adenot, v_addi; cbn [a_base a_off edenot]; evs;
            rewrite ?(u_small 0) by lia; repeat split; rewrite ?u_small by lia; first [lia | exact I] ].

  (* [comment removed for export] *)
  Definition preZ : list Z := Eval vm_compute in match kread_bytes knEe (EVar 0) (-464) 7 with Some vs => vs | None => [] end.
  Lemma preZ_eq : kread_bytes knEe (EVar 0) (-464) 7 = Some preZ.
  Proof. vm_compute. reflexivity. Qed.
  Lemma preZ_msg : map (fun v => Z_to_bv 8 v) preZ = PRE17.
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L1157467871.84 L14155031263.84L29200756447.84L44226926175.84L47645164127.84L59327463135.84L64277815263.8400000N00l01J01h02F02d03BS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLOS3sp05STKHI1P4path1L3buf5WINLO". (* [comment removed for export] *)
  Lemma preZ_range : Forall (fun v => 0 <= v < 256)%Z preZ.
  Proof. unfold preZ. repeat (constructor; [lia|]). constructor. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rd8_val : forall w : word, Z_to_bv 64 (extz false 8 (bytes_le_to_Z (word_to_le_bytes 8 w))) = w.
  Proof.
    intros w. cbn [extz]. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z.
    rewrite Z.mod_small by (apply u64_range). apply Z_to_bv_bv_unsigned.
  Qed.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L27027551807.94L37591743569.94L68231966417.95L8715917058.93 L8929206648.95 00001602<03Z05306YS3sp05STKHI2w83w163w243w323w403w483w563w641P4path1L3buf5WINLO1k2Hk3LENS3sp05STKHI2w83w163w243w323w403w483w563w641P4path1L3buf5WINLO1k2Hk3LENS3sp04SPlo5STKHI7STKHIlo2w83w163w243w323w403w483w563w641P4path1L3buf3Plo5WINLO1k2Hk1H3LEN1j2HjS3sp04SPlo5STKHI7STKHIlo2w83w163w243w323w403w483w563w641P4path1L3buf3Plo5WINLO1k2Hk1H3LENS3sp04SPlo5STKHI7STKHIlo7STKHIhi2w83w163w243w323w403w483w563w641P4path1L3buf3Plo5WINLO1k2Hk1H3LEN1j2Hj". (* [comment removed for export] *)
  Lemma frw_rdn : ltac2:(CDefT.buildp (gd_tbl_A_tail_usage_S7 ()) "PMk,Px,(0.&40.)(1.(0.&8.))Pk,$16.P,(56.R1.#8.)P,Pa,$2.P,(3.(4.(20.(21.&40.Vsp0,)+8.)R1.)(5.R1.(20.(21.&40.Vsp0,)+48.)))(6.(1.(0.&8.))A1.R5.(7.R2.)A1.VM,(7.R2.))(6.(1.(?.(0.&8.)))(10.$9.R4.(11.&40.(20.(20.(21.&40.Vsp0,)+8.)(57.+8.(58.R3.))))#8.)(12.(?.(0.&8.))(13.#8.(59.(0.&40.)R3.(;.(0.&40.)Vw8,(;.(0.&40.)Vw16,(;.(0.&40.)Vw24,(;.(0.&40.)Vw32,(;.(0.&40.)Vw40,(;.(0.&40.)Vw48,(;.(0.&40.)Vw56,(;.(0.&40.)Vw64,(>.(0.&40.))))))))))(11.&40.=)))))")
(* [comment removed for export] *).
  Proof.
    intros Mk k Hk AG. pose proof SPlo. pose proof SPhi. destruct FRW as [[WF B] _].
    pose proof (cells_bytes_length _ WF) as LEN. cbn [cells_size csize Nat.add] in LEN.
    rewrite <- (rdn_agree asegs M Mk).
    2:{ intros j Hj. rewrite u_small by lia. symmetry. apply (AG (bv_unsigned sp0 + 8 + 8 * Z.of_nat k + Z.of_nat j)). lia. }
    pose proof (bytes_at_rdn asegs M (bv_unsigned sp0 + 8) _ (8 * k) 8 B ltac:(rewrite LEN; lia)) as RD.
    replace (bv_unsigned sp0 + 8 + Z.of_nat (8 * k))%Z with (bv_unsigned sp0 + 8 + 8 * Z.of_nat k)%Z in RD by lia. unfold wa in RD. rewrite RD.
    do 8 (destruct k as [|k]; [cbn; reflexivity|]). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac regs_ext_us RC V' VFV HR :=
      apply (srzJ_getr_ext asegs
               (mkR (getr RC (Z_to_bv 5 1)) (Z_to_bv 64 (bv_unsigned sp0 + 80)) (getr RC (Z_to_bv 5 3)) (Z_to_bv 64 0x63ca90)
                    (getr RC (Z_to_bv 5 5)) (getr RC (Z_to_bv 5 6)) (getr RC (Z_to_bv 5 7)) (getr RC (Z_to_bv 5 8)) (getr RC (Z_to_bv 5 9))
                    (Z_to_bv 64 2) (getr RC (Z_to_bv 5 11)) (getr RC (Z_to_bv 5 12)) (getr RC (Z_to_bv 5 13))
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
                      | (cbn [ev]; rewrite (vf0 V' VFV); reflexivity)
                      | (lazymatch goal with |- _ = ev _ ?n =>
                           change (ev _ n) with (vals_ev V' n); rewrite (vf0 V' VFV); reflexivity end) ] ]
          end
      | ].

  (* [comment removed for export] *)
  Ltac frame_read V3 LV2 AGm :=
    lazymatch goal with |- exists bs, rdn _ (restrict _ ?Mk) _ 8 = Some bs /\ _ =>
      unfold adenot, v_addi; cbn [a_base a_off edenot ev];
      lazymatch goal with |- exists bs, rdn _ _ (Z_to_bv 64 (bv_unsigned ?spv + ?off)) 8 = Some bs /\ _ = vals_ev _ ?k =>
        let kk := eval vm_compute in (Z.to_nat ((off - 8) / 8)) in
        eexists; split;
        [ apply (RestrictRun.rdn_restrictD asegs D);
          [ replace (bv_unsigned spv + off)%Z with (bv_unsigned sp0 + 8 + 8 * Z.of_nat kk)%Z by (rewrite (vf0 V3) by assumption; lia);
            apply (frw_rdn Mk kk); [lia | intros a Ha; apply AGm; split; rewrite wa_unsigned by lia; lia]
          | rewrite (vf0 V3) by assumption; rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | rewrite (vf0 V3) by assumption; rewrite u_small by lia; intros z Hz; apply (D_frame z (z + 1)); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz; lia ]
        | repeat match goal with H : vals_ev _ _ = _ |- _ = vals_ev _ _ => rewrite H end; cbn [nth]; first [apply rd8_val | symmetry; apply rd8_val] ]
      end
    end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "02W0@L10522145838.106L10769333283.116L10769333283.117L10769333283.140L10789669994.126L10799694563.117L10802157449.116L11093386449.106L11799965518.138L11938850325.145L12162701095.116L12162701095.117L12352482293.106L12381576378.106L12773901487.150L14309645649.106L14389901238.138L14496887799.148L14564977834.106L15043846984.117L15045195298.116L15047244086.106L15526789558.138L16143434206.117L16145241268.116L16252466602.106L18381454536.116L18381454536.117L18381454536.140L18452601618.1  L20923682512.116L21099177730.138L22381155623.116L22836635619.117L22838081693.117L22838440585.116L23018909934.104L24632964406.138L24673046294.116L24675965564.117L25271896031.151L25273991249.150L25273991639.149L25274020488.147L25274267889.129L25276088791.148L25278169808.136L25278169810.134L25278169811.135L25278169812.132L25278169813.133L25278169815.131L25278169820.130L25367110702.145L26725352500.116L26725352500.117L27126499714.138L27598234713.116L27805037753.116L27816511892.116L27816511892.117L27816511892.140L27836737151.116L2819355096.116 L28403058713.117L29443215018.2  L29524722842.145L30135717720.116L30135878988.117L30198409910.138L30224865085.138L30247691664.147L3124531126.138 L31792382470.117L32012096746.116L32012096746.117L32032333883.3  L32649261494.138L33010498853.116L33017145423.117L33135475714.138L33178294566.106L33355456082.106L33381484148.116L33678035766.138L33748443578.106L3420509078.106 L34301841077.130L34634032557.104L35022435766.138L35203208118.138L36782180292.106L38557618280.116L38557618280.117L38948347337.116L38950490845.106L38955452579.117L39163178626.138L39835184468.106L40749834296.115L40852924661.126L40863868540.117L40865149718.116L43937984950.138L44072741110.150L45188403458.138L45219273270.138L46533078311.2  L46695365583.145L46952839184.117L46958833018.116L47747548489.116L47760128357.140L47760128357.149L48023884600.106L50774715085.106L51199591298.138L52135528630.106L52331461418.106L52726078230.106L5316274158.145 L53519159512.116L53519159512.117L54385772041.117L54388101987.116L54438962780.138L55810752186.106L55888914490.117L55890197840.116L565194678.138  L56739572530.118L56765667309.140L56765667309.149L57140523856.140L57140523856.149L57226917378.138L57743708342.138L57865633273.116L58980766646.138L5926590833.151 L5928689407.150 L5928689529.149 L5928709158.147 L5930786681.148 L5967283506.116 L5968498776.117 L61014438335.106L63235889282.138L63433483702.138L64160631775.138L65211166553.106L65307895382.116L65310225212.117L67691375097.116L67812584585.118L67818668628.151L67820762883.147L67820766300.149L67820766682.150L67822863452.148L7276823820.106 L8581753910.138 L8675981946.116 L9148513689.126 L9152865914.116 L9158275856.117 L9551653884.116 00000h01P02M03<03d04L05405W06A07007m08j09R0:?0;10;T0<H0=:0=;0=^0>A0>d0?X0@P0AH0Ak0BP0C80Cg0Cl0DO0E90Ea0FI0G10GY0HV0IE0J20J_0KI0L30L]0MG0N10N[0OE0Oo0PY0QC0Qm0RW0SA0Sk0TN0U60U`0VC0W<0X=0Y>0Ym0ZP0[30[V0[_0\n0]V0^>0^m0_W0`c0aW0b:0b]0cE0cR0dA0e:0f30f]0gZ0hW0i?0in0jk0kS0lc0mK0n?0o30ok11512?12b13E13h14R15J15m16Z17G18418h19Z1:D1;31;<1;k1<S1=;1=^1>P1?B1?C1@;1@e1AH1Ak1Al1B[1C>1Cf1D^1EV1F@1G=1H61Ho1I^1JL1KX1Ld1Mh1Nl1OV1PE1Pm1Qa1RK1S51S_1TI1U31V81W=1We1XO1YC1Ym1ZU1[Z1\_1]W1^X1_B1_l1`V1a@1aj1bR1cA1d:1db1eJ1f21fUS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV21z2HzS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV2V23LV21x2O2S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV22RC1i2HiFS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1zS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV21z2HzS3sp0S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L625WINLO1V2LV3Hlo1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo3L625WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV21z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS2lo4LOloS3sp04SPlo4SPal2lo5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo5WINLO1V2LV3Hlo2V23LV2S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo2lo4LOhi5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo2V23LV21z2HzS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp02lo4LOhiS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo2lo4LOhi5STKHI7STKHIlo7STKHI641P4path1L3buf3Plo5WINLO1V2LV3Hlo1x2O12O2S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo1z2HzS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3Hlo1z2HzS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV2V23LV21x2O1S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp03XAGS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV2V23LV21a2HaS3sp02lo5STKHI1P4path1L3buf5WINLO1V2LV2V23LV21a2HaFS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LVFS3sp04SPlo5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo4LMAX5WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S2AL2CS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2HzS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1V2LV3Hlo2V23LV21a2HaS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo5WINLO1V2LV3Hlo2V23LV21a2HaS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo2V23LV21a2HaS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3Hlo2V23LV21a2HaS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo4SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LV3HloS3sp04SPlo5STKHI7STKHIlo1P4path1L3buf3Plo5WINLO1V2LV3HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV1z2Hz4SPlo7STKHIlo3Plo3L623HloS3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp05STKHI1P4path1L3buf4LMAX5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LV2V23LV2S3sp04SPlo5STKHI7STKHIhi1P4path1L3buf3Plo4PL165WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp04SPhi5STKHI1P4path1L3buf5WINLO1V2LVS3sp05STKHI1P4path1L3buf5WINLO1V2LV". (* [comment removed for export] *)
  Theorem stage_E : S_E.
  Proof.
    intros V Rk Mk mok VFV LV HR HK AGk HKk FS FD XE1.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SSH_facts as SSF. pose proof (u64_range P) as PR.
    unfold EnvV in HR, HK. destruct XE1 as (XL1 & BYP1 & NL1). unfold XL in XL1. rename XL1 into EV150.
    assert (HL : L = Z.of_nat (length path)) by reflexivity.
    assert (Lsmall : (bv_unsigned (edenot {| ev := vals_ev V; eb := blobs_ev [] |} (EVar 150)) < 2 ^ 31)%Z).
    { cbn [edenot ev]. rewrite EV150, u_small by lia. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 144 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
    time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrE 237%nat true covtac).
    all: try solve_sc.
    all: try (lazymatch goal with |- srealizesJ _ _ _ => fail | _ => cbn [sc_denot branch_taken]; awn Lsmall; cmpL end).
    all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "E-SC-LEFT" g end.
    rename EQM into EQMA. rename OUT into OUTA. rename R0 into RA. rename M0 into MA0. rename HKmo into HKA. rename MM into MMA.
    assert (AGA : AGR M lo (bv_unsigned sp0) MA0) by (block_AG AGk EQMA OUTA).
    (* [comment removed for export] *)
    assert (BYPA : bytes_at asegs MA0 (bv_unsigned sp0 - 457) path).
    { eapply (bytes_at_block D _ Mk MA0 _ _ _ BYP1 EQMA). intros z Hz. split.
      - apply (D_frame z (z + 1)); unfold L in *; lia.
      - cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
        rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [unfold L in *; lia | exact I]. }
    assert (NLA : bytes_at asegs MA0 (bv_unsigned sp0 - 457 + L) SUF7).
    { eapply (bytes_at_block D _ Mk MA0 _ _ _ NL1 EQMA). intros z Hz. rewrite SUF7_len in Hz. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz. split.
      - apply (D_frame z (z + 1)); lia.
      - cbn [log_out]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
        rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; first [lia | exact I]. }
    clear AGk EQMA OUTA.
    (* [comment removed for export] *)
    unfold TT. rewrite msg_cannot_open_eq. unfold W.
    replace (PRE17 ++ path ++ SUF7) with ((PRE17 ++ path ++ SUF7) ++ []) by (rewrite app_nil_r; reflexivity).
    change (Z_to_bv 64 2) with (Z_to_bv 64 (sc_fd resF)).
    assert (FdA : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))).
    { unfold FD2 in FD. unfold m_fds in *. destruct MMA as (E1 & _). rewrite E1. exact FD. }
    assert (SC : stdio_call 237%nat srEe knEe = Some resF) by (vm_compute; reflexivity).
    assert (LP : Z.of_nat (length (PRE17 ++ path ++ SUF7)) = 14 + L).
    { rewrite !length_app, PRE17_len, SUF7_len. unfold L. lia. }
    eapply (stdio_call_sound_frA AL CS KI IMG K_halted K_mat K_vmonly V (blobs_ev []) srEe knEe RA MA0 mo resF (PRE17 ++ path ++ SUF7) []
              (t_exit (exit_code 2) (m_fs model)) HR HK);
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn resF edenot];
      rewrite ?LP; cbn [length Z.of_nat].
    + rewrite LV. exact SC.
    + evs. azl. unorm. lia.
    + evs. azl. unorm. lia.
    + reflexivity.
    + lia.
    + right. evs. azl. unorm. lia.
    + left. evs. azl. unorm. lia.
    + unorm. lia.
    + evs. azl. unorm. lia.
    + unorm. lia.
    + (* [comment removed for export] *)
      evs. rewrite alu_add_zlit by lia. rewrite u_small by lia.
      rewrite <- preZ_msg.
      change (length ((map (fun v : Z => Z_to_bv 8 v) preZ ++ path ++ SUF7) ++ [])) with (length (map (fun v : Z => Z_to_bv 8 v) preZ ++ path ++ SUF7)).
      rewrite length_app, length_map. change (length preZ) with 7%nat.
      apply rdn_app_Z; [ | | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
      * pose proof (kread_bytes_rdn _ MA0 knEe (EVar 0) 7 (-464) preZ HK preZ_eq preZ_range) as RD.
        cbn [edenot ev] in RD. rewrite (vf0 V VFV) in RD. apply RD; lia.
      * change (Z.of_nat 7) with 7. rewrite length_app, SUF7_len.
        apply rdn_app_Z; [ | | lia | lia].
        -- pose proof (bytes_at_rdn asegs MA0 _ path 0 (length path) BYPA ltac:(lia)) as RD. rewrite Z.add_0_r in RD. cbn [skipn] in RD. rewrite firstn_all in RD.
           unfold wa in RD. replace (bv_unsigned sp0 + -464 + 7) with (bv_unsigned sp0 - 457) by lia. exact RD.
        -- pose proof (bytes_at_rdn asegs MA0 _ SUF7 0 7 NLA ltac:(rewrite SUF7_len; lia)) as RD. rewrite Z.add_0_r in RD. cbn [skipn] in RD.
           unfold wa in RD. replace (bv_unsigned sp0 + -464 + 7 + Z.of_nat (length path)) with (bv_unsigned sp0 - 457 + L) by (unfold L; lia). exact RD.
    + reflexivity.
    + exact FdA.
    + exact HKA.
    + intros z Hz. revert Hz. evs. azl. intros Hz. apply WCS. lia.
    + intros z Hz. revert Hz. evs. azl. unorm. intros Hz. left. apply WCS. lia.
    + intros z Hz. revert Hz; unorm; intros Hz. lia.
    + unfold t_exit. apply t_emit_has_nil.
    + (* [comment removed for export] *)
      intros Rm MC moC HPOST HRm HKm HKC MMC. clear HR HK. rename HRm into HR. rename HKm into HK.
      pose proof (vf0 V VFV) as V0eq.
      assert (AGC : AGR M lo (bv_unsigned sp0) MC).
      { eapply AGR_trans; [exact AGA|]. destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
        cbn [sc_sp sc_f sc_bufp sc_bufsz resF edenot ev] in Pagree. rewrite ?V0eq in Pagree. revert Pagree. azl. intros Pagree.
        split; [| exact Pgrows]. intros x [O1 O2]. apply Pagree; lia. }
      pose proof AGC as AGC'. destruct AGC' as [AGCm GRCm].
      pose proof (VF_app V (junk_vals Rm) VFV) as VFV2. set (V2 := V ++ junk_vals Rm) in *.
      assert (LV2 : length V2 = 269%nat) by (subst V2; rewrite length_app, junk_vals_length, LV; reflexivity).
      clearbody V2.
      set (V' := V2 ++ [w64; w56; w48; w40; w32; w24; w16; w8]).
      apply (env_app_regs V2 [w64; w56; w48; w40; w32; w24; w16; w8] (blobs_ev []) (sc_sr resF) Rm ltac:(rewrite LV2; vm_compute; reflexivity)) in HR.
      apply (env_app_know asegs V2 [w64; w56; w48; w40; w32; w24; w16; w8] (blobs_ev []) MC (sc_kn resF) ltac:(rewrite LV2; vm_compute; reflexivity)) in HK.
      pose proof (VF_app V2 [w64; w56; w48; w40; w32; w24; w16; w8] VFV2) as VFV'. fold V' in HR, HK, VFV'.
      clear VFV. rename VFV' into VFV.
      assert (EV269 : vals_ev V' 269 = w64) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV270 : vals_ev V' 270 = w56) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV271 : vals_ev V' 271 = w48) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV272 : vals_ev V' 272 = w40) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV273 : vals_ev V' 273 = w32) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV274 : vals_ev V' 274 = w24) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV275 : vals_ev V' 275 = w16) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
      assert (EV276 : vals_ev V' 276 = w8) by (subst V'; rewrite vals_ev_app_ge, LV2 by (rewrite LV2; lia); reflexivity).
    (* [comment removed for export] *)
    try clear KND; lazymatch type of HR with regs_ok (Env (vals_ev ?Vx) ?bb) _ _ =>
      pose proof (kn_inD_residualS D (Env (vals_ev Vx) bb) sp0 (-4096) 144 LITS_KND ltac:(cbn [ev]; apply vf0; assumption) D_frameS HLITS_KND) as KND end.
      time (run_blockA3S RRUN KND FUEL_OF STOPS_OF scrF 269%nat true covtac).
      all: try solve_sc.
      all: try (frame_read V' LV2 AGCm).
      all: match goal with |- srealizesJ _ _ _ => idtac | |- ?g => idtac "F-SC-LEFT" g end.
      lazymatch goal with |- srealizesJ _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RC; rename Mn into MD end.
      rename EQM into EQMC. rename OUT into OUTC. rename HKmo into HKD. rename MM into MMD.
      (* [comment removed for export] *)
      regs_ext_us RC V' VFV HR.
      change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
      lazymatch goal with |- srealizesJ _ (mkCfg _ ?mox) _ => replace (m_fs model) with (m_fs mox) end.
      2:{ rewrite (mo_mat_fs _ _ MMD), (mo_mat_fs _ _ MMC), (mo_mat_fs _ _ MMA). exact FS. }
      apply (exit2_at_dddf8_deep AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly sp0 ltac:(lia) ltac:(lia) lo LOlo
               M can tid wp0 rp0 wp1 rp1 TM (bv_unsigned sp0 + 80) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros z Hz; apply SCS; lia));
        [| exact HKD |].
      * (* [comment removed for export] *)
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
      * (* [comment removed for export] *)
        assert (AGD : AGR M lo (bv_unsigned sp0) MD) by (block_AG AGC EQMC OUTC).
        destruct AGD as [AGm GRm].
        apply (stk_agree M MD); [| exact UFR]. intros a Ha. apply AGm. split; rewrite wa_unsigned by lia; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End OF.
