(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ShapeX BBFrame MemcpyLib AgentLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib NodesA NodesA2 SymDriveA RestrictRun.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg ARestrict A_stdio_defs A_stdio_write_run1 A_stdio_write_run2 A_code_e3000_e4000  .
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_stdio_write.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_A_stdio_write () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Loop.LM"; "Loop.KM"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_write_run2.mem_sw2"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Loop.RI"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "Corelib.Init.Peano.lt"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.app"; "LM"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_write_run1.mem_sw1"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_defs.sw_post"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_defs.sw_file"; "RocqVerifyHarness.AgentSubmission.LibA.Restrict.restrict"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_stdio_defs.ssp_cells"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"].


Lemma rz_emit_nilA : forall c K, srealizesJ RSEGS c K -> srealizesJ RSEGS c (t_emit [] K).
Proof.
  intros c K H. eapply srzJ_conseq; [exact H|].
  apply t_eq_sym. apply t_emit_nil_eq. exact (srzJ_nonempty _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma pc_e341c : v_addi (0x0e67c8 : word) 4 = (0x0e67cc : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma pc_e3394 : v_addi (0x0e6740 : word) 4 = (0x0e6744 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Section Loop.
  (* [comment removed for export] *)
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable K : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VK,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VK,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pmo,$0.Pmo',$0.P,A1.VK,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VK,R6.")
(* [comment removed for export] *).

  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : word -> option byte.
  Variable mo0 : Model.
  Variable KK : TSet.

  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis Flo : (0x0fa360 <= f)%Z.
  Hypothesis Fhi : (f + 232 <= 0x0fb358)%Z.
  Hypothesis FD : (0 < fd < 2147483648)%Z.
  Hypothesis Hfd : fd_lookup (m_fds mo0) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Hypothesis FRCS : forall z, (su - 112 <= z < su)%Z -> CS z.       (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ret.
  Hypothesis HKnil : KK [].
  Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
  Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
  Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
  Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
  Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
  Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
  Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
  Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
  Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
  Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x65cad0) 8%nat = Some (word_to_le_bytes 8 can).
  Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
  Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
  Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

  (* [comment removed for export] *)
  Let D : word -> bool := Dimg [(su - 112, su)%Z].

  #[using="Type"] Lemma D_Dseg : forall a : word, segcov RSEGS (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30813421528.60000009S2su1z2Hz". (* [comment removed for export] *)
  #[using="IMG FRCS"] Lemma D_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK AL CS IMG [(su - 112, su)%Z]); [|exact H].
    constructor; [|constructor]. cbn. intros z Hz. apply FRCS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L58121287578.56000009S2su4SUlo". (* [comment removed for export] *)
  #[using="SUlo"] Lemma D_D0 : D (Z_to_bv 64 0) = false.
  Proof. unfold D. apply Dimg_D0. constructor; [cbn; lia|constructor]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L28139165318.62L30813421528.62L58119383268.6200000900P00YS2su4SUhiS2su2lo2hi3Hlo3Hhi1z2HzS2su4SUlo". (* [comment removed for export] *)
  #[using="SUlo SUhi"] Lemma D_frame : forall lo hi, (su - 112 <= lo)%Z -> (hi <= su)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_cov [(su - 112, su)%Z] (su - 112) su); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.6200000DS2lo2hi3Hlo3Hhi1z2Hz". (* [comment removed for export] *)
  #[using="Type"] Lemma D_img : forall lo hi, (0x10000 <= lo)%Z -> (hi <= 0x65f000)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_img [(su - 112, su)%Z]). unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition KM (mo : Model) : Prop := K mo /\ mo_mat mo0 mo.
  #[using="Type"] Lemma KM_K : forall mo, KM mo -> K mo. Proof. intros mo [H _]; exact H. Qed.
  #[using="Type"] Lemma KM_step : forall mo mo', KM mo -> K mo' -> mo_mat mo mo' -> KM mo'.
  Proof. intros mo mo' [HK MM] HK' MM'. split; [exact HK'|]. eapply mo_mat_trans; eauto. Qed.
  #[using="Hfd"] Lemma KM_fds : forall mo, KM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
  Proof. intros mo [_ MM]. unfold m_fds in *. destruct MM as (E & _). rewrite E. exact Hfd. Qed.

  (* [comment removed for export] *)
  Definition rrun := rz_smsteps_RK RSEGS D AL CS K K_halted K_mat D_Dseg asegs_top D_DOK D_D0.

  (* [comment removed for export] *)
  Definition LM (m : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "(7.Px,(3.&40.)P,(12.(7.(13.(14.Vsu,+68.)(15.&40.R1.))(16.(15.&40.R1.)(14.Vsu,+48.))))(8.(9.(3.&8.))A1.O1.R2.A1.Vmem1,R2.)(17.Vmem1,O1.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Hypothesis HK : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pregs',(18.&5.(3.&40.))Pm,P,(3.&40.)(9.(3.&8.))Pmo,$0.P,(8.(3.&40.)(19.R3.(1:.&5.+:.$1;.))Vl,)P,(8.(3.&40.)(19.R4.(1:.&5.+2.$1;.))(1<.&40.Vsu,))P,(8.(3.&40.)(19.R5.(1:.&5.+1.$1;.))Vret,)P,(8.(3.&40.)(19.R6.(1:.&5.+8.$1;.))Ve8,)P,(8.(3.&40.)(19.R7.(1:.&5.+9.$1;.))Ve9,)P,(8.(3.&40.)(19.R8.(1:.&5.+12.$1;.))Ve18,)P,(8.(3.&40.)(19.R9.(1:.&5.+13.$1;.))Ve19,)P,(8.(3.&40.)(19.R:.(1:.&5.+14.$1;.))Ve20,)P,(8.(3.&40.)(19.R;.(1:.&5.+15.$1;.))Ve21,)P,(8.(3.&40.)(19.R<.(1:.&5.+16.$1;.))Ve22,)P,(8.(3.&40.)(19.R=.(1:.&5.+17.$1;.))Vg23,)P,(8.(3.&40.)(19.R>.(1:.&5.+18.$1;.))Vg24,)P,(8.(3.&40.)(19.R?.(1:.&5.+19.$1;.))Vg25,)P,(8.(3.&40.)(19.R10.(1:.&5.+1:.$1;.))Vg26,)P,(8.(3.&40.)(19.R11.(1:.&5.+1;.$1;.))Vg27,)P,(8.(3.&40.)(19.R12.(1:.&5.+3.$1;.))Vg3,)P,(8.(3.&40.)(19.R13.(1:.&5.+4.$1;.))Vg4,)P,(1=.R13.)P,(1>.R13.)(1?.$20.(21.(22.$23.R16.Vret,(24.R15.Vf,Vbufp,Vbufsz,)(25.$20.))R14.)VKK,)")
(* [comment removed for export] *).

  Definition RI (regs : bvmap 5 word) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "(7.(8.(3.&40.)(19.O1.(1:.&5.+2.$1;.))(1<.&40.(14.Vsu,+70.)))(7.(8.(3.&40.)(19.O1.(1:.&5.+8.$1;.))Vl,)(7.(8.(3.&40.)(19.O1.(1:.&5.+9.$1;.))(1<.&40.Vf,))(7.(8.(3.&40.)(19.O1.(1:.&5.+15.$1;.))(1<.&40.+65<:=0.))(7.(8.(3.&40.)(19.O1.(1:.&5.+3.$1;.))Vg3,)(7.(8.(3.&40.)(19.O1.(1:.&5.+4.$1;.))Vg4,)(7.(8.(3.&40.)(19.O1.(1:.&5.+17.$1;.))Vg23,)(7.(8.(3.&40.)(19.O1.(1:.&5.+18.$1;.))Vg24,)(7.(8.(3.&40.)(19.O1.(1:.&5.+19.$1;.))Vg25,)(7.(8.(3.&40.)(19.O1.(1:.&5.+1:.$1;.))Vg26,)(8.(3.&40.)(19.O1.(1:.&5.+1;.$1;.))Vg27,)))))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
  Proof.
    (intros regs regs' dd_H; ddestruct dd_H as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27); intros dd_H; ddestruct dd_H as (P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27)).
    unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
  Qed.

  #[using="Type"] Lemma LM_refl : LM mem1.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L34301897727.6800000@S2su1a1n2DJ1x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma LM_rdn : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pm,P,(3.&40.)(9.(3.&8.))Pa,(3.&40.)Pn,$4.Pbs,(1.(3.&8.))P,(1=.R4.)P,(8.(9.(1.(3.&8.)))(26.$20.Vmem1,R4.R3.)(;.(1.(3.&8.))R2.))P,(13.(27.(15.&40.R5.)(28.R4.))(29.+2.+40.))P,(2:.(13.(27.(15.&40.R6.)(28.R5.))(14.Vsu,+68.))(13.(14.Vsu,+48.)(15.&40.R6.)))(8.(9.(1.(3.&8.)))(26.$20.R8.R7.R6.)(;.(1.(3.&8.))R5.))")
(* [comment removed for export] *).
  Proof.
    intros m a n bs [E G] H Hnw DJ.
    rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
    intros x Hx. apply E. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma LM_store_ok : forall m (a : word) n,
    LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
  Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L11319347736.66L20950175652.66L26983618961.66L62729228902.6600000?00N00]010S2su4SUhi1a3HhiS2su4SUhi1a3HhiS2su4SUlo1a3HloS2su1a3Hlo3Hhi1x2Hx". (* [comment removed for export] *)
  #[using="SUlo SUhi"] Lemma LM_wbytes8 : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pm,P,(3.&40.)(9.(3.&8.))Pa,$2;.Pv,(3.&40.)P,(1=.R3.)P,(13.(14.Vsu,+68.)R3.)P,(13.(27.R4.+8.)(14.Vsu,+48.))(1=.(2<.R6.(1<.&40.R5.)(2=.#8.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros m a v [E G] Hlo Hhi. split.
    - intros x Hx. rewrite wbytes_outside.
      + apply E, Hx.
      + unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
      + rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rres T := first
    [ eapply (rdn_restrictD RSEGS D); [T | u_norm; lia | first [apply D_frame; u_norm; lia | apply D_img; u_norm; lia]]
    | eapply (store_ok_restrictD RSEGS D); [T | u_norm; lia | apply D_frame; u_norm; lia] ].
  (* [comment removed for export] *)
  Ltac dz := first [lia | apply D_frame; lia | apply D_img; lia].
  Ltac solve_outside := intros xx Hxx; repeat (rewrite (wbytes_agree_outD_Z D) by (first [exact Hxx | dz])); reflexivity.
  Ltac push_restrict_in H := repeat (rewrite (wbytes_restrict_Z D) in H by dz).
  (* [comment removed for export] *)
  Ltac rrunK RUN KMH KMnew :=
    push_restrict_in RUN;
    eapply rrun; [exact (KM_K _ KMH) | exact RUN | solve_outside | ];
    clear RUN;
    let mo1 := fresh "mo" in let HK1 := fresh "HKm" in let MM1 := fresh "MM" in
    intros mo1 HK1 MM1; pose proof (KM_step _ _ KMH HK1 MM1) as KMnew; clear HK1 MM1.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01_0?L11028903476.73L11543741168.73L12061352116.73L13495341050.73L14512263535.73L1452853103.73 L14792935650.73L14912416112.73L15222827396.73L16424100177.73L17330758512.73L17472106990.94L17472246959.92L1756071935.94 L1756226238.92 L19508727791.73L19617040132.73L20069264436.73L22151267440.73L23568027060.73L23590264756.73L23927344624.73L24841147632.73L25468653424.73L25529749871.73L25651175522.73L26863326539.73L27095630084.73L27265440465.73L28651210023.73L30299858826.94L30299996875.92L30705881473.73L30822078417.73L31532295407.73L31610493748.73L31735726443.73L32782209795.73L32884881611.73L33798409603.73L36007744431.92L36007900910.94L36231198534.73L37302444548.73L37549651567.73L38145045073.73L38920587851.73L42413582411.73L4308055387.73 L43585493487.73L43903110902.73L44151706292.73L44349209844.73L44476930052.73L44937813451.73L45367360496.73L46033524336.73L46481858068.73L47750215371.73L48449289163.73L48875468676.73L49005652945.73L49793874397.94L49794014364.92L5032659076.73 L50773147406.92L50773547599.94L50940489547.73L51390867779.94L51390974978.92L5222015947.92 L5222418058.94 L52239336148.73L52559673553.73L55099768860.92L55099893085.94L55626366703.73L5563238865.73 L55697392052.73L56784152783.94L56784522638.92L56959546059.73L5824608340.73 L58438760894.92L58439163135.94L59164172596.73L59846984529.73L6134983622.73 L61628514415.73L61942068598.73L62651575810.92L62651714371.94L62809963855.94L62810069006.92L62997873739.73L63403626577.73L6378420996.73 L64153007599.73L64464449919.94L64464819262.92L65705022173.94L65705179036.92L6590442819.94 L6590580738.92 L65925197643.92L65925335562.94L66560873092.73L68112258727.73L6965731054.94 L6966148015.92 L7494761594.73 00000900=00F00M00N00W00f00j01301701;01F01Q01R01S01\01e01n02202;02D02H02L02P02Y02h02l03503903@03G03N03W03[03d03m03n04504904@04K04V04]04f04o05305705;05<05E05F05O05P05Y05]05a05e05f05g05k06406806?06F06O06V06]06a06b06c06j07107807<07C07J07S07W07`07g07n08208908:08;08D08H08O08X08Y08Z08[08b08i08m09109:09C09D09E09L09S09T09U09\09c09l0:30:>0:I0:PS2su4SUhiS2suS2su4SUhiS1f3FloSS2su4SUloS2su1f4SUlo3FhiS2suS2su4SUhiS2suS2suS1f3Flo3FhiS1f3Flo3FhiFFS2su4SUloS2su4SUhiS2su4SUhiS2suS2su4SUhiS2su4SUhiS2suS2suS2suS2su4SUloS2su1f4SUlo3FhiS2suS2su4SUhiS2suS1f3FhiS1f3FhiS1f3FhiS2su4SUloS2suS2su4SUloS2su4SUhiSS1f3FhiS2suS1f3FhiS1f3Flo3FhiS1f3Flo3FhiS1f3FloS2su4SUhiS2su4SUloS2suS2suS2suFS2su4SUloFS2su4SUhiSS2su4SUhiS2suS2suS2suSSS2suS2su4SUhiS2suS1f3FhiS1f3FhiS2su4SUhiS1f3FloS1f3FloS2suFFS1f3FhiS1f3FhiS1f3FhiS2suS1f3FhiS1f3FhiS2su4SUloS2suS2su4SUhiS1f3FloS1f3FloS2suS1f3FhiFFS2su4SUhiS2suS1f3FloS2su4SUloFFFS1f3FloS1f3FloS2suS2suS2su4SUhiS2su4SUloFFS1f3FhiS1f3FhiFFS1f3FhiS1f3FhiS2su4SUhiS1f3FhiS1f3Flo3FhiS1f3Flo3FhiS1f3Flo". (* [comment removed for export] *)
  #[using="AL CS IMG K_halted K_mat bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FRCS Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz D HK"] Lemma finish : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pregs,(18.&5.(3.&40.))Pm,P,(3.&40.)(9.(3.&8.))Pmo,$0.P,(2>.R3.)P,(1=.R3.)P,(1>.R3.)(1?.$20.(21.(22.$23.R6.(1:.&40.+>674<.$1;.)R5.(25.$20.))R4.)VKK,)")
(* [comment removed for export] *).
  Proof.
    intros regs m mo RIr LMm KMmo.
    ddestruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    ddestruct (sw_done regs (restrict D m) (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
      as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
      try assumption.
    all: try (rres ltac:(eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia])).
    unfold mem_sw2 in RUN. rrunK RUN KMmo KM1. fold (mem_sw2 m f bufp bufsz).
    apply HK; try assumption.
    - rewrite Q23; exact R23.
    - rewrite Q24; exact R24.
    - rewrite Q25; exact R25.
    - rewrite Q26; exact R26.
    - rewrite Q27; exact R27.
    - rewrite Q3; exact R3.
    - rewrite Q4; exact R4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="AL CS IMG K_halted K_mat bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FRCS Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz D HK"] Lemma finish_nil : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pregs,(18.&5.(3.&40.))Pm,P,(3.&40.)(9.(3.&8.))Pmo,$0.P,(2>.R3.)P,(1=.R3.)P,(1>.R3.)(1?.$20.(21.(22.$23.R6.(1:.&40.+>674<.$1;.)R5.(25.$20.))R4.)(2?.(30.$31.)VKK,))")
(* [comment removed for export] *).
  Proof. intros. apply rz_emit_nilA. apply finish; assumption. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01d0@L12329863768.94 L13485030140.94 L13487025709.108L13487172651.123L13721927173.94 L1388607017.105 L14005042915.94 L14005153411.105L14007137273.107L14595720312.109L14860994493.124L15131436811.123L15131436811.124L15482806602.107L15485287472.105L18267722263.94 L18312414488.94 L1870224821.123 L1870602163.108 L2133584180.124 L21965917795.94 L22126922911.107L22128644581.105L23059349273.122L23059758367.107L23059758367.108L23950079757.109L24001246580.115L24001331040.115L24895548300.106L25209069666.109L25328974635.108L28146067512.124L29402847091.124L29402961269.108L30199669589.94 L30339192246.94 L30389315000.105L30389728728.94 L30391826626.107L30813421528.111L32377529384.106L32377906728.108L32379581177.94 L35312854505.109L36398202968.94 L36982274404.109L36982684514.124L36984725933.111L37003139223.94 L37004872774.108L37004872774.109L37005282880.123L37033469903.94 L37879971301.94 L38130568460.106L38481817782.115L39718860297.106L40699307608.94 L40928159283.124L41626128583.94 L41810202512.94 L43131829927.94 L43389386584.109L43936315312.105L43937999562.107L44478234046.127L44480114992.112L44480117814.113L45219283274.107L45221010480.105L45727832457.106L45729943384.94 L46087295189.109L47622960295.94 L4861192441.94  L4878356317.94  L49158300399.111L49160452128.124L49448570095.124L49648375619.108L49658117203.105L49660354857.107L50223214883.115L50926684401.94 L57118251985.124L57118366167.109L58119382268.94 L58141766505.94 L59310627411.80 L61052735102.94 L61549161020.105L61551146822.107L64662599664.124L64764976764.124L64912887836.109L6565153332.94  L66267405510.108L66267782848.123L66269923351.94 L66643565615.105L66645541205.107L67197089863.105L67197233191.94 L67199329597.107L7457647740.94  L7459732139.123 L7459846317.108 L7459846317.109 L8676958307.94  L8927290854.112 L8927291616.113 L8927474081.109 L8929245077.115 L934450997.123  L934597939.108  00000B00Y01001P01_01`02202D02V02i03N03f04>04Z05605M05N05n06E06c07507607707\08808b09109P09l0:>0:S0:g0;C0;[0;j0<?0<@0<R0<d0=60=M0=_0>10>C0>R0>d0?90?W0?l0@C0@Z0A10AQ0A`0Aa0B30BN0B`0C30CQ0Cf0D;0DR0De0EA0E]0FM0Fc0GA0GX0Go0HA0HS0Hb0I90I:0IL0I[0J30JK0Jd0Je0Jf0KA0K^0L;0LO0Lf0M;0MH0MW0Mi0N;0NV0O10OH0O]0P40PT0Pk0Q=0QO0Qf0R=0RT0Rk0SK0Sb0T90TK0T^0U70UJ0Uf0VF0V]S2su1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2Kb2k'2K12K2S1n1k2bs3LEN2KbFS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S2su1n1k1b2bs3LEN2Kb4DISJ2k'2K12K22NES1n1k2bs3LEN2Kb2k'2K12K2S1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo4SUhi1n1k2bs3LEN2KbS2su4SUlo4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbFS2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb3TSB2k'2K12K2S2su1n1k2bs3LEN2KbFFS2su4SUlo4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo4SUhi1n1k2bs3LEN2KbS2su4SUlo4SUhi1n1k1b2bs3LEN2Kb4DISJ3TSB2HbS1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M302k'2K12K22EQS1n1k2bs3LEN2Kb3M302k'2K12K2S2su1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb3TSBS1n1k1b2bs3LEN2Kb2NWS1n1k2bs3LEN2Kb3M302k'2K12K2S1n1k2bs3LEN2Kb2k'2K12K2S1n1k2bs3LEN2KbS1f3Flo1n1k2bs3LEN2KbFS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2Kb1z2HzS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb3TSBS1n1k1b2bs3LEN2Kb3TSB2k'2K12K2S1n1k1b2bs3LEN2Kb3TSBS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S1n1k2bs3LEN2KbFS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb2k'2K12K22EQS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S1n1k1b2bs3LEN2Kb3TSB2k'2K12K2S1f3Fhi1n1k2bs3LEN2KbS1f3Fhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S2su4SUlo4SUhi1n1k2bs3LEN2KbS2su4SUlo4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k1b2bs3LEN2Kb3TSB2k'2K12K22NE1H1z2HzS1n1k1b2bs3LEN2Kb1z2HzS1n1k1b2bs3LEN2Kb3TSB1z2Hz3EwrS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbFS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb2k'2K12K2S1n1k2bs3LEN2Kb2k'2K12K2S2su1n1k1b2bs3LEN2Kb4DISJFFS1n1k2bs3LEN2Kb2k'2K12K22NES2su1f4SUlo3Fhi1n1k2bs3LEN2KbS1n1k1b2bs3LEN2Kb2Hb2k'2K12K2S1n1k1b2bs3LEN2Kb2HbS2su4SUlo1n1k2bs3LEN2KbS1f3Flo1n1k2bs3LEN2KbS1k2bs3LEN2KbS1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb2k'2K12K22NES1n1k2bs3LEN2Kb2k'2K12K22EQS2su4SUhi1n1k2bs3LEN2KbS1f3Fhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUhi1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2Kb2k'2K12K2S2su4SUlo1n1k2bs3LEN2KbS2su4SUlo1n1k2bs3LEN2KbS2su1n1k2bs3LEN2KbS1n1k2bs3LEN2Kb3M30S1n1k1b2bs3LEN2Kb3TSB3EwrS1n1k2bs3LEN2Kb3M30S1n1k2bs3LEN2Kb3M302k'2K12K2S2su4SUhi1n1k2bs3LEN2Kb2k'2K12K2S2su4SUhi1n1k2bs3LEN2Kb". (* [comment removed for export] *)
  #[using="IMG K_halted K_mat bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd FRCS Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd D HK"] Lemma loop1 : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pn,$4.Pregs,(18.&5.(3.&40.))Pm,P,(3.&40.)(9.(3.&8.))Pmo,$0.Pk,$4.Pb,(3.&40.)Pbs,(1.(3.&8.))P,(32.(33.(3.&8.)R1.)R7.)P,(2>.R7.)P,(1=.R7.)P,(1>.R7.)P,Pz,$2;.P,(7.(13.(15.&40.R7.)R1.)(16.R1.(27.(15.&40.R7.)(28.(33.(3.&8.)R6.)))))(34.VAL,VCS,R2.)P,(8.(3.&40.)(19.R;.(1:.&5.+:.$1;.))(1<.&40.(28.R8.)))P,(8.(3.&40.)(19.R<.(1:.&5.+16.$1;.))(1<.&40.(28.(33.(3.&8.)R7.))))P,(8.(3.&40.)(19.R=.(1:.&5.+12.$1;.))(1<.&40.+1.))P,(8.(3.&40.)(19.R>.(1:.&5.+13.$1;.))(1<.&40.(14.Vsu,+58.)))P,(7.(32.#1.R<.)(35.R<.(33.(3.&8.)R:.)))P,(8.(9.(1.(3.&8.)))(26.$20.R?.(1<.&40.(14.Vsu,+58.))#8.)(;.(1.(3.&8.))(2=.#8.R<.)))P,(8.(9.(1.(3.&8.)))(26.$20.R10.(1<.&40.(14.Vsu,+50.))#8.)(;.(1.(3.&8.))(2=.#8.(1<.&40.(28.(33.(3.&8.)R<.))))))P,(8.(9.(1.(3.&8.)))(26.$20.Vmem1,R>.(33.(3.&8.)R=.))(;.(1.(3.&8.))R=.))P,(2:.(13.(27.(15.&40.R?.)(28.(33.(3.&8.)R>.)))(14.Vsu,+70.))(13.Vsu,(15.&40.R?.)))P,(13.(27.(15.&40.R10.)(28.(33.(3.&8.)R?.)))(29.+2.+40.))P,(13.(27.(15.&40.R11.)(28.(33.(3.&8.)R10.)))+800000000000.)P,(13.(28.(33.(3.&8.)R11.))(29.+2.+1>.))(1?.$20.(21.(22.$23.R17.(1:.&40.+>67=8.$1;.)R16.(25.$20.))R15.)(2?.(36.(3.&8.)$31.(37.(1<.&40.Vfd,))(38.(3.&8.)R14.R12.))VKK,))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros regs m mo k b bs LEN RIr LMm KMmo AOKb Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW TSB M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    ddestruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    (* [comment removed for export] *)
    ddestruct (sw_retry_a regs (restrict D m) (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { rres ltac:(eapply LM_store_ok; [exact LMm | exact SOK1]). }
    { rres ltac:(exact Mb). }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rres ltac:(exact Mn). }
    { rres ltac:(eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]). }
    rrunK RUN KMmo KM1.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    (* [comment removed for export] *)
    eapply (rz_writev1_wallA RSEGS AL CS K K_halted K_mat regs1 (0x0e67c8 : word) m' _ W_e3418 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) KK);
      [ exact F_e3418 | exact E_e3418 | exact (KM_K _ KM1) | exact (KM_fds _ KM1) | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | 
      | u_norm; intros z Hz; left; apply FRCS; lia
      | intros z Hz; apply AOKb; destruct (u_at_le b (Z.of_nat k) ltac:(lia) ltac:(lia)) as [Eat|[Eat Ewr]]; unfold at_ in Eat; rewrite Eat in Hz; rewrite u64_lit in Hz by lia; lia
      | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
    - u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
    - u_norm. lia.
    - u_norm. lia.
    - (* [comment removed for export] *)
      intros k' K1 K2 mo2 HK2 MM2. pose proof (KM_step _ _ KM1 HK2 MM2) as KM2. clear HK2 MM2.
      rewrite pc_e341c. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + (* [comment removed for export] *)
        ddestruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) (restrict D m') (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        rrunK RUN2 KM2 KM3.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil; [| exact LMm' | exact KM3].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + (* [comment removed for export] *)
        ddestruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) (restrict D m') (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        rrunK RUN2 KM2 KM3.
        apply (IH regs2 m' _ k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact KM3.
        * pose proof (u_at_le b (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. intros z Hz. apply AOKb. lia.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03f0@L12329750830.105L12329932989.105L12512005715.116L12513727273.118L13280409640.117L13280524840.119L13282440591.105L13368944527.105L13369028124.105L13371107880.117L13371222056.119L13485138314.105L13487025709.119L13487172651.134L1388607017.116 L14004790677.105L14595720312.120L14860994493.135L15131436811.134L15185501266.119L15185878612.135L15482316339.119L15482692661.134L15525119920.116L15526845130.118L15688928829.117L15688928829.119L15882612607.120L15934941693.135L16073330249.120L16399985333.134L16400099507.119L16771550251.105L16999775757.105L18125009076.135L18267539809.105L18267652338.105L18312353789.105L18312502894.105L18338371010.118L18340317368.116L18340399677.105L1870224821.134 L1870602163.119 L19510904657.105L21308939195.136L2133584180.135 L2150524013.135 L21965855878.105L21966001429.105L2305417016.105 L2305496747.105 L23057202721.118L23057202721.120L23059349273.132L23059758367.117L23059758367.119L24001246580.126L24001331040.126L24361843758.105L24362022333.105L24602181772.117L24613036018.105L24613213793.105L24895548300.117L25209069666.120L26793766726.119L26793766726.120L26794143040.134L26796353906.105L27171163695.116L27172885333.118L27403022860.117L28463687622.119L28464063936.134L28465965153.105L28466143730.105L29670166300.136L30199625763.105L30199738800.105L30389677742.105L30813421528.122L30912932890.120L3122268592.116 L3124516042.118 L32377906728.119L32713747379.135L33198816431.116L33200792021.118L33678086218.118L33679772976.116L34324482128.105L35312854505.120L36088903494.117L36088903494.119L36088903494.120L36089279808.135L36091359119.122L36398390062.105L36493952086.105L37002986465.105L37004872774.119L37004872774.120L37005282880.134L37033407786.105L37879916179.105L37880033024.105L38130568460.117L38208764674.119L39209563733.118L39211772719.116L39298156056.135L39300302624.120L39718860297.117L39749132041.120L40069819307.134L40070195629.119L40070195629.120L40071933849.105L40469550215.105L40928159283.135L41626190370.105L41626340273.105L41810140533.105L41810318566.105L42500456981.105L42500574086.105L42598706588.138L42601013522.123L42601016340.124L43131643345.105L43131759682.105L43717670067.120L43936315312.116L43937999562.118L44497811097.120L4456049267.122 L4458098876.135 L4458508986.120 L44684598305.135L44684975655.120L45219283274.118L45221010480.116L45616876079.135L45727832457.117L46078795051.134L46078943021.119L46080823434.105L46080940313.105L46949653151.120L46949767321.135L47614748860.116L47616439750.118L47623139281.105L47814889073.134L4860949391.105 L4861131292.105 L49158300399.122L49160452128.135L49837473654.120L49839782984.121L50223214883.126L50926474119.105L50926623252.105L51501192247.135L51596133180.116L51597860422.118L51755535113.117L53937290678.120L54109462973.117L54109462973.119L54568067256.105L55839140255.118L55841125605.116L56117638303.118L56119355877.116L563521968.116  L565245130.118  L56530858809.121L56535246178.122L56537366445.135L56890554374.120L57008335061.117L57613702704.116L57615911754.118L57763987081.117L57766165181.105L57766277934.105L58119208842.105L58119321113.105L58141827468.105L58141911071.105L58286516448.105L58704251412.120L59310627411.89 L59847102226.105L60192525639.116L60192870338.105L60194671094.117L60195033149.118L61549161020.116L61551146822.118L61657668143.120L63456137687.120L63896583115.122L63896583115.137L63896583115.138L63898859333.123L63898860099.124L6464229729.120 L64912887836.120L6565222609.105 L6565368130.105 L66267405510.119L66267782848.134L66269811553.105L67137529884.120L67197449041.105L67838202498.120L6784050575.105 L6785935912.119 L6786345000.117 L68209187537.105L68209300290.105L68210972022.117L68355622130.135L68426955787.126L6903871225.118 L6906030342.105 L6906375043.116 L7194169106.120 L7200641517.136 L7457568522.105 L7459732139.134 L7459846317.119 L7459846317.120 L8266974761.135 L844007327.118  L845732581.116  L8676719381.105 L8927290854.123 L8927291616.124 L8927474081.120 L8929245077.126 L934450997.134  L934597939.119  00000J00d00e00f01@01Z02402N02h03B03\04;04Z05B05C05]06806g07G07^08>08]09E09i0:M0:N0;10;L0;o0<J0=20=Q0=k0=l0>L0>k0?J0?K0?L0?f0@@0@Z0AB0Aa0Ab0B]0CD0Cj0DD0D^0E90ET0EU0FM0G=0Gd0HY0IC0Ij0JD0J^0K80KO0Kf0L@0Lh0MG0Mf0NN0Nm0OG0Oa0P;0PZ0QB0Qa0R@0S;0SX0T50TO0U10UH0Ul0VP0Vj0WN0Wh0XB0Xa0Y@0Y[0Z20ZP0[10[O0\60\T0\n0]I0]h0^G0^f0_N0_e0_f0_g0`A0`g0aA0a[0b;0bR0bl0cJ0d20dQ0e00eO0ef0fM0fj0gG0gd0hA0h[0i50j50jT0k;0kZ0l90l_0mC0mg0nE0nc0oJ0oh10O10m11L11k12K12e13M13l14K14j15E15i16C16]17<17\17]17^18518U18l19F19l1:Q1;61;Y1<31<M1<g1=>1=?1=b1><1>=1>>1>?1>@1>_1?>1?X1?o1@O1@f1A=1Aa1BE1B_1C91CS1D21DQ1Dn1EK1Eb1F91FK1Fb1GA1G`1H?1H^1I81IR1J01JK1Jj1KR1LR1M51M\1N31NR1No1OL1Ok1PS1Q21QQ1R01RG1Ra1S;1SU1T41TS1U21UR1V81VR1Vl1WF1Wa1X]1Y<1Yd1ZC1Zb1[B1[C1[D1[^1\H1]41]R1^91^a1_@S2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LEFFS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2GT2k'2K12K2FS2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302LES2su1n1k3bs02b13bs13LEN2Kb5DISJ12GT2k'2K12K22NES1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2GTFS2su1n1k3bs02b13bs13LEN2Kb5DISJ12LES1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K22EQS1n1k3bs03bs13LEN2Kb3M302LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTFS1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LEFFS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GTFS2su4SUhi1n1k2b03bs02b13bs13LEN2Kb3TS03TS12LE2k'2K12K22NE1HS1n1k3bs02b13bs13LEN2Kb3TS12GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2LE2k'2K12K22NE2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb3M302LEFS2su4SUlo4SUhi1n1k2b03bs03bs13LEN2Kb5DISJ03TS03Hb02LE2NKS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K22GTS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LE2GTS2su4SUlo4SUhi1n1k3bs02b13bs13LEN2Kb5DISJ13TS13Hb12GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K22EQ2GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K22GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS1n1k2b03bs03bs13LEN2Kb3TS02LE2b13TS12GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k2b03bs02b13bs13LEN2Kb3TS03TS12LE2k'2K12K22NE1HS1f3Flo1n1k3bs03bs13LEN2Kb2GTS1f3Flo1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LE1z2Hz2GTS1n1k3bs03bs13LEN2Kb2GTS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302GT2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb2LES1n1k3bs02b13bs13LEN2Kb3NW12LES1n1k3bs02b13bs13LEN2Kb3NW12LE2GTS1n1k3bs02b13bs13LEN2Kb3TS12GTS1n1k3bs02b13bs13LEN2Kb3TS12GT2k'2K12K2S1n1k3bs02b13bs13LEN2Kb3TS12GTS2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302LES2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2LEFFS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs02b13bs13LEN2Kb5DISJ12LE2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS1n1k2b03bs03bs13LEN2Kb3Hb02LES2su4SUlo1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUlo1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GTS1n1k3bs02b13bs13LEN2Kb3TS12GT2k'2K12K2S1f3Fhi1n1k3bs03bs13LEN2Kb2LES1f3Fhi1n1k3bs03bs13LEN2Kb2GTS1f3Fhi1n1k3bs03bs13LEN2Kb2LES1f3Fhi1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k2b03bs02b13bs13LEN2Kb3TS03TS12LE2k'2K12K22NE1H1z2HzS1n1k2b03bs03bs13LEN2Kb2LE1z2HzS1n1k2b03bs03bs13LEN2Kb3TS02LE1z2Hz3EwrS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su1n1k2b03bs03bs13LEN2Kb5DISJ02LE2NKS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs02b13bs13LEN2Kb3TS12LES1n1k2b03bs03bs13LEN2Kb3TS02LES1n1k2b03bs03bs13LEN2Kb3TS02LE2k'2K12K2S1n1k2b03bs03bs13LEN2Kb3TS02LES1n1k3bs02b13bs13LEN2Kb3Hb12GT2k'2K12K2S1n1k3bs02b13bs13LEN2Kb3Hb12GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S2su4SUlo1n1k3bs03bs13LEN2Kb2LES2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb3M302GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K2S2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K2FFS1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2k'2K12K2S1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LE2EKS1n1k3bs03bs13LEN2Kb2LE2k'2K12K22NE2GTS2su1f4SUlo3Fhi1n1k3bs03bs13LEN2Kb2GTS2su1f4SUlo3Fhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LE2k'2K12K22EQS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2LEFS2su1n1k3bs02b13bs13LEN2Kb5DISJ12LES2su1n1k3bs03bs13LEN2Kb2LEFFFFS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LE2EKS1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GTS2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUlo4SUhi1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2LES1f3Flo1n1k3bs03bs13LEN2Kb2LES1f3Flo1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GTS1k3bs03bs13LEN2KbS1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES1n1k2b03bs03bs13LEN2Kb3NW02LES1n1k3bs03bs13LEN2Kb3M302LES1n1k3bs02b13bs13LEN2Kb2LE1z2HzS1n1k3bs02b13bs13LEN2Kb2LE2k'2K12K21z2HzS2su4SUhi1n1k2b03bs02b13bs13LEN2Kb3TS03TS12GT2k'2K12K22NE1H1z2HzS1n1k3bs02b13bs13LEN2Kb2GT1z2Hz3EatS1n1k3bs02b13bs13LEN2Kb3TS12GT1z2Hz3EwrS1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1f3Fhi1n1k3bs03bs13LEN2Kb2LES1f3Fhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GTS2su4SUhi1n1k3bs03bs13LEN2Kb2LES2su4SUhi1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S1n1k3bs03bs13LEN2Kb2LE2k'2K12K22EQ2GTS2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES2su1n1k3bs03bs13LEN2Kb2LES1n1k3bs03bs13LEN2Kb3M302LES2su1n1k2b03bs02b13bs13LEN2Kb5DISJ03TS03Hb12LE2k'2K12K22NE1HS2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUlo1n1k3bs03bs13LEN2Kb2GTS2su4SUlo1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb2GT2k'2K12K2FFS2su1n1k3bs03bs13LEN2Kb2GTS1n1k3bs03bs13LEN2Kb3M302LE2b12GT1z2Hz3EatS1n1k2b03bs03bs13LEN2Kb3TS02LE3Ewr2b13TS12GTS1n1k3bs03bs13LEN2Kb3M302LE2GTS1n1k3bs03bs13LEN2Kb3M302LE2k'2K12K22GTS2su4SUhi1n1k3bs03bs13LEN2Kb2GT2k'2K12K2S2su4SUhi1n1k3bs03bs13LEN2Kb2GT". (* [comment removed for export] *)
  #[using="IMG K_halted K_mat bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22 SUlo SUhi Flo Fhi FD Hfd FRCS Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd D HK"] Lemma loop2 : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pn,$4.Pregs,(18.&5.(3.&40.))Pm,P,(3.&40.)(9.(3.&8.))Pmo,$0.Pk,$4.Pb0,(3.&40.)Pbs0,(1.(3.&8.))Pb1,(3.&40.)Pbs1,(1.(3.&8.))P,(32.(39.(33.(3.&8.)R3.)(33.(3.&8.)R1.))R9.)P,(2>.R9.)P,(1=.R9.)P,(1>.R9.)P,Pz,$2;.P,(7.(13.(15.&40.R9.)R1.)(16.R1.(27.(15.&40.R9.)(28.(33.(3.&8.)R8.)))))(34.VAL,VCS,R2.)P,Pz,$2;.P,(7.(13.(15.&40.R8.)R1.)(16.R1.(27.(15.&40.R8.)(28.(33.(3.&8.)R7.)))))(34.VAL,VCS,R2.)P,(8.(3.&40.)(19.R>.(1:.&5.+:.$1;.))(1<.&40.(28.R;.)))P,(8.(3.&40.)(19.R?.(1:.&5.+16.$1;.))(1<.&40.(27.(28.(33.(3.&8.)R:.))(28.(33.(3.&8.)R8.)))))P,(8.(3.&40.)(19.R10.(1:.&5.+12.$1;.))(1<.&40.+2.))P,(8.(3.&40.)(19.R11.(1:.&5.+13.$1;.))(1<.&40.(14.Vsu,+68.)))P,(7.(32.#1.R?.)(35.R?.(39.(33.(3.&8.)R=.)(33.(3.&8.)R;.))))P,(8.(9.(1.(3.&8.)))(26.$20.R12.(1<.&40.(14.Vsu,+68.))#8.)(;.(1.(3.&8.))(2=.#8.R?.)))P,(8.(9.(1.(3.&8.)))(26.$20.R13.(1<.&40.(14.Vsu,+60.))#8.)(;.(1.(3.&8.))(2=.#8.(1<.&40.(28.(33.(3.&8.)R?.))))))P,(8.(9.(1.(3.&8.)))(26.$20.R14.(1<.&40.(14.Vsu,+58.))#8.)(;.(1.(3.&8.))(2=.#8.R?.)))P,(8.(9.(1.(3.&8.)))(26.$20.R15.(1<.&40.(14.Vsu,+50.))#8.)(;.(1.(3.&8.))(2=.#8.(1<.&40.(28.(33.(3.&8.)R?.))))))P,(8.(9.(1.(3.&8.)))(26.$20.Vmem1,R13.(33.(3.&8.)R12.))(;.(1.(3.&8.))R12.))P,(8.(9.(1.(3.&8.)))(26.$20.Vmem1,R12.(33.(3.&8.)R11.))(;.(1.(3.&8.))R11.))P,(2:.(13.(27.(15.&40.R15.)(28.(33.(3.&8.)R14.)))(14.Vsu,+70.))(13.Vsu,(15.&40.R15.)))P,(13.(27.(15.&40.R16.)(28.(33.(3.&8.)R15.)))(29.+2.+40.))P,(13.(27.(15.&40.R17.)(28.(33.(3.&8.)R16.)))+800000000000.)P,(2:.(13.(27.(15.&40.R16.)(28.(33.(3.&8.)R15.)))(14.Vsu,+70.))(13.Vsu,(15.&40.R16.)))P,(13.(27.(15.&40.R17.)(28.(33.(3.&8.)R16.)))(29.+2.+40.))P,(13.(27.(15.&40.R18.)(28.(33.(3.&8.)R17.)))+800000000000.)P,(13.(27.(28.(33.(3.&8.)R1:.))(28.(33.(3.&8.)R18.)))(29.+2.+1>.))(1?.$20.(21.(22.$23.R20.(1:.&40.+>67=8.$1;.)R1?.(25.$20.))R1>.)(2?.(36.(3.&8.)$31.(37.(1<.&40.Vfd,))(38.(3.&8.)R1=.(3:.(3.&8.)R1;.R19.)))VKK,))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros regs m mo k b0 bs0 b1 bs1 LEN RIr LMm KMmo AOK0 AOK1 Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 TS0 DISJ1 NW1 TS1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    ddestruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      ddestruct (sw_retry_a regs (restrict D m) (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { rres ltac:(eapply LM_store_ok; [exact LMm | exact SOK1]). }
      { rres ltac:(exact Mb0). }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rres ltac:(exact Mn0). }
      { rres ltac:(eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]). }
      rrunK RUN KMmo KM1.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (rz_writev2_wallA RSEGS AL CS K K_halted K_mat regs1 (0x0e67c8 : word) m' _ W_e3418 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 KK);
        [ exact F_e3418 | exact E_e3418 | exact (KM_K _ KM1) | exact (KM_fds _ KM1) | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | 
        | u_norm; intros z Hz; left; apply FRCS; lia
        | intros z Hz; apply AOK0; destruct (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as [Eat|[Eat Ewr]]; unfold at_ in Eat; rewrite Eat in Hz; rewrite u64_lit in Hz by lia; lia
        | u_norm; intros z Hz; apply AOK1; lia
        | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2 mo2 HK2 MM2. pose proof (KM_step _ _ KM1 HK2 MM2) as KM2. clear HK2 MM2.
        rewrite pc_e341c. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * ddestruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) (restrict D m') (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          rrunK RUN2 KM2 KM3.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil; [| exact LMm' | exact KM3].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * ddestruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) (restrict D m') (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          rrunK RUN2 KM2 KM3.
          apply (IH regs2 m' _ k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact KM3.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. intros z Hz. apply AOK0. lia.
          -- intros z Hz; apply AOK1; lia.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- exact TS1.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      ddestruct (sw_retry_b regs (restrict D m) (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { rres ltac:(eapply LM_store_ok; [exact LMm | exact SOK1]). }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rres ltac:(exact Mn0). }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. rres ltac:(exact Mb1). }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. rres ltac:(exact Mn1). }
      { rres ltac:(eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]). }
      rrunK RUN KMmo KM1.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (rz_writev1_wallA RSEGS AL CS K K_halted K_mat regs1 (0x0e67c8 : word) m' _ W_e3418 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) KK);
        [ exact F_e3418 | exact E_e3418 | exact (KM_K _ KM1) | exact (KM_fds _ KM1) | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | 
        | u_norm; intros z Hz; left; apply FRCS; lia
        | intros z Hz; apply AOK1; destruct (u_at_le b1 (Z.of_nat (k - length bs0)) ltac:(lia) ltac:(lia)) as [Eat|[Eat Ewr]]; unfold at_ in Eat; rewrite Eat in Hz; rewrite u64_lit in Hz by lia; lia
        | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2 mo2 HK2 MM2. pose proof (KM_step _ _ KM1 HK2 MM2) as KM2. clear HK2 MM2.
        rewrite pc_e341c. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * ddestruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) (restrict D m') (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          rrunK RUN2 KM2 KM3.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil; [| exact LMm' | exact KM3].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * ddestruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) (restrict D m') (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          rrunK RUN2 KM2 KM3.
          apply (loop1 (length bs1) regs2 m' _ k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact KM3.
          -- pose proof (u_at_le b1 (Z.of_nat (k - length bs0)) ltac:(lia) ltac:(lia)). rewrite length_skipn. intros z Hz. apply AOK1. lia.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].

Local Ltac2 Set LiaOrc.tbl := fun () => "00k0?L11033083325.30L12048755517.30L13485029350.30L1448611046.30 L15226970637.30L19496125542.30L19621252237.30L19800062943.25L19802301230.30L20081829821.30L22028604802.25L22034910579.30L23055219749.25L23555425853.30L23602795581.30L25525607142.30L26796291725.30L27108199053.30L28045517811.30L28047801090.25L28339167839.25L28341353134.30L28466216461.30L30301955978.30L31536476006.30L31623024829.30L32020620566.25L32948137878.25L34301897727.30L37003138445.30L37306689933.30L37562285542.30L40071868518.30L41052754966.25L43572859494.30L44147497277.30L44489560973.30L46080870118.30L47622961597.30L48888069133.30L5020091149.30 L5224515210.30 L55622120806.30L55684762173.30L57591360046.30L57593410271.25L59168352957.30L60192935997.30L61632695270.30L6390952077.30 L64140476006.30L65923238410.30L66269922573.30L66565085453.30L67197232445.30L68209233085.30L7457644902.30 L9992057474.25 L9998264947.30 00000900B00K00T00]00f00o01601=01F01M01T01_01h02102:02C02L02S02Z02a02h03103803A03J03Q03X03l04504>04G04P04W04`04i05205;05D05M05V05]05f05o06606=06F06O06X06a06j07107:07C07L07U07^07e07lS2su4SUhiS2su4SUhiS2su4SUloS2su4SUloS2su4SUhiS2su4SUloS2su4SUhiS1f3FhiS1f3FhiS2su4SUhiS1f3FloS1f3FloS1f3Flo3FhiS2su4SUhiS2su4SUhiS2su4SUloS2su4SUhiS2su4SUhiS1f3FloS1f3FloS1f3FhiS1f3FhiS2su4SUhiS1f3FhiS2su4SUloS2su4SUhiS1f3FhiS1f3FhiS1f1x3Hx33Hx22su3Hx1S2su4SUhiS2su4SUhiS2su4SUloS2su4SUloS1f3FhiS2su4SUloS2su4SUhiS2su4SUhiS2su4SUloS2su4SUhiS2su4SUhiS2su4SUhiS1f3FhiS2su4SUloS2su4SUhiS1f3FhiS1f3FhiS2su4SUhiS2su4SUhiS2su4SUloS2su4SUhiS2su4SUloS1f3FhiS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUhiS2su4SUloS1f3FloS1f3Flo". (* [comment removed for export] *)
Lemma sw_post_of_LMA : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pmem,P,(3.&40.)(9.(3.&8.))Pm,P,(3.&40.)(9.(3.&8.))Psu,$2;.Pf,$2;.Pra,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Pcan,(3.&40.)Pwb,$2;.Pn,$2;.Ps,(3.&40.)Pl,(3.&40.)Pbufp,(3.&40.)Pbufsz,(3.&40.)P,(13.(27.+100000000.+70.)R11.)P,(13.R12.+800000000000.)P,(13.+?:360.R12.)P,(13.(27.R13.+>8.)+?;358.)P,(3;.R15.(3<.R17.R15.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R16.)(3=.R18.R16.R15.R7.R6.(24.R17.R15.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
  constructor.
  - intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
    unfold mem_sw2. do 3 wout1.
    rewrite (E x) by lia.
    unfold mem_sw1. do 13 wout1. reflexivity.
  - unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    eapply mem_grows_trans; [|exact G].
    unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
    apply mem_grows_refl.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
  - unfold mem_sw2. rdn_solve.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Thm.
  Variable AL : asan_layout.
  Variable CS : Z -> Prop.
  Variable K : Model -> Prop.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis K_halted : forall mo, K mo -> m_halted mo = None.
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pmo,$0.Pacc,(1.(2.(3.&40.)$4.))P,A1.VK,R2.P,(5.VAL,VCS,R2.)(6.$0.Lmo',$0.(7.(8.(9.$0.)(:.R5.R4.)(;.$0.R1.))(7.A1.VK,R1.(<.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pmo,$0.Pmo',$0.P,A1.VK,R2.P,(8.$=.(>.R2.)(>.R3.))P,(8.(1.(2.(3.&40.)(3.&40.)))(?.R3.)(?.R4.))P,(8.(1.(3.&40.))(10.R4.)(10.R5.))P,(8.(9.(3.&40.))(11.R5.)(11.R6.))A1.VK,R6.")
(* [comment removed for export] *).
  Variable su : Z.
  Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
  Hypothesis SUhi : (su <= 0x800000000000)%Z.
  Hypothesis FRCS : forall z, (su - 112 <= z < su)%Z -> CS z.

  Let D : word -> bool := Dimg [(su - 112, su)%Z].
  #[using="Type"] Lemma T_Dseg : forall a : word, segcov RSEGS (bv_unsigned a) = true -> D a = true.
  Proof. intros a H. unfold D. apply Dimg_Dseg. exact H. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L30813421528.16000009S2su1z2Hz". (* [comment removed for export] *)
  #[using="IMG FRCS"] Lemma T_DOK : forall a, D a = true -> aok_addr AL CS (bv_unsigned a).
  Proof.
    intros a H. unfold D in H. eapply (Dimg_DOK AL CS IMG [(su - 112, su)%Z]); [|exact H].
    constructor; [|constructor]. cbn. intros z Hz. apply FRCS. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L58121287578.12000009S2su4SUlo". (* [comment removed for export] *)
  #[using="SUlo"] Lemma T_D0 : D (Z_to_bv 64 0) = false.
  Proof. unfold D. apply Dimg_D0. constructor; [cbn; lia|constructor]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L28139165318.18L30813421528.18L58119383268.1800000900P00YS2su4SUhiS2su2lo2hi3Hlo3Hhi1z2HzS2su4SUlo". (* [comment removed for export] *)
  #[using="SUlo SUhi"] Lemma T_frame : forall lo hi, (su - 112 <= lo)%Z -> (hi <= su)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_cov [(su - 112, su)%Z] (su - 112) su); [left; reflexivity | lia | lia | lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40646207469.1800000DS2lo2hi3Hlo3Hhi1z2Hz". (* [comment removed for export] *)
  #[using="Type"] Lemma T_img : forall lo hi, (0x10000 <= lo)%Z -> (hi <= 0x65f000)%Z -> DcovZ D lo hi.
  Proof. intros lo hi Hlo Hhi z Hz. unfold D. apply (Dimg_img [(su - 112, su)%Z]). unfold AIMG_LO, AIMG_HI. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition rrunT := rz_smsteps_RK RSEGS D AL CS K K_halted K_mat T_Dseg asegs_top T_DOK T_D0.

  Ltac rres T := first
    [ eapply (rdn_restrictD RSEGS D); [T | u_norm; lia | first [apply T_frame; u_norm; lia | apply T_img; u_norm; lia]]
    | eapply (store_ok_restrictD RSEGS D); [T | u_norm; lia | apply T_frame; u_norm; lia] ].
  Ltac dz := first [lia | apply T_frame; lia | apply T_img; lia].
  Ltac solve_outside := intros xx Hxx; repeat (rewrite (wbytes_agree_outD_Z D) by (first [exact Hxx | dz])); reflexivity.
  Ltac push_restrict_in H := repeat (rewrite (wbytes_restrict_Z D) in H by dz).
  Ltac rrunK RUN KMH KMnew :=
    push_restrict_in RUN;
    eapply rrunT; [exact (KM_K _ _ _ KMH) | exact RUN | solve_outside | ];
    clear RUN;
    let mo1 := fresh "mo" in let HK1 := fresh "HKm" in let MM1 := fresh "MM" in
    intros mo1 HK1 MM1; pose proof (KM_step _ _ _ _ KMH HK1 MM1) as KMnew; clear HK1 MM1.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L13499376572.26L1753866288.26 L19802178785.26L22034803388.26L28646861153.26L30199515520.26L30301831237.26L32769736517.26L33794056645.26L36227160832.26L37879813936.26L41626253842.26L41810355525.26L43890696880.26L49791655442.26L50775506304.26L52235316882.26L5224374597.26 L57591205345.26L58141874620.26L5837345810.26 L58436926256.26L6130943872.26 L61954742576.26L62811904640.26L6565273825.26 L65707013394.26L68099521249.26L7490654268.26 L9998372284.26 00000700800?00F00M00T00[00b00i01001101801?01@01G01N01U01\01c01j02102202902:02A02H02O02V02]02dS1f3FloFS1f3FhiS1f3FloS1f3FhiS1f3FloS1f3FhiS1f3FhiS1f3FhiS1f3FloFS1f3FhiS1f3FhiFS1f3FhiS1f3FloS1f3FhiS1f3FhiS1f3FhiS1f3FloS1f3FhiFS1f3FloFS1f3FloS1f3FhiS1f3FhiS1f3FhiS1f3FloS1f3Flo". (* [comment removed for export] *)
  #[using="Type"] Lemma sw_file_restrict : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pmem,P,(3.&40.)(9.(3.&8.))Pf,$2;.Pwb,$2;.Pwp,$2;.Pfd,$2;.Pbufp,(3.&40.)Pbufsz,(3.&40.)P,(13.+?:360.R6.)P,(13.(27.R7.+>8.)+?;358.)P,(3>.R9.R8.R7.R6.R5.R4.R3.)(3>.(3?.VD,R:.)R9.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros mem f wb wp fd bufp bufsz Flo Fhi [A1 A2 A3 A4 A5]. constructor; rres ltac:(eassumption).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L1266586792.16 L14499528620.16L26277486856.16L31731642280.16L4295302040.16 L44353294903.16L44510601388.16L46477766871.16L47762692104.16L60068125336.16L61064426295.16L6972668375.16 00000100200300400500600700800900:00;00<SSSSFSSSSFSS". (* [comment removed for export] *)
  #[using="Type"] Lemma ssp_cells_restrict : forall mem can, ssp_cells mem can -> ssp_cells (restrict D mem) can.
  Proof. intros mem can [A1 A2]. split; rres ltac:(eassumption). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "07a0@L10451225604.118L10753966476.86 L10753966476.88 L11032983989.86 L11034810620.113L11034810620.116L11035180477.115L11035180477.118L11528582293.133L11558054968.113L11558054968.116L11558406521.115L11558406521.118L11903295040.133L12046658365.115L12046658365.118L12047076988.113L12047076988.116L12048920373.86 L12317367689.93 L12327803049.96 L12513727273.115L12513727273.118L12514162280.113L12514162280.116L1254622550.131 L1254622550.133 L1256872595.86  L12997348297.116L13280524840.118L13371222056.118L13417078888.113L13417078888.116L13417497897.115L13417497897.118L13485192174.88 L13487069094.82 L13819258665.115L13819258665.118L13819675240.113L13819675240.116L14007137273.115L14007137273.118L14007228088.113L14007228088.116L1448773870.88  L1450797864.77  L14901945081.115L14901945081.118L14902298552.113L14902298552.116L15043608204.86 L15043608204.88 L15227135493.88 L15229011777.73 L15482658610.79 L15482806602.115L15482806602.118L15483159563.113L15483159563.116L16075492727.122L16392498057.116L16397784372.80 L16601853929.116L16601853929.118L16699243275.113L16699243275.116L16699399754.115L16699399754.118L16896685374.133L17259695690.115L17259695690.118L17259866891.113L17259866891.116L17315663288.113L17315663288.116L17316096249.115L17316096249.118L17883224395.131L17883224395.133L1794551837.131 L1794551837.133 L18254759366.93 L18269782246.96 L18338279555.113L18338279555.116L18338371010.115L18338371010.118L18565594373.118L1870194232.82  L19255261340.118L19255376538.133L19496026222.88 L19498148524.74 L19621349509.88 L19623439297.78 L20079732669.115L20079732669.118L20080149244.113L20080149244.116L20081992629.86 L20140458629.93 L2106008076.86  L2106008076.88  L21313116166.133L21348632588.86 L21348632588.88 L21528774299.133L21967985810.96 L21970000306.93 L22157545465.115L22157545465.118L22157978296.113L22157978296.116L23057138836.69 L23059235098.70 L23059235224.71 L23059235358.72 L23059235476.74 L23059235484.73 L23059235610.75 L23059235736.76 L23059235870.77 L23059236122.79 L23061332120.78 L23061340758.84 L23061341002.83 L23061342530.82 L23061839391.68 L23555326517.86 L23557523005.115L23557523005.118L23557694332.113L23557694332.116L23602696245.86 L23604539772.113L23604539772.116L23604892733.115L23604892733.118L23937426232.113L23937426232.116L23937844857.115L23937844857.118L24363749123.113L24363749123.116L24364182082.115L24364182082.118L2438423736.76  L24834718264.113L24834718264.116L24834809721.115L24834809721.118L24998566707.70 L25085231024.133L25168608360.113L25168608360.116L25168763177.115L25168763177.118L25229160586.85 L25229160586.87 L25483190712.113L25483190712.116L25483281657.115L25483281657.118L25523437482.73 L25525706478.88 L25638372620.86 L25638372620.88 L26793766726.118L26794235463.79 L26796126853.88 L26873674627.113L26873674627.116L26873765570.115L26873765570.118L27066001620.118L27108101765.88 L27110353991.74 L27232730064.116L27356147980.86 L27356147980.88 L27626075660.86 L27626075660.88 L27678444970.133L28059454282.115L28059454282.118L28059889163.113L28059889163.116L28385701599.96 L28425419721.118L28461931073.80 L28466051589.88 L2896845708.86  L2896845708.88  L29665922209.133L30391459203.113L30391459203.116L30391826626.115L30391826626.118L30813421528.116L30813421528.118L30813421528.120L31534418214.76 L31536638830.88 L31620927677.115L31620927677.118L31621363196.113L31621363196.116L31623189685.86 L31643174668.122L32377906728.114L32377906728.116L32899143171.113L32899143171.116L32899576642.115L32899576642.118L3357332016.75  L33654464268.86 L33654464268.88 L34036561206.72 L34968463928.71 L35058197836.124L35486830865.131L35486830865.133L35862950177.131L3594750227.131 L36400303426.115L36400303426.118L36400670723.113L36400670723.116L3690547161.131 L3690547161.133 L36986514024.113L36986514024.116L36986933033.115L36986933033.118L37003039109.88 L37004872774.114L37004872774.116L37005194307.81 L37304634435.72 L37306527109.88 L37560228782.75 L37562120686.88 L37820196363.113L37820196363.116L37820351306.115L37820351306.118L3802989615.96  L38307110667.113L38307110667.116L38307543626.115L38307543626.118L38327674650.133L38910149058.115L38910149058.118L38910518403.113L38910518403.116L39229384489.115L39229384489.118L39229735528.113L39229735528.116L39432119625.122L40069845164.79 L40070195629.118L40072033390.88 L40080998986.115L40080998986.118L40081106699.113L40081106699.116L40685447784.113L40685447784.116L40685539113.115L40685539113.118L40755790193.131L40755790193.133L41368749068.86 L41368749068.88 L41991731940.131L42301405714.122L42301405714.124L42301585938.122L42301585938.124L42428212162.115L42428212162.118L42428368515.113L42428368515.116L42478870209.131L42478870209.133L42498413689.115L42498413689.118L42498584888.113L42498584888.116L43119389046.93 L43133889622.96 L4337688781.113 L43418818933.124L43573024366.88 L43585357997.70 L437925327.118  L438073289.133  L44145310844.113L44145310844.116L44145400125.115L44145400125.118L44147662133.86 L44336070248.113L44336070248.116L44336159529.115L44336159529.118L44489660293.88 L44491716045.76 L44589887818.115L44589887818.118L44589978635.113L44589978635.116L44935697986.115L44935697986.118L44936131331.113L44936131331.116L45381988473.115L45381988473.118L45382145336.113L45382145336.116L46022637752.113L46022637752.116L46022991353.115L46022991353.118L46076732074.80 L46080770798.88 L4685674552.131 L46949767321.133L47079107252.78 L47623060917.86 L47624887548.113L47624887548.116L47625058749.115L47625058749.118L47661233521.93 L48015335606.77 L481743678.133  L48371818922.131L48438646019.113L48438646019.116L48438816834.115L48438816834.118L48886045635.77 L48888166405.88 L49245793925.118L49660183656.113L49660183656.116L49660354857.115L49660354857.118L49817047736.97 L49819296274.116L49820552522.115L49820552522.118L49820985355.113L49820985355.116L5018084677.75  L5020190469.88  L50946827458.115L50946827458.118L50946916739.113L50946916739.116L51116099283.120L51116099283.135L5170034310.131 L5170034310.133 L51927948970.133L51967136041.115L51967136041.118L51967243368.113L51967243368.116L52195914368.96 L53953412492.86 L53953412492.88 L54517788264.113L54517788264.116L54517943081.115L54517943081.118L54912981537.131L54912981537.133L55015189288.93 L55026019848.96 L55622021486.88 L55624290472.72 L55684664885.86 L55686859325.115L55686859325.118L55687032700.113L55687032700.116L55970264938.131L56974105603.113L56974105603.116L56974211394.115L56974211394.118L57324473979.131L57615822347.113L57615822347.116L57615911754.115L57615911754.118L58117256717.96 L58131591981.93 L58243082892.86 L58243082892.88 L59166150652.113L59166150652.116L59166255805.115L59166255805.118L59168517813.86 L60192838709.86 L60194682236.113L60194682236.116L60195033149.115L60195033149.118L60423849022.93 L61285582255.118L61632752550.71 L61632860142.88 L62119007538.74 L62617226022.133L62982793859.113L62982793859.116L62983212994.115L62983212994.118L63053070388.73 L63405383435.113L63405383435.116L63405816394.115L63405816394.118L63426218685.133L63551916877.131L6378023494.70  L63790716683.113L63790716683.116L63791149642.115L63791149642.118L6390854789.88  L64026413559.114L64140573294.88 L64142481706.78 L64559369415.131L64559369415.133L64912887836.114L64912887836.116L65503296377.133L65922870997.133L66100072588.86 L66100072588.88 L66267882829.82 L66269757701.88 L66362623838.81 L66564922629.88 L66565175629.71 L66737158717.133L66737158717.135L67137529884.118L67197395253.86 L67199221884.113L67199221884.116L67199329597.115L67199329597.118L67305707640.118L67656267880.113L67656267880.116L67656621353.115L67656621353.118L6785935912.118 L68209133749.86 L68210977276.113L68210977276.116L68211330237.115L68211330237.118L6903871225.115 L6903871225.118 L6904222648.113 L6904222648.116 L7204885072.133 L74113128.113   L74113128.116   L74204457.115   L74204457.118   L7457482094.88  L7459815592.81  L7459846317.114 L7459846317.116 L7682958859.113 L7682958859.116 L7683310410.115 L7683310410.118 L8674428984.113 L8674428984.116 L8674864505.115 L8674864505.118 L8929243807.124 L934489398.81   00000I00J00k01B01Q01h02702N02O02Y02k03503G03a04004G04V04m05D05N05`05a05b05c05d06D06h07D07b08408F08G08H08I08J08a09809909:09;09<09F09X09b0:40:K0:b0:l0;>0;H0;Z0;[0<<0<S0<j0=A0=U0>10>E0>a0?@0?A0?X0?k0@B0@V0A20AF0Ab0BX0Bl0CH0C\0D80DB0DT0D^0E00EX0FR0FS0FT0Fc0G:0GD0GV0G`0H20HP0Hg0IE0Ik0JB0JY0K00KG0KV0Km0L<0LS0Lj0Lk0Ll0MM0MN0MO0N00NR0Nd0Nn0O80OJ0OT0Of0PB0P^0Q:0QV0R20RN0Rj0SF0Sb0T>0TZ0U@0Uf0VL0Vh0W?0WN0We0X40XK0Xb0Y10YH0YW0Yn0Z80ZJ0ZT0Zf0[00[B0[L0[^0\50\?0\Q0\[0\m0]D0]m0]n0]o0^00^10^20_40_>0_P0_Z0_l0`C0`Z0`[0a<0aS0aj0bA0bK0b]0bg0c90cS0cj0dA0dS0dT0e50e60eW0eX0el0fH0f\0g80g]0hA0hX0ho0i00iQ0iR0i\0in0j80jJ0jS0jf0k=0kT0kk0l:0lQ0l`0m70mN0md0mh0n60n@0nR0n\0nn0oE0oF0og10>10U11A11a12E12d13:13D13V13`14214314414514614714814O14X14k15B15Y16016G16^17217N17b18>18?18S18o19C19_19`19j1:<1:F1:X1:Y1:Z1:[1:\1;21;I1;`1<71<K1<g1=;1=W1=X1=Y1=Z1=[1=\1=]1=^1>?1>@1>b1?@1?_1@:1@D1@V1@`1A21A31A41A>1AP1AZ1Al1B;1BR1BS1CG1C^1D51DN1Do1E>1EU1Ed1F;1FR1FS1FT1FU1FV1Fm1GD1GX1H41HH1Hd1Hn1I@1IJ1I\1If1J81JB1JT1J^1K01K:1KL1Kc1L:1LM1Lh1M?1MV1Me1N<1NK1Nb1O51OL1P21P31P=1PO1PY1Pk1QB1QY1R;1R<1R=1R>1R?1S21S31SG1Sc1T71TS1Tj1UA1UK1U]1Ug1V91VS1W:1W;1W<1W=1W>1W?1W@1WA1W^1W_1X@1XA1XB1XC1XD1XE1XF1XG1XH1X_1Y61YM1Y\1Z31ZB1ZY1ZZ1Zd1[61[@1[R1[S1[g1\C1\W1]31]J1]Y1]Z1^;1^J1^a1_01_G1_^1`51`D1`[1`j1aA1a[1b41bK1bb1c91cP1cZ1cl1d61dH1d_1e31eO1ec1f?1f@1fV1fm1gA1g]1h11hM1hd1i:1iQ1ih1ii1ij1j31jF1jl1kT1kU1l61lM1ld1m@1mW1mn1nO1o41oK1ob20120H20W20n21S21T21U21V21W21i22@22O22f23523L23V23h24224D24E24F24G24H24I24`25725@25S25g26C26W27327=27O27Y27k28X28oS2wb2wp7pending5extra3WBPFS2su1s1l7pending5extra4LENE5DISJES2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraFS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS7pending5extra1k2K12K22EKS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraFFFFS1s1l2x06extra'4LENE3TSE1k2K12K2S1s1l7pending5extra4LENE3TSE1k2K12K2S1s1l7pending5extra4LENE3TSES2wp1l2x06extra'4LENP4LENE3M30S2su7pending5extraS2su7pending5extraFFFFS2su4SUlo7pending5extraS2su4SUlo7pending5extraFFFFS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraFS2su1s1l7pending5extra4LENE5DISJES2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2wp2x06extra'4LENP3M301k2K12K2SS2su4SUhi7pending5extraS1s1l2x06extra'3TSES1s1l7pending5extra3TSES2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su2wb2wp7pending5extra3WBP4LENP5DISJP3NEQ1k2K12K22NKS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su1s1l2x06extra'4LENE5DISJE1k2K12K22NKS2su2wb2wp1s1l7pending5extra3WBP4LENE5DISJE3NEQ1k2K12K22NKFFS2su4SUhi5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2wb2wp7pending5extra4LENP3M30S2su4SUhi7pending5extraS2wb2wp7pending5extra4LENP3TSPS2wb2wp7pending5extra4LENP3TSP1k2K12K2S2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraFFS2su1s1l7pending5extra4LENE5DISJEFFS2su1s1l7pending5extra4LENE5DISJES2wb2wp7pending5extra4LENP1k2K12K2S2su7pending5extraS2su5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi1f7pending5extra3Flo3FhiS2su4SUlo4SUhi1f7pending5extra3Flo3FhiS2su4SUlo4SUhi1f7pending5extra3Flo3FhiS2su4SUlo4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUhi7pending5extraS2wb2wp1l7pending5extra4LENP4LENE1k2K12K2FFFFFS2su4SUlo4SUhi2wb2wp1s1l7pending5extra3WBP4LENP4LENE5DISJP3TSP3TSES2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUlo7pending5extraS2su4SUlo7pending5extraFS2su1s1l7pending5extra4LENE5DISJES2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2wb2wp7pending5extra4LENPS2su4SUhi7pending5extraS2su4SUhi7pending5extraS1l2x06extra'4LENEFS2su1s1l7pending5extra4LENE5DISJEFS2su1s1l7pending5extra4LENE5DISJEFS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2wb2wp1l7pending5extra4LENP4LENE3M30S2wb2wp1l7pending5extra3WBP4LENE3NEQS2su4SUhi7pending5extraS2su4SUhi7pending5extraFS2su1s1l7pending5extra4LENE5DISJEFS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su1z2HzS2su2x06extra'1z2HzS2su7pending5extra1z2HzS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2x06extra'1k2K12K22NKS2suS2su2x06extra'S2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUhi7pending5extraFS2su1s1l7pending5extra4LENE5DISJES2su4SUhi7pending5extraS2su4SUhi7pending5extraS2wb2wp1l7pending5extra4LENP4LENE1k2K12K22EKS1s1l2x06extra'4LENE3TSE1k2K12K2S1s1l7pending5extra4LENE3TSE1k2K12K2S2wp2x06extra'4LENP3M301k2K12K2S2x06extra'1k2K12K22NKS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraFFFFFFS2su4SUhi7pending5extraS2su4SUhiS2su4SUhi2x06extra'S2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraFS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraFS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraFFFFS2x06extra'1k2K12K22EKS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraFFFFFFFS2su1s1l7pending5extra4LENE5DISJEFS2wp2x06extra'4LENP3M301k2K12K22EKS7pending5extra3M301k2K12K22EKS2wp2x06extra'4LENP3M301k2K12K2S7pending5extra3M301k2K12K2S2su5extraS2su7pending5extraS2su5extraS2su7pending5extraFFS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraFS2wb2wp1l7pending5extra3WBP4LENP4LENE3NEQ1k2K12K22NKS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2wb2wp7pending5extra3WBPS2wb2wp7pending5extra3WBP1k2K12K2S2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraFFFFS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2x06extra'1k2K12K2S7pending5extra3M301k2K12K2S2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2wp5extra3WBP4WPhiS2su4SUhi7pending5extraS2wb2wp7pending5extra4LENP3TSP1k2K12K2FS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2wb2wp7pending5extra3WBP4LENP3M30FFFFS4regs3mem2mo2wb2wp2fd2p08pending'5extra2KK4LENP2EQFS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2wb2wp7pending5extra1z2HzS2wb2wp7pending5extra4LENP1k2K12K21z2HzFFFFFFFS2wb2wp7pending5extra3WBP3NEQFS2su1s1l7pending5extra4LENE5DISJEFFFFFFFFS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraFS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraFS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo7pending5extraS2su4SUlo5extraFS2su1s1l7pending5extra4LENE5DISJES2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2wp1l5extra4LENP4LENE3M30S2wb2wp7pending5extra3TSPS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUhi7pending5extraS7pending5extra1k2K12K2S2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2su4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraFS2x06extra'1k2K12K22EKS2su4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUhi7pending5extraS2wp1s1l4LENP4LENE3TSES2su4SUlo7pending5extraS2su4SUlo7pending5extraFFS2su4SUhiS2su4SUhi2x06extra'S2wb2wp7pending5extra4LENP3TSP1k2K12K2S2wb2wp7pending5extra3WBP3NEQ1k2K12K22NKFS2su1s1l7pending5extra4LENE5DISJES2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUlo4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi7pending5extraS1s1l2x06extra'4LENE1k2K12K21z2HzS1s1l7pending5extra4LENE1k2K12K21z2HzS2su4SUhi7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2wb2wp1l7pending5extra4LENP4LENE3M30FFFFS2su7pending5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su4SUhi5extraS2su4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraFFFFFS2su4SUlo7pending5extraS2su4SUlo7pending5extraS2su4SUloS2su4SUlo2x06extra'S2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su4SUlo4SUhi5extraS2su4SUlo4SUhi7pending5extraS2su5extraS2su7pending5extraS2su5extraS2su7pending5extraS2wb2wp1l7pending5extra4LENP4LENE3M301k2K12K2S2su4SUhi7pending5extra". (* [comment removed for export] *)
#[using="IMG K_halted K_mat K_vmonly SUlo SUhi FRCS D"] Theorem ref_stdio_writeA : ltac2:(CDefT.buildp (gd_tbl_A_stdio_write ()) "Pregs,(18.&5.(3.&40.))Pmem,P,(3.&40.)(9.(3.&8.))Pmo,$0.Pf,$2;.Pwb,$2;.Pwp,$2;.Pfd,$2;.Ps,(3.&40.)Pl,(3.&40.)Pbufp,(3.&40.)Pbufsz,(3.&40.)Pcan,(3.&40.)Pret,(3.&40.)Ppending,(1.(3.&8.))Pextra,(1.(3.&8.))PKK,$40.P,(8.(3.&40.)(19.R10.(1:.&5.+2.$1;.))(1<.&40.Vsu,))P,(8.(3.&40.)(19.R11.(1:.&5.+:.$1;.))(1<.&40.R>.))P,(8.(3.&40.)(19.R12.(1:.&5.+;.$1;.))R;.)P,(8.(3.&40.)(19.R13.(1:.&5.+<.$1;.))R;.)P,(8.(3.&40.)(19.R14.(1:.&5.+1.$1;.))R8.)P,(8.$41.(42.$20.R14.(1<.&40.(14.Vsu,+70.))#70.)$43.)P,(13.+?:360.R13.)P,(13.(27.R14.+>8.)+?;358.)P,(3>.R17.R15.R14.R13.R12.R?.R>.)P,(44.R18.R>.)P,(7.(16.=R14.)(16.R14.+80000000.))P,(8.(9.$45.)(46.(47.R19.)(1<.&40.R15.))(;.$45.(48.(1<.&40.R15.))))P,A1.VK,R1:.P,Pz,$2;.P,(7.(13.R1:.R1.)(16.R1.R19.))(34.VAL,VCS,R2.)P,Pz,$2;.P,(7.(13.(15.&40.R18.)R1.)(16.R1.(27.(15.&40.R18.)(15.&40.R17.))))(34.VAL,VCS,R2.)P,(7.(13.=R1;.)(13.R1;.R1:.))P,(16.R1;.(29.+2.+40.))P,(8.$2;.(14.R1<.R1=.)(28.(33.(3.&8.)R14.)))P,(8.$2;.(15.&40.R1:.)(28.(33.(3.&8.)R14.)))P,(13.(27.(28.(33.(3.&8.)R16.))(28.(33.(3.&8.)R15.)))(29.+2.+1>.))P,(2:.(13.R1?.(14.Vsu,+70.))(13.Vsu,R20.))P,(2:.(13.(27.(15.&40.R1>.)(15.&40.R1=.))(14.Vsu,+70.))(13.Vsu,(15.&40.R1>.)))P,(13.(27.(15.&40.R1?.)(15.&40.R1>.))(29.+2.+40.))P,(13.R22.+800000000000.)P,(13.(27.(15.&40.R21.)(15.&40.R20.))+800000000000.)P,(8.(9.(1.(3.&8.)))(26.$20.R28.(1<.&40.R25.)(33.(3.&8.)R1<.))(;.(1.(3.&8.))R1<.))P,(8.(9.(1.(3.&8.)))(26.$20.R29.R23.(33.(3.&8.)R1<.))(;.(1.(3.&8.))R1<.))P,(49.R1?.)P,A1.R1=.(30.$31.)P,Pregs',(18.&5.(3.&40.))Pmem',P,(3.&40.)(9.(3.&8.))Pmo',$0.P,(8.(3.&40.)(19.R3.(1:.&5.+:.$1;.))R28.)P,(8.(3.&40.)(19.R4.(1:.&5.+2.$1;.))(1<.&40.Vsu,))P,(8.(3.&40.)(19.R5.(1:.&5.+1.$1;.))R26.)P,(8.(3.&40.)(19.R6.(1:.&5.+8.$1;.))(19.R33.(1:.&5.+8.$1;.)))P,(8.(3.&40.)(19.R7.(1:.&5.+9.$1;.))(19.R34.(1:.&5.+9.$1;.)))P,(8.(3.&40.)(19.R8.(1:.&5.+12.$1;.))(19.R35.(1:.&5.+12.$1;.)))P,(8.(3.&40.)(19.R9.(1:.&5.+13.$1;.))(19.R36.(1:.&5.+13.$1;.)))P,(8.(3.&40.)(19.R:.(1:.&5.+14.$1;.))(19.R37.(1:.&5.+14.$1;.)))P,(8.(3.&40.)(19.R;.(1:.&5.+15.$1;.))(19.R38.(1:.&5.+15.$1;.)))P,(8.(3.&40.)(19.R<.(1:.&5.+16.$1;.))(19.R39.(1:.&5.+16.$1;.)))P,(8.(3.&40.)(19.R=.(1:.&5.+17.$1;.))(19.R3:.(1:.&5.+17.$1;.)))P,(8.(3.&40.)(19.R>.(1:.&5.+18.$1;.))(19.R3;.(1:.&5.+18.$1;.)))P,(8.(3.&40.)(19.R?.(1:.&5.+19.$1;.))(19.R3<.(1:.&5.+19.$1;.)))P,(8.(3.&40.)(19.R10.(1:.&5.+1:.$1;.))(19.R3=.(1:.&5.+1:.$1;.)))P,(8.(3.&40.)(19.R11.(1:.&5.+1;.$1;.))(19.R3>.(1:.&5.+1;.$1;.)))P,(8.(3.&40.)(19.R12.(1:.&5.+3.$1;.))(19.R3?.(1:.&5.+3.$1;.)))P,(8.(3.&40.)(19.R13.(1:.&5.+4.$1;.))(19.R40.(1:.&5.+4.$1;.)))P,(3=.R40.Vsu,R3>.R38.R37.R13.)P,A1.VK,R13.P,(<.R41.R14.)(1?.$20.(21.(22.$23.R17.R38.R16.(25.$20.))R15.)R35.)(1?.$20.(21.(22.$23.R2>.(1:.&40.+>66;8.$1;.)R2=.(25.$20.))R2<.)(2?.(36.(3.&8.)$31.(37.(1<.&40.R28.))(3:.(3.&8.)R21.R20.))R1?.))")
(* [comment removed for export] *).
Proof.
  intros regs mem mo f wb wp fd s l bufp bufsz can ret pending extra KK
         Hsp Ha0 Ha1 Ha2 Hra SOK Flo Fhi SWF SSP FD Hfd HKmo AOKP AOKE WBP WPhi
         LENP LENE M30 DISJP DISJE SNW TSP TSE RDP RDE Hret HKnil HK.
  pose proof (conj HKmo (mo_mat_refl mo) : KM K mo mo) as KMmo.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x65cad0) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  (* [comment removed for export] *)
  assert (HK' : forall regs' m mo1,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m -> KM K mo mo1 ->
     srealizesJ RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) mo1) KK).
  { intros. lazymatch goal with H : KM _ _ _ |- _ => destruct H as [HK1 MM1] end.
    apply HK. all: try assumption.
    eapply sw_post_of_LMA; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil AL CS K IMG K_halted K_mat su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 mo KK
                SUlo SUhi Flo Fhi FRCS Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1 AL CS K IMG K_halted K_mat su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 mo KK
                SUlo SUhi Flo Fhi FD Hfd FRCS Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 AL CS K IMG K_halted K_mat su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 mo KK
                SUlo SUhi Flo Fhi FD Hfd FRCS Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    ddestruct (sw_enter_eq regs (restrict D mem) (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    all: try (rres ltac:(exact SOK)).
    all: try (apply sw_file_restrict; assumption).
    all: try (apply ssp_cells_restrict; assumption).
    unfold mem_sw1 in RUN1. rrunK RUN1 KMmo KM1. fold mem_sw1.
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; unfold mem_sw1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (rz_writev1_zeroA RSEGS AL CS K K_halted K_mat K_vmonly regs1 (0x0e6740 : word) mem1 _ W_e3390 fd (Z_to_bv 64 (su - 88)) s (t_emit [] KK));
        [ exact F_e3390 | exact E_e3390 | exact (KM_K _ _ _ KM1) | exact (KM_fds _ _ _ Hfd _ KM1) | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | u_norm; unfold TASK_SIZE; lia | unfold TASK_SIZE; lia
        | u_norm; intros z Hz; left; apply FRCS; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      intros mo2 HK2 MM2. pose proof (KM_step _ _ _ _ KM1 HK2 MM2) as KM2. clear HK2 MM2.
      rewrite pc_e3394.
      ddestruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) (restrict D mem1) (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      rrunK RUN2 KM2 KM3.
      apply FIN; [|exact LM1|exact KM3].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (rz_writev1_wallA RSEGS AL CS K K_halted K_mat regs1 (0x0e6740 : word) mem1 _ W_e3390 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') KK);
        [ exact F_e3390 | exact E_e3390 | exact (KM_K _ _ _ KM1) | exact (KM_fds _ _ _ Hfd _ KM1) | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | 
        | u_norm; intros z Hz; left; apply FRCS; lia
        | exact AOKE
        | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      * unfold TASK_SIZE. lia.           (* [comment removed for export] *)
      * cbn [length] in LENE. lia.
      * lia.
      * intros k K1 K2 mo2 HK2 MM2. pose proof (KM_step _ _ _ _ KM1 HK2 MM2) as KM2. clear HK2 MM2. rewrite pc_e3394.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- ddestruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) (restrict D mem1) (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           rrunK RUN2 KM2 KM3.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1|exact KM3].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- ddestruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) (restrict D mem1) (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           rrunK RUN2 KM2 KM3.
           apply (L1 (length (x0 :: extra')) regs2 mem1 _ k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact KM3.
           ++ intros z Hz. apply AOKE. lia.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    ddestruct (sw_enter regs (restrict D mem) (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    all: try (rres ltac:(exact SOK)).
    all: try (apply sw_file_restrict; assumption).
    all: try (apply ssp_cells_restrict; assumption).
    unfold mem_sw1 in RUN1. rrunK RUN1 KMmo KM1. fold mem_sw1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (rz_writev2_wallA RSEGS AL CS K K_halted K_mat regs1 (0x0e6740 : word) mem1 _ W_e3390 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra KK);
      [ exact F_e3390 | exact E_e3390 | exact (KM_K _ _ _ KM1) | exact (KM_fds _ _ _ Hfd _ KM1) | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | 
      | u_norm; intros z Hz; left; apply FRCS; lia
      | u_norm; intros z Hz; apply AOKP; lia
      | exact AOKE
      | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
    + u_norm. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
    + unfold TASK_SIZE. lia.           (* [comment removed for export] *)
    + u_norm. lia.
    + u_norm. lia.
    + intros k K1 K2 mo2 HK2 MM2. pose proof (KM_step _ _ _ _ KM1 HK2 MM2) as KM2. clear HK2 MM2. rewrite pc_e3394. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * ddestruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) (restrict D mem1) (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        rrunK RUN2 KM2 KM3.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1|exact KM3].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * ddestruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) (restrict D mem1) (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        rrunK RUN2 KM2 KM3.
        apply (L2 (length pending + length extra)%nat regs2 mem1 _ k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact KM3.
        -- u_norm. intros z Hz. apply AOKP. lia.
        -- intros z Hz; apply AOKE; lia.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
        -- u_norm. lia.   (* [comment removed for export] *)
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End Thm.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
