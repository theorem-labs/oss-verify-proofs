(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape ZBridge HeapIface Asn1Aux Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StoreOk MemcpyLib SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow Restrict NodesA SymDriveA AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_exit_front1 A_unreg_globals
  A_exit A_exit_main A_tailkit_defs A_fwrite_err1 A_fwrite_err2 A_oomtail A_main_tails A_main_inv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.
Open Scope Z_scope.
#[local] Existing Instance Lib.PropExec.fx0.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_main_fin () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.B.A_exit_base.file_clean"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.B.A_exit_defs.stdout_pendingA"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.B.A_tailkit_defs.tail_memA"; "xmemA"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Fin.FRAMEA"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "xoutA"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.A_exit_front1.atexit_cells"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.B.A_exit_front1.incb_cell"; "Fin.atx_clause"; "RocqVerifyHarness.AgentSubmission.LibB.ARtDrv.drv_static"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.W"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_exit"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.exit_code"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_short"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_overrun"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"].

#[local] Unset Lia Cache.

(* [comment removed for export] *)
Record xmemA (su : Z) (m : mem) (tid : Z) (wp0 rp0 : word) : Prop := XMEM {
  xm_mi   : mem_inv asegs m;
  xm_tid  : 0 < tid < 2^31;
  xm_lock : rw_cells asegs m 0x65cd00 [C4 (Z_to_bv 64 0)];
  xm_mtid : rw_cells asegs m 0x63c9e8 [C4 (Z_to_bv 64 tid)];
  (* [comment removed for export] *)
  xm_nl   : ro_cells asegs m 0x65cd23 [C1 (Z_to_bv 8 0)];
  xm_comp : rw_cells asegs m 0x106390 [C1 (Z_to_bv 8 0)];
  xm_rtc  : asan_rtc m;
  xm_mapped : mapped m 0x7fffa000 0x800d3000;
  xm_glob : stdio_globals m;
  xm_in   : file_clean m 0x0fa668 wp0 rp0;
  xm_err  : exists wp2 rp2, file_clean m 0x0fa488 wp2 rp2
}.

(* [comment removed for export] *)
Definition xoutA (m : mem) (mo : Model) (pending : list byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "(0.(1.(2.(3.(4.&8.))O1.(5.(4.&8.)))(6.(4.&40.)Lwp1,(4.&40.)(6.(4.&40.)Lrp1,(4.&40.)(7.O3.+?:578.R2.R1.))))(6.$8.Lwb,$8.(6.$8.Lwp,$8.(6.(4.&40.)Lbufp,(4.&40.)(6.(4.&40.)Lbufsz,(4.&40.)(6.(4.&40.)Lrp1,(4.&40.)(6.(4.&40.)Lcan,(4.&40.)(1.(9.O3.R6.R5.R4.R3.R2.R1.O1.)(2.(:.$;.)(<.(=.O2.)(>.&40.+1.))(?.$;.(10.(>.&40.+1.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma bytes_eq_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Ltac rdn_img_lit := etransitivity; [vm_compute; reflexivity|]; f_equal; apply bytes_eq_unsigned; vm_compute; reflexivity.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00@0>L12768794730.4L19145977962.4L20601910513.4L25353669098.4L28910316598.4L32621547505.4L46934714161.4L50698129521.4L53506590998.4L55683789162.4L56715544049.4L56765666148.7L56765666148.8L58955759111.7L58955759111.8L67692473962.400000100200300400500600700800900:00;00I00W00e013014SSSSSSSSSSSS1a2H12H21j2HjS1a2H12H21j2HjS1a2H12H21j2HjS1a2H12H21j2HjS". (* [comment removed for export] *)
Lemma stderr_pristine_clean : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Pm,Px,(4.&40.)(:.(4.&8.))P,Pa,$8.P,(1.(11.+?:488.R1.)(12.R1.+?:578.))(2.(:.(4.&8.))A1.R3.(>.&40.R2.)(13.(4.&8.)))(7.R2.+?:488.(>.&40.=)(>.&40.=))")
(* [comment removed for export] *).
Proof.
  intros m PR.
  assert (IMG8 : forall a, 0x0fa488 <= a -> a + 8 <= 0x0fa578 -> rdn asegs m (Z_to_bv 64 a) 8 = rdn asegs (fun _ => None) (Z_to_bv 64 a) 8).
  { intros a H1 H2. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply PR. lia. }
  assert (IMG4 : forall a, 0x0fa488 <= a -> a + 4 <= 0x0fa578 -> rdn asegs m (Z_to_bv 64 a) 4 = rdn asegs (fun _ => None) (Z_to_bv 64 a) 4).
  { intros a H1 H2. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply PR. lia. }
  unfold file_clean. rewrite IMG4, !IMG8 by lia. unfold word_to_le_bytes. rewrite !unsigned_lit by lia. repeat split; rdn_img_lit.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma xmem_of_tail : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Psp,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))Pcan,(4.&40.)Ptid,$8.Pwp0,(4.&40.)Prp0,(4.&40.)Pwp1,(4.&40.)Prp1,(4.&40.)Psu,$8.P,(14.R9.R8.R7.R6.R5.R4.R3.R2.)(15.R2.R9.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros * TM. destruct TM. split; try assumption. dexists (Z_to_bv 64 0), (Z_to_bv 64 0). apply stderr_pristine_clean. assumption.
Qed.


Lemma mo_frame_fds : forall mo mo', mo_frame mo mo' -> m_fds mo' = m_fds mo.
Proof. unfold mo_frame, m_fds; intros mo mo' H; intuition congruence. Qed.
Lemma mo_frame_fs : forall mo mo', mo_frame mo mo' -> m_fs mo' = m_fs mo.
Proof. unfold mo_frame, m_fs; intros mo mo' H; intuition congruence. Qed.
Lemma mo_mat_fds : forall mo mo', mo_mat mo mo' -> m_fds mo' = m_fds mo.
Proof. unfold mo_mat, m_fds; intros mo mo' H; intuition congruence. Qed.

Section Fin.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Variable HID : artD asegs R HIA.
  Let AL := arl_AL R.
  Let L := arl_L R.
  #[local] Existing Instance L.   (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Hypothesis HFREE : arl_free R = 0x6947c.
  Hypothesis HTP : arl_tp R = 0x63ca90.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).

  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.       (* [comment removed for export] *)
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.       (* [comment removed for export] *)
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (fs0 : Fs) (tid : Z) (wp0 rp0 : word).
  Variables (TOP STKHI : Z).
  Hypothesis HTOPlo : bv_unsigned sp0 - 48 <= TOP.
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Let msp : Z := bv_unsigned sp0 - 128.   (* [comment removed for export] *)
  Variable pad : list byte.                (* [comment removed for export] *)

  Definition FRAMEA : list cell := ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "(16.$17.(18.#8.Vpad,)(16.$17.(19.(>.&40.=))(16.$17.(19.(>.&40.=))(16.$17.(19.(>.&40.=))(16.$17.(19.(>.&40.=))(16.$17.(19.(>.&40.(1:.(1;.&40.Vsp0,)+20.)))(16.$17.(19.(>.&40.+970>0.))(16.$17.(19.(>.&40.+2.))(16.$17.(19.(>.&40.(1:.(1;.&40.Vsp0,)+8.)))(16.$17.(19.(>.&40.+>0::8.))(5.$17.)))))))))))")
(* [comment removed for export] *).

  Ltac done_regs := apply evtA_done; unfold mkR; repeat (first [ reflexivity | lia | progress f_equal ]).
  (* [comment removed for export] *)
  Ltac norm_getr :=
    repeat match goal with
    | |- context [getr (TNode ?a ?b ?c) ?r] =>
        let p := eval vm_compute in (bv_key r) in
        let v := eval cbn [tget] in (match tget p (TNode a b c) with Some v => v | None => w0 end) in
        change (getr (TNode a b c) r) with v
    end.

  (* [comment removed for export] *)
  #[using="IMG"] Lemma F1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "PCS,P,$8.SpPra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))(1<.$1=.VAL,R20.Lms',$1>.(2.$1>.R1.(1?.(20.(>.&40.+972=<.)(>.&40.Vmsp,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R19.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(21.&5.(4.&40.))(>.&40.+6947<.)(>.&20.=)(13.(4.&40.))R2.(22.$1=.)))(1?.(20.R1?.(>.&40.Vmsp,)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(21.&5.(4.&40.))(>.&40.+972=4.)(>.&20.=)(13.(4.&40.))R1.(22.$1=.)))")
(* [comment removed for export] *).
  Proof. intros *. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. zstep. zstep. done_regs. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L22642726558.60L23195586408.60L27469949392.60L31409816370.61L36667852792.0 L40778080266.60L48940594306.60L61440761469.60Q12959781403.60Q14248518728.60Q15481972123.60Q1646435810.60 Q18520262754.60Q18978768795.60Q20267518408.60Q21503593243.60Q22175591835.60Q24643483291.60Q25012974875.60Q25923601634.60Q26305658696.60Q29800356168.60Q29811418850.60Q30183762203.60Q32325168328.60Q32663974427.60Q33684359323.60Q35834547912.60Q38327325256.60Q41505951714.60Q42797381474.60Q44344739784.60Q4440670562.60 Q45225597339.60Q50380518728.60Q51599816347.60Q54821309154.60Q558935067.60  Q57602024475.60Q57733255963.60Q58363017826.60Q63619451291.60Q6955003035.60 Q8579690395.60 00000100200300800900:00?00@00J00O00Y00^00c00m01201<01F01P01Z01_01d01i01n02802=02G02Q02V02[02`02e02j02o03903>03H03M03W03a03k04004:04D04NFFFS3sp0SFS3sp0FS3sp04SPloS3sp0S3sp04SPloS3sp0S3sp0S3sp04SPloS3sp0S3sp04SPloS3sp04SPhiS3sp04SPhiS3sp04SPloS3sp0S3sp0S3sp0S3sp0S3sp04SPhiS3sp0S3sp04SPhiS3sp04SPhiS3sp0S3sp0S3sp0S3sp0S3sp0S3sp0S3sp04SPhiS3sp0S3sp04SPloS3sp0S3sp04SPhiS3sp04SPloS3sp04SPhiS3sp0S3sp04SPloS3sp04SPloS3sp04SPhi". (* [comment removed for export] *)
  #[using="IMG SPlo SPhi"] Lemma F2_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "PCS,P,$8.SpPra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))P,(23.$1=.R1.Vmsp,$24.)P,(25.R21.Vmsp,+50.)(1<.$1=.VAL,R22.Lms',$1>.(2.$1>.R1.(1?.(20.(>.&40.+>0::8.)(>.&40.(26.(1;.&40.Vsp0,)+30.))R21.R20.R1?.R1>.R1=.(>.&40.(1:.(1;.&40.Vsp0,)+8.))(>.&40.+2.)R1<.R19.R18.R17.R16.R15.R14.R13.(>.&40.+970>0.)(>.&40.(1:.(1;.&40.Vsp0,)+20.))(>.&40.=)(>.&40.=)(>.&40.=)(>.&40.=)R<.R;.R:.R9.R8.R7.R6.R5.)(21.&5.(4.&40.))(>.&40.+>0::8.)(>.&20.=)(13.(4.&40.))R4.(22.$1=.)))(1?.(20.R21.(>.&40.Vmsp,)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(21.&5.(4.&40.))(>.&40.+972=<.)(>.&20.=)(13.(4.&40.))R3.(22.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros * FR CSF. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. unfold FRAMEA in FR.
    do 12 zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0?L11745435968.51L12971186197.55L14375606357.57L15823104540.55L18869159509.57L18925010976.55L21918964855.55L22696620384.55L27045534584.52L28619777875.57L28619777875.59L30963002144.55L31564125703.55L32201861184.51L36029363060.56L36362444629.55L36548426016.57L3935439392.57 L40634434460.55L43004104224.55L43667030549.57L44713534213.54L47903664213.55L48586316832.57L49402993052.55L52399232597.55L54595678624.57L54967697052.55L56765667309.49L56765667309.50L57643738119.55L60427588053.55L62511752533.57L62874643296.57L63518782421.57L63709270919.55L64570401600.51L66442651500.55L866750368.55  L8851067672.51 L9911160071.55 00000900B00K00T00]00f00o01801E01R01_01h02102:02U02^02g03003903B03K03a03j04304<04E04N04W04j05=05F05O05X05a05j06306<06E06N06W06`S3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03msp1x1HS3sp03msp1x1HS3sp03msp1x1HS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3msp1A2cs2DS1a2HaS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3msp1A2cs2DSS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3msp1a2HaS3sp04SPlo3msp1a2HaS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03msp". (* [comment removed for export] *)
  #[using="HID SPlo"] Lemma xmem_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Pm,P,(4.&40.)(:.(4.&8.))Pm',P,(4.&40.)(:.(4.&8.))Ph',(27.$1=.VR,VHIA,)PLB,(3.$28.)PLB',(3.$28.)PLF,(3.$28.)P,(15.(26.(1;.&40.Vsp0,)+30.)R6.Vtid,Vwp0,Vrp0,)P,(29.$1=.VR,R4.R2.Vmsp,(2:.VR,)VSTKHI,(5.$2;.)R7.R6.)P,(2<.$1=.VR,VHIA,R6.R4.R3.R7.)P,(2=.$1=.R8.)(15.(26.(1;.&40.Vsp0,)+30.)R9.Vtid,Vwp0,Vrp0,)")
(* [comment removed for export] *).
  Proof.
    intros m m' h' LB LB' LF XM [HP SHD] HH MI.
    destruct XM as [MI0 TID LOCK MTID NL COMP RTC MAPPED GLOB FIN ERR].
    assert (AG : forall a, drv_static a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply (proj1 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) ltac:(exact I))). }
    assert (WV : forall a, drv_static a -> wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
    { intros a Ha. apply (proj2 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) ltac:(exact I))). }
    assert (MU : munch drv_compl m m').
    { intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
      apply AG. apply (proj1 (outside_drv_compl (bv_unsigned x) ltac:(lia))). exact Hx. }
    assert (RW : forall A cs, rw_cells asegs m A cs ->
                 (0x0fa460 <= A /\ A + Z.of_nat (cells_size cs) <= 0x0fa780) \/ (A = 0x106390 /\ cells_size cs = 1%nat) \/ (0x63c180 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c9ec) \/ (0x63cae8 <= A /\ A + Z.of_nat (cells_size cs) <= 0x65cd50) ->
                 rw_cells asegs m' A cs).
    { intros A cs H DS. eapply rw_cells_transport_w; [exact H | exact MU | intros a Ha; apply WV; unfold drv_static; lia |].
      unfold drv_compl. cbn [disjoint_from fst snd]. lia. }
    split.
    - exact MI.
    - exact TID.
    - apply RW; [exact LOCK | cbn; lia].
    - apply RW; [exact MTID | cbn; lia].
    - eapply ro_cells_transport; [exact NL | exact MU |]. unfold drv_compl. cbn [disjoint_from fst snd cells_size csize]. lia.
    - apply RW; [exact COMP | cbn; lia].
    - apply (hd_rtc _ _ _ HID). eapply (hm_rtc _ _ HIA). exact HH.
    - eapply (hd_lowsh _ _ _ HID). exact HH.
    - ddestruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
    - ddestruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
    - ddestruct ERR as (wp2 & rp2 & Q1 & Q2 & Q3 & Q4 & Q5). dexists wp2, rp2. unfold file_clean.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L13989151813.43L13989151813.58L14499512855.59L16800224304.43L16800224304.58L19055741040.43L19055741040.58L19308011440.58L25532486981.58L26548413381.58L28619777875.45L28619777875.60L28619777875.61L28836638512.43L28836638512.58L34849610928.43L34849610928.58L37355282480.58L38056922821.43L38056922821.58L40845400837.43L40845400837.58L440333557.58  L44353302412.59L46105950277.58L4761776432.43 L4761776432.58 L49395841840.58L50609894981.58L56765667309.39L57614457669.43L57614457669.58L61432258096.58L62122594629.43L62122594629.58L65505491013.5800000900J00[00d01501>01O01`02102B02O03603K03T03e03n04?04P04Y04j05305D05^05o06@06I06Z06k07<07O07X07i08:08C08T097S3sp03mspS3sp03msp7pendingS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp03msp7pendingS3sp03msp7pendingS3sp03msp7pendingS3sp03msp1x1HS3sp03msp7pending1x1H4SPlo2wb2wp2RG3LENS3sp03msp7pending1x1HS3sp03mspS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp03msp7pending2wb2wp2RGS3sp03msp7pendingS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp03msp7pendingS3sp03msp7pendingS3sp04SPlo3msp1a2HaS3sp03mspS3sp03msp7pendingS3sp03msp7pendingS3sp03mspS3sp03msp7pendingS3sp04SPlo3msp7pending2wb2wp2RG3LEN". (* [comment removed for export] *)
  #[using="HIA HID SPlo"] Lemma xout_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Pm,P,(4.&40.)(:.(4.&8.))Pm',P,(4.&40.)(:.(4.&8.))Pmo,$2>.Pmo',$2>.PLB,(3.$28.)PLF,(3.$28.)Ppending,(3.(4.&8.))P,(2?.R7.R5.R1.)P,(29.$1=.VR,R4.R3.Vmsp,(2:.VR,)VSTKHI,(5.$2;.)R8.R7.)P,(2.(3.(30.(4.&40.)$;.))(=.R6.)(=.R7.))P,(31.R9.)(2?.R:.R8.R5.)")
(* [comment removed for export] *).
  Proof.
    intros m m' mo mo' LB LF pending XO [HP _] FDS RTC.
    assert (AG : forall a, drv_static a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply (proj1 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) ltac:(exact I))). }
    destruct XO as [[-> (wp1 & rp1 & Q1 & Q2 & Q3 & Q4 & Q5)] | (wb & wp & bufp & bufsz & rp1 & can & SP & FD1)].
    - left. split; [reflexivity|]. dexists wp1, rp1. unfold file_clean.
      repeat split; (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
    - right. dexists wb, wp, bufp, bufsz, rp1, can. split; [| rewrite FDS; exact FD1].
      destruct SP as [L1 L2 L3 L4 L5 L6 L7 L8 L9 RG LEN MAX BY SSP]. split; try assumption;
        try (eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | assumption]).
      + destruct SSP as (S1 & S2). split; [apply (rtc_rdn8 _ _ _ RTC); unfold rtc_cells; cbn [In]; tauto |].
        eapply rdn_agree_static; [exact AG | unfold drv_static; intros; lia | lia | cbn; lia | exact S2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition atx_clause (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "(6.$32.Lb,$32.(6.(4.&8.)Lfin,(4.&8.)(6.(3.(4.&8.))Ljp,(3.(4.&8.))(6.(3.(4.&8.))Ljq,(3.(4.&8.))(6.(3.(4.&8.))Ljf,(3.(4.&8.))(1.(33.R5.O1.R4.R3.R2.R1.)P,(2.$32.R5.$34.)(35.O1.)))))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L10108817522.47L27045534584.48L36029363060.52L44713534213.50L55368882697.48L56765667309.45L56765667309.4600000900F00a01201;01N01aS3sp03mspS3sp03msp1x1HS3sp04SPlo3msp1A2cs2DS1a2HaS3sp03msp1A2cs2DSS3sp03mspS3sp04SPlo3msp1a2HaS3sp04SPlo3msp1a2Ha". (* [comment removed for export] *)
  #[using="HIA HID sp0 SPlo msp"] Lemma atx_presA : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Pm,P,(4.&40.)(:.(4.&8.))Pm',P,(4.&40.)(:.(4.&8.))PLB,(3.$28.)PLF,(3.$28.)PSP,$8.PSSP,$8.PSTKHI',$8.PW,(3.$2;.)P,(36.R8.)P,(29.$1=.VR,R7.R6.R5.R4.R3.R2.R9.R8.)P,Pa,$8.P,(37.R1.)(38.R5.R2.)(36.R:.)")
(* [comment removed for export] *).
  Proof.
    (intros m m' LB LF SP SSP STKHI' W dd_H; ddestruct dd_H as (b & fin & jp & jq & jf & AT & IC); intros [HP _] HW).
    assert (AG : forall a, drv_static a -> m' (wa a) = m (wa a)).
    { intros a Ha. apply (proj1 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) (HW a Ha))). }
    assert (WV : forall a, drv_static a -> wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
    { intros a Ha. apply (proj2 (HP a ltac:(unfold drv_static in Ha; lia) ltac:(right; left; exact (hd_static _ _ _ HID a Ha)) (HW a Ha))). }
    assert (MU : munch drv_compl m m').
    { intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)).
      apply AG. apply (proj1 (outside_drv_compl (bv_unsigned x) ltac:(lia))). exact Hx. }
    assert (RW : forall A cs, rw_cells asegs m A cs ->
                 (0x63c050 <= A /\ A + Z.of_nat (cells_size cs) <= 0x63c080) \/ (0x63cae8 <= A /\ A + Z.of_nat (cells_size cs) <= 0x65cd50) ->
                 rw_cells asegs m' A cs).
    { intros A cs H DS. eapply rw_cells_transport_w; [exact H | exact MU | intros a Ha; apply WV; unfold drv_static; lia |].
      unfold drv_compl. cbn [disjoint_from fst snd]. lia. }
    exists b, fin, jp, jq, jf. split.
    - unfold atexit_cells in *. apply RW; [exact AT | cbn; lia].
    - intros Hb. unfold incb_cell in *. apply RW; [exact (IC Hb) | cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L1111445933.82  L11408572375.119L11758988525.142L15047276929.82 L15146382547.82 L25219926960.113L35798422828.131L37043302749.82 L38352069152.82 L42571143189.82 L42571318834.114L45208862126.138L45515722715.114L45756776072.113L47247639486.135L47335380849.82 L47335462128.113L49890457993.117L52593474786.138L56765449480.142L59315053158.143L62022225487.82 L62230576424.139L64566498626.138L8729881216.135 L8788883649.117 00000C00c00l01501S01\01o02H02\03503>03N03f03o04=04P04c05105<05V05j06506@06U06c071S3sp04SPlo4SPal3mspS3sp04SPlo5STKHI6HSTKHI3msp1z2HzS3sp03mspS3sp03mspS3sp04SPlo4SPal3msp4code5HcodeS3sp03mspS3sp04SPlo4SPal3mspS1R3sp04SPlo5STKLO3msp2NFS3sp03TOP6HTOPlo3mspS3sp04SPlo3msp4code5HcodeS3sp03mspS3sp03msp1a2Ha1lS1R3sp05STKHI6HSTKHI3mspS3sp03mspS3sp04SPhi3mspS3sp04SPlo4SPhi3mspS3sp04SPlo4SPhi3mspS3sp04SPhi3mspS3sp03msp1aS3sp04SPlo4SPhi3msp1a2Ha1lS3sp04SPlo3msp1a1l1CS1R3sp03mspS3sp03msp1aS3sp04SPlo3msp1a2Ha1lS3sp04SPlo3mspS3sp04SPlo3msp". (* [comment removed for export] *)
  #[using="HID AL IMG ASB HFREE HTP HIMGCS SPlo SPhi SPal STKLO HTOPlo HSTKHI"] Theorem finA : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Pcode,$8.Ppending,(3.(4.&8.))Pbuf,$8.Pcap,$8.PLB,(3.$28.)Pra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))Pmo,$2>.Ph,(27.$1=.VR,VHIA,)P,(2<.$1=.VR,VHIA,R1.R1:.(5.$28.)R3.)P,(39.(30.$8.$8.)(3:.$8.$8.R1=.R1<.)R1;.)P,(3;.$1=.VR,VHIA,R3.R4.)P,(2.$8.(3<.$1=.VR,VHIA,R4.)VTOP,)P,(2.$8.(3=.$1=.VR,VHIA,R5.)VSTKHI,)P,(11.(1:.(3>.$1=.VR,VHIA,R6.)$3?.)$40.)P,(11.(1:.(41.$1=.VR,VHIA,R7.)(42.=))$43.)P,(2.$44.(45.R9.)Vfs0,)P,(15.(26.(1;.&40.Vsp0,)+30.)R;.Vtid,Vwp0,Vrp0,)P,(2?.R<.R;.R26.)P,(36.R=.)P,(23.$1=.R>.Vmsp,$24.)P,(46.$1=.R?.(2:.VR,)Vmsp,)P,(0.(2.$8.R2;.=)(2.$8.R2;.+2.))(47.$1=.(48.(1?.(20.R27.(>.&40.Vmsp,)(>.&40.+10800.)(>.&40.+63<:90.)R26.R25.R24.(>.&40.R2<.)(>.&40.R2:.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.(>.&40.=)(>.&40.=)(>.&40.=)(>.&40.=)R15.R14.R13.R12.)(21.&5.(4.&40.))(>.&40.+972=4.)(>.&20.=)(13.(4.&40.))R11.(22.$1=.))R10.)(49.(4:.+1.R2;.)(4;.(4<.R2<.)Vfs0,)))")
(* [comment removed for export] *).
  Proof.
    intros * HH IN HKmo HT HS HV HFR FS XM XO ATX FR ST Hcode.
    pose proof (hd_needs _ _ _ HID) as (NM & NF & NA). pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HKmo | apply (F1_steps (hcs asegs R HIA h)) |].
    cbn beta. intros ms1 mo1 -> HK1 MM1. rewrite <- HFREE.
    (* [comment removed for export] *)
    eapply srzJ_of_aevtS; [ | apply t_emit_has_nil | ].
    { eapply (heapA_freeD _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               bvmap_empty (Z_to_bv 32 0) m mo1 h LB [] buf cap (arl_stklo R) 0);
        rewrite ?unsigned_lit by lia;
        [ exact HH | exact HK1 | exact IN | exact ST | lia | cbv delta [msp]; lia | rewrite HT; cbv delta [msp]; lia | cbv delta [msp]; lia
        | exact (xm_mi _ _ _ _ _ XM) | rewrite HTP; reflexivity | reflexivity | exact HV
        | apply uwc_data; [lia | rewrite STKLO; lia]                     (* [comment removed for export] *)
        | exact HFR ]. }
    (intros c2 dd_H; ddestruct dd_H as (ms2 & mo2 & -> & P2)).
    ddestruct P2 as (v0 & v1 & v2 & r2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & MI2 & ST2 & MF2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HFRESH2 & HH2).
    rewrite ?unsigned_lit in ST2, HP2 by lia.
    replace (ret_pc (Z_to_bv 64 0x0972dc)) with (Z_to_bv 64 0x0972dc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (FR2 : rw_cells asegs m2 msp FRAMEA).
    { eapply (presA_rw_cells asegs R); [exact HP2 | exact FR | apply client_range_stack; lia | cbn; exact I]. }
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h2) (HK asegs R HIA h2) (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2)); [exact HK2 | |].
    { apply (F2_steps (hcs asegs R HIA h2)); [exact FR2|].
      eapply crange_mono; [exact HCS2|].   (* [comment removed for export] *)
      eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS; cbv delta [msp]; lia]. }
    cbn beta. intros ms3 mo3 -> HK3 MM3.
    change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
    replace (exit_code code) with (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)).
    2:{ unfold exit_code. apply bv_eq. destruct Hcode as [-> | ->]; reflexivity. }
    rewrite <- FS, <- (mo_mat_fs _ _ MM1), <- (mo_frame_fs _ _ MF2), <- (mo_mat_fs _ _ MM3).
    eapply (main_ret_exitA AL (hcs asegs R HIA h2) (HK asegs R HIA h2) IMG ALWF (hcs_ok _ _ HIA h2) ASB (HIMGCS h2)
              (hk_halted _ _ HIA h2) (hk_mat _ _ HIA h2) (hk_vmonly _ _ HIA h2) (bv_unsigned sp0 - 48)); [lia | lia | | | exact HK3].
    { intros z Hz. apply HCS2. eapply (hcs_stack _ _ HIA h); rewrite ?STKLO, ?HS; lia. }
    (* [comment removed for export] *)
    pose proof (xmem_presA m m2 h2 (lb_remove buf LB) _ [] XM ltac:(rewrite <- HS; exact HP2) HH2 MI2) as XM2.
    pose proof (atx_presA m m2 _ _ _ _ _ _ ATX HP2 ltac:(intros a Ha; exact I)) as ATX2. unfold atx_clause in ATX2.
    destruct XM2 as [MI2' TID LOCK MTID NL COMP RTC MAPPED GLOB FIN (wp2 & rp2 & ERR)].
    dexists tid, wp0, rp0, wp2, rp2. split.
    - split; try assumption; try reflexivity.
      + lia.
      + (* [comment removed for export] *)
        ddestruct ST2 as (S0 & S1 & S2). destruct FR2 as [_ (W0 & W1 & W2)]. cbn [cells_size csize FRAMEA Nat.add] in W2.
        split; [lia|]. split; [lia|]. intros a Ha.
        destruct (Z_lt_le_dec a msp).
        * apply S2. rewrite STKLO. cbv delta [msp] in l. lia.
        * split.
          -- replace a with (msp + (a - msp)) by lia. apply W2. cbv delta [msp] in *. lia.
          -- pose proof (W2 (a - msp) ltac:(cbv delta [msp] in *; lia)) as WV. replace (msp + (a - msp)) with a in WV by lia.
             unfold mrd. destruct (m2 (wa a)) as [b|] eqn:E; [exists b; reflexivity|].
             exfalso. apply WV. unfold wview. rewrite E.
             destruct (find_segment asegs (bv_unsigned (wa a)) 1) as [seg|] eqn:EF; [|reflexivity].
             exfalso. rewrite wa_unsigned in EF by (cbv delta [msp] in *; lia).
             pose proof (find_segment_cov asegs asegs a 1 seg EF ltac:(auto) 0 ltac:(cbn; lia)) as C.
             rewrite Z.add_0_r in C. apply asegs_segcov in C. unfold AIMG_LO, AIMG_HI in C. cbv delta [msp] in *. lia.
    - pose proof (xout_presA m m2 mo mo3 (lb_remove buf LB) [] pending XO ltac:(rewrite <- HS; exact HP2)
                    ltac:(rewrite (mo_mat_fds _ _ MM3), (mo_frame_fds _ _ MF2), (mo_mat_fds _ _ MM1); reflexivity) RTC) as XO2.
      exact XO2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?Q13314086828.61Q20071149798.61Q29762534956.61Q39581111910.61Q53522209153.61Q5640889772.61 Q63510961708.6100000900B00C00L00U00V00_S2AL4IMG'S2AL4IMG'SS2AL4IMG'S2AL4IMG'SS2AL4IMG'". (* [comment removed for export] *)
  #[using="IMG"] Lemma G1_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "PCS,P,$8.SpPra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))P,(31.R1.)(1<.$1=.VAL,R21.Lms',$1>.(2.$1>.R1.(1?.(20.(>.&40.+972=4.)(>.&40.Vmsp,)R20.R1?.R1>.R1=.R1<.R1;.R1:.(>.&40.+23360.)(>.&40.+1?.)(>.&40.+1.)(>.&40.+?:488.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(21.&5.(4.&40.))(>.&40.+58714.)(>.&20.=)(13.(4.&40.))R3.(22.$1=.)))(1?.(20.R20.(>.&40.Vmsp,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(21.&5.(4.&40.))(>.&40.+97298.)(>.&20.=)(13.(4.&40.))R2.(22.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros * RTC. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct (rtc_stderr_cells m RTC) as [Q1 Q2].
    do 9 zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?Q13314086828.61Q20071149798.61Q29762534956.61Q39581111910.61Q53522209153.61Q5640889772.61 Q63510961708.6100000900B00C00L00U00V00_S2AL4IMG'S2AL4IMG'SS2AL4IMG'S2AL4IMG'SS2AL4IMG'". (* [comment removed for export] *)
  #[using="IMG"] Lemma G2_steps : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "PCS,P,$8.SpPra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))P,(31.R1.)(1<.$1=.VAL,R21.Lms',$1>.(2.$1>.R1.(1?.(20.(>.&40.+972=4.)(>.&40.Vmsp,)R20.R1?.R1>.R1=.R1<.R1;.R1:.(>.&40.+16;=9.)(>.&40.+1?.)(>.&40.+1.)(>.&40.+?:488.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.)(21.&5.(4.&40.))(>.&40.+58714.)(>.&20.=)(13.(4.&40.))R3.(22.$1=.)))(1?.(20.R20.(>.&40.Vmsp,)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(21.&5.(4.&40.))(>.&40.+972;4.)(>.&20.=)(13.(4.&40.))R2.(22.$1=.)))")
(* [comment removed for export] *).
  Proof.
    intros * RTC. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct (rtc_stderr_cells m RTC) as [Q1 Q2].
    do 8 zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Variables (can : word) (wp1 rp1 : word).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01>0?L12481883950.69L12773992695.61L12773992695.77L12774442030.53L12774442413.52L12880385027.73L14365879209.53L14366218508.55L14790769198.73L14983301498.53L15386847365.73L18317015149.46L18927111863.73L19005153669.54L21916865248.69L21916865248.73L22698721271.73L23371404357.54L23858361134.73L25069796662.47L27327112460.72L28615818822.52L30965097911.73L31297999237.73L31566223504.69L31566223504.73L32574504843.54L33607720750.69L33607720750.73L34301895405.61L34301895405.77L36029363060.46L3629801620.69 L3629801620.73 L36346621131.54L3788567612.51 L37985840948.51L39551979141.54L41776330276.69L41776330276.73L42009734083.73L42231520660.69L42302128020.69L42355431755.54L43002003639.73L44168090616.51L44358273936.69L48421829614.69L48421829614.73L48563370349.53L49589711662.69L51180437125.73L51931485061.54L52858176067.73L5294377620.73 L53371273616.69L53501269908.73L54393418827.54L55686714054.54L56765666148.61L56765666148.77L57645836944.73L5870234947.73 L61114171182.73L6111778565.73 L63711370512.73L64069716500.73L66430260043.54L67484422124.72L68435088709.73L7408198262.53 L7408198645.52 L7985991406.61 L7985991406.77 L864649527.73  L8738974725.54 L9428705347.73 L9913254800.73 00000900S00m01;01N01W01d02102:02H02Q02o03803A03J03S03\03e03n04<04Q04e04n05705@05I05R05[05d06>06X06f06o07807A07Y07b07k08408=08F08O08X08a08j09809A09J09S09a09j0:30:<0:E0:N0:W0:`0:i0;20;O0;l0<50<>0<G0<P0<Y0<b0<k0=;0=D0=Q0=a0>>0>[0>d0>m0?60??S3sp03mspS3sp04SPlo3msp1a1n2Ha1j2HjS3sp04SPlo3msp1a1n2Hd1j2HjS3sp03msp1a2l1S3sp03msp1a2l04SPloS3sp03mspS3sp03msp1a1HS3sp03msp1a1HS3sp03mspS3sp03msp1a2l1S3sp03mspS3sp04SPlo3TOP6HTOPlo3msp1a2HaS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3mspS3sp04SPlo3msp1a1n2HnS3sp04SPlo3msp1a1H1lS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3msp1a1n2Hn1j2HjS3sp04SPlo3msp1a1n2Hn1j2HjS3sp03msp1a2HaS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo4SPhi3msp1x2HxS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3mspS3sp03mspS3sp03mspS3sp03mspS3sp03msp1a2l0S3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo3msp1a1n2Ha2Hn1j2HjS3sp04SPlo3msp1a1n2Ha2Hn1j2HjS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp03msp1a1n2HdS3sp03mspS3sp03msp1a1lS3sp03msp1a1l2l0S3sp04SPlo3msp1a1n2Ha2Hn1j2HjS3sp04SPlo3msp1a1n2Ha2Hn1j2HjS3sp03mspS3sp03mspS3sp03mspS3sp03msp". (* [comment removed for export] *)
  #[using="HID SPlo SPhi STKLO HTOPlo"] Lemma fin_facts_of_fw : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Pm,Px,(4.&40.)(:.(4.&8.))Pm',Px,(4.&40.)(:.(4.&8.))Ph,(27.$1=.VR,VHIA,)PLB,(3.$28.)P,Px,(4.&40.)P,(4=.(1.(11.(26.Vmsp,+1000.)(1;.&40.R1.))(12.(1;.&40.R1.)Vmsp,)))P,(4=.(1.(11.+?:488.(1;.&40.R2.))(12.(1;.&40.R2.)+?:570.)))(2.(:.(4.&8.))A1.R6.R3.A1.R7.R3.)P,(4>.(16.(30.$8.$8.)(3:.$8.$8.(26.Vmsp,+1000.)Vmsp,)(16.(30.$8.$8.)(3:.$8.$8.+?:488.+?:570.)(5.(30.$8.$8.))))R5.R4.)P,(4?.R6.R5.)P,(50.$1=.R7.R6.)P,(7.R7.+?:488.(>.&40.+65=198.)(>.&40.=))P,(14.(>.&40.Vmsp,)R9.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(2<.$1=.VR,VHIA,R8.R7.(5.$28.)R:.)P,(2.$8.(3<.$1=.VR,VHIA,R9.)VTOP,)P,(23.$1=.R<.Vmsp,$24.)P,(46.$1=.R=.(2:.VR,)Vmsp,)(1.(2<.$1=.VR,VHIA,R<.R;.(5.$28.)R=.)(1.(15.(26.(1;.&40.Vsp0,)+30.)R=.Vtid,Vwp0,Vrp0,)(1.Pmo,$2>.(2?.R>.R1.(5.(4.&8.)))(1.(23.$1=.R=.Vmsp,$24.)(1.(46.$1=.R=.(2:.VR,)Vmsp,)(36.R=.))))))")
(* [comment removed for export] *).
  Proof.
    intros m m' h LB AG MU GR WM CLEAN TM HH HT FR ST. pose proof (u64_range sp0) as SPR.
    assert (HH' : HM asegs R HIA h LB [] m').
    { eapply (hm_munch _ _ HIA); [exact HH | exact MU | exact WM |].
      constructor; [| constructor; [| constructor]]; cbn [fst snd]; intros a Ha.
      - left. left. rewrite HT, STKLO. cbv delta [msp] in Ha. lia.
      - left. right. left. apply (hd_static _ _ _ HID). unfold ARtDrv.drv_static. lia. }
    assert (MI' : mem_inv asegs m').
    { intros a b Hb. pose proof (u64_range a).
      destruct (m a) as [b0|] eqn:E0; [exact (tm_mi _ _ _ _ _ _ _ _ TM a b0 E0)|].
      destruct (Z_lt_le_dec (bv_unsigned a) (msp - 4096)).
      - destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa488); [| destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa570)].
        1,3: exfalso; rewrite AG in Hb by lia; congruence.
        rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        eapply wview_not_ro with (m := m).
        + pose proof (store_ok_data m (Z_to_bv 64 (bv_unsigned a)) 1 ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; cbn; lia)) as SO.
          pose proof (store_ok_wview asegs m _ 1 0 SO ltac:(lia)) as WV. rewrite u_small in WV by lia. rewrite Z.add_0_r in WV. exact WV.
        + unfold wa. rewrite Z_to_bv_bv_unsigned. exact E0.
      - destruct (Z_lt_le_dec (bv_unsigned a) msp).
        + rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply A_oomtail.ro_addr_high. unfold AIMG_HI. cbv delta [msp] in *. lia.
        + exfalso. rewrite AG in Hb by lia. congruence. }
    assert (ST' : stk asegs m' (arl_stklo R) msp).
    { eapply stk_transport; [exact ST | exact MU | exact WM |]. intros x Hx. right.
      ddestruct ST as (_ & _ & S3). destruct (S3 x Hx) as [_ (b & Hb)]. unfold mrd in Hb. destruct (m (wa x)) as [b0|] eqn:E0.
      - destruct (m' (wa x)) as [b1|] eqn:E1; [exists b1; reflexivity|]. exfalso. apply (GR (wa x)); [congruence | exact E1].
      - exfalso. pose proof (A_exit_lib.seg_rom_high x ltac:(unfold AIMG_HI; rewrite STKLO in Hx; cbv delta [msp] in Hx; lia)) as SR. rewrite SR in Hb. discriminate. }
    split; [exact HH'|]. split; [| split; [| split; [| split]]].
    - destruct TM as [WIN RO ERR CAN RTC ZI ZS STK MI0 TID LOCK MTID ATEXIT NL COMP MAPPED GLOB FIN FOUT].
      assert (DJ : forall a n, 0 <= a -> a + n <= 0x65f000 -> (a + n <= 0x0fa488 \/ 0x0fa570 <= a) ->
                   disjoint_from [(msp - 4096, msp); (0x0fa488, 0x0fa570)] a n).
      { intros a n Ha Hn Hd. cbn. cbv delta [msp]. repeat split; lia. }
      assert (RDN : forall (a : Z) n bs, 0 <= a -> a + Z.of_nat n <= 0x65f000 -> (a + Z.of_nat n <= 0x0fa488 \/ 0x0fa570 <= a) ->
                    rdn asegs m (Z_to_bv 64 a) n = Some bs -> rdn asegs m' (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Ha Hn Hd H. rewrite <- H. apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply AG; rewrite u_small by lia; cbv delta [msp]; lia. }
      split.
      + exact MI'.
      + exact TID.
      + eapply rw_cells_transport; [exact LOCK | exact MU | exact WM | apply DJ; cbn; lia].
      + eapply rw_cells_transport; [exact MTID | exact MU | exact WM | apply DJ; cbn; lia].
      + eapply ro_cells_transport; [exact NL | exact MU | apply DJ; cbn; lia].
      + eapply rw_cells_transport; [exact COMP | exact MU | exact WM | apply DJ; cbn; lia].
      + apply (hd_rtc _ _ _ HID). eapply (hm_rtc _ _ HIA). exact HH'.
      + eapply (hd_lowsh _ _ _ HID). exact HH'.
      + ddestruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals. repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]).
      + ddestruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean. repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]).
      + eexists. eexists. exact CLEAN.
    - intros mo. left. split; [reflexivity|]. dexists wp1, rp1. destruct (tm_out _ _ _ _ _ _ _ _ TM) as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
      assert (RDN : forall (a : Z) n bs, 0x0fa578 <= a -> a + Z.of_nat n <= 0x0fa780 -> rdn asegs m (Z_to_bv 64 a) n = Some bs -> rdn asegs m' (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Ha Hn H. rewrite <- H. apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply AG; rewrite u_small by lia; cbv delta [msp]; lia. }
      repeat split; (eapply RDN; [cbn; lia | cbn; lia | assumption]).
    - eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [cells_size csize FRAMEA Nat.add disjoint_from fst snd]; cbv delta [msp]; lia].
    - exact ST'.
    - (* [comment removed for export] *)
      destruct (tm_atexit _ _ _ _ _ _ _ _ TM) as (jp & jq & jf & AT). dexists false, (Z_to_bv 8 0), jp, jq, jf. split; [| intros; discriminate].
      unfold atexit_cells in *. eapply rw_cells_transport; [exact AT | exact MU | exact WM |]. cbn. cbv delta [msp]. repeat split; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L1121852567.80  L17739154611.80 L18503762536.81 L193399549.80   L21280231801.81 L22627425881.80 L2385379261.80  L24220245736.81 L26900307901.80 L31100424793.80 L34629949619.80 L41837267645.80 L47333272048.107L47335380848.104L47337560651.80 L50458900460.78 L53135768676.78 L62559580861.80 L9492012665.81  L9964289474.80  00000C00L00Z00h01601?01H01V01_01h02102:02M02`03303K03T03]03k049S3sp04SPlo4SPal3mspS3sp03mspS3sp03msp1j2HjS3sp04SPlo3mspS3sp03msp1j2HjS3sp03mspS3sp03mspS3sp03msp1j2HjS3sp03mspS3sp03mspS3sp03mspS3sp03mspS3sp04SPlo4SPhi3mspS3sp04SPlo4SPhi3mspS3sp04SPlo4SPhi3mspS1R3sp05STKHI6HSTKHI3mspS3sp03mspS3sp03mspS3sp03msp1j2HjS3sp04SPhi3msp". (* [comment removed for export] *)
  #[using="HID AL IMG ASB HFREE HTP HIMGCS SPlo SPhi SPal STKLO HTOPlo HSTKHI"] Theorem err_tailA : ltac2:(CDefT.buildp (gd_tbl_A_main_fin ()) "Ppc,$8.Pmsg,(3.(4.&8.))Pbuf,$8.Pcap,$8.Pra,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pm,P,(4.&40.)(:.(4.&8.))Pmo,$2>.Ph,(27.$1=.VR,VHIA,)P,(0.(1.(2.$8.R1=.+97298.)(2.(3.(4.&8.))R1<.$51.))(1.(2.$8.R1=.+972;4.)(2.(3.(4.&8.))R1<.$52.)))P,(2<.$1=.VR,VHIA,R2.(16.(30.$8.$8.)(3:.$8.$8.R1<.R1;.)(5.(30.$8.$8.)))(5.$28.)R4.)P,(3;.$1=.VR,VHIA,R3.R4.)P,(2.$8.(3<.$1=.VR,VHIA,R4.)VTOP,)P,(2.$8.(3=.$1=.VR,VHIA,R5.)VSTKHI,)P,(11.(1:.(3>.$1=.VR,VHIA,R6.)$3?.)$40.)P,(11.(1:.(41.$1=.VR,VHIA,R7.)(42.=))$43.)P,(2.$44.(45.R9.)Vfs0,)P,(2.(:.$;.)(<.(=.R:.)(>.&40.+2.))(?.$;.(10.(>.&40.+2.))))P,(14.(>.&40.Vmsp,)R<.Vcan,Vtid,Vwp0,Vrp0,Vwp1,Vrp1,)P,(23.$1=.R=.Vmsp,$24.)P,(46.$1=.R>.(2:.VR,)Vmsp,)(47.$1=.(48.(1?.(20.R25.(>.&40.Vmsp,)(>.&40.+10800.)(>.&40.+63<:90.)R24.R23.R22.(>.&40.+2.)(>.&40.R27.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.(>.&40.=)(>.&40.=)(>.&40.=)(>.&40.=)R13.R12.R11.R10.)(21.&5.(4.&40.))(>.&40.R29.)(>.&20.=)(13.(4.&40.))R?.(22.$1=.))R>.)(53.R28.Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros * CASE HH HKmo HT HS HV HFR FS FD2 TM FR ST.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK. pose proof (u64_range sp0) as SPR.
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    pose proof (hd_rtc _ _ _ HID m (hm_rtc _ _ HIA _ _ _ _ HH)) as RTC.
    assert (WCS : crange (hcs asegs R HIA h) (msp - 4096) 4096).
    { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS; cbv delta [msp]; lia]. }
    unfold t_die.
    destruct CASE as [[-> ->] | [-> ->]].
    - (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKmo | apply (G1_steps (hcs asegs R HIA h)); exact RTC |].
      cbn beta. intros ms1 mo1 -> HK1 MM1.
      change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
      assert (HMSG : rdn asegs m (Z_to_bv 64 0x23360) 31 = Some msg_short).
      { transitivity (rdn asegs (fun _ => None) (Z_to_bv 64 0x23360) 31); [| vm_compute; reflexivity].
        apply rdn_agree; intros j Hj; rewrite u_small by lia. apply (tm_ro _ _ _ _ _ _ _ _ TM). lia. }
      eapply (A_fwrite_err1.fwrite_errA AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ASB (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
                (Z_to_bv 64 msp) mo1); rewrite ?unsigned_lit by lia;
        [ cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia | exact HK1 | exact WCS
        | unfold A_fwrite_err1.HLO, A_fwrite_err1.MLEN; apply (hcs_img _ _ HIA h); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | apply (tail_fw_err1 _ _ _ _ _ _ _ _ TM) | reflexivity | exact HMSG
        | rewrite (mo_mat_fds _ _ MM1); exact FD2 | unfold t_exit; apply t_emit_has_nil | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 [AG2 MU2 GR2 WM2 CL2] HK2 MM2.
      unfold A_fwrite_err1.RET. unfold mkR. norm_getr. fold mkR.
      lazymatch goal with |- srealizesJ _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
        change RR with (mkR (Z_to_bv 64 0x0972d4) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0' t1' t2' (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3' t4' t5' t6') end.
      ddestruct (fin_facts_of_fw m m2 h [(buf, cap)] ltac:(intros x N1 N2; apply AG2; rewrite ?unsigned_lit in * by lia; assumption)
                  ltac:(rewrite ?unsigned_lit in MU2 by lia; exact MU2) GR2 WM2 CL2 TM HH HT FR ST) as (HH2 & XM2 & XO2 & FR2 & ST2 & ATX2).
      eapply srzJ_conseq; [| cbn [W map]; apply t_emit_nil_eq; unfold t_exit; apply t_emit_has_nil].
      eapply (finA 2 [] buf cap [(buf, cap)]); try eassumption.
      all: first [ left; reflexivity | right; reflexivity | apply XO2 | rewrite (mo_mat_fs _ _ MM2), (mo_mat_fs _ _ MM1); exact FS ].
    - (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKmo | apply (G2_steps (hcs asegs R HIA h)); exact RTC |].
      cbn beta. intros ms1 mo1 -> HK1 MM1.
      change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
      assert (HMSG : rdn asegs m (Z_to_bv 64 0x16bd9) 31 = Some msg_overrun).
      { transitivity (rdn asegs (fun _ => None) (Z_to_bv 64 0x16bd9) 31); [| vm_compute; reflexivity].
        apply rdn_agree; intros j Hj; rewrite u_small by lia. apply (tm_ro _ _ _ _ _ _ _ _ TM). lia. }
      eapply (A_fwrite_err2.fwrite_errA AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ASB (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
                (Z_to_bv 64 msp) mo1); rewrite ?unsigned_lit by lia;
        [ cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia | exact HK1 | exact WCS
        | unfold A_fwrite_err2.HLO, A_fwrite_err2.MLEN; apply (hcs_img _ _ HIA h); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | apply (tail_fw_err2 _ _ _ _ _ _ _ _ TM) | reflexivity | exact HMSG
        | rewrite (mo_mat_fds _ _ MM1); exact FD2 | unfold t_exit; apply t_emit_has_nil | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 [AG2 MU2 GR2 WM2 CL2] HK2 MM2.
      unfold A_fwrite_err2.RET. unfold mkR. norm_getr. fold mkR.
      lazymatch goal with |- srealizesJ _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
        change RR with (mkR (Z_to_bv 64 0x0972d4) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0' t1' t2' (Z_to_bv 64 2) (Z_to_bv 64 buf)
                          a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3' t4' t5' t6') end.
      ddestruct (fin_facts_of_fw m m2 h [(buf, cap)] ltac:(intros x N1 N2; apply AG2; rewrite ?unsigned_lit in * by lia; assumption)
                  ltac:(rewrite ?unsigned_lit in MU2 by lia; exact MU2) GR2 WM2 CL2 TM HH HT FR ST) as (HH2 & XM2 & XO2 & FR2 & ST2 & ATX2).
      eapply srzJ_conseq; [| cbn [W map]; apply t_emit_nil_eq; unfold t_exit; apply t_emit_has_nil].
      eapply (finA 2 [] buf cap [(buf, cap)]); try eassumption.
      all: first [ left; reflexivity | right; reflexivity | apply XO2 | rewrite (mo_mat_fs _ _ MM2), (mo_mat_fs _ _ MM1); exact FS ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Fin.
