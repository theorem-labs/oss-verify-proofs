(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev SysNodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib RestrictRun NodesA SymDriveA SymDriveAX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_base A_exit_lib A_exit_defs A_exit_front1 A_unreg_globals A_exit A_stdio_defs A_stdio_write A_stdio_call A_fwrite_oom.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance Lib.PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
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
Ltac2 gd_tbl_A_oomtail () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_oom"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].


(* [comment removed for export] *)
Lemma oom_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x156e6) 19%nat = Some msg_oom.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ro_addr_high : forall x, (AIMG_HI <= x < 2^64)%Z -> ro_addr RSEGS (wa x) = false.
Proof.
  intros x Hx. unfold ro_addr. unfold AIMG_HI in Hx.
  destruct (find_segment RSEGS (bv_unsigned (wa x)) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. rewrite wa_unsigned in E by lia.
  pose proof (find_segment_cov asegs asegs x 1 seg E ltac:(auto) 0 ltac:(cbn; lia)) as C.
  rewrite Z.add_0_r in C. apply asegs_segcov in C. unfold AIMG_LO, AIMG_HI in C. lia.
Qed.

(* [comment removed for export] *)
Lemma asan_rtc_munch_fw : ltac2:(CDefT.buildp (gd_tbl_A_oomtail ()) "Plo,$0.Phi,$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))P,(3.(4.(5.$0.$0.)(6.$0.$0.R4.R3.)(4.(5.$0.$0.)(6.$0.$0.+?:488.+?:570.)(7.(5.$0.$0.))))R2.R1.)P,(8.+65?000.R5.)P,(9.R4.)(9.R4.)")
(* [comment removed for export] *).
Proof.
  intros lo hi m m' MU LO [RC PR]. split.
  - apply Forall_forall. intros [[a n] v] Hin.
    pose proof (proj1 (Forall_forall _ _) RC _ Hin) as H. unfold rtc_holds in *.
    assert (B : ((a + 8 <= 0x0fa488 \/ 0x0fa570 <= a) /\ 0 <= a /\ a + 8 <= 0x65f000)%Z).
    { unfold rtc_cells in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; subst; cbn; lia |]). destruct Hin. }
    eapply ro_cells_transport; [exact H | exact MU |].
    assert (SZ : (Z.of_nat (cells_size [rtc_mkcell n v]) <= 8)%Z) by (destruct n as [|[|[|[|[|n]]]]]; cbn; lia).
    pose proof (Nat2Z.is_nonneg (cells_size [rtc_mkcell n v])).
    cbn [disjoint_from]. split; [lia | split; [lia | exact I]].
  - intros a Ha. rewrite (MU (wa a)); [apply PR; exact Ha|].
    unfold rtc_prist, rtc_pristine, AGLOB_LO, AGLOB_HI in Ha.
    assert (B : ((0x0f1520 <= a < 0x0f5cc0) \/ (0x0f5df0 <= a < 0x0f6b50) \/ (0x0fa400 <= a < 0x0fa460) \/ (0x0fa780 <= a < 0x106340))%Z).   (* [comment removed for export] *)
    { repeat (apply Exists_cons in Ha; destruct Ha as [Ha | Ha]; [cbn in Ha; lia|]). inversion Ha. }
    rewrite wa_unsigned by lia. cbn. repeat split; lia.
Qed.

(* [comment removed for export] *)
Record oom_memA (sp0 : word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word) : Prop := OOM_MEM {
  om_fw    : fw_memA sp0 M can;
  om_stk   : stk RSEGS M (bv_unsigned sp0 - 4096) (bv_unsigned sp0);
  om_mi    : mem_inv RSEGS M;
  om_tid   : (0 < tid < 2^31)%Z;
  om_lock  : rw_cells RSEGS M 0x65cd00 [C4 (Z_to_bv 64 0)];
  om_mtid  : rw_cells RSEGS M 0x63c9e8 [C4 (Z_to_bv 64 tid)];
  om_atexit : exists jp jq jf, atexit_cells false M (Z_to_bv 8 0) jp jq jf;
  om_nl    : ro_cells RSEGS M 0x65cd23 [C1 (Z_to_bv 8 0)];
  om_comp  : rw_cells RSEGS M 0x106390 [C1 (Z_to_bv 8 0)];
  om_rtc   : asan_rtc M;
  om_mapped : mapped M 0x7fffa000 0x800d3000;
  om_glob  : stdio_globals M;
  om_in    : file_clean M 0x0fa668 wp0 rp0;
  om_out   : file_clean M 0x0fa578 wp1 rp1
}.

Section OomTail.
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
  Hypothesis K_mat : ltac2:(CDefT.buildp (gd_tbl_A_oomtail ()) "Pmo,$:.Pacc,(;.(5.(1.&40.)$<.))P,A1.VKI,R2.P,(=.VAL,VCS,R2.)(>.$:.Lmo',$:.(?.(10.(2.$:.)(11.R5.R4.)(12.$:.R1.))(?.A1.VKI,R1.(13.R5.R1.))))")
(* [comment removed for export] *).
  Hypothesis K_vmonly : ltac2:(CDefT.buildp (gd_tbl_A_oomtail ()) "Pmo,$:.Pmo',$:.P,A1.VKI,R2.P,(10.$14.(15.R2.)(15.R3.))P,(10.(;.(5.(1.&40.)(1.&40.)))(16.R3.)(16.R4.))P,(10.(;.(1.&40.))(17.R4.)(17.R5.))P,(10.(2.(1.&40.))(18.R5.)(18.R6.))A1.VKI,R6.")
(* [comment removed for export] *).

  Variable sp0 : word.
  Variable model : Model.
  Hypothesis SPlo : (0x7fff7f000000 + 4096 <= bv_unsigned sp0)%Z.
  Hypothesis SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis SPal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Hypothesis HKI : KI model.
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Hypothesis WCS : crange CS (bv_unsigned sp0 - 4096) 4096.
  Hypothesis MCS : crange CS 0x156c0 147.

  Variables (R : bvmap 5 word) (M : word -> option byte) (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Hypothesis G1 : getr R 1 = Z_to_bv 64 0x097368.
  Hypothesis G2 : getr R 2 = sp0.
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x63ca90.
  Hypothesis G10 : getr R 10 = Z_to_bv 64 0x156e6.
  Hypothesis G11 : getr R 11 = Z_to_bv 64 19.
  Hypothesis G12 : getr R 12 = Z_to_bv 64 1.
  Hypothesis G13 : getr R 13 = Z_to_bv 64 0x0fa488.
  Hypothesis TM : oom_memA sp0 M can tid wp0 rp0 wp1 rp1.

  (* [comment removed for export] *)
  #[using="Type"] Lemma call_exit2 : ltac2:(CDefT.buildp (gd_tbl_A_oomtail ()) "Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pm,P,(1.&40.)(2.(1.&8.))(19.$1:.VAL,VCS,Lms',$1;.(10.$1;.R1.(1<.(1=.(1>.&40.+97370.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(1>.&40.+2.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)(1?.&5.(1.&40.))(1>.&40.+>11:8.)(1>.&20.=)(20.(1.&40.))R2.(21.$1:.)))(1<.(1=.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)(1?.&5.(1.&40.))(1>.&40.+97368.)(1>.&20.=)(20.(1.&40.))R1.(21.$1:.)))")
(* [comment removed for export] *).
  Proof. intros. zstep. zstep. apply evtA_done. reflexivity. Qed.

  #[using="AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly sp0 SPlo SPhi SPal HKI Hfd2 WCS MCS can tid wp0 rp0 wp1 rp1 G1 G2 G3 G4 G10 G11 G12 G13 TM"] Theorem oom_tailA : ltac2:(CDefT.buildp (gd_tbl_A_oomtail ()) "(22.$1:.(23.(24.$25.VR,(1>.&40.+58714.)VM,(21.$1:.))Vmodel,)(26.$27.(28.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    destruct TM as [FWM STK MI TID LOCK MTID ATEXIT NL COMP RTC MAPPED GLOB FIN FOUT].
    pose proof FWM as FWM'. destruct FWM' as [_ RO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    assert (HMSG : rdn RSEGS M (Z_to_bv 64 0x156e6) 19 = Some msg_oom).
    { rewrite <- oom_img. apply rdn_agree. intros j Hj. rewrite u_small by lia. apply RO. lia. }
    unfold t_die.
    eapply (fwrite_errA AL CS KI IMG ASB K_halted K_mat K_vmonly sp0 model SPlo SPhi SPal HKI WCS MCS R M can
              G1 G2 G3 G4 G10 G11 G12 G13 FWM msg_oom eq_refl HMSG Hfd2).
    { apply t_emit_has_nil. }
    intros t0 t1 t2 b0 b1 b2 b3 b4 b5 b6 b7 t3 t4 t5 t6 M' mo' POST HKI' MM'.
    (* [comment removed for export] *)
    eapply (rz_evtA_K RSEGS AL CS KI K_halted K_mat); [exact HKI' | apply call_exit2 | ].
    cbn beta. intros ms2 mo2 -> HKI2 MM2.
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pc Mx rom).
    (* [comment removed for export] *)
    destruct POST as [AG MU GR WM CLEAN].
    assert (DJ : forall a n, (0 <= a)%Z -> (a + n <= 0x65f000)%Z -> (a + n <= 0x0fa488 \/ 0x0fa570 <= a)%Z ->
                 disjoint_from [((bv_unsigned sp0 - 4096)%Z, bv_unsigned sp0); (0x0fa488%Z, 0x0fa570%Z)] a n).
    { intros a n Ha Hn Hd. cbn. repeat split; lia. }
    assert (OUT : forall x : word, (bv_unsigned x + 8 <= bv_unsigned sp0 - 4096 \/ True)%Z ->
                  (bv_unsigned x < 0x65f000)%Z -> (bv_unsigned x + 1 <= 0x0fa488 \/ 0x0fa570 <= bv_unsigned x)%Z -> M' x = M x).
    { intros x _ H1 H2. apply AG; lia. }
    assert (RDN : forall (a : Z) n bs, (0 <= a)%Z -> (a + Z.of_nat n <= 0x65f000)%Z -> (a + Z.of_nat n <= 0x0fa488 \/ 0x0fa570 <= a)%Z ->
                  rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Ha Hn Hd H. rewrite <- H. apply rdn_agree. intros j Hj. rewrite (u_small a) by lia. apply AG; rewrite u_small by lia; lia. }
    assert (MI' : mem_inv RSEGS M').
    { intros a b Hb. pose proof (u64_range a).
      destruct (M a) as [bb0|] eqn:E0; [exact (MI a bb0 E0)|].
      destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp0 - 4096)).
      - destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa488); [| destruct (Z_lt_le_dec (bv_unsigned a) 0x0fa570)].
        1,3: exfalso; rewrite AG in Hb by lia; congruence.
        (* [comment removed for export] *)
        rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)).
        eapply wview_not_ro with (m := M).
        + pose proof (store_ok_data M (Z_to_bv 64 (bv_unsigned a)) 1 ltac:(rewrite u_small by lia; lia) ltac:(rewrite u_small by lia; cbn; lia)) as SO.
          pose proof (store_ok_wview RSEGS M _ 1 0 SO ltac:(lia)) as WV. rewrite u_small in WV by lia. rewrite Z.add_0_r in WV. exact WV.
        + unfold wa. rewrite Z_to_bv_bv_unsigned. exact E0.
      - destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp0)).
        + rewrite <- (Z_to_bv_bv_unsigned a). change (Z_to_bv 64 (bv_unsigned a)) with (wa (bv_unsigned a)). apply ro_addr_high. unfold AIMG_HI. lia.
        + exfalso. rewrite AG in Hb by lia. congruence. }
    eapply srzJ_conseq.
    { eapply (ref_exitA AL CS KI IMG ALWF CSOK ASB IMGCS K_halted K_mat K_vmonly (bv_unsigned sp0) ltac:(lia) ltac:(lia)
                ltac:(intros z Hz; apply WCS; lia) _ M' mo2 (Z_to_bv 64 2) []); [| exact HKI2].
      dexists tid, wp0, rp0, (Z_to_bv 64 0x65d198), (Z_to_bv 64 0). split.
      - split.
        + unfold mkR. cbn. symmetry. apply Z_to_bv_bv_unsigned.
        + reflexivity.
        + reflexivity.
        + exact SPal.
        + eapply stk_transport; [eapply (proj2 (stk_split RSEGS M (bv_unsigned sp0 - 4096) (bv_unsigned sp0 - 320) (bv_unsigned sp0) STK ltac:(lia))) | exact MU | exact WM |].
          intros x Hx. right. ddestruct STK as (_ & _ & S3). destruct (S3 x ltac:(lia)) as [_ (b & Hb)].
          unfold mrd in Hb. destruct (M (wa x)) as [bb0|] eqn:E0.
          * destruct (M' (wa x)) as [bb1|] eqn:E1; [exists bb1; reflexivity|]. exfalso. apply (GR (wa x)); [congruence | exact E1].
          * exfalso. pose proof (seg_rom_high x ltac:(unfold AIMG_HI; lia)) as SR. change asegs with RSEGS in SR. cbn in Hb. congruence.
        + exact MI'.
        + exact TID.
        + eapply rw_cells_transport; [exact LOCK | exact MU | exact WM | apply DJ; cbn; lia].
        + eapply rw_cells_transport; [exact MTID | exact MU | exact WM | apply DJ; cbn; lia].
        + ddestruct ATEXIT as (jp & jq & jf & AT). dexists false, (Z_to_bv 8 0), jp, jq, jf. split; [| intros HB; discriminate HB].
          unfold atexit_cells in *. eapply rw_cells_transport; [exact AT | exact MU | exact WM | apply DJ; cbn; lia].
        + eapply ro_cells_transport; [exact NL | exact MU | apply DJ; cbn; lia].
        + eapply rw_cells_transport; [exact COMP | exact MU | exact WM | apply DJ; cbn; lia].
        + eapply asan_rtc_munch_fw; [exact MU | lia | exact RTC].
        + eapply mapped_transport; [exact MAPPED | exact MU | unfold AIMG_HI; lia | lia |]. intros x Hx. left. cbn. lia.
        + ddestruct GLOB as (Q1 & Q2 & Q3 & Q4 & Q5). unfold stdio_globals.
          repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]).
        + ddestruct FIN as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
          repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]).
        + exact CLEAN.
      - left. split; [reflexivity|]. dexists wp1, rp1.
        ddestruct FOUT as (Q1 & Q2 & Q3 & Q4 & Q5). unfold file_clean.
        repeat split; (eapply RDN; [lia | cbn; lia | cbn; lia | assumption]). }
    (* [comment removed for export] *)
    cbn [W map]. rewrite (mo_mat_fs _ _ MM2), (mo_mat_fs _ _ MM').
    replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity).
    apply t_emit_nil_eq. unfold t_exit. apply t_emit_has_nil.
  Qed.
End OomTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
