(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_copy P_mpi_shrink.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
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
Ltac2 gd_tbl_A_mpi_copy () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.copy_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "copy_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "copy_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.trim_i"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.zeros_above"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.copy_Rx"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Nat.mul"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_COPY"].


Definition A_WRAP_CALLOC_CP : Z := 0x69484.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMCPY_CP : Z := 0x67dbc.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMSET_CP : Z := 0x68258.    (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Definition copy_FR (d : Z) : Z := calls_FR 2 d.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29598275300.1000003S1d". (* [comment removed for export] *)
Lemma copy_FR_val : forall d, copy_FR d = 2 * (d + 3).
Proof. intros. unfold copy_FR, calls_FR, fr_charge. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition copy_PHI (dY : mpd) : Z := grow_PHI (md_n dY).

(* [comment removed for export] *)
Definition mpi_copy_stmtA_gen (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z)
    (Rr : mpd -> mpd -> list blk -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Ph,(0.O5.O4.O3.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdY,$7.Plo,$8.Pd,$8.P,(9.O5.O4.O3.R2:.R29.R28.R6.)P,(:.O5.O4.O3.R2;.R6.)P,(;.O5.R8.R2;.R6.)P,(<.(=.$>.(?.R7.)$10.))P,(;.O5.R:.R2=.R7.)P,(11.R9.R8.)P,(12.R:.R9.R8.(13.&40.R2<.))P,(14.(15.O4.)(16.$2.R30.(17.R2?.))R9.(18.R:.)+10.)P,P,(=.$>.(?.R;.)$19.)(14.(15.O4.)(16.$2.R32.(17.R31.))R;.(1:.R<.)(1;.+4.(1<.R<.)))P,(1=.O4.R32.R31.(13.&40.R2?.)(1>.O5.O4.O3.R33.)R=.)P,(1?.O5.R10.R<.(13.&40.R30.))P,(20.(21.O4.)R=.)P,(20.R>.(22.(22.(13.&40.R32.)+70.)(23.O4.)))P,(20.(13.&40.R33.)(1>.O5.O4.O3.R37.))P,(=.$8.(24.(13.&40.R34.)+10.)=)P,(=.(3.&40.)R33.(25.&40.(26.O4.)))P,(27.O5.R16.)P,(=.$8.(24.(13.&40.R38.)+2.)=)P,(28.O5.(29.O4.)(2:.O5.O4.O3.R3<.)R18.(18.R16.)+10.)P,(28.O5.(29.O4.)(2:.O5.O4.O3.R3=.)R19.(18.R16.)+10.)P,P,(=.$>.(?.R17.)$10.)(=.$2;.(2<.(1:.R18.)(1;.+4.(1<.R18.)))$2=.)P,(20.(2>.(2?.O5.O4.O3.R3?.)(30.R18.))$31.)P,(32.O4.(18.R1:.)+10.R17.)P,(20.(2>.(33.O5.O4.O3.R41.)(34.R18.))$35.)P,(=.(3.&40.)R36.(25.&40.(18.R1<.)))P,(=.(3.&40.)R36.(25.&40.(18.R1<.)))(36.O5.(37.O5.O4.O3.R41.R40.R3?.R3>.R3:.R39.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R22.R21.R44.R43.R42.R1>.A3.O1.R1=.R1>.R43.(30.R1=.)(34.R1;.)R1<.R20.R1?.)(38.(39.(3:.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(25.&40.O2.)R21.(3;.(3.&40.))R20.(3<.O5.))R1?.))")
(* [comment removed for export] *).

Definition mpi_copy_stmtA_x segs R HIA ENTRY := mpi_copy_stmtA_gen segs R HIA ENTRY copy_Rx.
Definition mpi_copy_stmtA segs R HIA ENTRY := mpi_copy_stmtA_gen segs R HIA ENTRY copy_R.

Lemma mpi_copy_stmtA_of_x : forall segs R HIA ENTRY, mpi_copy_stmtA_x segs R HIA ENTRY -> mpi_copy_stmtA segs R HIA ENTRY.
Proof.
  intros segs R HIA ENTRY HX. unfold mpi_copy_stmtA, mpi_copy_stmtA_x, mpi_copy_stmtA_gen in *.
  intros h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo dX dY lo d.
  intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26.
  eapply aevtS_mono.
  { exact (HX h LB LF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo dX dY lo d
             A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 A22 A23 A24 A25 A26). }
  cbv beta. intros c PO. unfold mpi_binop_postA in *.
  ddestruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & mo' & h' & LB' & dX' & r & PO).
  repeat match type of PO with _ /\ _ => destruct PO as [?H PO] end.
  deexists 20. repeat (split; [eassumption|]). exact (proj1 PO).
Qed.

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Hypothesis C24T : c24_transition.   (* [comment removed for export] *)
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_CP.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_CP.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_CP.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis RIMG : hl_img_lo L <= 0x10000 /\ 0x0f1000 <= hl_img_hi L.   (* [comment removed for export] *)
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X sgX nX pX : Z) (xs : list word) (padX : word) (ownX : limb_own)
            (Y sgY nY pY : Z) (ys : list word) (padY : word) (ownY : limb_own)
            (lo d : Z).
  Local Notation dX := (mkMPD X sgX nX pX xs padX ownX).
  Local Notation dY := (mkMPD Y sgY nY pY ys padY ownY).
  Hypothesis MAX : mpd_at asegs m LB dX.
  Hypothesis NST : ownX <> LStatic.
  Hypothesis MAY : mpd_at asegs m LB dY.
  Hypothesis NEQ : X <> Y.
  Hypothesis SEP : mpd_sep dX dY.
  Hypothesis CSEP : copy_sep dX dY lo (bv_unsigned sp).
  Hypothesis YCR : client_range L (LB ++ fdata LF) lo Y 16.
  Hypothesis YLCR : ownY = LHeap -> client_range L (LB ++ fdata LF) lo pY (4 * nY).
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 112 - arl_need_rt R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis YNZ : ownY = LStatic -> img_norz pY (4 * nY) = true.
  Hypothesis XUW : uw_obj R X 16 d.

  (* [comment removed for export] *)
  #[using="IMG"] Lemma hcs_img_cs_cp : forall hc, img_cs (hcs asegs R HIA hc).
  Proof.
    intros hc. ddestruct IMG as (G & LO & HI & GSB). eapply img_cs_of; [exact LO | exact HI | exact G | exact GSB |].
    intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA hc); assumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56765667309.68L59308579027.7000000900ES2sp1a2HaS2sp1a2Ha2H0". (* [comment removed for export] *)
  #[using="sp"] Lemma ro_addr_ge_cp : forall a : Z, 0x0f1000 <= a < 2^64 -> ro_addr asegs (wa a) = false.
  Proof.
    intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
    unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
    repeat match goal with
    | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
    | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
    | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
    end.
    repeat match goal with |- context [if ?c then _ else _] =>
      let b := fresh in destruct c eqn:b; [apply andb_prop in b; destruct b as [?%Z.leb_le ?%Z.leb_le]; first [reflexivity | exfalso; lia] | clear b] end.
    reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56765667309.68L59308579027.7000000900DS2sp1a2HaS2sp1a2Ha1H". (* [comment removed for export] *)
  #[using="sp"] Lemma ro_addr_low_cp : forall a : Z, 0 <= a < 0x10000 -> ro_addr asegs (wa a) = false.
  Proof.
    intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
    unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
    repeat match goal with
    | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
    | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
    | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
    end.
    repeat match goal with |- context [if ?c then _ else _] =>
      let b := fresh in destruct c eqn:b; [apply andb_prop in b; destruct b as [?%Z.leb_le ?%Z.leb_le]; first [reflexivity | exfalso; lia] | clear b] end.
    reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L10829342886.2L11611731062.2L36836628079.3L37477245982.3L54691089461.2L62509910829.800000600<00F00O00V00hS1n2HnS1n2HnS1P2P03HltS1P1n3HltS1P3HgeS1P1n2ws2HL2PB3Hge". (* [comment removed for export] *)
  #[using="sp"] Lemma static_limbs_low : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmm,P,(3.&40.)(5.(3.&8.))PP,$8.Pn,$8.Pws,(1.(3.&40.))P,(4:.$43.R4.R3.(4;.R1.))P,(=.$8.(3?.(40.(3.&40.)R2.))R3.)P,(20.+1.R4.)P,Pi,$8.P,(3=.(20.=R1.)(3>.R1.(1;.+4.R6.)))(=.$2;.(56.$43.(57.(2>.R8.R2.)))$2=.)(3=.(20.+10000.R7.)(20.(2>.R7.(1;.+4.R6.))+?1000.))")
(* [comment removed for export] *).
  Proof.
    intros mm P n ws HB HL Hn RO. dpose HB as (P0 & PB & _). rewrite u32s_length in PB. split.
    - destruct (Z_lt_ge_dec P 0x10000) as [Hlt|Hge]; [| clear - Hge; lia].
      exfalso. pose proof (RO 0 ltac:(clear - Hn; lia)) as R1. rewrite Z.add_0_r in R1.
      rewrite (ro_addr_low_cp P) in R1; [discriminate R1|]. clear - Hlt P0. lia.
    - destruct (Z_lt_ge_dec (P + 4 * n - 1) 0x0f1000) as [Hlt|Hge]; [clear - Hlt; lia|].
      exfalso. pose proof (RO (4 * n - 1) ltac:(clear - Hn; lia)) as R1.
      rewrite (ro_addr_ge_cp (P + (4 * n - 1))) in R1; [discriminate R1|]. clear - Hge PB HL Hn P0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.


(* [comment removed for export] *)

(* [comment removed for export] *)
