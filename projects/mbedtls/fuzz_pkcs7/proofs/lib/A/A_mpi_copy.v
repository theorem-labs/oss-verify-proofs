(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_copy P_mpi_shrink.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_zeroize_and_free.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import TacA.   (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_copy () : Init.string Init.list := ["OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "OSSVerify.KrLib.P.P_mpi_copy.copy_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.LibA.ARt.havol"; "copy_PHI"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.hfr"; "copy_FR"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.A.AImg.asegs"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.max"; "OSSVerify.KrLib.P.P_mpi_copy.trim_i"; "OSSVerify.KrLib.P.P_mpi_copy.zeros_above"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.mpd_keep"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.Spec.MpiVal.mpd_out"; "OSSVerify.KrLib.Spec.MpiVal.mpd_blk"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.P.P_mpi_copy.copy_Rx"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "OSSVerify.KrLib.Lib.Cells.CB"; "Corelib.Init.Nat.mul"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_COPY"].


Definition A_WRAP_CALLOC_CP : Z := 0x68f10.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMCPY_CP : Z := 0x67848.    (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ASAN_MEMSET_CP : Z := 0x67ce4.    (* [comment removed for export] *) (* [comment removed for export] *)

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
  Hypothesis RIMG : hl_img_lo L <= 0x10000 /\ 0x0ed000 <= hl_img_hi L.   (* [comment removed for export] *)
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

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -80)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHY := (Z_to_bv 64 (Z.shiftr Y 3)).
  (* [comment removed for export] *)
  Notation FRAME := ([C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).
  Notation POST mo := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                         (copy_Rx dY dX LB) (copy_PHI dY) (copy_FR d) lo m mo).

  Ltac basic_facts hc LBc mm HH TOPc :=
    pose proof (hcs_ok asegs R HIA hc) as CSOK; pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF'; pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO; pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA hc) as SCS0; pose proof (hm_top asegs R HIA hc LBc LF mm HH) as HTOP;
    pose proof (arl_need_rt_amem R) as NRA; pose proof (arl_need_rt_malloc R) as NRM; pose proof (arl_need_rt_free R) as NRF;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR;
    assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
    assert (SCS : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L30309475896.9L45370438041.9L60453088131.9L63312638695.9L819727256.9  L9364571742.9 00000B00M00_01101<01NS1X1Y2nY3NRY2XB2YBS1X1Y2XB2YBS1X2nX1Y3NRX2XB2YBS1X2nX1Y3NRX2XB2YBS1X1Y2XB2YBS1X1Y2nY3NRY2XB2YB". (* [comment removed for export] *)
  #[using="LB m pX padX ownX pY padY ownY MAX MAY NEQ SEP"] Lemma facts : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "(3=.(=.$8.(24.VX,+8.)=)(3=.(3>.=VX,)(3=.(=.$8.(3?.(40.(3.&40.)Vxs,))VnX,)(3=.(3=.(20.=VnX,)(20.VnX,+2710.))(3=.(41.(=.$8.VsgX,+1.)(=.$8.VsgX,-1.))(3=.(=.$8.(24.VY,+8.)=)(3=.(3>.=VY,)(3=.(=.$8.(3?.(40.(3.&40.)Vys,))VnY,)(3=.(3=.(20.=VnY,)(20.VnY,+2710.))(3=.(41.(=.$8.VsgY,+1.)(=.$8.VsgY,-1.))(3=.(20.(2>.VX,+10.)(42.+2.+40.))(3=.(20.(2>.VY,+10.)(42.+2.+40.))(41.(20.(2>.VX,+10.)VY,)(20.(2>.VY,+10.)VX,))))))))))))))")
(* [comment removed for export] *).
  Proof.
    ddestruct MAX as [[CHX (XAL & X0 & LENX & NRX & _)] SGX]. ddestruct MAY as [[CHY (YAL & Y0 & LENY & NRY & _)] SGY].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *. unfold MPI_MAX_LIMBS in NRX, NRY.
    pose proof (rw_cells_bound _ _ _ _ CHX) as XB. pose proof (rw_cells_bound _ _ _ _ CHY) as YB.
    unfold mpi_cells in XB, YB. cbn [cells_size csize Nat.add] in XB, YB.
    destruct SEP as [E|SEP']; [exfalso; apply NEQ; injection E; auto|]. cbn [md_addr] in SEP'.
    repeat split; try assumption; clear - XB YB SEP' NRX NRY; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG"] Lemma hcs_img_cs_cp : forall hc, img_cs (hcs asegs R HIA hc).
  Proof.
    intros hc. ddestruct IMG as (G & LO & HI & GSB). eapply img_cs_of; [exact LO | exact HI | exact G | exact GSB |].
    intros a n H1 H2 H3 H4. eapply (hcs_img asegs R HIA hc); assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG LB sp m X sgX nX pX xs padX ownX Y sgY ys padY lo MAY SEP CSEP YLCR YNZ"] Lemma opy_at : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Phc,(0.$43.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))P,(9.$43.VR,VHIA,R3.R2.VLF,R1.)P,P,(=.$>.VownY,$19.)(44.(45.$8.$8.)(46.$8.$8.VpY,(1;.+4.VnY,))R4.)P,(<.(=.$>.VownY,$47.))(28.$43.(29.VR,)(2:.$43.VR,VHIA,R6.)R4.VpY,(1;.+4.VnY,))")
(* [comment removed for export] *).
  Proof.
    intros hc LBc mc HH HIN ON. destruct ownY; [exfalso; exact (ON eq_refl)| |].
    - eapply hm_aobj_block; [exact HH| exact (HIN eq_refl)].
    - eapply (aobj_img asegs AL); [apply hcs_img_cs_cp| eapply (hm_img_shadow asegs R HIA); exact HH| exact (YNZ eq_refl)].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L1461017411.3 L15175825515.1L17030833117.4L63904838234.500000:00>00K00ZS2nY2ys2LYS2pYS2nY2pY2ys2LYS2nY2ys2LY1i2Hi". (* [comment removed for export] *)
  #[using="LB LF sp m X sgX nX pX xs padX ownX Y sgY padY lo MAY SEP CSEP YLCR YNZ"] Lemma pby_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "PLB0,(1.$2.)PLF0,(1.$2.)PSPx,$8.PTOPx,$8.PW,(1.$48.)PmA,P,(3.&40.)(5.(3.&8.))PmB,P,(3.&40.)(5.(3.&8.))P,(49.$43.VR,R7.R6.R5.(21.VR,)R4.R3.R2.R1.)P,(4:.$43.R3.VpY,(4;.Vys,))P,(27.$43.R4.)P,(27.$43.R4.)P,P,(=.$>.VownY,$19.)(44.(45.$8.$8.)(46.$8.$8.VpY,(1;.+4.VnY,))R<.)P,(<.(=.$>.VownY,$47.))P,(4<.R9.VpY,(1;.+4.VnY,))(4:.$43.R8.VpY,(4;.Vys,))")
(* [comment removed for export] *).
  Proof.
    intros LB0 LF0 SPx TOPx W mA mB HP HB MIA MIB HIN ON HD.
    dpose MAY as [[_ (_ & _ & LY & _ & OY)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LY, OY.
    destruct ownY; [exfalso; exact (ON eq_refl)| |].
    - eapply (presA_bytes_at asegs R); [exact HP| exact HB| |]; rewrite u32s_length.
      + eapply client_range_block; [apply in_app_iff; left; exact (HIN eq_refl)| clear; lia| clear - LY; lia].
      + replace (Z.of_nat (4 * length ys)) with (4 * nY) by (clear - LY; lia). exact HD.
    - ddestruct OY as (_ & _ & _ & _ & RO). eapply static_limbs_any_mem; [exact MIA| exact MIB| exact HB|].
      rewrite u32s_length. intros i Hi. apply RO. clear - Hi LY. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L15302269400.114L22446743512.114L24387680389.113L29428324939.5  L34705680216.114L35653441506.7  L3949578456.114 L41843875160.114L51454941784.114L5699067096.114 L58591023192.114L59506921496.112L60098763854.3  L67280348888.114L7632799155.114 Q15641568614.113Q18364007270.113Q21877861637.113Q24387680389.113Q27583156582.113Q27904925317.113Q30413285893.113Q31269115878.113Q32653586022.113Q33915848709.113Q36423571333.113Q3832210565.113 Q39941338501.113Q41154176102.113Q44650594790.113Q51233520870.113Q59254978790.113Q59840699110.113Q66523986693.113Q9840924165.113 00000400800O00a00e01?01C01G01K01O01S01W01a01e01i02002702J02]02d03703J03Q03X03k04>04Q04d04k05205905@05G05Z05mS2spS2spS1R5NEEDR2sp2lo3SLO3SPRS1R2lo3LOS3ALO3ACPS2spS1R3HIA2sp2lo2hc4TOPc4HTOPS2spS2spS2spS2spS2spS2spS1R2lo3LOSS2spS2spS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLOS2sp2loS2sp2loS2sp2loS2sp2loS2sp2loS1R5NEEDR2sp2lo3SLOS1R5NEEDR2sp2lo3SLO". (* [comment removed for export] *)
  #[using="IMG NEEDR LOS SLO"] Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Phc,(0.$43.VR,VHIA,)PLBc,(1.$2.)Pmm,P,(3.&40.)(5.(3.&8.))Pr,$8.Pxra,(3.&40.)Pxs0,(3.&40.)Pxs1,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs4,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,R1<.R1;.VLF,R1:.)P,(20.(13.&40.Vsp,)(1>.$43.VR,VHIA,R1=.))P,(4=.$43.R1<.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R1=.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R1>.)(52.$43.(29.VR,)(2:.$43.VR,VHIA,R21.)Lms',$53.(54.(3.&40.)Lx5,(3.&40.)(54.(3.&40.)Lx6,(3.&40.)(54.(3.&40.)Lx7,(3.&40.)(54.(3.&40.)La1',(3.&40.)(54.(3.&40.)La2',(3.&40.)(54.(3.&40.)La3',(3.&40.)(54.(3.&40.)La4',(3.&40.)(54.(3.&40.)La5',(3.&40.)(54.(3.&40.)La6',(3.&40.)(54.(3.&40.)La7',(3.&40.)(54.(3.&40.)Lx28,(3.&40.)(54.(3.&40.)Lx29,(3.&40.)(54.(3.&40.)Lx30,(3.&40.)(54.(3.&40.)Lx31,(3.&40.)(3=.(=.$53.R?.(39.(3:.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(25.&40.R2=.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R2>.(3<.$43.)))(1?.$43.R2>.Vlo,(13.&40.Vsp,)))))))))))))))))(39.(3:.R1=.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R13.R12.R11.R1<.R1;.(25.&40.R1>.)R10.R?.R>.R=.R<.R;.R:.R1:.R19.R18.R17.R16.R15.R14.Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(25.&40.+9;?<8.)Vfc,(3;.(3.&40.))R1?.(3<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc FR ST MI. basic_facts hc LBc mm HH TOPc.
    (* [comment removed for export] *)
    do 10 zstep.
    zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep.
    finish.
    all: match goal with |- ?g => idtac "EPI-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L56765667309.68L59308579027.7000000900ES2sp1a2HaS2sp1a2Ha2H0". (* [comment removed for export] *)
  #[using="sp"] Lemma ro_addr_ge_cp : forall a : Z, 0x0ed000 <= a < 2^64 -> ro_addr asegs (wa a) = false.
  Proof.
    intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
    unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. cbn [find_segment].
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
    unfold asegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments. cbn [find_segment].
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
  #[using="sp"] Lemma static_limbs_low : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmm,P,(3.&40.)(5.(3.&8.))PP,$8.Pn,$8.Pws,(1.(3.&40.))P,(4:.$43.R4.R3.(4;.R1.))P,(=.$8.(3?.(40.(3.&40.)R2.))R3.)P,(20.+1.R4.)P,Pi,$8.P,(3=.(20.=R1.)(3>.R1.(1;.+4.R6.)))(=.$2;.(56.$43.(57.(2>.R8.R2.)))$2=.)(3=.(20.+10000.R7.)(20.(2>.R7.(1;.+4.R6.))+>=000.))")
(* [comment removed for export] *).
  Proof.
    intros mm P n ws HB HL Hn RO. dpose HB as (P0 & PB & _). rewrite u32s_length in PB. split.
    - destruct (Z_lt_ge_dec P 0x10000) as [Hlt|Hge]; [| clear - Hge; lia].
      exfalso. pose proof (RO 0 ltac:(clear - Hn; lia)) as R1. rewrite Z.add_0_r in R1.
      rewrite (ro_addr_low_cp P) in R1; [discriminate R1|]. clear - Hlt P0. lia.
    - destruct (Z_lt_ge_dec (P + 4 * n - 1) 0x0ed000) as [Hlt|Hge]; [clear - Hlt; lia|].
      exfalso. pose proof (RO (4 * n - 1) ltac:(clear - Hn; lia)) as R1.
      rewrite (ro_addr_ge_cp (P + (4 * n - 1))) in R1; [discriminate R1|]. clear - Hge PB HL Hn P0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0280@C17025492443.168C25179474043.169C25179474043.170D13186458071.173K14981916448.172K60573057312.168K61251806371.172K6288013615.169 K6288013615.170 L10718992232.12 L1120085281.143 L11498582452.16 L11500183646.3  L11500585752.8  L1222472026.7   L1222472026.8   L12880976633.3  L1335938295.2   L14071871255.3  L14968616261.4  L14969017859.7  L14970763359.5  L15175825515.1  L15302269400.162L21929277458.9  L22446743512.162L22683776779.11 L23100341967.143L23144025037.4  L24385597572.166L27040582980.7  L27842804030.3  L29428324939.5  L29443285534.3  L32332382178.8  L3253508485.5   L32791889488.9  L34263059663.14 L34443820891.16 L34445823479.10 L34446468261.4  L34705680216.162L35653441506.7  L3641572268.13  L37035366229.2  L39172636981.0  L3949578456.162 L41084420269.1  L41523417557.7  L41843875160.162L41993492402.4  L44169409993.12 L44169409993.9  L45703525153.0  L46732241046.2  L48487841484.1  L48491422268.16 L48493695120.7  L51454941784.162L5259801613.142 L5699067096.162 L58059560066.11 L58591023192.162L59504824379.165L59579796581.1  L60098763854.3  L60576273221.2  L61237649950.4  L61646496682.6  L61764918690.7  L6276868363.3   L63614613648.8  L63614701339.5  L64957412299.2  L66253248513.142L67280348888.162L68268214829.8  L7632799155.162 N21806751459.169N37104593031.169O17025492443.168O25179474043.169O25179474043.170O26567557383.172O28520546523.168O32791873655.172O40272236209.171O45570296526.172O48965075207.172P14065054122.172P27840184195.171P29429130403.172P42008695055.168P60573057312.168P6288013615.169 P6288013615.170 Q12370813529.148Q14485421028.148Q15647878503.166Q17207432298.147Q18361895783.166Q21892523268.166Q24363954815.147Q24363994560.148Q24385597572.166Q25098505664.148Q26056220419.153Q27597822311.166Q27911231108.166Q30402748932.166Q30877736124.173Q31258583015.166Q32659924583.166Q33913700356.166Q36438237060.166Q37625261960.147Q38248387216.173Q3834260612.166 Q39935065476.166Q41074460176.173Q41139448935.166Q43879899724.173Q44652743143.166Q45132659991.148Q47177596183.148Q50107086626.148Q51223049447.166Q54202528384.147Q5485126037.147 Q5485174314.148 Q59244540135.166Q59830194919.166Q6143569392.148 Q66534486788.166Q67375263592.147Q9838812676.166 00000100200300400c00d01Y01Z01[01\02502J02K02L02M02N02W02X02Y02Z02o03003403V03W04904:04S04_05`05a05b06406506606G06H06I06[06\06]07?07Y07Z07[07\08>08C08[09=09>09?09@09A09H09I09]09^0:@0:_0;A0;_0<A0<c0<f0=00=10=20=@0=A0=B0=C0=S0=T0>g0?I0?d0@F0@m0AT0AU0AV0AW0AX0AY0AZ0A[0A\0A]0Bf0Bg0Bh0Cg0Ch0Ci0Cj0DM0Dm0EN0Eb0FC0G60GJ0G^0HQ0HR0IU0J60Ji0K\0LH0Li0MJ0N=0O00OD0Ob0PU0QH0Qg0RH0Ri0SJ0SK0SL0S`0TA0TU0Ti0U=0U^0V?0VS0WF0WZ0XMFFFFS2sp2xs2nY2pY2ys2lo1i3xs02Hi2C53PYB2LI3LIy4LENYFS2xs2nY2pY2ys1i2n'3pX'3xs02Hi3Hin3SY23PYB2LI3LIy4LENYFFFS2sp1X2xs1Y2pY2ys3xs03PYBS1R2sp2lo3SLO3NRA3SPRFFFFS2nY1i2HiFFFS2sp2nY2pY2lo1i2Hi2C5FS2pYS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyFS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyFS2sp1X2xs1Y2pY2ys3xs03PYBS2nY2pY1i2HiS1R5NEEDR2sp1X2xs1Y2nY2pY2ys2lo3SLO1i3xs02Hi3SPR2X02Y03PYB2LI3LIyFFS1R2lo3LOS3ALO3ACPFFS2nY2ys1i2Hi4LENYFFS1R3HIA2sp2hc4TOPcFFS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS1R3HIA2sp2lo2hc4TOPc4HTOPFFSS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS3pX'S2nY1i2n'3xs02Hi3Hin3LL0S2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyFFFSS2sp2loFS2sp2nY1i2Hi3SPR3NRYFS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS2sp1X2xs1Y2pY2ys3xs02X02XB3PYBS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS1R2lo3LOS1i2n'3pX'3Hin3ALO2BCS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS1iS1R2lo3LOSFFS1i2n'3pX'3HinFFFS2nY2pY1i2Hi3Y47FS1R5NEEDR2sp1X2xs1Y2nY2pY2ys2lo3LOS3SLO1i2n'3pX'3xs02Hi3Hin3ALO3SPR2X02Y02B02BC3PYBS2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS2nY2pY1i2n'3pX'2Hi3Hin3SY2S2sp1X2xs1Y2pY2ys1i3xs03PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIy3x151CS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIy3x151CFFFFFFFFFS1R5NEEDR2sp2xs2nY2pY2ys2lo3LOS3SLO1i2n'3pX'3xs02Hi3Hin3ALO2BC3PYB2LI3LIyFFS1R2sp2xs2nY2pY2ys2lo3LOS1i2n'3pX'3xs02Hi3Hin3ALO2BC3PYB2LI3LIyFFFS2sp1X2xs1Y2pY2ys3xs03XAL2X02Y03PYBS2sp1X2xs1Y2pY2ys3xs03YAL2Y03PYBS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS1X2xs2pY2ys3xs03PYBS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS2xs1Y2pY2ys3xs03PYBS2xs1Y2pY2ys3xs03PYBS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyFS1R5NEEDR2sp2xs2nY2pY2ys2lo3LOS3SLO1i3xs02Hi3ALO3ACP3SPR3PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS2xs2nY2pY2ys1i2n'3pX'3xs02Hi3Hin3PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS1X2xs2pY2ys3xs03PYBS2xs2pY2ys2lo1i3xs03PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS2xs2pY2ys1i3pX'3xs03PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyFFS2xs1Y2pY2ys3xs03PYBS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS2xs1Y2pY2ys3xs03PYBS1X2xs2pY2ys3xs03PYBS1X2xs2pY2ys3xs03PYBS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS2sp2xs2pY2ys2lo1i3xs03PYB2LI3LIyS1X2xs2pY2ys3xs03PYBS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIyS2xs1Y2pY2ys3xs03PYBS1R5NEEDR2sp2xs2nY2pY2ys2lo3SLO1i3xs02Hi3PYB2LI3LIy". (* [comment removed for export] *)
  #[using="IMG AMC NEEDR LB m sgX nX pX xs ownX MAX MAY NEQ SEP LOS SLO"] Lemma final_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Phc,(0.$43.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.Pn',$8.PpX',$8.Pxs0,(1.(3.&40.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,R1;.R1:.VLF,R19.)P,(20.(13.&40.Vsp,)(1>.$43.VR,VHIA,R1<.))P,(3=.(20.+1.R1:.)(20.R1:.VnY,))P,(20.R1;.R1:.)P,(20.R1;.+2710.)P,(4=.$43.R1>.VX,(58.R1;.(25.&40.VsgY,)R1<.VpadX,))P,(44.(45.$8.$8.)(46.$8.$8.R1<.(1;.+4.R1=.))R20.)P,(59.$43.R20.R1=.R1<.)P,(=.$8.(3?.(40.(3.&40.)R1=.))R1?.)P,(4=.$43.R22.VY,(58.VpY,(25.&40.VsgY,)VnY,VpadY,))P,(4:.$43.R23.VpY,(4;.Vys,))P,(<.(=.$>.VownY,$47.))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R27.)R25.VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R28.)R26.VY,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R29.)R27.VpY,(1;.+4.VnY,))P,(41.(20.(2>.VpY,(1;.+4.VnY,))R25.)(20.(2>.R25.(1;.+4.R26.))VpY,))P,(41.(20.(2>.VpY,(1;.+4.VnY,))Vlo,)(20.(13.&40.Vsp,)VpY,))P,(20.(2>.(2>.VpY,(1;.+4.VnY,))+8.)(42.+2.+2?.))P,(4=.$43.R2;.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R2<.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R2=.)(52.$43.(29.VR,)(2:.$43.VR,VHIA,R30.)Lms',$53.(54.(3.&40.)Lx5,(3.&40.)(54.(3.&40.)Lx6,(3.&40.)(54.(3.&40.)Lx7,(3.&40.)(54.(3.&40.)La1',(3.&40.)(54.(3.&40.)La2',(3.&40.)(54.(3.&40.)La3',(3.&40.)(54.(3.&40.)La4',(3.&40.)(54.(3.&40.)La5',(3.&40.)(54.(3.&40.)La6',(3.&40.)(54.(3.&40.)La7',(3.&40.)(54.(3.&40.)Lx28,(3.&40.)(54.(3.&40.)Lx29,(3.&40.)(54.(3.&40.)Lx30,(3.&40.)(54.(3.&40.)Lx31,(3.&40.)(54.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(3=.(=.$53.R10.(39.(3:.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R1.(3<.$43.)))(3=.(5:.(4>.(45.$8.$8.)(46.$8.$8.R3;.(2>.R3;.(1;.+4.R3=.)))(4>.(45.$8.$8.)(46.$8.$8.Vlo,(13.&40.Vsp,))(51.(45.$8.$8.))))R3>.R1.)(3=.(5;.$43.R3>.R1.)(3=.(27.$43.R1.)(3=.(5<.$43.R1.R3;.(4;.(5=.(3.&40.)(5>.R3=.)Vys,)))(3=.(1?.$43.R1.Vlo,(13.&40.Vsp,))(9.$43.VR,VHIA,R40.R3?.VLF,R1.))))))))))))))))))))))(39.(3:.R29.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R28.R27.R26.(25.&40.VX,)(25.&40.R2=.)(25.&40.VY,)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R1<.R1;.R1:.Vs9,Vs10,Vs11,R19.R18.R17.R16.)VF,(25.&40.+9;?90.)Vfc,(3;.(3.&40.))R2>.(3<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH TOPc Hi Hin N10 HXS HIN HXL LL0 HYS PBY OYN OX OY OPY SY2 C5 Y47 FR ST MI. basic_facts hc LBc mc HH TOPc.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    destruct (hm_apart asegs R HIA hc LBc LF mc HH) as [HF BA]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    dpose PBY as (PY0 & PYB & _). rewrite u32s_length in PYB.
    unfold mpi_cells in HXS, HYS.
    pose proof (munch_refl [(pX', pX' + 4 * i); (lo, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof HXL as PU. rewrite <- (firstn_skipn (Z.to_nat i) xs0) in PU. apply u32arr_app in PU. destruct PU as [PUi _].
    assert (LI : length (firstn (Z.to_nat i) xs0) = Z.to_nat i) by (apply firstn_length_le; clear - Hi Hin LL0; lia).
    assert (LIy : length (firstn (Z.to_nat i) ys) = Z.to_nat i) by (apply firstn_length_le; clear - Hi LENY; lia).
    pose proof PBY as PBY'. rewrite <- (firstn_skipn (Z.to_nat i) ys) in PBY'. rewrite u32s_app in PBY'. apply bytes_at_app in PBY'. destruct PBY' as [PBA _].
    pose proof (hm_aobj_block asegs R HIA hc LBc LF mc pX' (4 * n') HH HIN) as OPX.
    pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_CP) as SPC. unfold A_ASAN_MEMCPY_CP in SPC.
    callxA_sp (bv_unsigned sp + -80)
      (eapply SPC with (h := hc) (LB := LBc) (LF := LF) (DST := pX') (SRC := pY) (n := 4 * i) (lo := lo)
                        (ds := u32s (firstn (Z.to_nat i) xs0)) (ss := u32s (firstn (Z.to_nat i) ys));
       rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMC; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact PUi
             | rewrite u32s_length, LI; clear - Hi; lia
             | rewrite u32s_length, LIy; clear - Hi; lia
             | eapply aobj_sub; [exact OPX| clear; lia| clear - Hi Hin; lia]
             | eapply aobj_sub; [exact OPY| clear; lia| clear - Hi; lia]
             | right; clear - SY2 Hi Hin; lia
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOPc HTOP; lia]
             | left; clear - BC ALO LOS Hi Hin; lia
             | clear - C5 Hi; lia
             | eapply (blk_top47_sub asegs R HIA hc LBc LF mc); [exact HH| exact HIN| clear - Hi Hin; lia]
             | right; clear - Y47 Hi; lia
             | eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear; lia| clear - Hi Hin; lia]
             | f_equal; clear; lia
             | clear - Hi NRY LOS SLO NEEDR NRA TOPc SPA SPR; lia
             | match goal with |- ?g => idtac "MEMCPYF-PRE-LEFT:" g end ]).
    clear SPC.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPYF-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 pX' _ |- _ => rename H into HPA end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    (* [comment removed for export] *)
    zstep.
    do 10 zstep.
    zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    finish.
    all: match goal with |- ?g => idtac "LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L10351595562.3L41250020593.3L982998592.4  00000900B00MS2nY1i2HiS2nY1i2HiS1i2n'1E2I1". (* [comment removed for export] *)
  #[using="Type"] Lemma post_ok : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmo,$6.Pmo',$6.Ph',(0.$43.VR,VHIA,)Pm',P,(3.&40.)(5.(3.&8.))PLB',(1.$2.)Pi,$8.Pn',$8.PpX',$8.Pzs,(1.(3.&40.))Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Px28,(3.&40.)Px29,(3.&40.)Px30,(3.&40.)Px31,(3.&40.)P,(3=.(20.+1.R12.)(20.R12.VnY,))P,(20.R13.R12.)P,(3=.(20.VnX,R13.)(20.R13.(61.VnX,VnY,)))P,(41.(=.$8.R14.VnX,)(3=.(=.$8.R14.R15.)(62.Vys,R15.)))P,(63.Vys,R16.)P,Pk,$64.Pw,(3.&40.)P,(=.(5.(3.&40.))(65.(3.&40.)R16.R2.)(66.(3.&40.)R1.))(=.$8.(24.(13.&40.R2.)(42.+2.+20.))=)P,(27.$43.R1:.)P,(1?.$43.R1;.Vlo,(13.&40.Vsp,))P,(67.R1?.R1>.)P,(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,R1=.)P,(=.$8.(1>.$43.VR,VHIA,R1?.)(1>.$43.VR,VHIA,Vh,))P,(=.$8.(6:.$43.VR,VHIA,R20.)(6:.$43.VR,VHIA,Vh,))P,(=.$8.(6;.$43.VR,VHIA,R21.)(6;.$43.VR,VHIA,Vh,))P,(:.$43.VR,VHIA,R22.R23.)P,Px,$8.P,(2:.$43.VR,VHIA,Vh,R1.)(2:.$43.VR,VHIA,R25.R2.)P,(20.(2?.$43.VR,VHIA,R24.)(2>.(2?.$43.VR,VHIA,Vh,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))))P,(20.(33.$43.VR,VHIA,R25.)(2>.(33.$43.VR,VHIA,Vh,)(34.Vd,)))P,(9.$43.VR,VHIA,R26.R24.VLF,R25.)P,(;.$43.R26.R25.(69.VX,VsgY,R23.R22.(16.(3.&40.)(5=.(3.&40.)(5>.R24.)Vys,)R21.)VpadX,$19.))P,(6<.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)R26.(69.VX,VsgY,R24.R23.(16.(3.&40.)(5=.(3.&40.)(5>.R25.)Vys,)R22.)VpadX,$19.))P,(41.(44.(45.$8.$8.)(46.$8.$8.R24.(1;.+4.R25.))(6=.(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(6>.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,R24.(1;.+4.R25.)))P,(41.(44.(45.$8.$8.)(46.$8.$8.R25.(1;.+4.R26.))(6=.(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(<.(44.(45.$8.$8.)(46.$8.$8.R25.(1;.+4.R26.))VLB,)))(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R2=.(38.(39.(3:.Vra,Vsp,Vgp,Vtp,R24.R23.R22.Vs0,Vs1,(25.&40.=)R21.R20.R1?.R1>.R1=.R1<.R1;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1:.R19.R18.R17.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R2:.(3<.$43.))R2<.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros Hi Hin NB TR ZY ZS MI ST MF HP HT HS HFL HK HCS HV HFR HH MA MO FRA FRB.
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB', (mkMPD X sgY n' pX' (firstn (Z.to_nat i) ys ++ zs) padX LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|]. split; [exact MO|].
    split; [cbn [mpd_blk md_own md_p md_n]; intros b [<-|[]]; exact FRA|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split.
    { split.
      { left. split; [reflexivity|]. split; [| exact NB]. unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_app.
        rewrite (limbs_val_zeros zs ZS). rewrite limbs_val_firstn; [rewrite Z.mul_0_r, Z.add_0_r; reflexivity| clear - Hi; lia| exact ZY]. }
      split; [reflexivity|]. split; [reflexivity|]. intros b [<-|[]]. exact FRB. }
    intros _. unfold copy_trim, mpd_abs. cbn [md_n md_limbs].
    destruct TR as [E|[E TI]]; [left; exact E|]. right. destruct TI as [I1|(w & Hw & NZ)]; [left; clear - E I1; lia| right].
    pose proof (limbs_val_nth_lower ys (Z.to_nat (i - 1)) w Hw NZ) as LOW. rewrite Z2Nat.id in LOW by (clear - Hi; lia). rewrite E. exact LOW.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L39789476001.111L59321100280.4  L59321100283.4  L8273516665.0   00000@00N00\00]S2sp1X1Y3sgY3sg'S2nY1l2EY4LENYS2nX1l2EX4LENXS". (* [comment removed for export] *)
  #[using="MAX NST MAY NEQ SEP CSEP XW"] Lemma post_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmo,$6.Pmo',$6.Ph',(0.$43.VR,VHIA,)Pm',P,(3.&40.)(5.(3.&8.))Pr,$8.Psg',$8.Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Px28,(3.&40.)Px29,(3.&40.)Px30,(3.&40.)Px31,(3.&40.)P,(27.$43.R11.)P,(1?.$43.R12.Vlo,(13.&40.Vsp,))P,(67.R16.R15.)P,(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,R14.)P,(=.$8.(1>.$43.VR,VHIA,R16.)(1>.$43.VR,VHIA,Vh,))P,(=.$8.(6:.$43.VR,VHIA,R17.)(6:.$43.VR,VHIA,Vh,))P,(=.$8.(6;.$43.VR,VHIA,R18.)(6;.$43.VR,VHIA,Vh,))P,(:.$43.VR,VHIA,R19.R1:.)P,Px,$8.P,(2:.$43.VR,VHIA,Vh,R1.)(2:.$43.VR,VHIA,R1<.R2.)P,(20.(2?.$43.VR,VHIA,R1;.)(2>.(2?.$43.VR,VHIA,Vh,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))))P,(20.(33.$43.VR,VHIA,R1<.)(2>.(33.$43.VR,VHIA,Vh,)(34.Vd,)))P,(9.$43.VR,VHIA,R1=.VLB,VLF,R1<.)P,(;.$43.R1=.VLB,(69.VX,R1;.VnX,VpX,Vxs,VpadX,VownX,))P,(41.(=.$8.R1=.$70.)(3=.(=.$8.R1=.=)(3=.(=.$8.VnX,=)(=.$8.VnY,=))))(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R22.(38.(39.(3:.Vra,Vsp,Vgp,Vtp,R1<.R1;.R1:.Vs0,Vs1,(25.&40.R1>.)R19.R18.R17.R16.R15.R14.R13.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R1?.(3<.$43.))R21.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros MI ST MF HP HT HS HFL HK HCS HV HFR HH MA Hr.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB, (mkMPD X sg' nX pX xs padX ownX), r.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [eapply mpd_out_ext; [apply mpd_out_refl; cbn [md_own]; exact NST| reflexivity| cbn [md_own]; exact NST| reflexivity]|].
    split; [cbn [mpd_blk md_own md_p md_n]; intros b Hb; left; exact Hb|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split; [| intros E; unfold copy_trim; cbn [md_n]; left; reflexivity].
    split; [| split; [reflexivity| split; [reflexivity| intros b Hb; left; exact Hb]]].
    destruct Hr as [->|(-> & EX & EY)]; [right; repeat split; reflexivity| left].
    split; [reflexivity|]. split; [| rewrite EX, EY; clear; lia].
    unfold mpd_val. cbn [md_sg md_limbs].
    assert (xs = []) as -> by (destruct xs; [reflexivity| exfalso; cbn in LENX; clear - LENX EX; lia]).
    assert (ys = []) as -> by (destruct ys; [reflexivity| exfalso; cbn in LENY; clear - LENY EY; lia]).
    cbn. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01P0@C17025492443.168C24172564923.171C57547066598.169C57547066598.170D26117128935.172K11451933403.171K14278493136.171K14981916448.171K22605501532.169K22605501532.170K60573057312.168L11302909470.18 L11307674349.2  L11445796260.4  L11498582455.18 L11500183646.3  L11976331003.2  L14211216863.18 L14212572343.4  L14289919151.5  L14968616261.4  L17786296710.7  L18237047372.2  L18480872817.6  L21516681952.3  L22257015276.4  L22612200227.4  L23100341967.139L2340205082.14  L24391971372.5  L27633032728.4  L29428324939.5  L3253508485.5   L35339770834.11 L35653441506.7  L35691325410.12 L35944522234.138L37757228480.5  L38130778761.3  L39172636981.0  L39191974800.5  L41843607083.7  L43031326719.11 L46732241046.2  L47907397394.12 L47955327898.138L49659320776.5  L49858401057.0  L5262031770.138 L53562769825.2  L5376454999.5   L55196948550.11 L57628700040.10 L60098763854.3  L60124437587.5  L60459821746.2  L60576273221.2  L65284824489.11 L66255738774.138L67032356243.8  L67932008790.2  L7832156787.7   L8265267294.0   N10156624428.169N13003184628.169N21806751459.169N37104593031.169N4592533095.169 O11652562492.171O16756464443.171O17025492443.168O24172564923.171O32791873655.171O41046580696.168O57547066598.169O57547066598.170P11451933403.171P22605501532.169P22605501532.170P27642610023.171P5382893096.168 P60573057312.168Q12370813529.148Q17205206013.147Q18771245053.172Q22252422803.172Q26056220425.152Q37623291935.147Q37940043306.148Q38248387216.172Q43879899724.172Q45132659991.148Q47177596183.148Q5483425282.147 Q5485174314.148 Q6143569392.148 00000100200300400500600`01G01H01I01J01a01b01c02802902?02O02P02Q02R02j02k03403=03I03J03b03c03d03e04704H04e05=05c07107207307407507H07f07m08M08l09209309Q09W09X09Y0:10:;0:E0:M0:N0:g0<50<60<70<K0<L0<k0=S0>50>W0?60?70?80?90?:0?;0?<0?=0?>0??0?@0?A0@70@c0@d0AF0AV0Ao0BN0CF0CV0CW0D00DL0DM0DN0D^0Dn0E>FFFFFFS2nX2pX2xs2nY2pY2ys1i2Hi2Q34LENY2N13PYB2LRS2sp2nX2xs2nY2pY2ys2lo1i2Q54LENY3PYB2LRFFFS2sp2nX2nY1i2Hi3SPR3NRXFFS1R2sp2lo3SLO3NRA3SPRFS2pX1iS1R3HIA1h2sp3TOPFFFS2nX2xs2nY1i2Hi3Hin4LENXFS2nX2pX1iS2nY1i2HiS2pX2nY1i2HiFS2sp1X2pX2xs1Y2pY2ys3PYBFFFS1R2lo3LOS3ALO3ACPS2nY2ys1i2Hi4LENYS2sp2nX2pX1Y2nY2lo1i2Hi2Q12Q4S1R3HIA1h2sp2lo3TOP4HTOPS1R2sp2nX2pX2nY2lo3LOS1i2Hi3Hin3ALO2BCS1R5NEEDR2sp1X2nX2pX2xs1Y2nY2pY2ys2lo3LOS3SLO1i2Hi3Hin3ALO3SPR2X02Y02B02BC3PYBFFSFS2nX2xs2nY1i2Hi3HinS2sp1X2nX2pX2nY2lo1i2Hi2Q23DSXS2sp2loS1R2sp2nX2pX2lo3LOS1i3Hin3ALO2BCS2sp1X2nX2pX2xs1Y2pY2ys3NRX3PYBS2nX1iSS2sp1X2pX2xs1Y2pY2ys2X02XB3PYBS2nX1iFFS2sp2nX2pX2lo1i3Hin1x2HxS1R2lo3LOSS2nX1i3HinS2nX3NRXFS1R2nX2pX2lo3LOS1i3ALO2BCS1R5NEEDR2sp1X2nX2pX2xs1Y2nY2pY2ys2lo3LOS3SLO1i2Hi3Hin3ALO3SPR2X02Y02B02BC3PYBFFS2nX2xs2nY1i2Hi4LENXSS2nX2pX2xs2pY2ys1i3PYB2LR3x151CS2nX2pX2xs2nY2pY2ys1i2Hi2N13PYB2LR3x151CS2sp2nX2xs2pY2ys2lo1i3PYB2LR3x151CS2sp2nX2xs2pY2ys2lo1i3PYB2LR3x151CS2nX2pX2xs2pY2ys1i3PYB2LR3x151CFFFFFFFFFFFS1R5NEEDR2sp2nX2pX2xs2pY2ys2lo3LOS3SLO1i3ALO2BC3PYB2LRS1R2sp2nX2pX2xs2pY2ys2lo3LOS1i3ALO2BC3PYB2LRFS2sp1X2pX2xs1Y2pY2ys3XAL2X02Y03PYBS1X2xs2pY2ys3PYBS2nX2pX2xs2pY2ys1i3PYB2LRS2nX2pX2xs2nY2pY2ys1i2Hi3PYB2LRS1R5NEEDR2sp2nX2xs2pY2ys2lo3LOS3SLO1i3ALO3ACP3SPR3PYB2LRS1X2xs2pY2ys3PYBFS2nX2xs2pY2ys2lo1i3PYB2LRS2sp2nX2xs2pY2ys2lo1i3PYB2LRFFS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYB". (* [comment removed for export] *)
  #[using="IMG AMC AMS NEEDR m sgX MAX MAY NEQ SEP LOS SLO TOP"] Lemma memset_path : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,Vh,VLB,VLF,R15.)P,(3=.(20.+1.R15.)(20.R15.VnY,))P,(20.R16.VnX,)P,(=.$>.VownX,$19.)P,(4=.$43.R19.VX,(58.VpX,(25.&40.VsgY,)VnX,VpadX,))P,(59.$43.R1:.VpX,Vxs,)P,(4=.$43.R1;.VY,(58.VpY,(25.&40.VsgY,)VnY,VpadY,))P,(4:.$43.R1<.VpY,(4;.Vys,))P,(<.(=.$>.VownY,$47.))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1>.VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1?.VY,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R20.VpY,(1;.+4.VnY,))P,(41.(20.(2>.VpY,(1;.+4.VnY,))VpX,)(20.(2>.VpX,(1;.+4.VnX,))VpY,))P,(41.(20.(2>.VpY,(1;.+4.VnY,))Vlo,)(20.(13.&40.Vsp,)VpY,))P,(20.(2>.(2>.VpY,(1;.+4.VnY,))+8.)(42.+2.+2?.))P,(41.(20.(2>.VY,+10.)VpX,)(20.(2>.VpX,(1;.+4.VnX,))VY,))P,(41.(20.(2>.VX,+10.)VpX,)(20.(2>.VpX,(1;.+4.VnX,))VX,))P,(41.(20.(2>.VX,+10.)Vlo,)(20.(13.&40.Vsp,)VX,))P,(41.(20.(2>.VY,+10.)Vlo,)(20.(13.&40.Vsp,)VY,))P,(4=.$43.R28.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R29.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R2:.)(52.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)Lms',$53.(54.(3.&40.)Lx5,(3.&40.)(54.(3.&40.)Lx6,(3.&40.)(54.(3.&40.)Lx7,(3.&40.)(54.(3.&40.)La1',(3.&40.)(54.(3.&40.)La2',(3.&40.)(54.(3.&40.)La3',(3.&40.)(54.(3.&40.)La4',(3.&40.)(54.(3.&40.)La5',(3.&40.)(54.(3.&40.)La6',(3.&40.)(54.(3.&40.)La7',(3.&40.)(54.(3.&40.)Lx28,(3.&40.)(54.(3.&40.)Lx29,(3.&40.)(54.(3.&40.)Lx30,(3.&40.)(54.(3.&40.)Lx31,(3.&40.)(54.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(3=.(=.$53.R10.(39.(3:.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R1.(3<.$43.)))(3=.(5:.(4>.(45.$8.$8.)(46.$8.$8.VpX,(2>.VpX,(1;.+4.VnX,)))(4>.(45.$8.$8.)(46.$8.$8.Vlo,(13.&40.Vsp,))(51.(45.$8.$8.))))R3;.R1.)(3=.(5;.$43.R3;.R1.)(3=.(27.$43.R1.)(3=.(59.$43.R1.VpX,(16.(3.&40.)(5=.(3.&40.)(5>.R3:.)Vys,)(71.(3.&40.)(25.&40.=)(5>.(22.VnX,R3:.)))))(3=.(1?.$43.R1.Vlo,(13.&40.Vsp,))(9.$43.VR,VHIA,Vh,VLB,VLF,R1.))))))))))))))))))))))(39.(3:.R29.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R28.R27.R26.(25.&40.VX,)(25.&40.R2:.)(25.&40.VnX,)(25.&40.VY,)R25.R24.R23.R22.R21.R20.R1?.R1>.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R1=.R1<.R1;.Vs9,Vs10,Vs11,R1:.R19.R18.R17.)VF,(25.&40.+9;><<.)Vfc,(3;.(3.&40.))R2;.(3<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH Hi Hin EO HXS HXL HYS PBY OYN OX OY OPY Q3 Q5 Y47 Q1 Q2 DSX Q4 FR ST MI. basic_facts h LB mc HH TOP.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite EO in HOWN.
    ddestruct HOWN as (N1 & HIN & P16 & _).
    destruct (hm_apart asegs R HIA h LB LF mc HH) as [HF BA]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    dpose PBY as (PY0 & PYB & _). rewrite u32s_length in PYB.
    unfold mpi_cells in HXS, HYS.
    pose proof (munch_refl [(pX, pX + 4 * nX); (lo, bv_unsigned sp)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (munch_refl [(pX + 4 * i, pX + 4 * nX); (lo, bv_unsigned sp)] mc) as MU'.
    pose proof (hm_aobj_block asegs R HIA h LB LF mc pX (4 * nX) HH HIN) as OPX.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
    zstep. zstep.
    (* [comment removed for export] *)
    pose proof HXL as PU. rewrite <- (firstn_skipn (Z.to_nat i) xs) in PU. apply u32arr_app in PU. destruct PU as [PUi PUr].
    rewrite firstn_length_le in PUr by (clear - Hi Hin LENX; lia). replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) in PUr by (clear - Hi; lia).
    assert (LR : length (skipn (Z.to_nat i) xs) = Z.to_nat (nX - i)) by (rewrite length_skipn; clear - Hi Hin LENX; lia).
    pose proof (conj HXS I) as HXS0. pose proof (conj HYS I) as HYS0. pose proof (conj HXL I) as HXL0. clear HXS HYS.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_CP) as SPM. unfold A_ASAN_MEMSET_CP in SPM.
    callxA_sp (bv_unsigned sp + -80)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := pX + 4 * i) (v := 0) (n := 4 * (nX - i)) (lo := lo)
                        (ds := u32s (skipn (Z.to_nat i) xs));
       rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; exact PUr
             | rewrite u32s_length, LR; clear - Hi Hin; lia
             | eapply aobj_sub; [exact OPX| clear - Hi; lia| clear - Hi Hin; lia]
             | clear; lia
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
             | left; clear - BC ALO LOS Hi Hin; lia
             | eapply (blk_top47_sub asegs R HIA h LB LF mc); [exact HH| exact HIN| clear - Hi Hin; lia]
             | eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear - Hi; lia| clear - Hi Hin; lia]
             | f_equal; clear; lia
             | clear - Hi Hin NRX LOS SLO NEEDR NRA TOP SPA SPR; lia
             | match goal with |- ?g => idtac "MEMSETP-PRE-LEFT:" g end ]).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMSETP-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 (pX + 4 * i) _ |- _ => rename H into HPZ end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : HM asegs R HIA h LB LF m5 |- _ => rename H into HH5 end.
    match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
    (* [comment removed for export] *)
    try clear PUi. destruct HXS0 as [HXS _]. destruct HYS0 as [HYS _]. destruct HXL0 as [HXL _].
    pose proof (rw_cells_transport asegs _ mc m5 _ _ HXS MU' WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - Q2 DSX Hi Hin; lia)) as HXS5.
    pose proof (rw_cells_transport asegs _ mc m5 _ _ HYS MU' WM ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - Q1 Q4 Hi Hin; lia)) as HYS5.
    clear HXS HYS.
    rewrite <- (firstn_skipn (Z.to_nat i) xs) in HXL. apply u32arr_app in HXL. destruct HXL as [HXL _].
    pose proof (u32arr_transport asegs _ mc m5 _ _ HXL MU' WM) as PUi.
    rewrite firstn_length_le in PUi by (clear - Hi Hin LENX; lia).
    specialize (PUi ltac:(cbn [disjoint_from]; clear - BC ALO LOS Hi Hin; lia)). clear HXL MU'.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evtA_mono.
    { eapply (final_walk h LB m5 i nX pX (firstn (Z.to_nat i) xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (nX - i))));
        try eassumption.
      1: clear - NRX; lia.
      1: { apply u32arr_app. split; [exact PUi|]. rewrite firstn_length_le by (clear - Hi Hin LENX; lia).
           replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) by (clear - Hi; lia).
           replace (Z.to_nat (4 * (nX - i))) with (4 * Z.to_nat (nX - i))%nat in HPZ by (clear - Hi Hin; lia).
           apply (rw_cells_of_u8arr asegs) in HPZ.
           eapply (u32arr_of_cells asegs); [exact HPZ| symmetry; apply u32s_repeat0]. }
      rewrite length_app, firstn_length_le, repeat_length by (clear - Hi Hin LENX; lia); clear - Hi Hin LENX; lia. }
    cbv beta. intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & E9 & MU9 & WM9 & MI9 & HA9 & ST9 & HH9).
    deexists 15. split; [exact E9|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU9]; clear - Hi Hin; intros x Hx; cbn [outside] in *; lia]|].
    split; [eapply wmono_trans; [exact WM| exact WM9]|].
    split; [exact MI9|].
    split; [| split; [exact ST9| exact HH9]].
    apply u32arr_app. split.
    - eapply (u32arr_of_cells asegs); [| reflexivity]. apply (rw_cells_of_u8arr asegs) in HA9. rewrite u32s_length, firstn_length_le in HA9 by (clear - Hi LENY; lia).
      exact HA9.
    - rewrite firstn_length_le by (clear - Hi LENY; lia). replace (4 * Z.of_nat (Z.to_nat i)) with (4 * i) by (clear - Hi; lia).
      replace (Z.to_nat (4 * (nX - i))) with (4 * Z.to_nat (nX - i))%nat in HPZ by (clear - Hi Hin; lia).
      apply (rw_cells_of_u8arr asegs) in HPZ.
      eapply (u32arr_of_cells asegs); [| symmetry; apply u32s_repeat0].
      eapply (rw_cells_transport asegs _ m5 m9); [exact HPZ| exact MU9| exact WM9|].
      rewrite repeat_length. cbn [disjoint_from cells_size csize Nat.add]. clear - Hi Hin BC ALO LOS; lia.
    all: match goal with |- ?g => idtac "MP-LEFT2:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@D24976250634.154D52014138856.154D52014138856.155D62155808737.155K21652967687.154K21652967687.155K38539219888.154K38539219888.155K43762715123.154K43762715123.155K44044790992.154K44044790992.155L18160155068.4  L21646329835.2  L23100341967.143L29428324939.5  L35653441506.7  L38549538015.2  L39953140637.9  L40254489227.4  L43767073266.3  L44051262612.3  L46160487540.142L49578233423.143L50790580594.6  L57628700040.7  L60098763854.3  Q12370813529.152Q16425390503.154Q16425390503.155Q17205256176.151Q24974040330.153Q26207421841.150Q26207721832.151Q26207967338.148Q31654082872.150Q37623178258.151Q39212284437.151Q42081808994.151Q43925228937.151Q45132659991.152Q47177596183.152Q52016320488.153Q52016320488.154Q5483506191.151 Q5485174314.152 Q60511567613.151Q60697995187.151Q6143569392.152 Q62157788641.154Q62965564504.152Q62965564504.153Q7891539809.152 Q8880503606.148 Q9538787269.148 00000S01601Y02<03003d04H04l05Y06K07207Y07f07g08908K08e08f09:09=09>09?09W09i0:@0:R0:\0;80;^0<D0<Q0<o0=<0=I0=V0=c0>00>=0>P0>]0>^0>_0?=0?[0?h0@50@@0@P0@]0A;0AT0Am0B@0BM0BXS2sp1X2xs1Y2ys1i3xs02HB5Ha_st5Hl_stS2sp1X2xs1Y2ys1i3xs02HB5Ha_st5Hl_stS2sp1X2xs1Y2ys1A3xs02HB5Ha_st5Hl_stS2sp1X2xs1Y2ys1A3xs02HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs2ys2lo3SLO1i3xs03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs2ys2lo3SLO1A3xs03DSX2HB5Ha_st5Hl_stS1X2xs1Y2ys1i3xs03SXY2HB5Ha_st5Hl_stS1X2xs1Y2ys1A3xs03SXY2HB5Ha_st5Hl_stS1X2xs2nY2pY2ys1i3xs03XPY4LENY2HB5Ha_st5Hl_stS1X2xs2nY2pY2ys1i1A3xs02Hi3XPY4LENY2HB5Ha_st5Hl_stS1X2xs2ys1i1A3xs03LL02XA2HB5Ha_st5Hl_stS1X2xs2ys1i1A3xs03LL02XA2HB5Ha_st5Hl_stS2nY1i2Hi3NRYFS2sp1X2xs1Y2ys3xs0S1R2lo3LOS3ALO3ACPS1R3HIA2sp2lo2hc4TOPc4HTOPFS2sp1X2lo1i1A3DSX2XAS1iFFS2sp1X2xs1Y2ys3xs02X02XBS2sp1X2xs1Y2ys3xs0S1R5NEEDR2sp2lo3LOS3SLOS2sp1X2lo1i1A1x2HxS1R2lo3LOSS2sp1X2xs1Y2ys3xs03XAL2X02Y0S2sp1X2xs2ys2lo1i1A3xs02HB5Ha_st5Hl_stS2sp1X2xs2ys2lo1i1A3xs02HB5Ha_st5Hl_stS1X2xs2ys3xs0S1X2xs2ys1i3xs02HB5Ha_st5Hl_stS1X2xs2ys3xs0S1X2xs2ys3xs0S1X2xs2ys3xs0S1X2xs2ys3xs0S1X2xs2ys3xs0S1X2xs2ys3xs0S1X2xs2ys3xs02X02HBS1X2xs2ys3xs0FFS1X2xs2ys1i3xs02HB5Ha_st5Hl_stS1X2xs2ys1A3xs02HB5Ha_st5Hl_stS1X2xs2ys3xs0S1X2xs2ys3xs0S2xs2ys3xs0S1X2xs2ys3xs02X0S1X2xs2ys3xs0S1X2xs2ys1A3xs02HB5Ha_st5Hl_stS1X2xs2ys3xs02XB2HB5Ha_stS1X2xs2ys3xs02XB2HB5Ha_stS1X2xs2ys3xs02X02HBS1X2xs2ys3xs0S2xs2ys3xs0". (* [comment removed for export] *)
  #[using="IMG AMC NEEDR LB m sgX pX xs ownX MAX MAY NEQ SEP LOS SLO"] Lemma fin_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Phc,(0.$43.VR,VHIA,)PLBc,(1.$2.)Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.PA,$8.Ppold,$8.Pxs0,(1.(3.&40.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs7,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,R17.R16.VLF,R15.)P,(=.$8.(1>.$43.VR,VHIA,R18.)(1>.$43.VR,VHIA,Vh,))P,(20.(13.&40.Vsp,)(1>.$43.VR,VHIA,R19.))P,(3=.(20.+1.R17.)(20.R17.VnY,))P,(3=.(20.=R17.)(3>.R17.(42.+2.+40.)))P,(3=.(20.=R17.)(3>.R17.(42.+2.+40.)))P,(4=.$43.R1;.VX,(4>.$4?.(50.(25.&40.R18.))(4>.$4?.(72.(25.&40.VsgY,))(4>.$4?.(72.(25.&40.VnX,))(4>.$4?.(73.VpadX,)(51.$4?.))))))P,(74.(15.VR,)(16.$2.R1=.(17.VLF,))(13.&40.Vsp,)(1>.$43.VR,VHIA,Vh,)VX,+10.)P,(44.(45.$8.$8.)(46.$8.$8.R1;.(1;.+4.R1<.))R1>.)P,(59.$43.R1>.R1<.R1:.)P,(=.$8.(3?.(40.(3.&40.)R1;.))R1>.)P,(4=.$43.R20.VY,(58.VpY,(25.&40.VsgY,)VnY,VpadY,))P,(4:.$43.R21.VpY,(4;.Vys,))P,(<.(=.$>.VownY,$47.))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R25.)R23.VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R26.)R24.VY,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R27.)R25.VpY,(1;.+4.VnY,))P,(41.(20.(2>.VpY,(1;.+4.VnY,))R24.)(20.(2>.R24.(1;.+4.R25.))VpY,))P,(41.(20.(2>.VpY,(1;.+4.VnY,))Vlo,)(20.(13.&40.Vsp,)VpY,))P,(20.(2>.(2>.VpY,(1;.+4.VnY,))+8.)(42.+2.+2?.))P,(41.(20.(2>.VX,+10.)Vlo,)(20.(13.&40.Vsp,)VX,))P,(41.(20.(2>.VY,+10.)R28.)(20.(2>.R28.(1;.+4.R29.))VY,))P,(41.(20.(2>.VX,+10.)R29.)(20.(2>.R29.(1;.+4.R2:.))VX,))P,(41.(20.(2>.VX,+10.)VpY,)(20.(2>.VpY,(1;.+4.VnY,))VX,))P,(4=.$43.R2=.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R2>.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R2?.)(52.$43.(29.VR,)(2:.$43.VR,VHIA,R32.)Lms',$53.(54.(3.&40.)Lx5,(3.&40.)(54.(3.&40.)Lx6,(3.&40.)(54.(3.&40.)Lx7,(3.&40.)(54.(3.&40.)La1',(3.&40.)(54.(3.&40.)La2',(3.&40.)(54.(3.&40.)La3',(3.&40.)(54.(3.&40.)La4',(3.&40.)(54.(3.&40.)La5',(3.&40.)(54.(3.&40.)La6',(3.&40.)(54.(3.&40.)La7',(3.&40.)(54.(3.&40.)Lx28,(3.&40.)(54.(3.&40.)Lx29,(3.&40.)(54.(3.&40.)Lx30,(3.&40.)(54.(3.&40.)Lx31,(3.&40.)(54.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(3=.(=.$53.R10.(39.(3:.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R1.(3<.$43.)))(3=.(5:.(4>.(45.$8.$8.)(46.$8.$8.R3>.(2>.R3>.(1;.+4.R3?.)))(4>.(45.$8.$8.)(46.$8.$8.Vlo,(13.&40.Vsp,))(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))))R40.R1.)(3=.(5;.$43.R40.R1.)(3=.(27.$43.R1.)(3=.(5<.$43.R1.R3>.(4;.(5=.(3.&40.)(5>.R3?.)Vys,)))(3=.(4=.$43.R1.VX,(58.R3>.(25.&40.VsgY,)R3?.VpadX,))(3=.(1?.$43.R1.Vlo,(13.&40.Vsp,))(9.$43.VR,VHIA,R42.R41.VLF,R1.)))))))))))))))))))))))(39.(3:.R2;.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R2:.R29.R28.(25.&40.VX,)(25.&40.R2?.)(25.&40.VY,)R27.R26.R25.R24.R23.R22.R21.(25.&40.(2>.VX,+:.))(25.&40.R2>.)(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))(25.&40.(2>.(60.VX,+3.)(5?.(29.VR,))))R20.(25.&40.(60.(2>.VX,+:.)+3.))Vs9,Vs10,Vs11,R1?.R1>.R1=.R1<.)VF,(25.&40.+9;?74.)Vfc,(3;.(3.&40.))R30.(3<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH HT TOPc Hi AB PB HXS CW HIN HAL LL0 HYS PBY OYN OX OY OPY SY2 Q5 Y47 DSX Q1 XA XPY FR ST MI. basic_facts hc LBc mc HH TOPc.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    destruct (hm_apart asegs R HIA hc LBc LF mc HH) as [HF BA]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    assert (CWs : client_wrange L (LBc ++ fdata LF) (arl_stklo R) (htop asegs R HIA hc) X 16) by (rewrite HT; eapply client_wrange_sp_mono; [| exact CW]; clear - LOS SLO NEEDR; lia).
    unfold mpi_cells in HYS.
    pose proof (munch_refl [(A, A + 4 * i); (lo, bv_unsigned sp); (X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    (* [comment removed for export] *)
    zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    eapply evtA_mono.
    { eapply (final_walk hc LBc m4 i i A xs0); try eassumption.
      all: clear - Hi NRY; lia. }
    cbv beta. intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & E9 & MU9 & WM9 & MI9 & HA9 & ST9 & HH9).
    deexists 15. split; [exact E9|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU9]; clear; intros x Hx; cbn [outside] in *; lia]|].
    split; [eapply wmono_trans; [exact WM| exact WM9]|].
    split; [exact MI9|]. split; [exact HA9|].
    split; [| split; [exact ST9| exact HH9]].
    unfold mpi_cells. eapply (rw_cells_transport asegs _ m4 m9); [exact HXS| exact MU9| exact WM9|].
    cbn [disjoint_from cells_size csize Nat.add]. clear - XA DSX Hi; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0>L1164172544.1 L26892418956.1L35666020638.8L37714553091.1L41751294858.3L50790809970.7L57124062131.2L59308588187.5L60280819195.4L62018535662.1L64900791963.400000300700R00U00_01601;01J01W01Z01fS1XS2spS1R3HIA2sp2lo2hh4TOPh5HTOPhS1AS1R3HIA2hhS1R5NEEDR2sp2lo3LOS3SLOS1A1kS2sp2lo2Hl1x2HxS1k2kb2Hk3HkbS1RS1A1k2kb3Hkb". (* [comment removed for export] *)
  #[using="NEEDR LOS SLO"] Lemma presA_tail3 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Phh,(0.$43.VR,VHIA,)PLBh,(1.$2.)PA,$8.Pk,$8.Pkb,$8.Pmm,P,(3.&40.)(5.(3.&8.))PmX,P,(3.&40.)(5.(3.&8.))Pm1,P,(3.&40.)(5.(3.&8.))Pm2,P,(3.&40.)(5.(3.&8.))P,(9.$43.VR,VHIA,R9.R8.VLF,R4.)P,Pb,$2.P,(44.$2.R1.(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)))(44.$2.R2.R;.)P,(44.(45.$8.$8.)(46.$8.$8.R9.R7.)R:.)P,(6>.VR,VLB,VLF,R:.R8.)P,(3>.=R:.)P,(20.R;.R:.)P,(20.(13.&40.Vsp,)(1>.$43.VR,VHIA,R?.))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,R10.)R:.VX,+10.)P,(5:.(4>.(45.$8.$8.)(46.$8.$8.R?.(2>.R?.R>.))(4>.(45.$8.$8.)(46.$8.$8.Vlo,(13.&40.Vsp,))(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))))R:.R9.)P,(5;.$43.R;.R:.)(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,R13.)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))R<.R;.)")
(* [comment removed for export] *).
  Proof.
    intros hh LBh A k kb mm mX m1 m2 HH HI HIN HFRA Hk Hkb TOPh OX MU WM.
    pose proof (hcs_ok asegs R HIA hh) as CSOK. pose proof (hm_top asegs R HIA hh LBh LF mm HH) as HTOPh. pose proof (hcs_stack asegs R HIA hh) as SCS0.
    pose proof (art_lo asegs R HIA) as ALO.
    pose proof (hm_aobj_block asegs R HIA hh LBh LF mm A kb HH HIN) as OA.
    apply (munch_weaken _ [(lo, bv_unsigned sp); (A, A + k); (X, X + 16)]) in MU; [| clear; intros x Hx; clear - Hx; cbn [outside] in *; tauto (* [comment removed for export] *)].
    eapply (presA_drop_fresh asegs R HIA hh (mpd_keep LB dX) LF [(X, X + 16)] A k m1 m2 (bv_unsigned sp));
      [| apply fresh_apart_keep; eapply fresh_apart_sub; [exact HFRA| clear - Hk Hkb; lia]| clear - ALO LOS SLO NEEDR; lia].
    eapply (presA_weaken asegs R LBh (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
              (hstkhi asegs R HIA hh) (hstkhi asegs R HIA hh) [(A, A + k); (X, X + 16)]);
      [| exact HI| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
    eapply (presA_drop_below asegs R HIA hh LBh LF _ lo (bv_unsigned sp) mm m1 m2); [exact HH| | clear; lia| exact LOS].
    eapply (presA_of_munch asegs R LBh LF _ _ _ _ m1 m2 (hcs asegs R HIA hh) CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU | exact WM].
    unfold w_client. apply Forall_cons; [cbn [fst snd]|].
    { destruct (Z_lt_le_dec lo (bv_unsigned sp)) as [Hl|Hl].
      - eapply crange_sub; [exact SCS0| exact LOS| clear - TOPh HTOPh Hl; lia].
      - intros x Hx. exfalso. clear - Hx Hl. lia. }
    apply Forall_cons; [cbn [fst snd]; replace (A + k - A) with k by (clear; lia); eapply aobj_crange; eapply aobj_sub; [exact OA| clear; lia| clear - Hkb; lia]|].
    apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Grow.
    Variables (mo : Model) (m1 : mem) (i : Z).
    Hypothesis HH1 : HM asegs R HIA h LB LF m1.
    Hypothesis Hi : 1 <= i <= nY.
    Hypothesis Hin : nX < i.
    Hypothesis ZY : zeros_above ys i.
    Hypothesis TI : trim_i ys i.
    Hypothesis HXS1 : rw_cells asegs m1 X [C8 (Z_to_bv 64 pX); C2 (Z_to_bv 64 sgY); C2 (Z_to_bv 64 nX); C4 padX].
    Hypothesis PCH1 : ownX = LHeap -> rw_cells asegs m1 pX [CB (4 * length xs)%nat (u32s xs)].
    Hypothesis HYS1 : rw_cells asegs m1 Y [C8 (Z_to_bv 64 pY); C2 (Z_to_bv 64 sgY); C2 (Z_to_bv 64 nY); C4 padY].
    Hypothesis PBY1 : bytes_at asegs m1 pY (u32s ys).
    Hypothesis OYN : ownY <> LNull.
    Hypothesis OX1 : aobj asegs AL CS m1 X 16.
    Hypothesis OY1 : aobj asegs AL CS m1 Y 16.
    Hypothesis FR1 : rw_cells asegs m1 (bv_unsigned sp + -80) FRAME.
    Hypothesis ST1 : stk asegs m1 lo (bv_unsigned sp + -80).
    Hypothesis MI1 : mem_inv asegs m1.
    Hypothesis HP1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,Vm1,)")
(* [comment removed for export] *).
    Hypothesis BUD : havol asegs R HIA h + copy_PHI dY <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + copy_FR d <= FR_MAX.
    (* [comment removed for export] *)
    Hypothesis Q1 : X + 16 <= pY \/ pY + 4 * nY <= X.
    Hypothesis Q2 : ownX = LHeap -> Y + 16 <= pX \/ pX + 4 * nX <= Y.
    Hypothesis Q3 : ownX <> LHeap \/ pX + 4 * nX <= pY \/ pY + 4 * nY <= pX.
    Hypothesis Q4 : Y + 16 <= lo \/ bv_unsigned sp <= Y.
    Hypothesis Q5 : pY + 4 * nY <= lo \/ bv_unsigned sp <= pY.
    Hypothesis Y47 : pY + 4 * nY + 8 <= 2^47.
    Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
    Hypothesis DXP : ownX = LHeap -> X + 16 <= pX \/ pX + 4 * nX <= X.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
    Hypothesis PYfresh : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "PA,$8.Pk,$8.P,(6>.VR,VLB,VLF,R2.R1.)P,(41.(20.(2>.R3.R2.)(75.(15.VR,)))(20.(76.(15.VR,))R3.))P,(3>.=R3.)(41.(20.(2>.VpY,(1;.+4.VnY,))R5.)(20.(2>.R5.R4.)VpY,))")
(* [comment removed for export] *).
    Hypothesis Yfresh : forall A k, fresh_apart R LB LF A k -> 0 < k -> Y + 16 <= A \/ A + k <= Y.

    (* [comment removed for export] *)
    Ltac calloc_call cntv :=
      replace (Z_to_bv 64 429840) with (Z_to_bv 64 (arl_calloc R)) by (rewrite CALLOC; reflexivity);
      eapply aevtA_call;
      [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
        intros mo1 [HK1 MF1];
        eapply (heapA_calloc asegs R HIA) with (h := h) (LB := LB) (LF := LF) (cnt := cntv) (sz := 4) (lo := lo) (d := d);
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
        first [ eapply uw_obj_uwc; [exact XUW | clear; lia]
              | clear - SPA; lia
              | unfold copy_PHI, grow_PHI, copy_FR, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *; cbn [md_n] in *; qlia
              | apply c24_of_transition; exact C24T   (* [comment removed for export] *)
              | match goal with |- ?g => idtac "CALLOC-PRE-LEFT:" g end ]
      | ].

    (* [comment removed for export] *)
    Ltac free_limbs_call hh LBx HIN PCHx :=
      let SPZ := fresh "SPZ" in
      pose proof ZF as SPZ; unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ;
      eapply aevtA_call;
      [ let mo1 := fresh "mo1" in let HK1 := fresh "HK1" in let MF1 := fresh "MF1" in
        intros mo1 [HK1 MF1];
        eapply SPZ with (h := hh) (LB := LBx) (LF := LF) (buf := pX) (len := nX * 4) (lo := lo) (d := d) (junk := u32s xs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia; rewrite ?(unsigned_lit X) by qlia; try eassumption; try reflexivity;
        first [ right; split; [right; replace (nX * 4) with (4 * nX) by (clear; lia); exact HIN | exact PCHx]
              | eapply uw_obj_uwc; [exact XUW | clear; lia]
              | clear - SPA; lia
              | unfold copy_PHI, grow_PHI, copy_FR, calls_FR, fr_charge in *; unfold AMAX, AVOL_CALL in *; cbn [md_n] in *; qlia
              | match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end ]
      | clear SPZ ].

    Local Ltac2 Set LiaOrc.tbl := fun () => "04V0@C17025492443.253C31740276271.254D16049893661.255D32789656011.283D32789775952.192D32791823958.284D32793938021.193D32793938021.284D32793938021.285D32954576255.282D32965073634.283D36958348202.282D36958348202.284D36958348202.285D36958348202.286D36958348202.287D37439549899.280D37439549899.284D37703914153.280D37703914153.282D37710325044.283D37730786031.280D38983586459.284D39230898703.284D39230898703.285D39233014844.284D39235206049.283D39375086430.192D39375475909.284D42750138435.280D42750138435.282D42764775390.283D43864128417.280D43864128417.284D49468338534.192D49468338534.194D49468338534.195D50796826103.255D6148729117.284 D61560670416.284D63595235433.255D64336185449.255K1227220751.254 K14981916448.254K1792796448.254 K23294715799.254K25897202343.254K36795542264.254K5848377239.254 K60573057312.253K61205767951.254L10358394922.3  L11404239431.12 L11498238124.4  L11504513181.19 L1233234968.4   L12694533441.2  L12750819336.13 L12755534717.11 L14211003588.5  L14350476896.7  L14968616261.4  L16247715997.4  L16256253080.7  L1649577667.2   L1675511041.5   L17585880332.15 L1779758405.3   L17852819865.6  L18161466201.5  L18493781998.8  L19061415402.1  L20813968635.12 L21563705165.3  L23100341967.201L23100341967.234L23301287040.3  L23926814669.1  L24391384886.2  L25033921014.12 L25436154562.19 L25890634160.3  L27002460723.5  L27006593843.19 L27711224602.12 L27841768630.289L2851373008.7   L28553555646.2  L28655862141.5  L28715365361.3  L28767265244.7  L28813938827.14 L28814040852.201L29428324939.5  L30990067275.3  L31465033794.6  L31532528036.5  L31532528036.7  L32027975233.0  L32250862063.4  L3253508485.5   L32960714453.7  L3309110695.3   L33799276397.1  L33816268745.3  L34171955900.9  L34423643938.4  L35653441506.7  L35655538624.7  L36440793763.3  L36457694076.4  L36807145629.3  L37714553091.1  L38948636245.0  L39172636981.0  L39280637297.0  L40249794171.1  L40281191306.3  L40290687782.1  L40823592413.2  L41841290036.4  L41858767142.4  L42640703895.189L42762855401.8  L42865824567.3  L43646462316.7  L44397119898.2  L44697879740.4  L46160487540.211L46160655259.200L46380960401.6  L46732241046.2  L47107138245.3  L47858894730.7  L47860712607.10 L47955344026.2  L47956781558.210L47961733431.233L48132467214.7  L49659320776.5  L50635453427.5  L51622416288.9  L52476066706.201L52476227847.15 L52476359169.5  L52476506375.12 L52476506375.13 L52478458753.6  L5260163351.200 L53018262813.17 L53018625706.18 L54232820919.18 L54271395752.2  L54437155233.0  L5479049730.1   L5841841280.4   L59308587409.7  L59308587542.6  L59308632307.1  L59308633593.3  L59308661072.10 L59308668813.4  L59308742867.3  L59310648656.8  L59310758218.10 L59314873579.5  L59335885566.2  L60098763854.3  L60544169544.7  L60549562490.3  L60576273221.2  L60684097692.2  L61211782168.3  L62018535662.1  L62622656665.46 L62624471726.46 L62624471726.53 L62624751897.46 L62625145375.53 L62627242265.44 L62627242265.52 L63261865031.2  L63799194974.10 L64194470200.2  L64372451842.1  L64626866417.15 L64633158647.15 L64834004734.3  L64966926188.10 L64968776825.7  L656136024.1    L66256213271.3  L66610753222.8  L68469196698.2  L6935467336.1   L9223833819.5   L9596616833.4   N12401863469.254N14951461807.254N20716133971.254N31170017719.254N32071669760.254O10066905207.254O10068491663.254O11257354870.254O17025492443.253O26871806789.254O31740276271.254O32791873655.254O39322336069.254O48499521681.254O49587672251.253O53059091855.254O57399310481.254O65674534437.254P16252889848.254P1792794630.192 P24292699494.190P25462954850.282P25897202343.254P28709353702.254P35876208370.279P35876208370.284P35876325737.190P35876325737.192P44704452523.253P50646218980.254P5575725762.284 P60573057312.253Q10353739506.158Q11498601372.158Q12370813529.215Q12370813529.252Q14211170292.158Q16049893661.256Q16049893661.257Q17203157328.251Q17207595622.214Q17377103875.158Q21563673726.260Q26056220419.237Q26056447029.158Q26056447030.260Q26058334103.176Q26058334103.278Q26207421841.228Q26207721832.229Q26220303696.251Q26220304629.226Q26999889969.260Q31649524217.251Q31654082872.228Q34423215121.260Q34555067928.257Q34841007899.158Q37621080754.251Q37625031044.214Q37703787028.257Q37940043306.252Q38248387216.257Q39212284437.229Q41836510700.158Q43879899724.257Q43925228937.229Q45132659991.215Q45132659991.252Q45998615361.281Q45998742746.191Q46954851733.260Q49589754978.260Q5262061745.158 Q5262061746.260 Q5473021103.251 Q5485174314.215 Q5485174314.252 Q5485356953.214 Q54967815506.158Q57478834698.256Q57478834698.257Q60511567613.229Q60537634283.190Q60537752176.279Q60537752176.280Q60544073197.282Q60697995187.229Q6143569392.215 Q6143569392.252 Q63595235433.256Q63595235433.257Q65983947055.215Q65983947055.252Q8674270796.257 Q8885009321.226 Q9534281562.226 00000100200300400500600700800900:00;00_01C01D01h01i01j01k02H02e03B03a04Q04R04S04T04U04j05G05H05I05J05K05L05h06D06E07B07C08;08<08=08g09F09_0:F0:G0:a0;O0;P0<70<80<J0<K0<`0<a0<b0<c0<d0<e0=70=80=90=O0=W0=i0=j0=k0=l0>90>:0>>0>Y0>Z0?10?N0?O0?R0?S0?j0@E0@F0@G0@Y0@Z0A70AL0AS0AT0AU0B00B_0C]0Co0D90D:0DF0DU0DV0De0E60EJ0EK0EN0EW0F20F30FK0Ff0G20G?0G@0GC0GD0GE0GF0GI0GR0GU0GY0GZ0Gh0H=0H>0HG0HY0Ha0Hb0IE0Ib0Ic0Ij0J60J70JG0JO0K30KW0L20L<0L=0LR0M^0M_0M`0Ma0NP0NQ0Nn0No0O00O10O80O90O<0O=0OR0Ob0Of0Oo0PG0PU0P_0Q90QR0Q_0Qf0R00RG0RO0RP0RQ0RR0RU0RV0RW0RX0RY0RZ0R[0R\0Rd0SC0SJ0SN0SO0SP0SY0Sn0So0T20T;0TS0TZ0T^0Tn0U<0V10V20VL0Vf0Vg0Vh0Vi0Vj0Vk0Vl0Vm0Vn0Vo0W00W10W20W30W40W`0X90XR0YA0YB0Z80ZK0Z^0[10[D0[f0\R0]A0]B0]X0^60^W0_>0_[0_\0_]0_m0`=0`_0aC0b30bc0cS0dC0e30eC0eS0ec0f30fR0fb0g20gL0ge0hE0hU0he0i50i60iG0iW0iX0il0j<0j=0j>0j?0j@0ji0kN0kd0l:0lJ0lZ0lj0m:0mT0mU0mV0md0nH0nl0oP10410G10W10g10h10i10j10k10l11<11JFFFFFFFFFFFS2sp1X2pX2xs1Y2pY2ys3PYB2P01A3x432HxS2sp1X2pX2xs1Y2pY2ys3PYB2P01A3x432HxFS2sp1X2pX2xs1Y2pY2ys3PYB2P01A3x432HxFFFS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS2sp1X2pX2xs1Y2pY2ys1i3PYB2P01AS2sp1X2nX2pX2xs1Y2pY2ys3SPR2X02Y03PYB2P01A2A02N1FFFFS2sp1X2xs1Y2pY2ys3PYBS2sp1X2pX2xs1Y2pY2ys3PYB2P01AFFFFFS2sp1X2xs1Y2pY2ys3PYB3x142HxS2sp1X2xs1Y2pY2ys3PYB3x142HxFS1R5NEEDR2sp1X2pX2xs1Y2pY2ys2lo3LOS3SLO3SPR2X02Y03PYB2P01A2A0FS2sp1X2nX2pX2xs1Y2pY2ys1i3Hin3SPR2X04LENX2Y03PYB2P01A2A0FFS2nX2pX2xs2pY2ys1i3Hin4LENX3PYB2P01A2KP2PAS2sp2xs2nY2pY2ys2lo2Q54LENY3PYBS2sp2xs1Y2pY2ys2lo2Q43PYBS2nX2pX2xs1Y2pY2ys1i3Hin3PYB2P01A2YA2KPFS2sp1X2xs2pY2ys2lo3DSX3PYBS2nX2pX2xs2nY2pY2ys1i3Hin4LENY3PYB2P01A3YPA2KPFS1X2nX2pX2xs2pY2ys1i3Hin3PYB2P01A2XA2KPFS2nX2lo1i3Hin1A2ASFS1R2sp2lo3SLO3NRA3SPRFFFFFS2nX2pX1i3Hin1A2PAFFS1R3HIA1h1d2D02h24HFR2S2nX3NRXS2nX2xs1i3Hin4LENXFFFS2sp1Y1a2Ha1QFS2nXS2sp1X2nX2lo1i3Hin3DSX1A2XAFS2sp1X2xs1Y2pY2ys3PYB1AS2sp1X2pX2xs1Y2pY2ys3PYB2P01AFS1iFS1R2nX2pX2lo3LOS3ALO2PCS2sp2nX2nY1i2Hi3Hin3SPR3NRYFFS1R3HIA2sp2h24TOP2FS2sp1X2pX2xs1Y2pY2ys3PYB2P01AS1R2lo3LOS1i3ALO1A2ACS2nX2pXFFS1R5NEEDR2sp2lo3LOS3SLO3ALOS1R5NEEDR2sp2nY2lo3LOS3SLO1i2Hi3ALO3SPR1A2A02ACS1R5NEEDR2sp1X2xs1Y2nY2pY2ys2lo3SLO1i2Hi3SPR2X02Y03PYB1A2A02ASS1R2lo3LOS3ALO3ACPS2nX1i3HinFS2nX1i3Hin1AS2nX2xs1i3Hin1ASS2nX2pX2xs4LENXS2nY2ys1i2Hi4LENYS2nX2xs1i3Hin4LENX1AFS1iS2nY1i2HiS1R3HIA1h1d2h24HFR22h44HFR4FS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA2sp2lo2h24TOP25HTOP2S2nX2xs4LENXS2nY1i2Hi3NRYFS1ASSSS1iS1R3HIA1hS1XS2spFS2nX2xs4LENX1AS2sp1X2xs1Y2pY2ys3PYBFS2nY1i2HiS2nX2xs1i3Hin4LENXS2nX3NRXFS2sp1X2pX2xs1Y2pY2ys2X02XB3PYB2P01AS2sp1X2xs1Y2pY2ys2X02XB3PYB1AFS2sp2loS2nX2xs4LENXFS1R2nX2pX2PC3ACVS2nX3NRXS2sp1X2nX2pX2xs1Y2pY2ys3NRX3PYB2P01AS2sp1X2nX2pX2xs1Y2pY2ys3NRX3PYB2P01AS1R5NEEDR2sp2lo3LOS3SLO3ALOS2nX1i3HinFS2nX2pX1i3Hin1A2N12PAS1R5NEEDR2sp1X2nX2pX2xs1Y2pY2ys2lo3LOS3SLO3ALO3SPR2X04LENX2Y03PYB2P02PC1A2A0FFFS1R5NEEDR2sp2nX2pX2lo3LOS3SLO3ALO3SPR3NRX2P02PCFS2sp1X2xs1Y2pY2ys2X02XB3PYB1AFFFS2nX2pXSS1XFS2nX2pX1Y3Q2'1a2Ha2HrS1Y2lo1a2Ha1Q2HsS2KPS1A2A02KZS2nX2pX1i3Hin1A2N12PA2E1S2nX1l4LENX2EnS2pX2KP2B0S2nX2pX2nY2pY2N13Q3'1E3NY1S2nX2pX1i3Hin1A2N12PA3E1'S2nY1i2Hi1A1HS2pX2B0S1R2lo3LOSS1R5NEEDR2sp2lo3LOS3SLOS2nX1i1AFFFS1RFFFFFFFS2sp3SPAS1R3HIA1h2nY1i2Hi2h23HV22h43HV4S1R3ACPS2pXFFS2nY1i2HiS1R2nX1i3Hin1A2AC3ACVFS1XS2nY1i2HiS1R3HIA1h2nY1i2Hi2h23HV2S2nX2N1S2spS2nX2nY1i2Hi3HinS2nX2xs4LENX1AS1R2sp2nX2xs2pY2ys2lo3LOS1i3Hin3ALO3PYB1A2AC2N13x291CFS2sp2xs2pY2ys2lo3PYB3x291CS2sp2xs2pY2ys2lo3PYB3x291CFFFFFFFFFFFFFFS1R2sp2nX2pX2xs2pY2ys2lo3LOS3ALO4LENX3PYB2PCS2sp2xs1Y2pY2ys2lo2Q43PYBS2sp2xs1Y2pY2ys2lo2Q43PYBS1R5NEEDR2sp1X2xs1Y2pY2ys2lo3NEQ3SLO2Q43DSX3PYBFS1R5NEEDR2sp2nX2xs2pY2ys2lo3LOS3SLO1i3Hin3ALO3PYB1A2ACS2sp1X2xs2pY2ys3PYBS2sp1X2xs2pY2ys3PYBS2sp1X2xs2pY2ys3PYBS2sp1X2xs2pY2ys3PYBS2sp2nX2xs2pY2ys2lo1i3Hin3PYB1A2ASS1R2sp2nX2xs2pY2ys2lo3LOS1i3Hin3ALO3PYB1A2ACS1R5NEEDR2sp1X2xs1Y2pY2ys2lo3NEQ3SLO2Q43DSX3PYBFS2xs2nY2pY2ys1i2Hi3PYBS1R2sp2xs2pY2ys2lo3SLO3NRM3PYBS2sp1X2xs1Y2pY2ys3XAL2X02Y03PYB1AS2sp1X2pX2xs1Y2pY2ys3XAL2X02Y03PYB2P01AS1R3HIA1h2sp2xs2pY2ys3TOP3PYBFFS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1R3HIA1h2xs2nY2pY2ys1i2Hi3BUD3PYBS2nX2xs2nY2pY2ys1i2Hi3Hin3NRY3PYB2N1S1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3ACP3SPR3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3ACP3SPR3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3ACP3SPR3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3ACP3SPR3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3ALO3ACP3SPR3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1R3HIA2sp2xs2pY2ys3PYB2h24TOP2S1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1R2sp2xs2pY2ys2lo3SLO3PYBS2nX2xs2pY2ys1i3Hin3PYB1AS1R3HIA1h2xs2pY2ys1d4BUDF2D03PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS2xs2pY2ys3PYB1AFS2xs2pY2ys2lo3PYBS1X2xs2pY2ys3PYBFS2sp2xs2pY2ys2lo3PYBS1X2xs2pY2ys3PYBFFFFS1R3HIA1h2xs2nY2pY2ys1i2Hi3BUD3PYB2h23HV2S1R3HIA1h2xs2pY2ys1d4BUDF3PYB2h24HFR2S1X2xs2pY2ys2X02XB3PYBS1X2xs2pY2ys2X02XB3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBS2xs2nY2pY2ys1i2Hi3NRY3PYBFFS2xs2pY2ys3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1R5NEEDR2sp2xs2pY2ys2lo3LOS3SLO3PYBS1X2xs2pY2ys2X03PYBS1X2xs2pY2ys3PYBS1X2xs2pY2ys3PYBFFFFFS1X2xs2pY2ys3PYBS2xs2pY2ys3PYB". (* [comment removed for export] *)
    #[using="C24T IMG ZF CALLOC AMC NEEDR HND DIMG MAX NST MAY NEQ SEP CSEP YCR YLCR XW LOS SLO TOP SPA TPV YNZ XUW HH1 Hi Hin ZY TI HXS1 PCH1 HYS1 PBY1 OYN OX1 OY1 FR1 ST1 MI1 HP1 BUD BUDF Q1 Q2 Q3 Q4 Q5 Y47 DSX DXP CW PYfresh Yfresh"] Lemma grow_path : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)(77.$43.(78.$43.VR,VHIA,Vh,Vmo,)(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(39.(3:.R13.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R12.R11.R10.(25.&40.VX,)(25.&40.Vi,)R?.(25.&40.VY,)R>.R=.R<.R;.R:.R9.(25.&40.(2>.VX,+:.))R8.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R7.R6.R5.Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(25.&40.+9;?04.)Vfc,(3;.(3.&40.))Vm1,(3<.$43.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. basic_facts h LB m1 HH1 TOP. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0.
      dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
      pose proof (HND _ _ _ _ HH1) as ND.
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      dpose PBY1 as (PY0 & PYB & _). rewrite u32s_length in PYB.
      (* [comment removed for export] *)
      assert (PB : 0 <= pX /\ pX + 4 * nX <= alloc_ceiling
                   /\ (ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ 1 <= nX)
                   /\ (ownX = LNull -> pX = 0 /\ nX = 0)).
      { dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN.
        destruct (hm_apart asegs R HIA h LB LF m1 HH1) as [HF _]. rewrite Forall_forall in HF.
        destruct ownX; [| | exfalso; exact (NST eq_refl)].
        - destruct HOWN as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
          split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
        - ddestruct HOWN as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
          split; [clear - B0; lia|]. split; [exact BC|].
          split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| exact N1]]]| intros E; discriminate E]. }
      ddestruct PB as (P0 & PC & PHEAP & PNULL).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      calloc_call i.
      all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "CALLOC1-LEFT:" g end.
      (intros ms' mo' dd_H; ddestruct dd_H as (mo1' & [HK1 MF1] & PO)).
      ddestruct PO as (ms2 & mo2 & E & PO). injection E as E1 E2. subst ms2 mo2.
      unfold call_postA in PO. destruct_exs PO. destruct PO as [E PO]. subst ms'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
      ddestruct PO as (MI2 & ST2 & MF2 & WM2 & HP2 & h2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & CASES).
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m2 end.
      (* [comment removed for export] *)
      assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]).
      { intros E0. ddestruct (PHEAP E0) as (B0' & HIN' & _).
        eapply (presA_rw_cells asegs R); [exact HP2| exact (PCH1 E0)| | cbn; clear; tauto].
        simpl_sizes. eapply client_range_block; [apply in_app_iff; left; exact HIN'| clear; lia| clear - LENX; lia]. }
      assert (YBLK : ownY = LHeap -> In (pY, 4 * nY) LB).
      { intros E0. dpose MAY as [[_ (_ & _ & _ & _ & OY)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in OY. rewrite E0 in OY.
        exact (proj1 (proj2 OY)). }
      pose proof (pby_keep _ _ _ _ _ _ _ HP2 PBY1 MI1 MI2 YBLK OYN ltac:(cbn; exact I)) as PBY2.
      presA_transport HP2.
      assert (HPX2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|].
        eapply presA_weaken; [exact HP2| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y _; exact I]. }
      clear HP2.
      apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo' (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
      pose proof (AIh_laws asegs R HIA h2) as LAWS2. pose proof (KF_kinv asegs R HIA h2 mo) as KINV2.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OX1) as OX2.
      pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS2 OY1) as OY2.
      assert (TOP2 : bv_unsigned sp <= htop asegs R HIA h2) by (rewrite HT2; exact TOP).
      pose proof (hcs_ok asegs R HIA h2) as CSOK2. pose proof (cs_ok_sb _ _ CSOK2) as SB64'. pose proof (hcs_stack asegs R HIA h2) as SCS2.
      destruct CASES as [[E0 HH2] | (A & E0 & A16 & HFRA & HAS & HH2 & HNEW)]; match type of E0 with ?v = _ => subst v end.
      - (* [comment removed for export] *)
        pose proof (hm_top asegs R HIA h2 LB LF m2 HH2) as HTOP2.
        assert (MA2 : mpd_at asegs m2 LB (mkMPD X sgY nX pX xs padX ownX)).
        { eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; exact HXS1| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGY| exact PNULL|].
          intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact (PCH2 E)| reflexivity]. }
        zstep. zstep. zstep.
        eapply (aevtA_cut_evtA asegs AL _ LAWS2 _ _ _ _ _ _ KINV2);
          [ eapply epi_walk with (hc := h2) (LBc := LB) (r := MBEDTLS_ERR_MPI_ALLOC_FAILED); try eassumption
          | intros y Hy; exact Hy | ].
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFAIL-PRE-LEFT:" g end.
        intros ms' PO. destruct_exs PO. destruct PO as [E ST9]. subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply post_keep; try eassumption.
        all: match goal with |- ?g => idtac "GFAIL-LEFT:" g end.
        { unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; cbn [md_n] in *. clear - HV2 Hi. lia. }
        { unfold copy_FR, calls_FR, fr_charge in *. clear - HFR2 D0. lia. }
        { left; reflexivity. }
      - (* [comment removed for export] *)
        replace (i * 4) with (4 * i) in HFRA, HAS, HH2, HNEW by (clear; lia).
        pose proof (hm_top asegs R HIA h2 _ LF m2 HH2) as HTOP2.
        assert (SCS2' : crange (hcs asegs R HIA h2) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]).
        dpose HFRA as (A0 & AC & AD & HAP).
        pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * i) :: LB) LF m2 A (4 * i) HH2 (or_introl eq_refl)) as OA.
        assert (HINA : In (A, 4 * i) (((A, 4 * i) :: LB) ++ fdata LF)) by (left; reflexivity).
        assert (XA : X + 16 <= A \/ A + 4 * i <= X).
        { destruct (fresh_apart_client R LB LF (bv_unsigned sp) X 16 A (4 * i) HFRA); [| clear; lia| clear - Hi; lia| clear - ALO LOS SLO NEEDR; lia| right; assumption| left; assumption].
          eapply client_range_inside; [exact CW| intros b Hb; exact Hb| clear; lia| clear; lia]. }
        assert (AS : A + 4 * i <= lo) by (clear - AC ALO LOS; lia).
        assert (AIMG : A + 4 * i <= hl_img_lo L \/ hl_img_hi L <= A).
        { destruct (hm_apart asegs R HIA h2 ((A, 4 * i) :: LB) LF m2 HH2) as [HFa _]. rewrite Forall_forall in HFa.
          ddestruct (HFa (A, 4 * i) ltac:(apply in_app_iff; left; left; reflexivity)) as (_ & _ & _ & AI). exact AI. }
        pose proof (PYfresh A (4 * i) HFRA AIMG ltac:(clear - Hi; lia)) as YPA.
        pose proof (Yfresh A (4 * i) HFRA ltac:(clear - Hi; lia)) as YA.
        (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by (pose proof (alloc_ceiling_val R); clear - A0 AC H; lia); clear - KZ A0; lia|]. clear KZ.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. if_cases KP; zify_cond KP.
        + (* [comment removed for export] *)
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          assert (EO : ownX = LNull) by (destruct ownX; [reflexivity| exfalso; destruct (PHEAP eq_refl) as [B0 _]; clear - B0 KP; lia| exfalso; exact (NST eq_refl)]).
          destruct (PNULL EO) as [EP En].
          assert (CW3 : client_wrange L (((A, 4 * i) :: LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CW|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; right; exact Hb| right; exact Hb]. }
          assert (xs = []) as EL by (destruct xs; [reflexivity| exfalso; cbn in LENX; clear - LENX En; lia]).
          assert (HA2 : u32arr asegs m2 A (repeat (Z_to_bv 64 0) (Z.to_nat i))).
          { replace (Z.to_nat (4 * i)) with (4 * Z.to_nat i)%nat in HNEW by (clear - Hi; lia).
            eapply (u32arr_of_cells asegs); [exact HNEW| symmetry; apply u32s_repeat0]. }
          eapply (aevtA_cut_evtA asegs AL _ LAWS2 _ _ _ _ _ _ KINV2);
            [ eapply (fin_walk h2 ((A, 4 * i) :: LB) m2 i A pX (repeat (Z_to_bv 64 0) (Z.to_nat i))); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite repeat_length; clear - Hi; lia).
          all: try (clear - A0 AC ALO LOS SLO SPR NEEDR Hi; lia).
          all: try (clear - P0 PC ALO LOS SLO SPR NEEDR; lia).
          all: try (left; reflexivity).
          all: try (eapply opy_at; [exact HH2| intros E0; right; exact (YBLK E0)| exact OYN]).
          all: try (clear - YPA; lia).
          all: try (clear - YA; lia).
          all: try (rewrite EP; clear; lia).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN0-PRE-LEFT:" g end.
          intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & E9 & MU9 & WM9 & MI9 & HA9 & HX9 & ST9 & HH9). subst ms'.
          apply aevtA_done. intros mo9 [HK9 MF9].
          assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
          { eapply presA_trans; [exact HPX2|]. rewrite <- HS2.
            eapply (presA_tail3 h2 ((A, 4 * i) :: LB) A (4 * i) (4 * i) m2 m2 m2 m9);
              [exact HH2| intros b Hb; right; eapply In_mpd_keep; exact Hb| left; reflexivity| exact HFRA| clear - Hi; lia| clear; lia| exact TOP2| exact OX2| exact MU9| exact WM9]. }
          eapply (post_ok mo mo9 h2 m9 ((A, 4 * i) :: LB) i i A []); try eassumption.
          * clear; lia.
          * clear - Hi Hin; lia.
          * right. split; [reflexivity| exact TI].
          * intros k w Hk. destruct k; discriminate Hk.
          * unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; cbn [md_n] in *. clear - HV2 Hi. lia.
          * unfold copy_FR, calls_FR, fr_charge in *. clear - HFR2 D0. lia.
          * rewrite app_nil_r. eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - Hi NRY; lia| exact SGY| intros E; discriminate E|].
            { rewrite firstn_length_le by (clear - Hi LENY; lia). clear - Hi; lia. }
            intros _. split; [clear - Hi; lia|]. split; [left; reflexivity|]. split; [exact A16|].
            apply (rw_cells_of_u8arr asegs) in HA9. eapply (u32arr_of_cells asegs); [exact HA9| reflexivity].
          * unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
            split; [reflexivity|]. split; [discriminate|].
            split; [intros b [Hb|Hb]; [right; left; exact Hb| left; exact Hb]|].
            split; [intros b Hb _; right; exact Hb|]. intros b [].
          * right. apply fresh_apart_keep. exact HFRA.
          * right. intros Hin'. destruct (HAP A (4 * i) ltac:(apply in_app_iff; left; exact Hin')); clear - H Hi; lia.
        + (* [comment removed for export] *)
          assert (EO : ownX = LHeap).
          { destruct ownX; [| reflexivity| exfalso; exact (NST eq_refl)]. exfalso. rewrite (proj1 (PNULL eq_refl)) in KP.
            rewrite ?unsigned_lit in KP by (clear; lia). clear - KP. lia. }
          ddestruct (PHEAP EO) as (B0 & HIN & HP16 & N1). pose proof (PCH2 EO) as PCH. clear PCH2.
          rewrite ?unsigned_lit in KP by (pose proof (alloc_ceiling_val R); clear - P0 PC H; lia).
          pose proof (DXP EO) as DXP'. pose proof (Q2 EO) as Q2'.
          assert (Q3' : pX + 4 * nX <= pY \/ pY + 4 * nY <= pX) by (destruct Q3 as [Q|Q]; [exfalso; exact (Q EO)| exact Q]).
          pose proof (hm_aobj_block asegs R HIA h2 ((A, 4 * i) :: LB) LF m2 pX (4 * nX) HH2 (or_intror HIN)) as OP.
          assert (PA : A + 4 * i <= pX \/ pX + 4 * nX <= A) by (apply HAP; apply in_app_iff; left; exact HIN).
          assert (HINP : In (pX, 4 * nX) (((A, 4 * i) :: LB) ++ fdata LF)) by (right; apply in_app_iff; left; exact HIN).
          (* [comment removed for export] *)
          zstep. shadow_chk OX2 (X + 10) 2.
          zstep.
          replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
            by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
          zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
          zstep. zstep.
          (* [comment removed for export] *)
          assert (HN2 : rw_cells asegs m2 A ([CB (4 * length xs)%nat (repeat (Z_to_bv 8 0) (4 * length xs))]
                                              ++ [CB (Z.to_nat (4 * (i - nX))) (repeat (Z_to_bv 8 0) (Z.to_nat (4 * (i - nX))))])).
          { eapply rw_cells_reshape; [exact HNEW| |].
            - cbn. rewrite !repeat_length; repeat split; reflexivity.
            - cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. clear - LENX Hin; lia. }
          apply rw_cells_app in HN2. destruct HN2 as [HNA HNB]. cbn [cells_size csize Nat.add] in HNB. clear HNEW.
          replace (A + Z.of_nat (4 * length xs + 0)) with (A + nX * 4) in HNB by (clear - LENX; lia).
          apply (u8arr_of_rw_cells asegs) in HNA.
          pose proof (proj1 (u32arr_of_cells asegs m2 pX _ _ xs PCH eq_refl)) as PBA.
          pose proof (munch_refl [(A, A + nX * 4); (lo, bv_unsigned sp); (X, X + 16)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2'.
          pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + nX * 4)] m2) as MUX.
          pose proof (conj HXS1 I) as HXS0. pose proof (conj HYS1 I) as HYS0. pose proof (conj PBY2 I) as PBY0.
          pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY_CP) as SPC. unfold A_ASAN_MEMCPY_CP in SPC.
          acallxA_sp (bv_unsigned sp + -80)
            (eapply SPC with (h := h2) (LB := (A, 4 * i) :: LB) (LF := LF) (DST := A) (SRC := pX) (n := nX * 4) (lo := lo)
                              (ds := repeat (Z_to_bv 8 0) (4 * length xs)) (ss := u32s xs);
             rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
             try eassumption; try reflexivity;
             first [ left; rewrite AMC; reflexivity
                   | rewrite repeat_length; clear - LENX; lia
                   | rewrite u32s_length; clear - LENX; lia
                   | eapply aobj_sub; [exact OA| clear; lia| clear - Hin LENX NRX; lia]
                   | eapply aobj_sub; [exact OP| clear; lia| clear; lia]
                   | right; clear - PA Hin N1; lia
                   | left; clear - AS PC ALO LOS Hin N1; lia
                   | right; pose proof (alloc_ceiling_val R) as ACV; clear - AC PC Hin N1 ACV; lia
                   | eapply crange_sub; [exact SCS2| clear - LOS; lia| clear - TOP2 HTOP2; lia]
                   | eapply client_wrange_block; [exact HINA| clear; lia| clear - Hin NRX; lia]
                   | clear - NRX NRY Hi Hin LOS SLO NEEDR NRA TOP2 SPA SPR; lia
                   | match goal with |- ?g => idtac "MEMCPY1-PRE-LEFT:" g end ]).
          clear SPC.
          all: match goal with |- aevtA _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY1-SIDE:" g end.
          lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
          match goal with H : u8arr asegs m3 A (u32s xs) |- _ => rename H into HPA end.
          match goal with H : stk asegs m3 lo _ |- _ => rename H into ST3 end.
          match goal with H : HM asegs R HIA h2 _ LF m3 |- _ => rename H into HH3 end.
          match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
          try clear HXS1. destruct HXS0 as [HXS1 _].
          apply (rw_cells_transport asegs _ m2 m3 _ _ HXS1 MUX) in WM2' as HXS3; [| cbn [disjoint_from cells_size csize Nat.add]; clear - XA DSX Hin Hi NRX; lia].
          (* [comment removed for export] *)
          zstep. zstep. zstep.
          replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
            by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
          zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
          zstep.
          replace (4 * length xs)%nat with (Z.to_nat (nX * 4)) in PCH by (clear - LENX; lia).
          assert (CW4 : client_wrange L (((A, 4 * i) :: lb_remove pX LB) ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16).
          { eapply client_wrange_mono; [exact CWk|]. intros b Hb. apply in_app_iff in Hb. apply in_app_iff.
            destruct Hb as [Hb|Hb]; [left; right; eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb] | right; exact Hb]. }
          pose proof (conj HXS3 I) as HXS0'. pose proof (conj HPA I) as HPA0. clear HYS0 PBY0.
          match goal with H : rw_cells asegs m3 Y _ |- _ => pose proof (conj H I) as HYS0 end.
          match goal with H : bytes_at asegs m3 pY (u32s ys) |- _ => pose proof (conj H I) as PBY0 end. pose proof (conj MI3 I) as MI30.
          match goal with H : aobj asegs AL (hcs asegs R HIA h2) m3 Y 16 |- _ => pose proof (conj H I) as OY20 end.
          free_limbs_call h2 ((A, 4 * i) :: LB) HIN PCH.
          all: match goal with |- forall _ _, _ -> aevtS _ _ _ => idtac | |- ?g => idtac "ZF1-LEFT:" g end.
          (intros ms' mo4' dd_H; ddestruct dd_H as (mo3 & [HK3 MF3] & PO)).
          destruct_exs PO. destruct PO as [E PO]. injection E as E1 E2. subst ms' mo4'.
          rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in PO by qlia.
          ddestruct PO as (MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & HH4).
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
            replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
          lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
          match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
          rewrite (lb_remove_cons_other A (4 * i) pX LB) in HP4, HH4 by (clear - PA Hin N1 Hi; lia).
          assert (HP4' : presA asegs R ((A, 4 * i) :: lb_remove pX LB) LF (bv_unsigned sp + -80) (arl_stklo R) (hstkhi asegs R HIA h2) [] m3 m4).
          { eapply (presA_drop_freed asegs R HIA h2 ((A, 4 * i) :: LB) LF _ [] pX (4 * nX) m3 m3 m4);
              [exact HH3| right; exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia
              | replace (pX + 4 * nX) with (pX + nX * 4) by (clear; lia); exact HP4].
            intros b xb [Hb|Hb] Hr.
            - subst b. split; [left; reflexivity|]. intros E. injection E as E1' E2'. clear - E1' PA Hin N1 Hi. lia.
            - split; [right; eapply In_lb_remove; exact Hb|]. intros E. subst b. exact (lb_remove_notin LB pX (4 * nX) ND Hb). }
          clear HP4 PCH PBA OP HINP HINA.
          presA_transport HP4'.
          (* [comment removed for export] *)
          assert (YCR4 : client_range L (((A, 4 * i) :: lb_remove pX LB) ++ fdata LF) (bv_unsigned sp + -80) Y 16).
          { intros a Ha. destruct Q4 as [Q|Q]; [| left; clear - Q Ha; lia].
            destruct (YCR a Ha) as [Hs|[Hd|(b & Hb & Hr)]]; [exfalso; clear - Hs Q Ha; lia| right; left; exact Hd| right; right].
            apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exists b; split; [apply in_app_iff; right; exact Hb| exact Hr]].
            destruct b as [B k]. exists (B, k). split; [| exact Hr]. apply in_app_iff. left. right. apply In_lb_remove_keep; [exact Hb|].
            intros ->. cbn in Hr. pose proof (nodup_fst_neq LB pX (4 * nX) pX k ND HIN Hb) as NE.
            destruct (Z.eq_dec k (4 * nX)) as [->|NK]; [clear - Hr Ha Q2'; lia|]. apply NE; [| reflexivity]. intros E. injection E as E'. exact (NK E'). }
          assert (YBLK4 : ownY = LHeap -> In (pY, 4 * nY) ((A, 4 * i) :: lb_remove pX LB)).
          { intros E0. right. apply In_lb_remove_keep; [exact (YBLK E0)|]. intros E. dpose MAY as [[_ (_ & _ & LY & _ & OY)] _].
            cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in LY, OY. rewrite E0 in OY. destruct OY as [NY1 _]. clear - E Q3' NY1 N1. lia. }
          destruct HYS0 as [HYS3 _]. destruct HPA0 as [HPA3 _]. destruct PBY0 as [PBY3 _]. try clear MI3. destruct MI30 as [MI3 _]. try clear OY2. destruct OY20 as [OY2 _].
          pose proof (presA_rw_cells asegs R _ _ _ _ _ _ m3 m4 Y _ HP4' HYS3 YCR4 ltac:(cbn; exact I)) as HYS4.
          pose proof (pby_keep _ _ _ _ _ _ _ HP4' PBY3 MI3 MI4 YBLK4 OYN ltac:(cbn; exact I)) as PBY4.
          assert (HPA4 : u8arr asegs m4 A (u32s xs)).
          { apply (rw_cells_of_u8arr asegs) in HPA3. apply (u8arr_of_rw_cells asegs) with (n := length (u32s xs)).
            eapply (presA_rw_cells asegs R); [exact HP4'| exact HPA3| | cbn; exact I].
            cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, u32s_length.
            eapply client_range_block; [apply in_app_iff; left; left; reflexivity| clear; lia| clear - LENX Hin NRX; lia]. }
          pose proof (presA_aobj0 asegs R (hcs asegs R HIA h2) _ _ _ _ _ _ m3 m4 Y 16 CSOK2 HP4' OY2 (hcs_below_top asegs R HIA h2) ltac:(right; split; [exact YCR4| clear - ALO LOS SLO NEEDR; lia])) as OY4.
          presA_transport HP4'.
          apply (aevtA_enter asegs (KF asegs R HIA h4 mo) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
          pose proof (AIh_laws asegs R HIA h4) as LAWS4. pose proof (KF_kinv asegs R HIA h4 mo) as KINV4.
          pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OX2) as OX4. pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCS4 OY4) as OY4'.
          assert (TOP4 : bv_unsigned sp <= htop asegs R HIA h4) by (rewrite HT4; exact TOP2).
          assert (HINA4 : In (A, 4 * i) ((A, 4 * i) :: lb_remove pX LB)) by (left; reflexivity).
          apply (rw_cells_of_u8arr asegs) in HPA4. rewrite u32s_length in HPA4.
          assert (HA4 : u32arr asegs m4 A (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (i - nX)))).
          { apply u32arr_app. split; [eapply (u32arr_of_cells asegs); [exact HPA4| reflexivity]|].
            replace (A + 4 * Z.of_nat (length xs)) with (A + nX * 4) by (clear - LENX; lia).
            replace (Z.to_nat (4 * (i - nX))) with (4 * Z.to_nat (i - nX))%nat in HNB by (clear - Hin Hi; lia).
            eapply (u32arr_of_cells asegs); [exact HNB| symmetry; apply u32s_repeat0]. }
          (* [comment removed for export] *)
          zstep.
          eapply (aevtA_cut_evtA asegs AL _ LAWS4 _ _ _ _ _ _ KINV4);
            [ eapply (fin_walk h4 ((A, 4 * i) :: lb_remove pX LB) m4 i A pX (xs ++ repeat (Z_to_bv 64 0) (Z.to_nat (i - nX)))); try eassumption; try reflexivity
            | intros y Hy; exact Hy | ].
          all: try (rewrite HT4; exact HT2).
          all: try (rewrite length_app, repeat_length; clear - Hi Hin LENX; lia).
          all: try (clear - A0 AC ALO LOS SLO SPR NEEDR Hi; lia).
          all: try (clear - P0 PC ALO LOS SLO SPR NEEDR NRX; lia).
          all: try (eapply opy_at; [exact HH4| exact YBLK4| exact OYN]).
          all: try (clear - YPA; lia).
          all: try (clear - YA; lia).
          all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "GFIN1-PRE-LEFT:" g end.
          intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & E9 & MU9 & WM9 & MI9 & HA9 & HX9 & ST9 & HH9). subst ms'.
          apply aevtA_done. intros mo9 [HK9 MF9].
          (* [comment removed for export] *)
          assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
          { eapply presA_trans; [exact HPX2|]. eapply presA_trans; [| eapply presA_trans].
            - (* [comment removed for export] *)
              rewrite <- HS2. eapply (presA_tail3 h2 ((A, 4 * i) :: LB) A (nX * 4) (4 * i) m3 m4 m2 m3);
                [exact HH3| intros b Hb; right; eapply In_mpd_keep; exact Hb| left; reflexivity| exact HFRA| clear - N1; lia| clear - Hin; lia| exact TOP2| exact OX2| exact MU2| exact WM2'].
              all: match goal with |- ?g => idtac "M23-LEFT:" g end.
            - (* [comment removed for export] *)
              eapply presA_weaken; [exact HP4'| | intros b Hb; exact Hb| clear; lia| clear; lia| rewrite HS2; clear; lia| intros y _; exact I].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb].
            - (* [comment removed for export] *)
              rewrite <- HS2, <- HS4.
              eapply (presA_tail3 h4 ((A, 4 * i) :: lb_remove pX LB) A (4 * i) (4 * i) m4 m4 m4 m9);
                [exact HH4| | left; reflexivity| exact HFRA| clear - Hi; lia| clear; lia| exact TOP4| exact OX4| exact MU9| exact WM9].
              intros b Hb. right. eapply (in_keep_remove LB dX); [exact ND| exact EO| exact HIN| exact Hb]. }
          eapply (post_ok mo mo9 h4 m9 ((A, 4 * i) :: lb_remove pX LB) i i A []); try eassumption.
          * clear; lia.
          * clear - Hi Hin; lia.
          * right. split; [reflexivity| exact TI].
          * intros k w Hk. destruct k; discriminate Hk.
          * rewrite HT4; exact HT2.
          * rewrite HS4; exact HS2.
          * rewrite HF4; exact HF2.
          * intros y Hy. apply HCS4, HCS2, Hy.
          * unfold copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; cbn [md_n] in *. clear - HV2 HV4 Hi. lia.
          * unfold copy_FR, calls_FR, fr_charge in *. clear - HFR2 HFR4 D0. lia.
          * rewrite app_nil_r. eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - Hi NRY; lia| exact SGY| intros E; discriminate E|].
            { rewrite firstn_length_le by (clear - Hi LENY; lia). clear - Hi; lia. }
            intros _. split; [clear - Hi; lia|]. split; [left; reflexivity|]. split; [exact A16|].
            apply (rw_cells_of_u8arr asegs) in HA9. eapply (u32arr_of_cells asegs); [exact HA9| reflexivity].
          * unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
            split; [reflexivity|]. split; [discriminate|].
            split; [intros b [Hb|Hb]; [right; left; exact Hb| left; eapply In_lb_remove; exact Hb]|].
            split.
            { intros [Bb kb] Hb Hn. right. apply In_lb_remove_keep; [exact Hb|].
              apply (nodup_fst_neq LB pX (4 * nX) Bb kb ND HIN Hb). intros E. apply Hn. left. symmetry. exact E. }
            intros b [<-|[]] [E|Hb']; [exfalso; injection E as E1 E2; clear - E1 PA Hi Hin N1; lia| exfalso; exact (lb_remove_notin LB pX (4 * nX) ND Hb')].
          * right. apply fresh_apart_keep. exact HFRA.
          * right. intros Hin'. destruct (HAP A (4 * i) ltac:(apply in_app_iff; left; exact Hin')); clear - H Hi; lia.
      all: match goal with |- ?g => idtac "GROW-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Grow.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L10569489964.3  L13015518834.1  L16586317243.118L27255558078.3  L28155996092.112L28156049118.115L30259373055.6  L33522118006.2  L36571201320.0  L372355051.4    L43442341258.4  L45270656294.3  L57933094146.4  L59308551419.6  L59310683537.4  L68633794283.3  Q15161612445.118Q23053006273.118Q23053041492.115Q23053365576.118Q26295627581.118Q44945662387.115Q50458135125.118Q51776267970.118Q7881909887.118 Q8943673138.115 00000800;00o01901k02]02e02k02l03903F03P03]04204?04I04e05:05O05d06906U06j07F07_084S1k1j2HjS1jS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y04LENY3PY03PYB1wS2nY1j3HjrS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y04LENY3PY03PYBS2sp1X2xs1Y2nY2pY2ys1k1j2Hj3Hjr2X02Y04LENY3PY03PYBS1j1i2HiS2pY1jSS2nY1j3Hjr2K3S2nY1j3Hjr2K3S2nY1j3HjrS2nY1j3Hjr2K3S2nY2ys1j3Hjr4LENY2NXS2nY1j2Hj3HjrS2nY1j3HjrS2xs2nY2pY2ys1k1j2Hj3Hjr3PYBS2xs2pY2ys1k1j2Hj3PYBS2xs2pY2ys1k1j2Hj3PYBS2xs2pY2ys1k1j2Hj3PYBS2xs2pY2ys1k1j2Hj3PYBS2xs2nY2pY2ys1k1j2Hj3Hjr3PYBS2xs2pY2ys1k1j2Hj3PYBS2xs2nY2pY2ys1k1j2Hj3Hjr3PYBS2xs2pY2ys1k1j2Hj3PY03PYBS2xs2pY2ys1k1j2Hj3PYB". (* [comment removed for export] *)
  #[using="IMG LB m sgX nX pX xs padX ownX sgY padY ownY MAX MAY NEQ SEP"] Lemma scan_loop : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pk,$64.Pj,$8.Pmm,P,(3.&40.)(5.(3.&8.))Pxra,(3.&40.)Pxs1,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(=.$8.R14.(3?.R15.))P,(3=.(20.+1.R15.)(20.R15.(22.VnY,+1.)))P,(63.Vys,(2>.R16.+1.))P,(4:.$43.R16.VpY,(4;.Vys,))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R17.VpY,(1;.+4.VnY,))P,(27.$43.R18.)(52.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)Lms',$53.(54.$8.Li,$8.(54.(3.&40.)Lxa0',(3.&40.)(54.(3.&40.)Lxa2',(3.&40.)(54.(3.&40.)Lxa4',(3.&40.)(54.(3.&40.)Lxa5',(3.&40.)(41.(3=.(=.$53.R6.(39.(3:.R1>.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R1<.R1;.R1:.(25.&40.VX,)R1=.R4.(25.&40.VY,)R3.(25.&40.(22.R5.+1.))R2.R1.R17.R16.R15.R14.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R13.R12.R11.Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(25.&40.+9;=68.)Vfc,(3;.(3.&40.))R1?.(3<.$43.)))(3=.(3=.(20.+2.R5.)(20.R5.(2>.R20.+1.)))(3=.(63.Vys,R5.)(62.Vys,R5.))))(3=.(=.$53.R6.(39.(3:.R1>.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R1<.R1;.R1:.(25.&40.VX,)R1=.R4.(25.&40.VY,)R3.(25.&40.=)R2.R1.R17.R16.R15.R14.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R13.R12.R11.Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(25.&40.+9;>7<.)Vfc,(3;.(3.&40.))R1?.(3<.$43.)))(3=.(=.$8.R5.+1.)(63.Vys,+1.)))))))))(39.(3:.R18.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R16.R15.R14.(25.&40.VX,)R17.(25.&40.(2>.VpY,(1;.+4.R1:.)))(25.&40.VY,)(25.&40.(2>.VpY,(1;.+4.R1:.)))(25.&40.R1:.)R13.R12.R11.R10.R?.R>.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R=.R<.R;.Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(25.&40.+9;>40.)Vfc,(3;.(3.&40.))R19.(3<.$43.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until xt6; intros Hj Hjr ZY PBY OPY MI; [exfalso; clear - Hj Hjr; lia|].
    pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
    pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    dpose PBY as (PY0 & PYB & _). rewrite u32s_length in PYB.
    destruct (nth_error ys (Z.to_nat j)) as [w|] eqn:NX; [| apply nth_error_None in NX; exfalso; clear - NX Hjr LENY; lia].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk OPY (pY + 4 * j) 4.
    (* [comment removed for export] *)
    pose proof (u32ro_read asegs mm pY ys j w _ PBY NX ltac:(clear - Hjr; lia) eq_refl) as RD.
    zstep. clear RD.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(clear; lia)) as Bw.
    (* [comment removed for export] *)
    zstep. if_cases K2; zify_cond K2; rewrite ?bv_unsigned_sx32 in K2.
    - (* [comment removed for export] *)
      apply evtA_done. exists (j + 1). deexists 4. left.
      split; [replace (j + 1 - 1) with j by (clear; lia); reflexivity|].
      split; [clear - Hjr; lia|]. split; [exact ZY|].
      right. exists w. split; [replace (Z.to_nat (j + 1 - 1)) with (Z.to_nat j) by (clear - Hjr; lia); exact NX|].
      intros WZ. apply K2. apply (proj2 (sxz_zero_iff _ Bw)). exact WZ.
    - (* [comment removed for export] *)
      apply (proj1 (sxz_zero_iff _ Bw)) in K2.
      pose proof (zeros_above_down' ys j w ltac:(clear - Hjr; lia) ZY NX K2) as ZY'.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by (clear - Hjr NRY; lia).
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (pY + 4 * j + -4)) with (Z_to_bv 64 (pY + 4 * (j - 1))) by (f_equal; clear; lia).
        replace (Z_to_bv 64 (j + -1)) with (Z_to_bv 64 (j - 1)) by (f_equal; clear; lia).
        eapply evtA_mono; [eapply (IH (j - 1)); try eassumption; [clear - Hj; lia| clear - Hjr K3; lia| replace (j - 1 + 1) with j by (clear; lia); exact ZY'] |].
        cbv beta. intros ms' PO. ddestruct PO as (i & xa2' & xa3' & xa5' & xa6' & [(E & Hi & Zi & Ti)|(E & Hi & Zi)]).
        * exists i. deexists 4. left. split; [exact E|]. split; [clear - Hi K3 Hjr; lia|]. split; [exact Zi| exact Ti].
        * exists i. deexists 4. right. split; [exact E|]. split; [exact Hi| exact Zi].
      + (* [comment removed for export] *)
        zstep. replace (Z_to_bv 64 (j + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K3 Hjr; lia).
        apply evtA_done. exists 1. deexists 4. right. split; [reflexivity|]. split; [reflexivity|].
        replace 1 with j by (clear - K3 Hjr; lia). exact ZY'.
    all: match goal with |- ?g => idtac "SCAN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma sign_mod16 : forall s, s = 1 \/ s = -1 -> (bv_unsigned (Z_to_bv 64 s) mod 2 ^ 16) mod 2 ^ 16 = s mod 2 ^ 16.
  Proof. intros s [-> | ->]; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Tail.
    Variable mo : Model.
    Hypothesis OYN : ownY <> LNull.
    Hypothesis BUD : havol asegs R HIA h + copy_PHI dY <= AVOL_MAX.
    Hypothesis BUDF : hfr asegs R HIA h + copy_FR d <= FR_MAX.
    Hypothesis Q1 : X + 16 <= pY \/ pY + 4 * nY <= X.
    Hypothesis Q2 : ownX = LHeap -> Y + 16 <= pX \/ pX + 4 * nX <= Y.
    Hypothesis Q3 : ownX <> LHeap \/ pX + 4 * nX <= pY \/ pY + 4 * nY <= pX.
    Hypothesis Q4 : Y + 16 <= lo \/ bv_unsigned sp <= Y.
    Hypothesis Q5 : pY + 4 * nY <= lo \/ bv_unsigned sp <= pY.
    Hypothesis Y47 : pY + 4 * nY + 8 <= 2^47.
    Hypothesis DSX : X + 16 <= lo \/ bv_unsigned sp <= X.
    Hypothesis DXP : ownX = LHeap -> X + 16 <= pX \/ pX + 4 * nX <= X.
    Hypothesis CW : client_wrange L (LB ++ fdata LF) (bv_unsigned sp) (htop asegs R HIA h) X 16.
    Hypothesis PYfresh : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "PA,$8.Pk,$8.P,(6>.VR,VLB,VLF,R2.R1.)P,(41.(20.(2>.R3.R2.)(75.(15.VR,)))(20.(76.(15.VR,))R3.))P,(3>.=R3.)(41.(20.(2>.VpY,(1;.+4.VnY,))R5.)(20.(2>.R5.R4.)VpY,))")
(* [comment removed for export] *).
    Hypothesis Yfresh : forall A k, fresh_apart R LB LF A k -> 0 < k -> Y + 16 <= A \/ A + k <= Y.
    Hypothesis YBLK : ownY = LHeap -> In (pY, 4 * nY) LB.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L1164172544.1  L14579576775.14L1649577667.2  L19945316590.2 L2547996026.5  L26892418956.1 L29428324939.5 L32027975233.0 L3253508485.5  L35653441506.7 L38723301197.5 L40281191306.3 L41858356445.5 L4235704437.5  L48132467214.7 L59308668813.6 L60098763854.3 L62018535662.1 L62622784051.44L68294535841.2 L7007305626.5  00000300H00P00W00^00b01401501F01^01m02602F02V03103D03N03Q03R03Y03jS1XS2sp1X2nX2pX2lo3DSX1HS2nX3NRXS2sp2loS2nX2nYS2spS1R2lo3LOS3ALO3ACPSS2nY2ys1i2Hi4LENYS1R3HIA1h2sp2lo3TOP4HTOPS1R3HIA1h1d3D0'S1R3HIA1hS2nX2nY1i2Hi3HinS1R3HIA1h2nY3NRYS1R5NEEDR2sp2lo3LOS3SLO3ALOS2nX2nY1i2Hi3Hin2EnS1R2lo3LOSS1RFS2nX2pXS2nX2pX2nY2pY3Q3'". (* [comment removed for export] *)
    #[using="IMG AMC AMS NEEDR HND DIMG MAX NST MAY NEQ SEP CSEP YLCR XW LOS SLO TOP YNZ XUW OYN Q2 Q3 Q4 Q5 Y47 DSX DXP YBLK"] Lemma memset_finish : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmc,P,(3.&40.)(5.(3.&8.))Pi,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,Vh,VLB,VLF,R15.)P,(3=.(20.+1.R15.)(20.R15.VnY,))P,(20.R16.VnX,)P,(63.Vys,R17.)P,(41.(=.$8.VnX,VnX,)(3=.(=.$8.VnX,R18.)(62.Vys,R18.)))P,(4=.$43.R1:.VX,(4>.$4?.(50.(25.&40.VpX,))(4>.$4?.(72.(25.&40.VsgY,))(4>.$4?.(72.(25.&40.VnX,))(4>.$4?.(73.VpadX,)(51.$4?.))))))P,P,(=.$>.VownX,$19.)(4=.$43.R1<.VpX,(4>.$4?.(79.(7:.#4.(40.(3.&40.)Vxs,))(4;.Vxs,))(51.$4?.)))P,(4=.$43.R1<.VY,(4>.$4?.(50.(25.&40.VpY,))(4>.$4?.(72.(25.&40.VsgY,))(4>.$4?.(72.(25.&40.VnY,))(4>.$4?.(73.VpadY,)(51.$4?.))))))P,(4:.$43.R1=.VpY,(4;.Vys,))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1>.VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1?.VY,+10.)P,(4=.$43.R20.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R21.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R22.)P,(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,R23.)(77.$43.(78.$43.VR,VHIA,Vh,Vmo,)(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(39.(3:.R22.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R21.R20.R1?.(25.&40.VX,)(25.&40.R23.)(25.&40.VnX,)(25.&40.VY,)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R16.R15.R14.Vs9,Vs10,Vs11,R13.R12.R11.R10.)VF,(25.&40.+9;><<.)Vfc,(3;.(3.&40.))R24.(3<.$43.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HHc Hi Hin ZY _ HXS PCH HYS PBY OX OY FR ST MI HP. basic_facts h LB mc HHc TOP.
      dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      assert (EO : ownX = LHeap).
      { dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN.
        destruct ownX; [destruct HOWN as [_ En]; exfalso; clear - En Hi Hin; lia| reflexivity| exfalso; exact (NST eq_refl)]. }
      dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite EO in HOWN.
      ddestruct HOWN as (N1 & HIN & P16 & _).
      assert (Q3' : pX + 4 * nX <= pY \/ pY + 4 * nY <= pX) by (destruct Q3 as [Q|Q]; [exfalso; exact (Q EO)| exact Q]).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply (memset_path mc i); try eassumption; try exact EO
        | intros y Hy; exact Hy | ].
      all: try (unfold mpi_cells; exact HXS).
      all: try (eapply (u32arr_of_cells asegs); [exact (PCH EO)| reflexivity]).
      all: try (eapply opy_at; [exact HHc| exact YBLK| exact OYN]).
      all: try exact (Q2 EO). all: try exact (DXP EO). all: try (clear - Q3'; lia).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "MSF-PRE-LEFT:" g end.
      intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & E9 & MU9 & WM9 & MI9 & HA9 & ST9 & HH9). subst ms'.
      apply aevtA_done. intros mo9 [HK9 MF9].
      assert (HPX9 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m9).
      { eapply presA_trans; [exact HP|].
        apply (munch_weaken _ [(lo, bv_unsigned sp); (pX, pX + 4 * nX); (X, X + 16)]) in MU9; [| clear; intros x Hx; clear - Hx; cbn [outside] in *; tauto (* [comment removed for export] *)].
        eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] pX (4 * nX) mc mc m9);
          [exact HHc| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
        { intros b xb Hb Hr. split; [eapply In_mpd_keep; exact Hb|]. intros E. subst b.
          exact (lb_remove_notin LB pX (4 * nX) (HND _ _ _ _ HHc) (in_keep_remove LB dX _ (HND _ _ _ _ HHc) EO HIN Hb)). }
        eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                  (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX); (X, X + 16)]);
          [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
        eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) mc mc m9); [exact HHc| | clear; lia| exact LOS].
        eapply (presA_of_munch asegs R LB LF _ _ _ _ mc m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HHc| | exact Hc]; clear; lia | exact MU9 | exact WM9].
        unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (pX + 4 * nX - pX) with (4 * nX) by (clear; lia); eapply aobj_crange; eapply hm_aobj_block; [exact HHc| exact HIN]|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil. }
      eapply (post_ok mo mo9 h m9 LB i nX pX (repeat (Z_to_bv 64 0) (Z.to_nat (nX - i)))); try eassumption; try reflexivity.
      * clear - Hin NRY; lia.
      * left; reflexivity.
      * intros k w Hk. apply nth_error_In, repeat_spec in Hk. subst w. rewrite unsigned_lit by (clear; lia). reflexivity.
      * intros y Hy; exact Hy.
      * unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]. clear - NRY. lia.
      * unfold copy_FR, calls_FR, fr_charge. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'. clear - D0'. lia.
      * eapply mpd_at_rebuild; [discriminate| unfold mpi_cells| exact XAL| exact X0| | unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGY| intros E; discriminate E|].
        { eapply (rw_cells_transport asegs _ mc m9); [exact HXS| exact MU9| exact WM9| cbn [disjoint_from cells_size csize Nat.add]; clear - DSX DXP EO Hi Hin; pose proof (DXP EO); lia]. }
        { rewrite length_app, firstn_length_le, repeat_length by (clear - Hi LENY; lia). clear - Hi Hin; lia. }
        intros _. split; [exact N1|]. split; [exact HIN|]. split; [exact P16| exact HA9].
      * unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. rewrite EO.
        split; [reflexivity|]. split; [discriminate|].
        split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b _ _; reflexivity.
      * left. cbn [mpd_blk md_own md_p md_n]. rewrite EO. left. reflexivity.
      * left. cbn [mpd_blk md_own md_p md_n]. rewrite EO. left. reflexivity.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0120@D24976250634.158D50797141399.158D52014138856.158K21652967687.158K38539219888.158K43762715123.158L10320308030.6  L11913617988.5  L21646329835.2  L29074168500.147L29074644410.144L29428324939.5  L35653441506.7  L37314864565.142L37314936640.145L38549538015.2  L39268637205.0  L40825300204.149L41849979366.5  L43767073266.3  L44397119898.2  L46160487540.148L46165130556.145L47955344026.2  L47957477937.148L48773092713.148L48773092840.149L59308628433.5  L60098763854.3  L67984097661.1  L68470634364.14 Q12047062176.150Q20414272036.158Q22285631880.155Q22286196081.152Q22288293173.154Q24974040330.157Q26207721832.156Q26209519062.155Q26220436439.153Q31651985791.155Q39212284437.153Q39212284437.155Q39212284437.156Q39424119965.153Q42081808994.155Q43925228937.156Q49046334496.153Q4926406185.155 Q4957738831.154 Q52016320488.157Q54255983964.154Q56761401107.155Q60511567613.153Q60511567613.155Q60511567613.156Q60697995187.156Q61417945732.150Q61418027910.153Q61418027910.154Q62965564504.156Q63232048813.152Q8884615307.153 Q9534674040.153 Q9538243134.152 Q9538787269.150 00000Q01O02002b03D03n04704@04A04U04i05;05S05g06;06<06=06K06T06U06]07107E07M07b08F08j09:09D09G09m0:60:X0:a0:j0;30;O0;X0;a0;j0<30<<0<E0<N0<W0<f0<o0=;0=D0=M0=i0>20>>0>E0>L0>S0>_0>h0?10?:0?O0?X0?a0?h0?o0@6S2sp1X2xs1Y3sgY2ys2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs1Y3sgY2ys2lo3LOS3SLO3SPR2X02Y02HB5Ha_st5Hl_stS2sp1X2xs1Y3sgY2ys2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs3sgY2ys2lo3SLO3DSX2HB5Ha_st5Hl_stS1X2xs1Y3sgY2ys3SXY2HB5Ha_st5Hl_stS1X2xs3sgY2nY2pY2ys2Q14LENY2HB5Ha_st5Hl_stS2nX2ys1iS2nX1i2K1FS2sp1X2xs1Y2ys2X02XBS2sp1X2xs1Y2ys2X02XBS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS2sp1X2xs1Y2ys2Y02YBS2sp1X2xs1Y2ys2Y02YBFSS2sp1X2xs1Y2ysS2nX1i2K1FS2nX3NRXS2sp1X2xs1Y2ys2X02XBS2sp1X2xs1Y2ys2X02XBS2nX3NRXS2sp1X2nX2xs1Y2ys3NRXS2sp1X2xs1Y2nY2ys1i2Hi3SPR2X02Y03NRYS2sp1X2xs1Y2nY2ys1i2Hi3SPR2X02Y03NRYS2nY1i2Hi3NRY2K2S1R2lo3LOSS1iS1R2sp1X2nX2pX2xs2lo3LOS3ALO4LENX2BC1DS2xs1Y2ysS2sp1X2xs3sgY2ys2lo2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs3sgY2ys2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS2xs1Y2ysS1X2xs2ysS1X2xs2ysS2xs1Y2ysS1X2xs2ys2X02HBS1X2xs2ysS2xs1Y2ys2Y0S1X2xs2ysS2xs1Y2ysS1X2xs3sgY2ys2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ys2X0S2xs2ysS2xs2ysS2xs2ysS1X2xs2ys2X0S2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS1X2xs2ys2XB2HB5Ha_stS1X2xs2ysS1X2xs2ysS2xs2ysS2xs2ysS2xs2ys". (* [comment removed for export] *)
    #[using="C24T IMG ZF CALLOC AMC AMS NEEDR HND DIMG MAX NST MAY NEQ SEP CSEP YCR YLCR XW LOS SLO TOP SPA TPV YNZ XUW OYN BUD BUDF Q1 Q2 Q3 Q4 Q5 Y47 DSX DXP CW PYfresh Yfresh YBLK"] Lemma tail_i : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pm1,P,(3.&40.)(5.(3.&8.))Pi,$8.Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs1,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,Vh,VLB,VLF,R16.)P,(4=.$43.R17.VX,(4>.$4?.(50.(25.&40.VpX,))(4>.$4?.(72.(25.&40.VsgX,))(4>.$4?.(72.(25.&40.VnX,))(4>.$4?.(73.VpadX,)(51.$4?.))))))P,P,(=.$>.VownX,$19.)(4=.$43.R19.VpX,(4>.$4?.(79.(7:.#4.(40.(3.&40.)Vxs,))(4;.Vxs,))(51.$4?.)))P,(4=.$43.R19.VY,(4>.$4?.(50.(25.&40.VpY,))(4>.$4?.(72.(25.&40.VsgY,))(4>.$4?.(72.(25.&40.VnY,))(4>.$4?.(73.VpadY,)(51.$4?.))))))P,(4:.$43.R1:.VpY,(4;.Vys,))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1;.VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1<.VY,+10.)P,(4=.$43.R1=.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R1>.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R1?.)P,(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,R20.)P,(3=.(20.+1.R20.)(20.R20.VnY,))P,(63.Vys,R21.)P,(62.Vys,R22.)(77.$43.(78.$43.VR,VHIA,Vh,Vmo,)(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(39.(3:.R22.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R21.R20.R1?.(25.&40.VX,)R18.R1>.(25.&40.VY,)R1=.(25.&40.(22.R23.+1.))R1<.R1;.R1:.R19.R17.R16.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R15.R14.R13.Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(25.&40.+9;=68.)Vfc,(3;.(3.&40.))R24.(3<.$43.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HH1 HXS1 PCH1 HYS1 PBY1 OX1 OY1 FR1 ST1 MI1 HP1 Hi ZY TI. basic_facts h LB m1 HH1 TOP.
      dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OY1 (Y + 8) 2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX1 (X + 8) 2.
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      unfold zx16 in HXS1.
      apply (rw_cells_C2_congr asegs m2 X [C8 (Z_to_bv 64 pX)] _ sgY) in HXS1; [| apply sign_mod16; exact SGY]. cbn [app] in HXS1.
      assert (HP2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|]. eapply (presA_tail asegs R HIA h LB); [exact HH1| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact OX1| exact MU| exact WM]. }
      assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]).
      { intros E0. dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite E0 in HOWN.
        ddestruct HOWN as (N1 & HIN & _). destruct (hm_apart asegs R HIA h LB LF m2 HH1) as [HF _]. rewrite Forall_forall in HF.
        destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        eapply (rw_cells_transport asegs _ m1 m2); [exact (PCH1 E0)| exact MU| exact WM|].
        cbn [disjoint_from cells_size csize Nat.add]. pose proof (DXP E0) as D. clear - D BC ALO LOS SLO NEEDR LENX; lia. }
      clear MU WM HP1 PCH1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
      zstep. replace (i - 1 + 1) with i by (clear; lia).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - Hi NRX NRY; lia).
      - (* [comment removed for export] *)
        eapply (memset_finish m2 i); try eassumption. all: try (clear - K1 Hi; lia).
        all: match goal with |- ?g => idtac "TI-MS-LEFT:" g end.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases K2; zify_cond K2.
        + eapply (grow_path mo m2 i); try eassumption. all: try (clear - K1 Hi; lia).
          all: match goal with |- ?g => idtac "TI-GP-LEFT:" g end.
        + exfalso. revert K2. rewrite ?unsigned_lit by (clear - Hi NRY; lia). rewrite Z.shiftr_div_pow2 by (clear; lia). clear - Hi NRY. intros K2. lia.
      all: match goal with |- ?g => idtac "TI-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00n0@D24976250634.158D50797141399.158D52014138856.158K21652967687.158K38539219888.158K43762715123.158L11660204229.4  L11660204229.5  L21646329835.2  L29074168500.147L29074644410.144L29428324939.5  L35653441506.7  L37314864565.142L37314936640.145L38549538015.2  L43767073266.3  L44397119898.2  L46160487540.148L46165130556.145L47955344026.2  L47957477937.148L4909666665.5   L56256620456.6  L60098763854.3  L68470634364.14 L895616489.4    Q12047062176.150Q20414272036.158Q22285631880.155Q22286196081.152Q22288293173.154Q24974040330.157Q26207721832.156Q26209519062.155Q26220436439.153Q31651985791.155Q39212284437.153Q39212284437.155Q39212284437.156Q39424119965.153Q42081808994.155Q43925228937.156Q49046334496.153Q4926406185.155 Q4957738831.154 Q52016320488.157Q54255983964.154Q56761401107.155Q60511567613.153Q60511567613.155Q60511567613.156Q60697995187.156Q61417945732.150Q61418027910.153Q61418027910.154Q62965564504.156Q63232048813.152Q8884615307.153 Q9534674040.153 Q9538243134.152 Q9538787269.150 00000Q01O02002b03D03n04604>04?04S04g05905Q05e06906:06;06C06W06k07307H07S07Z07d08J08Q08Z09<09E09N09W0:30:<0:E0:N0:W0:`0:i0;20;;0;J0;S0;_0;h0<10<M0<V0<b0<i0=00=70=C0=L0=U0=^0>30><0>E0>L0>S0>ZS2sp1X2xs1Y3sgY2ys2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs1Y3sgY2ys2lo3LOS3SLO3SPR2X02Y02HB5Ha_st5Hl_stS2sp1X2xs1Y3sgY2ys2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2xs3sgY2ys2lo3SLO3DSX2HB5Ha_st5Hl_stS1X2xs1Y3sgY2ys3SXY2HB5Ha_st5Hl_stS1X2xs3sgY2nY2pY2ys2Q14LENY2HB5Ha_st5Hl_stS2nY3HnYS2nY3HnYFS2sp1X2xs1Y2ys2X02XBS2sp1X2xs1Y2ys2X02XBS1R2lo3LOS3ALO3ACPS1R3HIA1h2sp2lo3TOP4HTOPS2sp1X2xs1Y2ys2Y02YBS2sp1X2xs1Y2ys2Y02YBFFS2nX3NRXS2sp1X2xs1Y2ys2X02XBS2sp1X2xs1Y2ys2X02XBS2nX3NRXS2sp1X2nX2xs1Y2ys3NRXS2nX3NRX2K1S2nX2ysS1R2lo3LOSS1R2sp1X2nX2pX2xs2lo3LOS3ALO4LENX2BC1DS2nX2K1S2xs1Y2ysS2sp1X2xs3sgY2ys2lo2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs3sgY2ys2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS2xs1Y2ysS1X2xs2ysS1X2xs2ysS2xs1Y2ysS1X2xs2ys2X02HBS1X2xs2ysS2xs1Y2ys2Y0S1X2xs2ysS2xs1Y2ysS1X2xs3sgY2ys2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ys2X0S2xs2ysS2xs2ysS2xs2ysS1X2xs2ys2X0S2xs1Y2ysS2xs1Y2ysS2xs1Y2ysS1X2xs2ys2XB2HB5Ha_stS1X2xs2ysS1X2xs2ysS2xs2ysS2xs2ysS2xs2ys". (* [comment removed for export] *)
    #[using="C24T IMG ZF CALLOC AMC AMS NEEDR HND DIMG MAX NST MAY NEQ SEP CSEP YCR YLCR XW LOS SLO TOP SPA TPV YNZ XUW OYN BUD BUDF Q1 Q2 Q3 Q4 Q5 Y47 DSX DXP CW PYfresh Yfresh YBLK"] Lemma tail_1 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pm1,P,(3.&40.)(5.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs1,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,Vh,VLB,VLF,R16.)P,(4=.$43.R17.VX,(4>.$4?.(50.(25.&40.VpX,))(4>.$4?.(72.(25.&40.VsgX,))(4>.$4?.(72.(25.&40.VnX,))(4>.$4?.(73.VpadX,)(51.$4?.))))))P,P,(=.$>.VownX,$19.)(4=.$43.R19.VpX,(4>.$4?.(79.(7:.#4.(40.(3.&40.)Vxs,))(4;.Vxs,))(51.$4?.)))P,(4=.$43.R19.VY,(4>.$4?.(50.(25.&40.VpY,))(4>.$4?.(72.(25.&40.VsgY,))(4>.$4?.(72.(25.&40.VnY,))(4>.$4?.(73.VpadY,)(51.$4?.))))))P,(4:.$43.R1:.VpY,(4;.Vys,))P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1;.VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1<.VY,+10.)P,(4=.$43.R1=.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R1>.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R1?.)P,(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,R20.)P,(20.+1.VnY,)P,(63.Vys,+1.)(77.$43.(78.$43.VR,VHIA,Vh,Vmo,)(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,Vmo,)(39.(3:.R22.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R21.R20.R1?.(25.&40.VX,)R17.R1>.(25.&40.VY,)R1=.R1<.R1;.R1:.R19.R18.R16.R15.(25.&40.(5?.(29.VR,)))(25.&40.(60.VY,+3.))R14.R13.R12.Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(25.&40.+9;>7<.)Vfc,(3;.(3.&40.))R23.(3<.$43.)))")
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HH1 HXS1 PCH1 HYS1 PBY1 OX1 OY1 FR1 ST1 MI1 HP1 HnY ZY. assert (TI : trim_i ys 1) by (left; reflexivity). basic_facts h LB m1 HH1 TOP.
      dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
      pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
      pose proof (client_wrange_keep L LB LF _ _ dX X 16 CW DXP) as CWk.
      pose proof (munch_refl [(lo, bv_unsigned sp); (X, X + 16)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OY1 (Y + 8) 2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX1 (X + 8) 2.
      (* [comment removed for export] *)
      zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      unfold zx16 in HXS1.
      apply (rw_cells_C2_congr asegs m2 X [C8 (Z_to_bv 64 pX)] _ sgY) in HXS1; [| apply sign_mod16; exact SGY]. cbn [app] in HXS1.
      assert (HP2 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m2).
      { eapply presA_trans; [exact HP1|]. eapply (presA_tail asegs R HIA h LB); [exact HH1| intros b Hb; eapply In_mpd_keep; exact Hb| exact LOS| exact TOP| exact OX1| exact MU| exact WM]. }
      assert (PCH2 : ownX = LHeap -> rw_cells asegs m2 pX [CB (4 * length xs)%nat (u32s xs)]).
      { intros E0. dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite E0 in HOWN.
        ddestruct HOWN as (N1 & HIN & _). destruct (hm_apart asegs R HIA h LB LF m2 HH1) as [HF _]. rewrite Forall_forall in HF.
        destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        eapply (rw_cells_transport asegs _ m1 m2); [exact (PCH1 E0)| exact MU| exact WM|].
        cbn [disjoint_from cells_size csize Nat.add]. pose proof (DXP E0) as D. clear - D BC ALO LOS SLO NEEDR LENX; lia. }
      clear MU WM HP1 PCH1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX1 (X + 10) 2.
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
      zstep.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - NRX; lia).
      - (* [comment removed for export] *)
        eapply (grow_path mo m2 1); try eassumption. all: try (clear - K1 HnY; lia).
        all: match goal with |- ?g => idtac "T1-GP-LEFT:" g end.
      - (* [comment removed for export] *)
        eapply (memset_finish m2 1); try eassumption. all: try (clear - K1 HnY NRX; lia).
        all: match goal with |- ?g => idtac "T1-MS-LEFT:" g end.
      all: match goal with |- ?g => idtac "T1-LEFT:" g end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Tail.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01l0@C17025492443.162C62520918539.163D15994190938.164D16043977870.164D24976250634.143D50796826103.164D52014138856.143D62012212072.164K21652967687.143K3634076879.163 K36795542264.163K60573057312.162K789726268.143  L11498582455.14 L11500183646.3  L14211216863.14 L14212572343.4  L14583701847.8  L15302269400.158L16247715997.4  L20666177036.7  L21646329835.2  L22324590442.3  L22446743512.158L23100341967.136L2340205082.10  L24387303207.162L24579960702.2  L29072134102.132L29074168500.135L29428324939.5  L34145086486.4  L34705680216.158L35511548052.2  L35653441506.7  L3629223086.3   L36807145629.3  L37757228480.5  L39172636981.0  L39376392229.2  L3949578456.158 L40768744533.1  L41843875160.158L4296725181.7   L46732241046.2  L47542916419.3  L47955443607.135L50790580594.6  L51454941784.158L5262147479.135 L54649464481.0  L55802464936.14 L55805087656.1  L5699067096.158 L58307024458.1  L58591023192.158L59504824379.161L60098763854.3  L60576273221.2  L64372451842.1  L67280348888.158L7632799155.158 L802980925.3    L8265267294.0   L919506048.7    N21806751459.163N22834764276.163N37104593031.163O10455381340.163O17025492443.162O5739683649.162 O57399310481.163O62520918539.163P22320919014.163P34158132851.162P3634076879.163 P60573057312.162Q12370813529.141Q15641193156.162Q17205256176.140Q18363862212.162Q21877711527.162Q22155430506.164Q22285631880.140Q22286196081.139Q22287617821.137Q24387303207.162Q24974040330.142Q26056220425.144Q27583012548.162Q27905069351.162Q30413104551.162Q31269460036.162Q32653238724.162Q33915930535.162Q36423686183.162Q37623178258.140Q37940043306.141Q38248387216.164Q3832294183.162 Q39212284437.140Q39941749287.162Q41154259908.162Q41925929058.143Q42081808994.140Q43879899724.164Q44650778180.162Q4926406185.140 Q51233928004.162Q52016320488.142Q54253886744.139Q5483506191.140 Q5485174314.141 Q56761401107.140Q59254634308.162Q59841074500.162Q60511567613.140Q6143569392.141 Q62965564504.141Q63229275329.137Q64360393870.164Q66524132519.162Q9540491346.137 Q9841301927.162 00000100200300400T01E01e02802f02g03:03;03b04704804H04I04`05105205305405505F05W05X06E06L06c07:07L07M07^07_08708808908:08;08B08S08T08e08f08m09909T09k0:<0:S0:T0:c0:d0;50;90;J0;[0;e0;f0;j0<;0<L0<M0<N0<e0=80=90=L0=M0=N0=O0=P0=Q0>;0>[0>\0>]0?80?E0?N0?[0@40@A0@J0@S0@\0A50AM0B60BC0B\0C50CB0CO0Ch0DA0DJ0DK0DU0Dn0E70EP0E]0FA0FP0F]0Fj0G30G@0GX0Ga0Gj0H30H?0HL0HY0H`0Hi0I>0IG0IQ0Ij0J10JJFFFFS2sp1X2pX2xs1Y2ys2HB5Ha_st5Hl_stS1R5NEEDR2sp1X2pX2xs1Y2ys2lo3LOS3SLO3SPR2X02Y02B0S2sp1X2pX2xs1Y2ys2HB5Ha_st5Hl_stS1R2sp1X2pX2xs1Y2ysS1R5NEEDR2sp1X2xs2ys2lo3SLO3DSX2HB5Ha_st5Hl_stFS2sp1X2xs2ys2lo3DSXFS1X2nX2pX2xs2ys3DXP4LENX2HB5Ha_st5Hl_stS1R2sp2lo3SLO3NRA3SPRFS1R3HIA1h2sp3TOPFS2sp1X2nX2pX2lo3DXP3DSXS2sp1X2pX2xs1Y2ysFFFFS2sp1X2pX2xs1Y2ysS2sp1X2pX2xs1Y2ysFS1R5NEEDR2sp1X2pX2xs1Y2ys2lo3SLO3SPR2X02Y02B0S2nX2pXS2sp1X2pX2xs1Y2ys2X02XBS2sp1X2pX2xs1Y2ys2X02XBS1R2lo3LOS3ALO3ACPFS2sp1X2pX2xs1Y2ysFS1R3HIA1h2sp2lo3TOP4HTOPFFFSS2nX2N1S2sp1X2pX2xs1Y2ysFS2sp1X2pX2xs1Y2ysFS2sp2loS2nX2xs4LENXS2sp1X2nX2pX2xs1Y2ys2N13NRXS1R5NEEDR2sp2lo3LOS3SLOS2sp1X2pX2xs1Y2ysS2sp1X2pX2xs1Y2ys2X02XBSS2sp2nX3SPR3NRXFS2sp1X2pX2xs1Y2ysS2nXS2sp1X2pX2xs1Y2ysS2sp1X2pX2xs1Y2ysS1R2lo3LOSFS2pXS2sp1X2pX2xs1Y2ysS2sp1X2pX2xs1Y2ysFSS1R2nX2pX2lo3LOS3ALO2BCS2sp2xs2ys2lo3x151CFS2sp2xs2ys2lo3x151CFFFFFS1R5NEEDR2sp2nX2pX2xs2ys2lo3LOS3SLO3ALO2BCS1R2sp2nX2pX2xs2ys2lo3LOS3ALO2BCFFS2sp1X2pX2xs1Y2ys3XAL2X02Y0S2sp2xs2ys2loS1X2xs2ysS2sp2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS2nX2pX2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ysS1R5NEEDR2sp2xs2ys2lo3SLOS1X2xs2ys2HB5Ha_st5Hl_stS1R5NEEDR2sp2xs2ys2lo3LOS3SLO3ALO3ACP3SPRS2sp2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS1R5NEEDR2sp2xs2ys2lo3SLOS2sp2xs2ys2loS2sp2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS1R5NEEDR2sp2xs2ys2lo3SLOS1X2xs2ysFS2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS1X2xs2ysS1R5NEEDR2sp2xs2ys2lo3SLOS2sp2xs2ys2loS2sp1X2nX2pX2xs2ys2lo2HB5Ha_st5Hl_stS1X2xs2ys2X02HBS2sp2xs2ys2loS2sp2xs2ys2loS1X2xs2ysS2sp2xs2ys2loS1X2xs2ys2HB5Ha_st5Hl_stS1X2xs2ysS1X2xs2ysS1X2xs2ysS1X2xs2ys2X0S2sp2xs2ys2loS2sp2xs2ys2loS2xs2ysS1X2xs2ysS1X2xs2ys2XB2HB5Ha_stS1X2xs2ysS2pX2xs2ysS1R5NEEDR2sp2xs2ys2lo3SLOS2xs2ysS1R5NEEDR2sp2xs2ys2lo3SLO". (* [comment removed for export] *)
  #[using="IMG AMS NEEDR m Y sgY pY ys padY ownY MAX MAY NEQ SEP LOS SLO TOP"] Lemma zero_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmc,P,(3.&40.)(5.(3.&8.))Pxra,(3.&40.)Pxt0,(3.&40.)Pxt1,(3.&40.)Pxt2,(3.&40.)Pxa0,(3.&40.)Pxa1,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Pxs1,(3.&40.)Pxs2,(3.&40.)Pxs3,(3.&40.)Pxs5,(3.&40.)Pxs6,(3.&40.)Pxs7,(3.&40.)Pxs8,(3.&40.)Pxt3,(3.&40.)Pxt4,(3.&40.)Pxt5,(3.&40.)Pxt6,(3.&40.)P,(9.$43.VR,VHIA,Vh,VLB,VLF,R17.)P,(=.$8.VnY,=)P,(20.+1.VnX,)P,(=.$>.VownX,$19.)P,(4=.$43.R1;.VX,(4>.$4?.(50.(25.&40.VpX,))(4>.$4?.(72.(25.&40.VsgX,))(4>.$4?.(72.(25.&40.VnX,))(4>.$4?.(73.VpadX,)(51.$4?.))))))P,(59.$43.R1<.VpX,Vxs,)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)R1=.VX,+10.)P,(74.(15.VR,)(16.$2.VLB,(17.VLF,))(13.&40.Vsp,)(1>.$43.VR,VHIA,Vh,)VX,+10.)P,(41.(20.(2>.VX,+10.)VpX,)(20.(2>.VpX,(1;.+4.VnX,))VX,))P,(41.(20.(2>.VX,+10.)Vlo,)(20.(13.&40.Vsp,)VX,))P,(4=.$43.R21.(2>.(13.&40.Vsp,)-50.)(4>.$4?.(50.Vs8,)(4>.$4?.(50.Vs7,)(4>.$4?.(50.Vs6,)(4>.$4?.(50.Vs5,)(4>.$4?.(50.Vs4,)(4>.$4?.(50.Vs3,)(4>.$4?.(50.Vs2,)(4>.$4?.(50.Vs1,)(4>.$4?.(50.Vs0,)(4>.$4?.(50.Vra,)(51.$4?.))))))))))))P,(1?.$43.R22.Vlo,(2>.(13.&40.Vsp,)-50.))P,(27.$43.R23.)(52.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)Lms',$53.(54.(3.&40.)Lx5,(3.&40.)(54.(3.&40.)Lx6,(3.&40.)(54.(3.&40.)Lx7,(3.&40.)(54.(3.&40.)La1',(3.&40.)(54.(3.&40.)La2',(3.&40.)(54.(3.&40.)La3',(3.&40.)(54.(3.&40.)La4',(3.&40.)(54.(3.&40.)La5',(3.&40.)(54.(3.&40.)La6',(3.&40.)(54.(3.&40.)La7',(3.&40.)(54.(3.&40.)Lx28,(3.&40.)(54.(3.&40.)Lx29,(3.&40.)(54.(3.&40.)Lx30,(3.&40.)(54.(3.&40.)Lx31,(3.&40.)(54.P,(3.&40.)(5.(3.&8.))Lm',P,(3.&40.)(5.(3.&8.))(3=.(=.$53.R10.(39.(3:.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(25.&40.=)R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R1.(3<.$43.)))(3=.(5:.(4>.(45.$8.$8.)(46.$8.$8.VpX,(2>.VpX,(1;.+4.VnX,)))(4>.(45.$8.$8.)(46.$8.$8.Vlo,(13.&40.Vsp,))(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))))R34.R1.)(3=.(5;.$43.R34.R1.)(3=.(27.$43.R1.)(3=.(59.$43.R1.VpX,(71.(3.&40.)(25.&40.=)(5>.VnX,)))(3=.(4=.$43.R1.VX,(58.VpX,(25.&40.+1.)VnX,VpadX,))(3=.(1?.$43.R1.Vlo,(13.&40.Vsp,))(9.$43.VR,VHIA,Vh,VLB,VLF,R1.)))))))))))))))))))))))(39.(3:.R23.(25.&40.(2>.(13.&40.Vsp,)-50.))Vgp,Vtp,R22.R21.R20.(25.&40.VX,)R18.R1?.R1>.(25.&40.VnX,)R1=.R1<.R1;.R1:.R19.R17.R16.(25.&40.(5?.(29.VR,)))R15.R14.R13.R12.Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(25.&40.+9;=>4.)Vfc,(3;.(3.&40.))R24.(3<.$43.)))")
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HH EY N1 EO HXS HXL OX CW DXP DSX FR ST MI. basic_facts h LB mc HH TOP.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    dpose MAX as [[_ (_ & _ & _ & _ & HOWN)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HOWN. rewrite EO in HOWN.
    ddestruct HOWN as (_ & HIN & P16 & _).
    destruct (hm_apart asegs R HIA h LB LF mc HH) as [HF BA]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC. clear HF BA.
    assert (CWs : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X 16) by (eapply client_wrange_sp_mono; [| exact CW]; clear - LOS SLO NEEDR; lia).
    pose proof (munch_refl [(pX, pX + 4 * nX); (lo, bv_unsigned sp); (X, X + 16)] mc) as MU. pose proof (wmono_refl asegs mc) as WM.
    pose proof (hm_aobj_block asegs R HIA h LB LF mc pX (4 * nX) HH HIN) as OPX.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 8) 2.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ ?pc _ _ ?mx _) => idtac "ZW-PC:" pc; rename mx into m2 end.
    match goal with H : rw_cells asegs m2 X _ |- _ => pose proof (conj H I) as HXS0 end.
    pose proof (munch_refl [(pX, pX + 4 * nX); (lo, bv_unsigned sp)] m2) as MUX. pose proof (wmono_refl asegs m2) as WMX.
    pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET_CP) as SPM. unfold A_ASAN_MEMSET_CP in SPM.
    callxA_sp (bv_unsigned sp + -80)
      (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := pX) (v := 0) (n := 4 * nX) (lo := lo) (ds := u32s xs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -80)) by qlia;
       try eassumption; try reflexivity;
       first [ left; rewrite AMS; reflexivity
             | apply MpiWalkAux.u8arr_of_u32arr; eassumption
             | rewrite u32s_length; clear - LENX; lia
             | clear; lia
             | eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]
             | left; clear - BC ALO LOS; lia
             | eapply (blk_top47_sub asegs R HIA h LB LF _); [exact HH| exact HIN| clear; lia]
             | eapply client_wrange_block; [apply in_app_iff; left; exact HIN| clear; lia| clear; lia]
             | f_equal; clear; lia
             | clear - NRX LOS SLO NEEDR NRA TOP SPA SPR; lia
             | match goal with |- ?g => idtac "ZMEMSET-PRE-LEFT:" g end ]).
    clear SPM.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-ZMEMSET-SIDE:" g end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : u8arr asegs m5 pX _ |- _ => rename H into HPZ end.
    match goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
    destruct HXS0 as [HXS2 _].
    pose proof (rw_cells_transport asegs _ m2 m5 _ _ HXS2 MUX WMX ltac:(cbn [disjoint_from cells_size csize Nat.add]; clear - DXP DSX N1; lia)) as HXS5.
    replace (Z.to_nat (4 * nX)) with (4 * Z.to_nat nX)%nat in HPZ by (clear - N1; lia).
    apply (rw_cells_of_u8arr asegs) in HPZ. pose proof (u32arr_of_cells asegs m5 pX _ _ (repeat (Z_to_bv 64 0) (Z.to_nat nX)) HPZ ltac:(symmetry; apply u32s_repeat0)) as HZ5.
    (* [comment removed for export] *)
    zstep. zstep.
    do 10 zstep.
    zstep.
    release_frame FR ST5 (bv_unsigned sp).
    zstep.
    finish.
    all: try (unfold mpi_cells; exact HXS5).
    all: match goal with |- ?g => idtac "ZW-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L33992082665.2L59321100280.4L6998223978.1 00000700E00JS2nX2N1S2nY1l2EY4LENYS3sgY". (* [comment removed for export] *)
  #[using="MAX NST MAY NEQ SEP CSEP"] Lemma post_zero : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmo,$6.Pmo',$6.Ph',(0.$43.VR,VHIA,)Pm',P,(3.&40.)(5.(3.&8.))Px5,(3.&40.)Px6,(3.&40.)Px7,(3.&40.)Pxa1,(3.&40.)Pxa2,(3.&40.)Pxa3,(3.&40.)Pxa4,(3.&40.)Pxa5,(3.&40.)Pxa6,(3.&40.)Pxa7,(3.&40.)Px28,(3.&40.)Px29,(3.&40.)Px30,(3.&40.)Px31,(3.&40.)P,(=.$8.VnY,=)P,(20.+1.VnX,)P,(=.$>.VownX,$19.)P,(27.$43.R12.)P,(1?.$43.R13.Vlo,(13.&40.Vsp,))P,(67.R17.R16.)P,(49.$43.VR,(68.VLB,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,))VLF,(13.&40.Vsp,)(21.VR,)(6:.$43.VR,VHIA,Vh,)(4>.(45.$8.$8.)(46.$8.$8.VX,(2>.VX,+10.))(51.(45.$8.$8.)))Vm,R15.)P,(=.$8.(1>.$43.VR,VHIA,R17.)(1>.$43.VR,VHIA,Vh,))P,(=.$8.(6:.$43.VR,VHIA,R18.)(6:.$43.VR,VHIA,Vh,))P,(=.$8.(6;.$43.VR,VHIA,R19.)(6;.$43.VR,VHIA,Vh,))P,(:.$43.VR,VHIA,R1:.R1;.)P,Px,$8.P,(2:.$43.VR,VHIA,Vh,R1.)(2:.$43.VR,VHIA,R1=.R2.)P,(20.(2?.$43.VR,VHIA,R1<.)(2>.(2?.$43.VR,VHIA,Vh,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))))P,(20.(33.$43.VR,VHIA,R1=.)(2>.(33.$43.VR,VHIA,Vh,)(34.Vd,)))P,(9.$43.VR,VHIA,R1>.VLB,VLF,R1=.)P,(;.$43.R1>.VLB,(69.VX,+1.VnX,VpX,(71.(3.&40.)(25.&40.=)(5>.VnX,))VpadX,$19.))(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R22.(38.(39.(3:.Vra,Vsp,Vgp,Vtp,R1>.R1=.R1<.Vs0,Vs1,(25.&40.=)R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(55.Vra,)Vfc,(3;.(3.&40.))R1?.(3<.$43.))R21.))")
(* [comment removed for export] *).
  Proof.
    intros until x31. intros EY N1 EO MI ST MF HP HT HS HFL HK HCS HV HFR HH MA.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    unfold mpi_binop_postA. deexists 14. dexists m', mo', h', LB, (mkMPD X 1 nX pX (repeat (Z_to_bv 64 0) (Z.to_nat nX)) padX LHeap), 0.
    split; [reflexivity|]. split; [exact MI|]. split; [exact ST|]. split; [exact MF|]. split; [exact HP|].
    split; [exact HT|]. split; [exact HS|]. split; [exact HFL|]. split; [exact HK|]. split; [exact HCS|].
    split; [exact HV|]. split; [exact HFR|]. split; [exact HH|]. split; [exact MA|].
    split; [eapply mpd_out_ext; [apply mpd_out_refl; cbn [md_own]; exact NST| reflexivity| cbn [md_own]; discriminate| cbn [mpd_blk md_own md_p md_n]; rewrite EO; reflexivity]|].
    split; [cbn [mpd_blk md_own md_p md_n]; rewrite EO; intros b Hb; left; exact Hb|].
    unfold copy_Rx, copy_R. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own mpd_blk mpd_val].
    split; [| intros _; unfold copy_trim; cbn [md_n]; left; reflexivity].
    split; [| split; [reflexivity| split; [reflexivity| rewrite EO; intros b Hb; left; exact Hb]]].
    left. split; [reflexivity|]. split; [| rewrite EY; clear - N1; lia].
    unfold mpd_val. cbn [md_sg md_limbs]. rewrite limbs_val_repeat0.
    assert (ys = []) as -> by (destruct ys; [reflexivity| exfalso; cbn in LENY; clear - LENY EY; lia]). cbn. clear; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02]0@D3399625391.150 D3399625391.151 D35881667587.150D35881667587.151D41065047062.151K42587433812.150K42587433812.151K63462517886.150K63462517886.151L1120085281.148 L1157912586.147 L1164172544.1   L12092711958.3  L12457983458.9  L15302269400.142L15756354262.4  L1649577667.2   L1685717371.0   L19945316590.2  L19946008845.147L20880416051.5  L21897055936.153L22446743512.142L22698354369.3  L25214214772.142L2592037667.153 L26892418956.1  L28587818495.4  L29428324939.5  L31225147636.142L33290602421.2  L34387710479.147L34705680216.142L35203275068.146L35653441506.7  L36897755907.142L37246946676.141L38723301197.5  L38948636245.0  L38983344078.7  L39172636981.0  L39280637297.0  L3949578456.141 L39579186692.3  L40281191306.3  L40374333670.146L40834179097.146L41843875160.142L4235704437.5   L42594106808.2  L43061363337.144L43135913741.3  L44397119898.2  L44435606829.1  L4459036701.145 L4459037467.147 L4461097141.2   L45937649471.2  L46160478397.145L46160487540.148L47560987722.142L47560995072.145L47955344026.2  L47957478064.148L48132467214.7  L49283344500.142L50664059503.12 L51326438992.3  L51454941784.142L5259987890.143 L52825213806.4  L55310518004.142L55528324167.10 L56205172016.146L5699067096.142 L57256937215.5  L57818804596.142L58591023192.142L59308668813.3  L59314873579.3  L59335885566.2  L60098763854.3  L61282314347.4  L61321319284.142L62018535662.1  L62624979503.54 L63452461841.2  L63612514602.3  L63619150122.3  L63829069812.142L64056784486.2  L64194470200.2  L67280348888.142L67351568884.142L68294535841.2  L7424514157.9   L7632799155.142 L774765788.5    L9325687840.146 L9327837598.143 Q14485421028.155Q15643324129.146Q17530203490.149Q17530203490.150Q18365925601.147Q18694146040.151Q20246173414.151Q20246227035.148Q20246661663.150Q21798041355.151Q21879645826.147Q24363880261.154Q24363994560.155Q24389563138.147Q25157988860.151Q25513505925.149Q25513505925.150Q25662358575.151Q26207721832.154Q26207774294.151Q26209519061.153Q27584944865.147Q27907200258.147Q30415036802.147Q31228709292.151Q31271525473.147Q31394594844.151Q31651985788.153Q32655500769.147Q33918256002.147Q35014437530.151Q35030107133.151Q35717497884.151Q36425882626.147Q37138808053.151Q3830427394.147 Q39212284437.151Q39212284437.154Q39939554818.147Q41152393185.147Q4143427880.151 Q42349454934.150Q43925228937.154Q44183705525.151Q44648843873.147Q48533421759.148Q49698585326.148Q49698585326.149Q50107086626.155Q51235796833.147Q5300226131.147 Q5300226131.148 Q53969758199.151Q54126458602.148Q54202978234.154Q59256763233.147Q59843137889.147Q60511567613.151Q60511567613.154Q60697995187.154Q61802139820.151Q6416456232.151 Q64255486968.151Q66522067074.147Q67375714898.154Q67528989526.150Q67528989526.151Q7748271680.151 Q8880817418.151 Q8892514873.150 Q9538463866.148 Q9538464249.151 Q9843367298.146 00000m02?02k03o04l05g07:08409F09T09b09e0:00:K0:Y0:g0:o0;00;70;H0;I0<60<D0<M0<[0<i0<m0=40=F0=T0=\0>E0>S0>T0>l0?:0?H0?W0?X0?Y0?Z0?[0?i0@40@=0@K0@[0@i0A90A:0Aa0Ae0Am0B10BF0B[0Bc0Bj0C>0CR0Cf0D:0DB0DW0E20E@0Ec0Ek0F90FM0F[0Fi0G@0Gi0H70H80HF0HT0H^0Hg0Hn0I80IF0IT0IW0IX0IY0Ic0Il0J:0JB0JI0JW0Je0Jl0Jm0K;0KN0Kb0L60LK0LX0MC0NC0NP0N^0Ng0O00O90O:0OS0O\0Oe0P>0PL0Pk0Qb0Qc0Ql0R50R>0RK0Rd0S=0SL0SY0S`0Si0T60TO0T^0Tg0Th0UA0UB0U[0Ud0Um0VF0VS0VT0V]0Vf0Vg0W40W=0WT0Wk0X40XA0XN0X[0Xj0Y70Y@0YM0YZ0Ya0Yh0Z40Z50ZC0ZD0Z]0Zf0[Q0\T0\`0\i0]T0][0]b0^;S1R5NEEDR2ra2sp1X2xs1Y2ys2lo3LOS3SLO3SPR2X02Y02HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X2xs1Y2ys2lo3LOS3SLO3SPR2X02Y02HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S1R3HIA1h2ra2sp1X2xs1Y2ys3TOP2HB5Ha_st5Hl_stS1R3HIA1h2sp2s01X2xs1Y2ys3TOP2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S1R5NEEDR2sp2s81X2xs1Y2ys2lo3LOS3SLO3SPR2X02Y02HB5Ha_st5Hl_stS1R5NEEDR2ra2sp1X2pX2xs2pY2ys2lo3SLO3PX03DSX2HB5Ha_st5Hl_stS1R5NEEDR2sp2s01X2pX2xs2pY2ys2lo3SLO3PX03DSX2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S1R5NEEDR2ra2sp2pX2xs1Y2pY2ys2lo3SLO2Q43PX02HB5Ha_st5Hl_stS1R5NEEDR2sp2s02pX2xs1Y2pY2ys2lo3SLO2Q43PX02HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS1XS2nY3NRY2K1S1R4RIMG2nY2pY1A1k2AI2SL2SHS2sp1X2xs1Y2ysS1R2lo3LOS3ALOS2nX3NRXSS2sp2loS2sp1X2xs1Y2ys2loFS2sp1X2pX2xs1Y2nY2pY2ys3NEQ3NRY3SXY3PX02K02K1S2sp1X2xs1Y2ysS2nY1i2HiS2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS2spS2nY2K3S1R2lo3LOS3ALO3ACPS2sp1X2xs1Y2ysS2nY3NRYS2sp1X2pX2xs1Y2nY2pY2ys3NEQ3NRY3PX02K02K1S2sp1X2xs1Y2ysFS1R3HIA1h2sp2lo3TOP4HTOPS2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS1R3HIA1h1d3D0'SFSSS2sp1X2xs1Y2ysS2nY3NRY2K1S1R3HIA1hS2sp1X2xs1Y2ysS1R2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS1R3HIA1h2nY3NRYFS1R5NEEDR2sp1X2xs1Y2ys2lo3SLO3SPR2X02Y0S2nYS2nX3NRXS2nYS2sp1X2xs1Y2nY2ys3NRYS2sp1X2xs1Y2nY2ys3NRYS2nY3NRYS2nY2pYS2sp1X2xs1Y2ys2X02XBS2sp1X2xs1Y2ys2X02XBS2sp1X2xs1Y2ys2Y02YBS2sp1X2xs1Y2ys2Y02YBS2nX3NRXS2sp1X2nX2xs1Y2ys3NRXS1R5NEEDR2sp2lo3LOS3SLO3ALOS2sp1X2xs1Y2ysS1R2sp2nX2pX2xs2lo3LOS3ALO4LENX3PXCS1A1k2A0S2sp1X2xs1Y2ysS2sp1X2xs1Y2ys2X02XBS2nY3NRY2K12K3S2sp1X2xs1Y2ysS2sp2nY2pY2ys2lo4LENY1HS2sp1X2pX2xs1Y2nY2pY2ys3NEQ3NRY3PX02K02K1S2sp1X2xs1Y2ysFS2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS2nX2K22EnS2nY2K11HS2pX2B0S1R2lo3LOSS2nY3NRY2K12K3S2sp1X2xs1Y2ysS1RFFS2nY2pY2SHS2nY2pY1HS2sp1X2xs1Y2ysS2nX3NRXS1R3ACPS2sp1X2xs1Y2ysS2sp1X2xs1Y2ysS2nX2pXFS2sp1X2xs1Y2ysS1R5NEEDR2sp2lo3SLOS2sp1X2xs1Y2ys2Y02YBS2sp1X2xs1Y2ys2Y02YBS2sp1X2xs1Y2ys3YAL2Y0S2sp2xs2ys2loS1R5NEEDR2ra2sp2xs2ys2lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2s02xs2ys2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2xs2ys2loS1R2xs2ys4IMG'S2xs1Y2ysS2xs1Y2ysS2xs1Y2ysFS1R5NEEDR2sp2xs2ys2lo3SLOS2xs1Y2ysS2xs1Y2ysS1R5NEEDR2sp2xs2ys2lo3SLOS1R2xs2ys4IMG'S2ra2sp2xs2ys2lo2HB5Ha_st5Hl_stS2sp2s02xs2ys2lo2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8FS1X2xs2ysS1X2xs2ysS1X2xs2ysS2sp2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS1R5NEEDR2sp2xs2ys2lo3SLOS1R2xs2ys5ALWF'S2sp2xs2ys2loS2xs2ysS1X2xs2ysS2sp2xs2ys2loS1R5NEEDR2sp2xs2ys2lo3SLOS1R2xs2ys5ALWF'S2xs1Y2ysFS1R5NEEDR2sp2xs2ys2lo3SLOFS1R5NEEDR2sp2xs2ys2lo3SLOS2xs1Y2ysS1X2xs2ysS1R5NEEDR2sp2xs2ys2lo3SLOS2sp2xs2ys2loFS2xs1Y2ysS1X2xs2ysFS2sp2xs2ys2loS2xs1Y2ysS2sp2xs2ys3SPR2HB5Ha_stS2sp2xs2ys3SPR2HB5Ha_stS2xs1Y2ysS2sp2xs2ys2loS2sp2xs2ys2HBS2sp2xs2ys2HBS1R2xs2ys5ALWF'S2sp2xs2ys2HBS2xs1Y2ysS2sp2xs2ys2loS2sp2xs2ys2loS2xs2ysS2xs2ysS1X2xs2ys2X0FS1R2xs2ys4IMG'FS1R5NEEDR2sp2xs2ys2lo3SLOS2xs1Y2ysS1R5NEEDR2ra2sp2xs2ys2lo3SLO2HB5Ha_st5Hl_stS1R5NEEDR2sp2s02xs2ys2lo3SLO2HB5Ha_st5Hl_st2s12s22s32s42s52s62s72s8S2xs1Y2ys2Y0S1X2xs2ysS1R5NEEDR2sp2s82xs2ys2lo3SLO2HB5Ha_st5Hl_stS2xs2ysS2xs2ysS1R5NEEDR2sp2xs2ys2lo3SLO". (* [comment removed for export] *)
  #[using="C24T IMG ZF CALLOC AMC AMS NEEDR HND DIMG RIMG MAX NST MAY NEQ SEP CSEP YCR YLCR XW LOS SLO TOP SPA TPV YNZ XUW"] Lemma main_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_copy ()) "Pmo,$6.Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)P,(9.$43.VR,VHIA,Vh,VLB,VLF,Vm,)P,(:.$43.VR,VHIA,Vh,R?.)P,(1?.$43.Vm,Vlo,(13.&40.Vsp,))P,(27.$43.Vm,)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)Vm,VX,+10.)P,(28.$43.(29.VR,)(2:.$43.VR,VHIA,Vh,)Vm,VY,+10.)P,(20.(2>.(2?.$43.VR,VHIA,Vh,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)))$31.)P,(20.(2>.(33.$43.VR,VHIA,Vh,)(34.Vd,))$35.)(36.$43.(37.$43.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)(6?.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,)(69.VX,VsgX,VnX,VpX,Vxs,VpadX,VownX,)VLB,)(30.(69.VY,VsgY,VnY,VpY,Vys,VpadY,VownY,))(34.Vd,)Vlo,Vm,R16.)(38.(39.(3:.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,(25.&40.VX,)(25.&40.VY,)R12.R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(25.&40.$7;.)Vfc,(3;.(3.&40.))Vm,(3<.$43.))R16.))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH HKmo ST MI OX OY BUD BUDF. unfold A_MPI_COPY. basic_facts h LB m HH TOP.
    dpose facts as (XAL & X0 & LENX & NRX & SGX & YAL & Y0 & LENY & NRY & SGY & XB & YB & SXY).
    pose proof (HND _ _ _ _ HH) as ND.
    dpose MAX as [[HXS (_ & _ & _ & _ & HOWNX)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HXS, HOWNX.
    dpose MAY as [[HYS (_ & _ & _ & _ & HOWNY)] _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in HYS, HOWNY.
    destruct XW as [CW DXP0]. cbn [md_addr md_own md_p md_n] in CW, DXP0.
    ddestruct CSEP as (Q1' & Q2' & Q3' & Q4 & Q5' & _). cbn [md_addr md_own md_p md_n] in Q1', Q2', Q3', Q4, Q5'.
    destruct (hm_apart asegs R HIA h LB LF m HH) as [HF BA]. rewrite Forall_forall in HF.
    unfold MPI_MAX_LIMBS in *.
    (* [comment removed for export] *)
    assert (PBX : 0 <= pX /\ pX + 4 * nX <= alloc_ceiling
                 /\ (ownX = LHeap -> 0 < pX /\ In (pX, 4 * nX) LB /\ pX mod 16 = 0 /\ u32arr asegs m pX xs /\ 1 <= nX)
                 /\ (ownX = LNull -> pX = 0 /\ nX = 0)).
    { destruct ownX; [| | exfalso; exact (NST eq_refl)].
      - destruct HOWNX as [E0 En]. split; [rewrite E0; clear; lia|]. split; [rewrite E0, En; clear - ACP; lia|].
        split; [intros E; discriminate E| intros _; split; [exact E0| exact En]].
      - ddestruct HOWNX as (N1 & HIN & HP16 & HXL). destruct (HF _ ltac:(apply in_app_iff; left; exact HIN)) as (B0 & _ & BC & _). cbn in B0, BC.
        split; [clear - B0; lia|]. split; [exact BC|].
        split; [intros _; split; [exact B0| split; [exact HIN| split; [exact HP16| split; [exact HXL| exact N1]]]]| intros E; discriminate E]. }
    ddestruct PBX as (PX0 & PXC & PHEAP & PNULL). clear HOWNX.
    assert (YBLK : ownY = LHeap -> In (pY, 4 * nY) LB) by (intros E0; rewrite E0 in HOWNY; exact (proj1 (proj2 HOWNY))).
    assert (PBY : ownY <> LNull -> bytes_at asegs m pY (u32s ys)).
    { intros ON. destruct ownY; [exfalso; exact (ON eq_refl)| ddestruct HOWNY as (_ & _ & _ & [PB _]); exact PB| ddestruct HOWNY as (_ & _ & _ & PB & _); exact PB]. }
    assert (NY0 : ownY = LNull -> nY = 0) by (intros E0; rewrite E0 in HOWNY; exact (proj2 HOWNY)).
    assert (DSX : X + 16 <= lo \/ bv_unsigned sp <= X).
    { eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDR; lia]. }
    (* [comment removed for export] *)
    assert (Y47 : ownY <> LNull -> pY + 4 * nY + 8 <= 2^47).
    { intros ON. destruct ownY; [exfalso; exact (ON eq_refl)| |].
      - pose proof (blk_top47 asegs R HIA h LB LF m pY (4 * nY) HH (YBLK eq_refl)). clear - H. lia.
      - ddestruct HOWNY as (N1 & _ & _ & PB & RO). pose proof (static_limbs_low m pY nY ys PB LENY N1 RO) as [_ SH]. clear - SH. lia. }
    (* [comment removed for export] *)
    assert (Yfresh : forall A k, fresh_apart R LB LF A k -> 0 < k -> Y + 16 <= A \/ A + k <= Y).
    { intros A k HFRA Hk. destruct (fresh_apart_client R LB LF lo Y 16 A k HFRA); [exact YCR| clear; lia| exact Hk| clear - ALO LOS; lia| right; assumption| left; assumption]. }
    assert (PYfresh : forall A k, fresh_apart R LB LF A k -> (A + k <= hl_img_lo L \/ hl_img_hi L <= A) -> 0 < k -> pY + 4 * nY <= A \/ A + k <= pY).
    { intros A k HFRA AI Hk. dpose HFRA as (A0 & AC & AD & HAP). destruct ownY.
      - rewrite (proj1 HOWNY), (proj2 HOWNY). clear - A0. lia.
      - destruct (HAP pY (4 * nY) ltac:(apply in_app_iff; left; exact (YBLK eq_refl))); [right| left]; assumption.
      - ddestruct HOWNY as (N1 & _ & _ & PB & RO). pose proof (static_limbs_low m pY nY ys PB LENY N1 RO) as [SL SH].
        clear - SL SH AI RIMG. lia. }
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo) as KINV.
    apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HKmo (mo_frame_refl mo))).
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    unfold mpi_cells in HXS, HYS.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    do 11 zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    (* [comment removed for export] *)
    assert (HP1 : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m m1).
    { eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(X, X + 16)]);
        [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
      eapply (presA_drop_below asegs R HIA h LB LF [(X, X + 16)] lo (bv_unsigned sp) _ m m1); [exact HH| | clear; lia| exact LOS].
      eapply (presA_of_munch asegs R LB LF _ _ _ _ m m1 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | | exact WM0].
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by lia; exact SCS|].
        apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by lia; eapply aobj_crange; exact OX|]. apply Forall_nil.
      - eapply munch_weaken; [| exact MU0]. clear. intros y Hy; clear - Hy; cbn [outside] in *. tauto (* [comment removed for export] *). }
    assert (PCH1 : ownX = LHeap -> rw_cells asegs m1 pX [CB (4 * length xs)%nat (u32s xs)]).
    { intros E. ddestruct (PHEAP E) as (B0 & _ & _ & HXL & _). apply u32arr_cells.
      eapply (u32arr_transport asegs _ m m1); [exact HXL| exact MU0| exact WM0| cbn [disjoint_from]; clear - PXC ALO LOS SLO NEEDR LENX; lia]. }
    assert (PBY1 : ownY <> LNull -> bytes_at asegs m1 pY (u32s ys)).
    { intros ON. eapply (bytes_at_transport asegs _ m m1); [exact (PBY ON)| exact MU0|]. rewrite u32s_length. cbn [disjoint_from].
      pose proof (Q5' ON). clear - H LENY LO0 SLO; lia. }
    clear MU0 WM0.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - X0 XB Y0 YB; lia); exact (NEQ K0)|].
    (* [comment removed for export] *)
    zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    zstep. zstep. zstep. clear GOT GSB AB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OY (Y + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 nY)) with (Z_to_bv 64 nY)
      by (unfold zx16; rewrite !unsigned_lit by (clear - NRY; lia); rewrite Z.mod_small by (clear - NRY; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear - NRY; lia).
    { (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
      (* [comment removed for export] *)
      zstep.
      replace (zx16 (Z_to_bv 64 nX)) with (Z_to_bv 64 nX)
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRX; lia); rewrite Z.mod_small by (clear - NRX; lia); reflexivity).
      (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - NRX; lia).
      - (* [comment removed for export] *)
        zstep.
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply epi_walk with (hc := h) (LBc := LB) (r := 0); try eassumption
          | intros y Hy; exact Hy | ].
        intros ms' PO. destruct_exs PO. destruct PO as [E ST9]. subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_keep mo mo9 h m1 0 sgX); try eassumption; try reflexivity.
        + intros y Hy; exact Hy.
        + unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]. clear - NRY. lia.
        + unfold copy_FR, calls_FR, fr_charge. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'. clear - D0'. lia.
        + eapply mpd_at_rebuild; [exact NST| unfold mpi_cells; exact HXS| exact XAL| exact X0| exact LENX| unfold MPI_MAX_LIMBS; clear - NRX; lia| exact SGX| exact PNULL|].
          intros E. ddestruct (PHEAP E) as (B0 & HIN & HP16 & _ & N1). split; [exact N1|]. split; [exact HIN|]. split; [exact HP16|].
          eapply (u32arr_of_cells asegs); [exact (PCH1 E)| reflexivity].
        + right. split; [reflexivity|]. split; [exact K2| exact K1].
      - (* [comment removed for export] *)
        assert (EO : ownX = LHeap) by (destruct ownX; [exfalso; destruct (PNULL eq_refl) as [_ En]; clear - En K2; lia| reflexivity| exfalso; exact (NST eq_refl)]).
        ddestruct (PHEAP EO) as (B0 & HIN & HP16 & _ & N1).
        eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
          [ eapply (zero_walk m1); try eassumption; try exact EO
          | intros y Hy; exact Hy | ].
        all: try (eapply (u32arr_of_cells asegs); [exact (PCH1 EO)| reflexivity]).
        all: try exact (DXP0 EO).
        all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "ZW-PRE-LEFT:" g end.
        intros ms' PO. ddestruct PO as (y5 & y6 & y7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & m9 & E9 & MU9 & WM9 & MI9 & HA9 & HX9 & ST9 & HH9). subst ms'.
        apply aevtA_done. intros mo9 [HK9 MF9].
        eapply (post_zero mo mo9 h m9); try eassumption; try reflexivity.
        + eapply presA_trans; [exact HP1|].
          apply (munch_weaken _ [(lo, bv_unsigned sp); (pX, pX + 4 * nX); (X, X + 16)]) in MU9; [| clear; intros x Hx; clear - Hx; cbn [outside] in *; tauto (* [comment removed for export] *)].
          eapply (presA_drop_freed asegs R HIA h LB LF (mpd_keep LB dX) [(X, X + 16)] pX (4 * nX) m1 m1 m9);
            [exact HH| exact HIN| | exact (proj1 DIMG)| exact (proj2 DIMG)| clear - ALO LOS SLO NEEDR; lia|].
          { intros b xb Hb Hr. split; [eapply In_mpd_keep; exact Hb|]. intros E. subst b.
            exact (lb_remove_notin LB pX (4 * nX) ND (in_keep_remove LB dX _ ND EO HIN Hb)). }
          eapply (presA_weaken asegs R LB (mpd_keep LB dX) LF LF (bv_unsigned sp) (bv_unsigned sp) (arl_stklo R) (arl_stklo R)
                    (hstkhi asegs R HIA h) (hstkhi asegs R HIA h) [(pX, pX + 4 * nX); (X, X + 16)]);
            [| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros y Hy; exact Hy].
          eapply (presA_drop_below asegs R HIA h LB LF _ lo (bv_unsigned sp) m1 m1 m9); [exact HH| | clear; lia| exact LOS].
          eapply (presA_of_munch asegs R LB LF _ _ _ _ m1 m9 CS CSOK); [| intros c0 Hc; eapply cshd_hcs; [exact HH| | exact Hc]; clear; lia | exact MU9 | exact WM9].
          unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS|].
          apply Forall_cons; [cbn [fst snd]; replace (pX + 4 * nX - pX) with (4 * nX) by (clear; lia); eapply aobj_crange; eapply hm_aobj_block; [exact HH| exact HIN]|].
          apply Forall_cons; [cbn [fst snd]; replace (X + 16 - X) with 16 by (clear; lia); eapply aobj_crange; exact OX|]. apply Forall_nil.
        + intros y Hy; exact Hy.
        + unfold copy_PHI, grow_PHI; unfold AVOL_CALL; cbn [md_n]. clear - NRY. lia.
        + unfold copy_FR, calls_FR, fr_charge. pose proof (uw_obj_nonneg _ _ _ _ XUW) as D0'. clear - D0'. lia.
        + eapply mpd_at_rebuild; [discriminate| exact HX9| exact XAL| exact X0| rewrite repeat_length; clear - NRX; lia| unfold MPI_MAX_LIMBS; clear - NRX; lia| left; reflexivity| intros E; discriminate E|].
          intros _. split; [exact N1|]. split; [exact HIN|]. split; [exact HP16| exact HA9]. }
    (* [comment removed for export] *)
    assert (OYN : ownY <> LNull) by (intros E0; pose proof (NY0 E0); clear - H K1; lia).
    assert (Q3x : ownX <> LHeap \/ pX + 4 * nX <= pY \/ pY + 4 * nY <= pX).
    { destruct Q3' as [E|[Q|[Q|Q]]]; [exfalso; injection E; intros; exact (NEQ ltac:(assumption))| left; exact Q| exfalso; exact (OYN Q)| right; exact Q]. }
    zstep. zstep. zstep. zstep. zstep.
    replace ((nY + -1) mod 4294967296) with (nY - 1) by (rewrite Z.mod_small; clear - K1 NRY; lia).
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by (clear - NRY; lia).
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. zstep.
      replace (Z_to_bv 64 (pY + (nY - 1) * 4)) with (Z_to_bv 64 (pY + 4 * (nY - 1))) by (f_equal; clear; lia).
      eapply (aevtA_cut_evtA asegs AL _ LAWS _ _ _ _ _ _ KINV);
        [ eapply (scan_loop (Z.to_nat (nY - 1)) (nY - 1) m1); try eassumption
        | intros y Hy; exact Hy | ].
      all: try (clear - K1 K3 NRY; lia).
      all: try (replace (nY - 1 + 1) with nY by (clear; lia); apply zeros_above_all; exact LENY).
      all: try (exact (PBY1 OYN)).
      all: try (eapply opy_at; [exact HH| exact YBLK| exact OYN]).
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- aevtA _ _ _ _ => idtac | |- forall _, _ => idtac | |- ?g => idtac "SC-PRE-LEFT:" g end.
      intros ms' PO. ddestruct PO as (i & xa2' & xa3' & xa5' & xa6' & [(E & Hi & Zi & Ti)|(E & Hi & Zi)]); subst ms'.
      + eapply (tail_i mo OYN BUD BUDF (Q1' OYN) Q2' Q3x Q4 (Q5' OYN) (Y47 OYN) DSX DXP0 CW PYfresh Yfresh YBLK m1 i); try eassumption.
        all: try exact (PBY1 OYN). all: try (clear - Hi; lia).
        all: match goal with |- ?g => idtac "TIA-LEFT:" g end.
      + subst i. eapply (tail_1 mo OYN BUD BUDF (Q1' OYN) Q2' Q3x Q4 (Q5' OYN) (Y47 OYN) DSX DXP0 CW PYfresh Yfresh YBLK m1); try eassumption.
        all: try exact (PBY1 OYN). all: try (clear - K1 NRY; lia).
        all: match goal with |- ?g => idtac "T1A-LEFT:" g end.
    - (* [comment removed for export] *)
      eapply (tail_i mo OYN BUD BUDF (Q1' OYN) Q2' Q3x Q4 (Q5' OYN) (Y47 OYN) DSX DXP0 CW PYfresh Yfresh YBLK m1 nY); try eassumption.
      all: try exact (PBY1 OYN). all: try (clear - K1 K3 NRY; lia).
      all: try (apply zeros_above_all; exact LENY).
      all: try (left; exact K3).
      all: match goal with |- ?g => idtac "TIB-LEFT:" g end.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.


(* [comment removed for export] *)

(* [comment removed for export] *)
