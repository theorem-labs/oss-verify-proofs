(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_mpi_bitlen.
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
Ltac2 gd_tbl_A_pk_ecparams_aux () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "pure_ret_postA"; "ASN1_OUT_OF_DATA_U"; "A_ASN1_GET_INT_U"].


Definition A_ECP_POINT_READ_BINARY_U : Z := 0xcb3e4.   (* [comment removed for export] *)
Definition A_ASN1_GET_INT_U : Z := 0x99b4c.            (* [comment removed for export] *)
Definition ECP_BAD_INPUT_DATA_U : Z := -0x4F80.
Definition ECP_FEATURE_UNAVAILABLE_U : Z := -0x4E80.
Definition ASN1_OUT_OF_DATA_U : Z := -0x60.
(* [comment removed for export] *)
Notation ECP_POINT_READ_UNSET_STACK_A := 128 (only parsing).

(* [comment removed for export] *)
Definition pure_ret_postA (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_aux ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O15.O14.O13.O12.R?.R>.R=.O11.O10.(8.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(9.O15.)O4.(:.(2.&40.))R1.(;.O16.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.O2.(11.&40.O14.))(12.(>.$?.$?.)))O1.R1.)(4.(13.O16.O1.R1.)(4.(14.O16.R1.)(15.O16.R1.O2.(11.&40.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_point_read_unset_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (G Q B LEN lo : Z) (dP : mpd) (sX padX : word) (nX : Z),
  mpd_at segs m LB dP -> md_addr dP = G + 8 -> (md_own dP = LHeap -> 0 < md_p dP) ->
  rw_cells segs m (G + 56) (mpi_cells 0 sX nX padX) -> G mod 8 = 0 -> 0 < G -> G + 192 <= 2^64 ->
  mem_inv segs m -> 0 <= LEN < 2^64 ->
  al_wf AL -> cs_ok AL CS -> abase segs AL m ->
  aobj segs AL CS m (G + 8) 16 -> (1 <= md_n dP -> aobj segs AL CS m (md_p dP) (4 * md_n dP)) -> aobj segs AL CS m (G + 56) 8 ->
  stk segs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - ECP_POINT_READ_UNSET_STACK_A -> bv_unsigned sp mod 16 = 0 ->
  crange CS lo (bv_unsigned sp - lo) ->
  (G + 192 <= lo \/ bv_unsigned sp <= G) -> (1 <= md_n dP -> md_p dP + 4 * md_n dP <= lo \/ bv_unsigned sp <= md_p dP) ->
  bv_unsigned ra mod 2 = 0 ->
  a0 = Z_to_bv 64 G -> a1 = Z_to_bv 64 Q -> a2 = Z_to_bv 64 B -> a3 = Z_to_bv 64 LEN ->
  evtA segs AL CS (pure_ret_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                     (if LEN =? 0 then ECP_BAD_INPUT_DATA_U else ECP_FEATURE_UNAVAILABLE_U) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section Unset.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  #[using="IMG"] Lemma A_ecp_point_read_unset : ecp_point_read_unset_stmtA asegs AL A_ECP_POINT_READ_BINARY_U.
  Proof.
    unfold ecp_point_read_unset_stmtA, A_ECP_POINT_READ_BINARY_U. intros until nX.
    intros MP EPA PNZ CGX GAL GPOS GHI MI LENR ALWF CSOK AB OP OPL OGX ST LO0 SLO SPA SCS GSP PSP RAE -> -> -> ->.
    unfold mpi_cells in CGX.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'.
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (conj MP (conj MI (conj OPL I))) as MPbox. clear MP OPL.
    carve_frame 96%nat ST.
    do 13 zstep.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL; rewrite ?Z.mod_small in KL by exact LENR.
    { (* [comment removed for export] *)
      do 14 zstep.
      lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -96) _, STx : stk _ _ lo (bv_unsigned sp + -96) |- _ => release_frame FRx STx (bv_unsigned sp); rename STx into STf end.
      zstep. zstep.
      apply evtA_done. unfold pure_ret_postA. deexists 14. eexists.
      split; [| split; [eassumption| split; [eassumption| split; [eassumption| exact STf]]]].
      replace (LEN =? 0) with true by (symmetry; apply Z.eqb_eq; exact KL). unfold ECP_BAD_INPUT_DATA_U.
      repeat f_equal. all: match goal with |- ?gg => idtac "UNSET0-LEFT:" gg end. }
    (* [comment removed for export] *)
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - GPOS GHI; lia); clear - K0 GPOS; lia|]. clear K0.
    assert (AL7 : Z.land G 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact GAL | clear - GAL; Z.div_mod_to_equations; lia]).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    zstep. zstep. zstep. zstep. zstep. zstep. clear GOT GSB. zstep. zstep.
    ddestruct MPbox as (MP & MI0 & OPL0 & _).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mP end.
    assert (MP1 : mpd_at asegs mP LB dP).
    { destruct MP as [MPr SGN]. split; [| exact SGN].
      eapply mpdr_at_munch; [exact MPr| eassumption| eassumption| exact MI0| eassumption| rewrite EPA; cbn [disjoint_from fst snd]; split; [clear - GSP; lia| exact I]|].
      intros EO. cbn [disjoint_from fst snd]. split; [| exact I].
      dpose MPr as (_ & _ & _ & _ & _ & OW). rewrite EO in OW. destruct OW as (N1 & _). apply PSP. exact N1. }
    assert (OPL1 : 1 <= md_n dP -> aobj asegs AL CS mP (md_p dP) (4 * md_n dP)).
    { intros N1. lazymatch goal with MUx : munch _ m mP |- _ => eapply (aobj_munch asegs AL CS CSOK _ m mP); [| exact MUx| exact (OPL0 N1)] end.
      unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. exact SCS. }
    pose proof (A_mpi_size_spec AL IMG) as SPC. unfold mpi_size_stmtA, mpi_query_stmtA in SPC.
    callxA_sp (bv_unsigned sp + -96)
      (eapply SPC with (CS := CS) (LB := LB) (dX := dP) (v := Q) (lo := lo);
         rewrite ?(unsigned_lit (bv_unsigned sp + -96)) by (clear - LO0 SLO SPR; lia); rewrite ?EPA; try eassumption; try reflexivity;
         first [ solve_crange
               | exact I
               | exact OPL1
               | (eapply crange_sub; [exact SCS| clear; lia| clear - SLO; lia])
               | (intros N1; destruct (PSP N1) as [K|K]; [left; exact K| right; clear - K; lia])
               | (clear - LO0 SLO SPR SPA GSP; first [lia | Z.div_mod_to_equations; lia])
               | match goal with |- ?g => idtac "SIZE-PRE-LEFT:" g end ]).
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SIZE-LEFT:" g end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    do 15 zstep.
    lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -96) _, STx : stk _ _ lo (bv_unsigned sp + -96) |- _ => release_frame FRx STx (bv_unsigned sp); rename STx into STf end.
    zstep. zstep.
    apply evtA_done. unfold pure_ret_postA. deexists 14. eexists.
    split; [| split; [eassumption| split; [eassumption| split; [eassumption| exact STf]]]].
    replace (LEN =? 0) with false by (symmetry; apply Z.eqb_neq; exact KL). unfold ECP_FEATURE_UNAVAILABLE_U.
    repeat f_equal.
    all: match goal with |- ?gg => idtac "UNSET-LEFT:" gg end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG"] Lemma A_asn1_get_int_empty : ltac2:(CDefT.buildp (gd_tbl_A_pk_ecparams_aux ()) "PCS,P,$?.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(16.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$?.PP,$?.Plo,$?.P,(17.$18.R4.R3.(=.$19.(1:.(8.&40.R2.))(12.$19.)))P,(4.(1;.=R3.)(1<.R3.(1=.+2.+40.)))P,(5.$?.(1>.R5.+8.)=)P,(1<.=R6.)P,(14.$18.R8.)P,(1?.VAL,)P,(20.VAL,R2<.)P,(21.$18.VAL,R;.)P,(22.$18.VAL,R2>.R<.R;.+8.)P,(15.$18.R=.R:.(11.&40.R2=.))P,(1;.=R;.)P,(1;.R<.(23.(11.&40.R2?.)+30.))P,(5.$?.(1>.(11.&40.R30.)+10.)=)P,(24.R33.R>.(23.(11.&40.R31.)R>.))P,(25.(1;.(26.R11.+8.)R?.)(1;.(11.&40.R32.)R11.))P,(5.$?.(1>.(11.&40.R34.)+2.)=)P,(5.(2.&40.)R2<.(8.&40.R13.))P,(5.(2.&40.)R2<.(8.&40.R13.))(27.$18.VAL,R38.(28.$18.R37.R36.R35.R34.R30.R2?.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R18.R17.$29.R13.R16.)(6.(7.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(8.&40.$2:.)R17.(:.(2.&40.))R16.(;.$18.)))")
(* [comment removed for export] *).
  Proof.
    unfold A_ASN1_GET_INT_U. intros until lo.
    intros CPP PR PAL PPOS MI ALWF CSOK AB OPP ST LO0 SLO SPA SCS PSP RAE -> ->.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'.
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    pose proof (rw_cells_bound _ _ _ _ CPP) as PPB. cbn [cells_size csize Nat.add length] in PPB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by (clear - PPOS PPB; lia); clear - K0 PPOS; lia|]. clear K0.
    assert (AL7 : Z.land PP 7 = 0)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; first [exact PAL | clear - PAL; Z.div_mod_to_equations; lia]).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; clear - KA AL7; rewrite ?AL7 in KA; rewrite ?Zmod_0_l in KA; lia|]. clear KA.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG') in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. replace (P - P) with 0 by (clear; lia).
    if_cases KE; zify_cond KE.
    2:{ exfalso. clear - KE. vm_compute in KE. first [discriminate KE | (apply KE; reflexivity) | lia | congruence]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with FRx : rw_cells _ _ (bv_unsigned sp + -48) _, STx : stk _ _ lo (bv_unsigned sp + -48) |- _ => release_frame FRx STx (bv_unsigned sp); rename STx into STf end.
    zstep. zstep.
    apply evtA_done. unfold pure_ret_postA. deexists 14. eexists.
    split; [| split; [eassumption| split; [eassumption| split; [eassumption| exact STf]]]].
    unfold ASN1_OUT_OF_DATA_U. repeat f_equal.
    all: match goal with |- ?gg => idtac "EMPTY-LEFT:" gg end.
  Qed.
End Unset.
