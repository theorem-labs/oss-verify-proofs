(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_bitlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_mpi_core_bitlen.
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
Ltac2 gd_tbl_A_mpi_bitlen () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_query_postA"; "mpi_query_stmtA"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"].


Definition A_MPI_BITLEN_Q : Z := 0x09c8a8.   (* [comment removed for export] *)
Definition A_MPI_SIZE_Q : Z := 0x09c91c.     (* [comment removed for export] *)
Definition A_MPI_GET_BIT_Q : Z := 0x09c434.  (* [comment removed for export] *)
Notation MPI_BITLEN_STACK_A := 16 (only parsing).    (* [comment removed for export] *)
Notation MPI_SIZE_STACK_A := 32 (only parsing).      (* [comment removed for export] *)
Notation MPI_GET_BIT_STACK_A := 16 (only parsing).

Definition mpi_query_postA (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (R : Z -> Prop) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_bitlen ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(5.(6.$0.R11.(7.(8.O15.O14.O13.O12.R10.R?.R>.O11.O10.(9.&40.R1.)R=.R<.R;.R:.R9.R8.R7.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R6.R5.R4.R3.)O5.(:.O15.)O4.(;.(2.&40.))R2.(<.O16.)))(5.(=.(>.(?.$4.$4.)(10.$4.$4.O2.(11.&40.O14.))(12.(?.$4.$4.)))O1.R2.)(5.(13.O16.O1.R2.)(5.(14.O16.R2.)(5.(15.O16.R2.O2.(11.&40.O14.))A1.O3.R1.)))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_query_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY STACK : Z)
    (PRE : mpd -> Z -> Prop) (R : mpd -> Z -> Z -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_bitlen ()) "PCS,P,$4.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(16.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(17.$18.)PdX,$19.Pv,$4.Plo,$4.P,(1:.O6.R5.R4.R3.)P,P,(6.$1;.(1<.R4.)$1=.)(1>.=(1?.R5.))P,(14.O6.R7.)P,A2.O2.R6.R5.P,(20.O5.)P,(21.O5.R2<.)P,(22.O6.O5.R;.)P,(23.O6.O5.R2>.R<.(24.R:.)+10.)P,P,(25.+1.(26.R;.))(23.O6.O5.R30.R>.(1?.R<.)(27.+4.(26.R<.)))P,(15.O6.R>.R:.(11.&40.R2>.))P,(25.=R;.)P,(25.R<.(28.(11.&40.R30.)O3.))P,(6.$4.(29.(11.&40.R31.)+10.)=)P,(2:.R34.R>.(28.(11.&40.R32.)R>.))P,(2;.(25.(2<.(24.R11.)+10.)R?.)(25.(11.&40.R33.)(24.R11.)))P,P,(25.+1.(26.R12.))(2;.(25.(2<.(1?.R13.)(27.+4.(26.R13.)))R11.)(25.(11.&40.R35.)(1?.R13.)))P,(6.(2.&40.)R2=.(9.&40.(24.R13.)))P,(6.(2.&40.)R2=.(9.&40.R13.))(2=.O6.O5.R39.(2>.O6.R38.R37.R36.R35.R31.R30.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R19.R18.A2.O1.R15.R14.R13.R17.)(7.(8.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(9.&40.O4.)R18.(;.(2.&40.))R17.(<.O6.)))")
(* [comment removed for export] *).

Definition mpi_bitlen_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_bitlen ()) "(2?.O3.O2.O1.+10.L,$19.L,$4.$30.LdX,$19.L,$4.Lr,$4.(6.$4.R1.(31.(32.R3.)(26.R3.))))")
(* [comment removed for export] *).
Definition mpi_size_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_bitlen ()) "(2?.O3.O2.O1.+20.L,$19.L,$4.$30.LdX,$19.L,$4.Lr,$4.(6.$4.R1.(33.(2<.(31.(32.R3.)(26.R3.))+7.)+8.)))")
(* [comment removed for export] *).
Definition mpi_get_bit_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_bitlen ()) "(2?.O3.O2.O1.+10.L,$19.Lpos,$4.(5.(25.=R1.)(1>.R1.(34.+2.+40.)))L,$19.L,$4.Lr,$4.(5.(25.=R1.)(25.R1.+1.)))")
(* [comment removed for export] *).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09c900; 0x09c980; 0x09c4e8]).
Local Ltac zchk_new ::= constr:([0x09c8b0; 0x09c8b4; 0x09c8b8; 0x09c918; 0x09c924; 0x09c928; 0x09c92c; 0x09c998; 0x09c43c; 0x09c440; 0x09c444; 0x09c494; 0x09c498; 0x09c49c; 0x09c4a0; 0x09c4a4; 0x09c4a8; 0x09c4ac; 0x09c4b0; 0x09c4c8]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  Ltac al_facts ALWF CSOK :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Ltac query_facts MA PNZ sp :=
    pose proof (mpd_limbs_bytes _ _ _ _ MA PNZ) as (PB & LEN & NR & PC);
    destruct MA as [[CH (XAL & X0 & _ & _ & OWN)] SG]; unfold mpi_cells in CH;
    pose proof (rw_cells_bound _ _ _ _ CH) as XB; cbn [cells_size csize Nat.add] in XB;
    pose proof (bytes_at_bound _ _ _ _ PB) as PBB; rewrite u32s_length in PBB;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  #[using="IMG"] Lemma A_mpi_bitlen_walk : mpi_bitlen_stmtA asegs AL A_MPI_BITLEN_Q.
  Proof.
    unfold mpi_bitlen_stmtA, mpi_query_stmtA, A_MPI_BITLEN_Q. intros until lo. intros MA PNZ MI _ ALWF CSOK AB OX OP ST LO0 SLO SPA SCS DSX DSP -> ->.
    al_facts ALWF CSOK. query_facts MA PNZ sp.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (md_addr dX + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dX))) with (Z_to_bv 64 (md_n dX))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    (* [comment removed for export] *)
    zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (OP1 : 1 <= md_n dX -> aobj asegs AL CS m1 (md_p dX) (4 * md_n dX)).
    { intros Hn. eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m m1); [| exact MU| exact (OP Hn)].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    destruct PC as [[N0 P0]|[PP PAL]].
    - (* [comment removed for export] *)
      rewrite N0, P0. assert (EL : md_limbs dX = []) by (destruct (md_limbs dX); [reflexivity| cbn in LEN; clear - LEN N0; lia]).
      pose proof (A_mpi_core_bitlen_z_spec AL IMG) as SP. unfold mpi_core_bitlen_z_stmtA, A_MPI_CORE_BITLEN, MPI_CORE_BITLEN_STACK_A in SP.
      eapply evtA_mono; [eapply SP with (A := 0) (lo := lo); try eassumption; try reflexivity; clear; lia|].
      cbv beta. intros ms' PO. unfold mpi_core_bitlen_postA, MPI_CORE_BITLEN_STACK_A in PO. destruct_exs PO. ddestruct PO as (-> & MU1 & WM1 & MI1 & -> & ST1).
      unfold mpi_query_postA. deexists 15. exists (core_bitlen [] 0). split; [reflexivity|].
      split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]; intros y Hy; cbn [outside] in *; clear - SLO Hy; lia]|].
      split; [eapply wmono_trans; [exact WM| exact WM1]|]. split; [exact MI1|]. split; [exact ST1|]. rewrite EL. reflexivity.
    - pose proof (A_mpi_core_bitlen_spec AL IMG) as SP. unfold mpi_core_bitlen_stmtA, A_MPI_CORE_BITLEN, MPI_CORE_BITLEN_STACK_A in SP.
      assert (N1 : 1 <= md_n dX) by (destruct (md_own dX); [destruct OWN as [P0 _]; exfalso; clear - P0 PP; lia| exact (proj1 OWN)| exact (proj1 OWN)]).
      eapply evtA_mono; [eapply SP with (A := md_p dX) (n := md_n dX) (xs := md_limbs dX) (lo := lo); try eassumption; try reflexivity|].
      all: try (apply OP1; exact N1).
      all: try (clear - NR LEN PBB PP N1 LO0 SLO SPA SPR DSP; first [lia | destruct (DSP N1); lia]).
      all: match goal with |- forall _, _ => idtac | |- ?g => idtac "BITLEN-PRE-LEFT:" g end.
      cbv beta. intros ms' PO. unfold mpi_core_bitlen_postA, MPI_CORE_BITLEN_STACK_A in PO. destruct_exs PO. ddestruct PO as (-> & MU1 & WM1 & MI1 & -> & ST1).
      unfold mpi_query_postA. deexists 15. eexists. split; [reflexivity|].
      split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]; intros y Hy; cbn [outside] in *; clear - SLO Hy; lia]|].
      split; [eapply wmono_trans; [exact WM| exact WM1]|]. split; [exact MI1|]. split; [exact ST1|]. reflexivity.
    all: match goal with |- ?g => idtac "BITLEN-LEFT:" g end.
  Qed.

  #[using="IMG"] Lemma A_mpi_size_walk : mpi_size_stmtA asegs AL A_MPI_SIZE_Q.
  Proof.
    unfold mpi_size_stmtA, mpi_query_stmtA, A_MPI_SIZE_Q. intros until lo. intros MA PNZ MI _ ALWF CSOK AB OX OP ST LO0 SLO SPA SCS DSX DSP -> ->.
    al_facts ALWF CSOK. query_facts MA PNZ sp.
    pose proof (core_bitlen_range (md_limbs dX) (md_n dX) ltac:(clear - NR; lia)) as CBR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (md_addr dX + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dX))) with (Z_to_bv 64 (md_n dX))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (OP1 : 1 <= md_n dX -> aobj asegs AL CS m1 (md_p dX) (4 * md_n dX)).
    { intros Hn. eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m m1); [| exact MU| exact (OP Hn)].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]. }
    assert (SCS1 : crange CS lo (bv_unsigned sp + -16 - lo)) by (eapply crange_sub; [exact SCS| clear; lia| clear; lia]).
    match goal with H : stk asegs m1 lo _ |- _ => rename H into ST1 end.
    match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
    (* [comment removed for export] *)
    eapply (evtA_cut asegs AL CS (mpi_core_bitlen_postA asegs _ _ gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (md_limbs dX) (md_n dX) lo m1)).
    { destruct PC as [[N0 P0]|[PP PAL]].
      - assert (EL : md_limbs dX = []) by (destruct (md_limbs dX); [reflexivity| cbn in LEN; clear - LEN N0; lia]).
        rewrite EL, N0, P0.
        pose proof (A_mpi_core_bitlen_z_spec AL IMG) as SP. unfold mpi_core_bitlen_z_stmtA, MPI_CORE_BITLEN_STACK_A, A_MPI_CORE_BITLEN in SP.
        eapply SP with (A := 0) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia; try eassumption; try reflexivity.
        all: clear - SLO SPA SPR LO0; try lia.
        all: match goal with |- ?g => idtac "SIZE0-PRE-LEFT:" g end.
      - assert (N1 : 1 <= md_n dX) by (destruct (md_own dX); [destruct OWN as [P0 _]; exfalso; clear - P0 PP; lia| exact (proj1 OWN)| exact (proj1 OWN)]).
        pose proof (A_mpi_core_bitlen_spec AL IMG) as SP. unfold mpi_core_bitlen_stmtA, MPI_CORE_BITLEN_STACK_A, A_MPI_CORE_BITLEN in SP.
        eapply SP with (A := md_p dX) (n := md_n dX) (xs := md_limbs dX) (lo := lo); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by qlia; try eassumption; try reflexivity.
        all: first [ apply OP1; exact N1
                   | clear - NR LEN PBB PP N1 LO0 SLO SPA SPR; lia
                   | destruct (DSP N1); clear - NR LEN PBB PP N1 LO0 SLO SPA SPR H; lia
                   | match goal with |- ?g => idtac "SIZE1-PRE-LEFT:" g end ]. }
    cbv beta. intros ms' PO. unfold mpi_core_bitlen_postA, MPI_CORE_BITLEN_STACK_A in PO.
    destruct_exs PO. ddestruct PO as (-> & MU1 & WM1 & MI2 & -> & ST2).
    rewrite ?(unsigned_lit (bv_unsigned sp + -16)) in MU1, ST2 by qlia.
    replace (ret_pc (Z_to_bv 64 0x09c96c)) with (Z_to_bv 64 0x09c96c) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    apply (rw_cells_transport asegs _ m1 m2 _ _ FR MU1 WM1) in FR || (eapply (rw_cells_transport asegs _ m1 m2) in FR; [| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; clear; lia]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    release_frame FR ST2 (bv_unsigned sp).
    zstep.
    apply evtA_done. unfold mpi_query_postA. deexists 15. eexists. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]; intros y Hy; cbn [outside] in *; clear - SLO Hy; lia]|].
    split; [eapply wmono_trans; [exact WM| exact WM1]|]. split; [exact MI2|]. split; [assumption|].
    rewrite Z.shiftr_div_pow2 by (clear; lia). reflexivity.
    all: match goal with |- ?g => idtac "SIZE-LEFT:" g end.
  Qed.

  #[using="IMG"] Lemma A_mpi_get_bit_walk : mpi_get_bit_stmtA asegs AL A_MPI_GET_BIT_Q.
  Proof.
    unfold mpi_get_bit_stmtA, mpi_query_stmtA, A_MPI_GET_BIT_Q. intros until lo. intros MA PNZ MI POS ALWF CSOK AB OX OP ST LO0 SLO SPA SCS DSX DSP -> ->.
    al_facts ALWF CSOK. query_facts MA PNZ sp.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (md_addr dX + 10) 2.
    (* [comment removed for export] *)
    zstep.
    replace (zx16 (Z_to_bv 64 (md_n dX))) with (Z_to_bv 64 (md_n dX))
      by (unfold zx16; rewrite !unsigned_lit by (clear - NR; lia); rewrite Z.mod_small by (clear - NR; lia); reflexivity).
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by (clear - POS NR; lia).
      zstep. zstep. zstep.
      match goal with H : stk asegs ?mx lo _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR H (bv_unsigned sp) end.
      zstep.
      apply evtA_done. unfold mpi_query_postA. deexists 15. exists 0. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| clear; lia].
    - rewrite ?unsigned_lit in K by (clear - POS NR; lia).
      destruct PC as [[N0 _]|[PP PAL]]; [exfalso; clear - N0 K POS; lia|].
      assert (N1 : 1 <= md_n dX) by (destruct (md_own dX); [destruct OWN as [P0 _]; exfalso; clear - P0 PP; lia| exact (proj1 OWN)| exact (proj1 OWN)]).
      specialize (OP N1). specialize (DSP N1).
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        apply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m mx (md_p dX) (4 * md_n dX)) in OP;
          [| unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil] | exact MU] end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. rewrite (Z.shiftr_div_pow2 v 3) by (clear; lia). rewrite land_m4' by (clear - POS; lia).
      replace (4 * (v / 2 ^ 3 / 4)) with (4 * (v / 32)) by (rewrite Z.div_div by (clear; lia); reflexivity).
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OP (md_p dX + 4 * (v / 32)) 4.
      (* [comment removed for export] *)
      rd PB (v / 32).
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep.
      match goal with H : stk asegs ?mx lo _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR H (bv_unsigned sp) end.
      zstep.
      apply evtA_done. unfold mpi_query_postA. deexists 15.
      lazymatch goal with |- context [Z_to_bv 64 (Z.land ?w 1)] => exists (Z.land w 1) end.
      split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      apply land1_range. apply Z.mod_pos_bound. clear; lia.
    all: match goal with |- ?g => idtac "GETBIT-LEFT:" g end.
  Qed.

End Walk.

Lemma A_mpi_bitlen_spec : forall AL, asan_img_ok AL -> mpi_bitlen_stmtA asegs AL A_MPI_BITLEN_Q.
Proof. intros. apply A_mpi_bitlen_walk. assumption. Qed.
Lemma A_mpi_size_spec : forall AL, asan_img_ok AL -> mpi_size_stmtA asegs AL A_MPI_SIZE_Q.
Proof. intros. apply A_mpi_size_walk. assumption. Qed.
Lemma A_mpi_get_bit_spec : forall AL, asan_img_ok AL -> mpi_get_bit_stmtA asegs AL A_MPI_GET_BIT_Q.
Proof. intros. apply A_mpi_get_bit_walk. assumption. Qed.
