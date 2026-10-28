(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_set_bit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT.
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
Ltac2 gd_tbl_A_mpi_set_bit () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_set_bit0_postA"].


Definition A_MPI_SET_BIT_E : Z := 0x09c514.   (* [comment removed for export] *)
Notation MPI_SET_BIT_STACK_A' := 112 (only parsing).

Definition mpi_set_bit0_postA (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LB : list blk) (dX : mpd) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_set_bit ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O16.O15.O14.O13.R10.R?.R>.O12.O11.(9.&40.=)R=.R<.R;.R:.R9.R8.R7.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R6.R5.R4.R3.)O6.(:.O16.)O5.(;.(2.&40.))R2.(<.O17.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O2.(12.&40.O15.))(>.(?.$10.$10.)(11.$10.$10.(13.O3.)(14.(13.O3.)(15.+4.(16.O3.))))(17.(?.$10.$10.))))O1.R2.)(5.(18.O17.O1.R2.)(5.(19.O17.R2.)(5.(1:.O17.R2.O2.(12.&40.O15.))(5.(1;.O17.R2.O4.(1<.(1=.O3.)(1>.O3.)(16.O3.)(13.O3.)R1.(1?.O3.)(20.O3.)))(6.$21.(22.(2.&40.)R1.)(22.(2.&40.)(23.O3.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_set_bit0_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_set_bit ()) "PCS,P,$10.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(24.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(4.$25.)PdX,$26.Ppos,$10.Plo,$10.P,(1;.O3.R5.R4.R3.)P,(27.(6.$28.(20.R4.)$29.))P,P,(6.$28.(20.R5.)$2:.)(5.(2;.=(13.R6.))(2<.(14.(13.R6.)(15.+4.(16.R6.)))R4.))P,(19.O3.R8.)P,(5.(2<.=R6.)(2;.R6.(2=.+2.+40.)))P,(2>.O2.)P,(2?.O2.R2=.)P,(30.O3.O2.R<.)P,(31.O3.O2.R2?.R=.(1=.R;.)+10.)P,P,(2<.+1.(16.R<.))(31.O3.O2.R31.R?.(13.R=.)(15.+4.(16.R=.)))P,(1:.O3.R?.R;.(12.&40.R2?.))P,(2<.=R<.)P,(2<.R=.(32.(12.&40.R31.)+70.))P,(6.$10.(33.(12.&40.R32.)+10.)=)P,(34.R35.R?.(32.(12.&40.R33.)R?.))P,(35.(2<.(14.(1=.R12.)+10.)R10.)(2<.(12.&40.R34.)(1=.R12.)))P,P,(6.$28.(20.R13.)$2:.)(35.(2<.(14.(1=.R14.)+10.)(13.R14.))(2<.(14.(13.R14.)(15.+4.(16.R14.)))(1=.R14.)))P,(6.(2.&40.)R2>.(9.&40.(1=.R14.)))P,(6.(2.&40.)R2>.(9.&40.R14.))P,(6.(2.&40.)R2>.(9.&40.=))(36.O3.O2.R3;.(37.O3.R3:.R39.R38.R37.R33.R32.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1;.R1:.R18.R17.R15.R19.)(7.(8.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R1;.(9.&40.O1.)R1:.(;.(2.&40.))R19.(<.O3.)))")
(* [comment removed for export] *).

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import BX_zchk.
Local Ltac zchk_fails ::= constr:([0x09c71c]).
Local Ltac zchk_new ::= constr:([0x09c54c; 0x09c550; 0x09c554; 0x09c5a4; 0x09c5a8; 0x09c5ac; 0x09c5b0; 0x09c5b4; 0x09c5b8; 0x09c5bc; 0x09c5c0; 0x09c5ec; 0x09c5f8; 0x09c614; 0x09c660; 0x09c680; 0x09c6ac; 0x09c6b0; 0x09c6b4; 0x09c714; 0x09c718; 0x09c740; 0x09c744; 0x09c74c]).
Local Ltac zstep ::= zpre; step; zsimp; zpre.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.

  #[using="IMG"] Lemma A_mpi_set_bit0_walk : mpi_set_bit0_stmtA asegs AL A_MPI_SET_BIT_E.
  Proof.
    unfold mpi_set_bit0_stmtA, A_MPI_SET_BIT_E. intros until lo. intros MA NST PLO MI POS ALWF CSOK AB OX OP ST LO0 SLO SPA SCS XS XP -> -> ->.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
    destruct dX as [X sg n P limbs pad own].
    dpose MA as [[CH (XAL & X0 & LEN & NR & OWN)] SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    unfold mpi_cells in CH. unfold MPI_MAX_LIMBS in NR.
    pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 4 * n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
    carve_frame 96%nat ST.
    (* [comment removed for export] *)
    do 12 zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (abase_got _ _ _ AB) as GOT. pose proof (abase_gsb _ _ _ AB) as GSB. rewrite (proj1 IMG) in GOT.
    (* [comment removed for export] *)
    zstep. zstep. zstep. clear GOT GSB.
    (* [comment removed for export] *)
    zstep. zstep. zstep. shadow_chk OX (X + 10) 2.
    (* [comment removed for export] *)
    zstep. rewrite zx16_small by (clear - NR; lia).
    zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32.
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (clear - NR POS; lia).
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      do 11 zstep. zstep.
      match goal with H : stk asegs ?mx lo _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR H (bv_unsigned sp) end.
      zstep.
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply evtA_done. unfold mpi_set_bit0_postA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. deexists 15. exists limbs.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
      split; [| reflexivity].
      eapply mpd_at_munch; [exact MA| exact NST| exact MU0| exact WM| cbn; split; [clear - XS; lia| exact I]| intros HO; cbn; split; [| exact I]; destruct (PLO HO); clear - H0; lia].
    - (* [comment removed for export] *)
      destruct own eqn:EO; [destruct OWN as [_ N0]; exfalso; clear - N0 K POS; lia| | exfalso; exact (NST eq_refl)].
      ddestruct OWN as (N1 & PIN & PAL & PX). destruct (PLO eq_refl) as [P0 PL]. specialize (XP eq_refl). specialize (OP N1).
      lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      apply (fun H => u32arr_transport asegs _ m m1 _ _ H MU0 WM) in PX; [| cbn; split; [clear - PL LEN; lia| exact I]].
      apply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m m1 P (4 * n)) in OP;
        [| unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil] | exact MU0].
      clear MU0.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 5) with 32. change (2 ^ 2) with 4.
      assert (IB : 0 <= pos / 32 < n) by (split; [apply Z.div_pos; clear - POS; lia| apply Z.div_lt_upper_bound; clear - K POS; lia]).
      set (i := pos / 32) in *. try replace (i * 4) with (4 * i) by (clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk OP (P + 4 * i) 4.
      (* [comment removed for export] *)
      rd PX i.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      pose proof (u32arr_store_ok asegs _ P limbs i _ PX ltac:(lia) ltac:(f_equal; lia)) as SOKw0.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write asegs _ P limbs i v PX ltac:(lia)) as PX0 end.
      store_done.
      shadow_chk OP (P + 4 * i) 4.
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      pose proof (u32arr_store_ok asegs _ P _ i _ PX0 ltac:(rewrite upd_length; lia) ltac:(f_equal; lia)) as SOKw.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write asegs _ P _ i v PX0 ltac:(rewrite upd_length; lia)) as PX' end.
      store_done.
      (* [comment removed for export] *)
      zstep.
      do 11 zstep. zstep.
      match goal with H : stk asegs ?mx lo _ |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => release_frame FR H (bv_unsigned sp) end.
      zstep.
      apply evtA_done. unfold mpi_set_bit0_postA. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. deexists 15.
      lazymatch type of PX' with u32arr _ _ _ ?l => exists l end.
      split; [reflexivity|]. split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
      split; [| rewrite !upd_length; reflexivity].
      split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [unfold mpi_cells; assumption|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite !upd_length; exact LEN|]. split; [unfold MPI_MAX_LIMBS; clear - NR; lia|].
      split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact PX'].
    all: match goal with |- ?g => idtac "SETBIT-LEFT:" g end.
  Qed.
End Walk.

Lemma A_mpi_set_bit0_spec : forall AL, asan_img_ok AL -> mpi_set_bit0_stmtA asegs AL A_MPI_SET_BIT_E.
Proof. intros. apply A_mpi_set_bit0_walk. assumption. Qed.
