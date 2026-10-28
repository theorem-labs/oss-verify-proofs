(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_core_bitlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_bitlen () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_query_post"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.core_bitlen"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "mpi_size_post"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_bitlen.mpi_core_bitlen_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_bitlen.U_MPI_CORE_BITLEN"].


Definition U_MPI_BITLEN : Z := 0x1fb64.
Definition U_MPI_SIZE : Z := 0x1fb84.
Definition U_MPI_GET_BIT : Z := 0x1f8f4.

Notation MPI_SIZE_STACK := 16 (only parsing).

(* [comment removed for export] *)
Lemma mpd_limbs_bytes : ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)Pd,$5.P,(6.R4.R3.R2.R1.)P,P,(7.$8.(9.R2.)$:.)(;.=(<.R3.))(=.(>.R6.R5.(<.R3.)(?.(10.R3.)))(=.(7.$11.(12.(13.(2.&40.)(10.R3.)))(14.R3.))(=.(=.(15.=(14.R3.))(15.(14.R3.)+2710.))(16.(=.(7.$11.(14.R3.)=)(7.$11.(<.R3.)=))(=.(;.=(<.R3.))(7.$11.(17.(<.R3.)+4.)=))))))")
(* [comment removed for export] *).
Proof.
  (intros segs m LB d dd_H; ddestruct dd_H as [[_ (_ & _ & HL & HN & HO)] _]; intros PNZ). unfold MPI_MAX_LIMBS in HN.
  refine (let K := _ : bytes_at segs m (md_p d) (u32s (md_limbs d)) /\ (md_n d = 0 /\ md_p d = 0 \/ 0 < md_p d /\ md_p d mod 4 = 0) in
          conj (proj1 K) (conj HL (conj HN (proj2 K)))).
  destruct (md_own d) eqn:EO.
  - destruct HO as [HP HN0]. rewrite HP. assert (md_limbs d = []) as -> by (destruct (md_limbs d); [reflexivity| cbn in HL; lia]).
    split; [| left; split; [exact HN0| reflexivity]]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - ddestruct HO as (N1 & PIN & PAL & [HB _]). split; [exact HB| right]. split; [exact (PNZ eq_refl)|].
    apply Z.mod_divide in PAL; [| lia]. apply Z.mod_divide; [lia|]. destruct PAL as [k E]. exists (4 * k). lia.
  - ddestruct HO as (N1 & PAL & PP & HB & _). split; [exact HB| right; split; [exact PP| exact PAL]].
Qed.

Definition mpi_query_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (R : Z -> Prop) (W : list (Z * Z)) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Lms',$18.(19.(2.&40.)Lt0,(2.&40.)(19.(2.&40.)Lt1,(2.&40.)(19.(2.&40.)Lt2,(2.&40.)(19.(2.&40.)La1,(2.&40.)(19.(2.&40.)La2,(2.&40.)(19.(2.&40.)La3,(2.&40.)(19.(2.&40.)La4,(2.&40.)(19.(2.&40.)La5,(2.&40.)(19.(2.&40.)La6,(2.&40.)(19.(2.&40.)La7,(2.&40.)(19.(2.&40.)Lt3,(2.&40.)(19.(2.&40.)Lt4,(2.&40.)(19.(2.&40.)Lt5,(2.&40.)(19.(2.&40.)Lt6,(2.&40.)(19.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(19.$11.Lr,$11.(=.(7.$18.R11.(1:.(1;.O15.O14.O13.O12.R10.R?.R>.O11.O10.(1<.&40.R1.)R=.R<.R;.R:.R9.R8.R7.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R6.R5.R4.R3.)O5.(1=.O15.)O4.(1>.(2.&40.))R2.(1?.O16.)))(=.(20.O2.O1.R2.)(=.(21.O16.O1.R2.)(=.(22.O16.R2.)A1.O3.R1.))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_bitlen_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PdX,$5.P,(6.O2.R3.R2.R1.)P,P,(7.$8.(9.R2.)$:.)(;.=(<.R3.))P,(22.O2.R5.)P,(7.(2.&40.)R1>.(1<.&40.(24.R4.)))(25.O2.(26.O2.R28.R27.R26.R25.R21.R20.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R9.R8.Lr,$11.(7.$11.R1.(27.(10.R6.)(14.R6.)))(28.(29.$11.$11.))R7.)(1:.(1;.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(1<.&40.O1.)R8.(1>.(2.&40.))R7.(1?.O2.)))")
(* [comment removed for export] *).

Definition mpi_size_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Lms',$18.(19.(2.&40.)Lt0,(2.&40.)(19.(2.&40.)Lt1,(2.&40.)(19.(2.&40.)Lt2,(2.&40.)(19.(2.&40.)La1,(2.&40.)(19.(2.&40.)La2,(2.&40.)(19.(2.&40.)La3,(2.&40.)(19.(2.&40.)La4,(2.&40.)(19.(2.&40.)La5,(2.&40.)(19.(2.&40.)La6,(2.&40.)(19.(2.&40.)La7,(2.&40.)(19.(2.&40.)Lt3,(2.&40.)(19.(2.&40.)Lt4,(2.&40.)(19.(2.&40.)Lt5,(2.&40.)(19.(2.&40.)Lt6,(2.&40.)(19.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(=.(7.$18.R10.(1:.(1;.O15.O14.O13.O12.R?.R>.R=.O11.O10.(1<.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(1=.O15.)O4.(1>.(2.&40.))R1.(1?.O16.)))(=.(20.(2:.(29.$11.$11.)(2;.$11.$11.(2<.(2=.&40.O14.)+10.)(2=.&40.O14.))(28.(29.$11.$11.)))O1.R1.)(=.(21.O16.O1.R1.)(=.(22.O16.R1.)(2>.O16.R1.O2.(2=.&40.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_size_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PdX,$5.Plo,$11.P,(6.O2.R4.R3.R2.)P,P,(7.$8.(9.R3.)$:.)(;.=(<.R4.))P,(22.O2.R6.)P,(2>.O2.R7.R4.(2=.&40.R27.))P,(15.R5.(2<.(2=.&40.R28.)+10.))P,(7.$11.(17.(2=.&40.R29.)+10.)=)P,(16.(15.(2?.(24.R8.)+10.)R7.)(15.(2=.&40.R2:.)(24.R8.)))P,(16.(15.(2?.(<.R9.)(30.+4.(14.R9.)))R8.)(15.(2=.&40.R2;.)(<.R9.)))P,(7.(2.&40.)R24.(1<.&40.(24.R:.)))(25.O2.(31.O2.R2>.R2=.R2<.R2;.R27.R26.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R?.R>.(32.(2?.(27.(10.R;.)(14.R;.))+7.)+8.)R:.R=.)(1:.(1;.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(1<.&40.O1.)R>.(1>.(2.&40.))R=.(1?.O2.)))")
(* [comment removed for export] *).

Definition mpi_get_bit_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PdX,$5.Ppos,$11.P,(6.O2.R4.R3.R2.)P,P,(7.$8.(9.R3.)$:.)(;.=(<.R4.))P,(22.O2.R6.)P,(=.(15.=R4.)(;.R4.(33.+2.+40.)))P,(7.(2.&40.)R20.(1<.&40.(24.R6.)))P,(7.(2.&40.)R20.(1<.&40.R6.))(25.O2.(26.O2.R2;.R2:.R29.R28.R24.R23.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R<.R;.Lr,$11.(=.(15.=R1.)(15.R1.+1.))(28.(29.$11.$11.))R:.)(1:.(1;.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(1<.&40.O1.)R;.(1>.(2.&40.))R:.(1?.O2.)))")
(* [comment removed for export] *).

Local Ltac cond_decide :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  repeat match goal with
    | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
    | |- context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
    | |- context [Z.eqb ?x ?y] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
    | |- context [Z.b2z ?b] => progress cbn [Z.b2z]
    | |- context [negb ?b] => progress cbn [negb]
    | |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
  end; reflexivity.
Local Ltac if_false_x :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in assert (E : c = false) by cond_decide; rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land_zero_any :=
  repeat match goal with
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
      rewrite E; clear E
  | |- context [Z.land ?p 3] => let E := fresh "E" in
      assert (E : Z.land p 3 = 0) by (change (Z.land p 3) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia);
      rewrite E; clear E
  end.
Local Ltac rec_checks := zstep; if_false_x; zstep; land_zero_any; zstep; if_false.

(* [comment removed for export] *)
Lemma U_core_bitlen_null : ltac2:(CDefT.buildp (gd_tbl_P_mpi_bitlen ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$11.P,(22.$34.R2.)P,(=.(15.=R2.)(;.R2.(33.+2.+40.)))P,(7.(2.&40.)R1<.(1<.&40.R3.))P,(7.(2.&40.)R1<.(1<.&40.=))(25.$34.(35.$34.R27.R26.R25.R24.R20.R1?.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R8.R7.(28.(2.&40.))=R6.)(1:.(1;.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R8.(1<.&40.$36.)R7.(1>.(2.&40.))R6.(1?.$34.)))")
(* [comment removed for export] *).
Proof.
  intros until A. intros MI HA -> ->. unfold U_MPI_CORE_BITLEN.
  zstep. zstep. zstep. if_false. zstep. if_true.
  zstep. zstep.
  apply evt_done. unfold mpi_core_bitlen_post. deexists 15. split; [reflexivity|].
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. reflexivity.
Qed.

Lemma U_mpi_bitlen_spec : mpi_bitlen_stmt usegs U_MPI_BITLEN.
Proof.
  unfold mpi_bitlen_stmt, U_MPI_BITLEN. intros until dX. intros MA PNZ MI ->.
  pose proof (mpd_limbs_bytes _ _ _ _ MA PNZ) as (PB & LEN & NR & PC).
  ddestruct MA as [[CH (XAL & X0 & _ & _ & _)] SG]. unfold mpi_cells in CH.
  pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
  rec_checks. zstep. zstep. zstep. zstep.
  replace (zx16 (Z_to_bv 64 (md_n dX))) with (Z_to_bv 64 (md_n dX)) by (unfold zx16; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
  destruct PC as [[N0 P0]|[PP PAL]].
  - rewrite N0, P0. eapply evt_mono; [eapply U_core_bitlen_null with (A := 0); [exact MI| lia| reflexivity| reflexivity]|].
    cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO. destruct_exs PO. ddestruct PO as (-> & _ & _ & MI' & ->).
    unfold mpi_query_post. deexists 15. exists (core_bitlen [] 0). split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI'|].
    assert (md_limbs dX = []) as -> by (destruct (md_limbs dX); [reflexivity| cbn in LEN; lia]). reflexivity.
  - pose proof U_mpi_core_bitlen_spec as SP. unfold mpi_core_bitlen_stmt, U_MPI_CORE_BITLEN in SP.
    eapply evt_mono; [eapply SP with (xs := md_limbs dX); try eassumption; try reflexivity; try lia|].
    cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO. destruct_exs PO. ddestruct PO as (-> & _ & _ & MI' & ->).
    unfold mpi_query_post. deexists 15. eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI'|]. reflexivity.
Qed.

Lemma U_mpi_size_spec : mpi_size_stmt usegs U_MPI_SIZE.
Proof.
  unfold mpi_size_stmt, U_MPI_SIZE. intros until lo. intros MA PNZ MI ST SLO SPA XS PS ->.
  pose proof (mpd_limbs_bytes _ _ _ _ MA PNZ) as (PB & LEN & NR & PC).
  ddestruct MA as [[CH (XAL & X0 & _ & _ & OWN)] SG]. unfold mpi_cells in CH.
  pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  pose proof (core_bitlen_range (md_limbs dX) (md_n dX) ltac:(lia)) as CBR.
  carve_frame 16%nat ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
  rec_checks. zstep. zstep. zstep. zstep. zstep.
  replace (zx16 (Z_to_bv 64 (md_n dX))) with (Z_to_bv 64 (md_n dX)) by (unfold zx16; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (CALL : evt usegs (mpi_core_bitlen_post usegs (Z_to_bv 64 0x1fba8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (md_limbs dX) (md_n dX) m1)
            (MS (mkR (Z_to_bv 64 0x1fba8) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (md_p dX)) (Z_to_bv 64 (md_n dX)) (Z_to_bv 64 (md_p dX)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 U_MPI_CORE_BITLEN) fc None m1 (seg_rom usegs))).
  { destruct PC as [[N0 P0]|[PP PAL]].
    - rewrite N0, P0. assert (md_limbs dX = []) as -> by (destruct (md_limbs dX); [reflexivity| cbn in LEN; lia]).
      eapply U_core_bitlen_null with (A := 0); [assumption| lia| reflexivity| reflexivity].
    - pose proof U_mpi_core_bitlen_spec as SP. unfold mpi_core_bitlen_stmt in SP.
      eapply SP; try eassumption; try reflexivity; try lia. }
  unfold U_MPI_CORE_BITLEN in CALL.
  eapply evt_cut; [exact CALL|]. clear CALL. cbv beta. intros ms' PO. unfold mpi_core_bitlen_post in PO.
  destruct_exs PO. ddestruct PO as (-> & _ & _ & MI1 & ->).
  replace (ret_pc (Z_to_bv 64 0x1fba8)) with (Z_to_bv 64 0x1fba8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  replace ((core_bitlen (md_limbs dX) (md_n dX) + 7) ≫ 3) with ((core_bitlen (md_limbs dX) (md_n dX) + 7) / 8)
    by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  apply evt_done. unfold mpi_size_post. deexists 15. split; [reflexivity| split; [exact MU| split; [exact WM| split; [assumption| assumption]]]].
Qed.

Lemma land_m4' : forall i, 0 <= i < 2^64 -> Z.land i 18446744073709551612 = 4 * (i / 4).
Proof.
  intros i Hi.
  replace 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))) by reflexivity.
  rewrite Z.land_assoc. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^2) with 4. lia.
Qed.

Lemma land1_range : forall a, 0 <= a -> 0 <= Z.land a 1 <= 1.
Proof.
  intros a Ha. pose proof (Z.land_ones a 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. rewrite E.
  change (2 ^ 1) with 2. pose proof (Z.mod_pos_bound a 2 ltac:(lia)). lia.
Qed.

Lemma U_mpi_get_bit_spec : mpi_get_bit_stmt usegs U_MPI_GET_BIT.
Proof.
  unfold mpi_get_bit_stmt, U_MPI_GET_BIT. intros until pos. intros MA PNZ MI POS -> ->.
  pose proof (mpd_limbs_bytes _ _ _ _ MA PNZ) as (PB & LEN & NR & PC).
  ddestruct MA as [[CH (XAL & X0 & _ & _ & OWN)] SG]. unfold mpi_cells in CH.
  pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
  pose proof (proj1 (proj2 PB)) as PBND. rewrite u32s_length in PBND.
  rec_checks. zstep. zstep.
  replace (bv_unsigned (zx16 (Z_to_bv 64 (md_n dX))) ≪ 5) with (32 * md_n dX)
    by (unfold zx16; rewrite !unsigned_lit by lia; rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep; if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    zstep. zstep. apply evt_done. unfold mpi_query_post. deexists 15. exists 0. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| lia].
  - destruct PC as [[N0 _]|[PP PAL]]; [exfalso; lia|].
    zstep. zstep. zstep. rewrite (Z.shiftr_div_pow2 pos 3) by lia. rewrite land_m4' by lia.
    replace (4 * (pos / 2 ^ 3 / 4)) with (4 * (pos / 32)) by (rewrite Z.div_div by lia; reflexivity).
    zstep. zstep; if_false_x. zstep. zstep. zstep. zstep; if_false_x. zstep; if_false_x.
    zstep. land_zero_any. zstep; if_false.
    rd PB (pos / 32).
    zstep. zstep. zstep.
    apply evt_done. unfold mpi_query_post. deexists 15.
    lazymatch goal with |- context [Z_to_bv 64 (Z.land ?v 1)] => exists (Z.land v 1) end.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    apply land1_range. apply Z.mod_pos_bound. lia.
Qed.
