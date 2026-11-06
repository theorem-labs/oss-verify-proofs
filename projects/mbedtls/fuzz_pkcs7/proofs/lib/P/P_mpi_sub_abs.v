(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_layout P_string P_platform_zeroize P_mpi_free P_mpi_addsub P_mpi_cmp
     P_mpi_sub_abs_C P_mpi_sub_abs_B.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_sub_abs () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.P.P_mpi_sub_abs_C.sub_frame"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.P.P_mpi_cmp.SIGF"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_NEGATIVE_VALUE"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Exec.evt"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.MpiCoreAux.lval"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.P.P_layout.P_layout"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub_front_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (X Aa Ba nA nB lo : Z) (zs : list word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Lms',$0.(1.P,(2.&40.)(3.(2.&8.))Lm1,P,(2.&40.)(3.(2.&8.))(1.$4.Ln,$4.(5.(6.(7.(8.$4.$4.)(9.$4.$4.(:.(;.&40.O19.)+40.)(;.&40.O19.))(<.(8.$4.$4.)))O8.R2.)(5.(=.$>.O8.R2.)(5.(?.$>.R2.)(5.(10.$>.R2.(:.(;.&40.O19.)+40.)(11.O1:.O16.O15.O14.O13.O12.O11.O10.))(5.(12.$>.R2.O2.(:.(;.&40.O19.)+40.))(5.(13.O1.O3.R1.)(14.(1.(2.&40.)Lraj,(2.&40.)(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Ls4j,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(5.(15.R11.O4.)(16.$0.R13.(17.(18.R10.(19.&40.(:.(;.&40.O19.)+40.))O18.O17.R?.R>.R=.(19.&40.O7.)(19.&40.R11.)R<.R;.(19.&40.O4.)R:.R9.R8.R7.R6.(19.&40.O5.)(19.&40.O6.)R5.(19.&40.O4.)(19.&40.(1:.O6.+:.))O?.O>.O=.O<.O;.R4.R3.R2.R1.)O:.(19.&40.+1?=80.)O9.(1;.(2.&40.))R12.(1<.$>.))))))))))))))))))))(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(5.(1=.O4.R?.)(16.$0.R11.(17.(18.O1:.O19.O18.O17.R>.R=.R<.O16.O15.(19.&40.$1>.)R;.R:.R9.R8.R7.R6.R5.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R4.R3.R2.R1.)O:.(1?.O1:.)O9.(1;.(2.&40.))R10.(1<.$>.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Section Front.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (X Aa Ba pA pB nA nB lo : Z) (sAw sBw padA padB : word) (zs : list word).
  Hypothesis CA : rw_cells psegs m Aa [C8 (Z_to_bv 64 pA); C2 sAw; C2 (Z_to_bv 64 nA); C4 padA].
  Hypothesis CB : rw_cells psegs m Ba [C8 (Z_to_bv 64 pB); C2 sBw; C2 (Z_to_bv 64 nB); C4 padB].
  Hypothesis BV : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "P,(15.+1.VnB,)(5.(20.$>.Vm,VpB,(21.Vzs,))(5.(1=.=VpB,)(5.(16.$4.(22.VpB,+4.)=)(14.(15.(1:.VpB,(23.+4.VnB,))Vlo,)(15.(;.&40.Vsp,)VpB,)))))")
(* [comment removed for export] *).
  Hypothesis LENB : Z.of_nat (length zs) = nB.
  Hypothesis NRA : 0 <= nA <= 10000.
  Hypothesis NRB : 0 <= nB <= 10000.
  Hypothesis AB : 0 < Aa /\ Aa + 16 <= 2^64.
  Hypothesis BB : 0 < Ba /\ Ba + 16 <= 2^64.
  Hypothesis AS : Aa + 16 <= lo \/ bv_unsigned sp <= Aa.
  Hypothesis BS : Ba + 16 <= lo \/ bv_unsigned sp <= Ba.
  Hypothesis ST : stk psegs m lo (bv_unsigned sp).
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis MI : mem_inv psegs m.

  Let FQ := sub_front_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m X Aa Ba nA nB lo zs.

  (* [comment removed for export] *)
  #[using="pB BV NRA NRB SLO LO0"] Lemma front_tail : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Pmz,P,(2.&40.)(3.(2.&8.))Pn,$4.Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(6.(7.(8.$4.$4.)(9.$4.$4.(:.(;.&40.Vsp,)+40.)(;.&40.Vsp,))(<.(8.$4.$4.)))Vm,R11.)P,(=.$>.Vm,R12.)P,(?.$>.R13.)P,(10.$>.R14.(:.(;.&40.Vsp,)+40.)(11.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,))P,(12.$>.R15.Vlo,(:.(;.&40.Vsp,)+40.))P,(10.$>.R16.VAa,(7.$24.(25.(19.&40.VpA,))(7.$24.(26.VsAw,)(7.$24.(26.(19.&40.VnA,))(7.$24.(27.VpadA,)(<.$24.))))))P,(13.Vzs,VnB,R16.)(28.$>.VFQ,(17.(18.Vra,(19.&40.(:.(;.&40.Vsp,)+40.))Vgp,Vtp,R16.R15.R14.(19.&40.VX,)(19.&40.R17.)R13.R12.R11.R10.R?.R>.R=.R<.(19.&40.VBa,)(19.&40.VAa,)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(19.&40.+1?=70.)Vfc,(1;.(2.&40.))R18.(1<.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MIz FRz STz CAz SB. dpose SB as (SB1 & SB2 & SB3).
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    zstep. rewrite zx16_small by (clear - NRA; lia). zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. unfold sub_frame in FRz.
      call sub_epilogue; [exact FRz| exact MIz| clear - SLO LO0; lia|].
      apply evt_done. unfold FQ, sub_front_post. dexists mz, n.
      split; [exact MU|]. split; [exact WM|]. split; [exact MIz|]. split; [exact FRz|]. split; [exact STz|]. split; [exact SB|].
      right. deexists 14. split; [exact K0| reflexivity].
    - zstep. zstep.
      apply evt_done. unfold FQ, sub_front_post. dexists mz, n.
      split; [exact MU|]. split; [exact WM|]. split; [exact MIz|]. split; [exact FRz|]. split; [exact STz|]. split; [exact SB|].
      left. deexists 16. split; [clear - K0; lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  #[using="BV LENB NRA NRB SLO LO0"] Lemma front_loop : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Pmz,P,(2.&40.)(3.(2.&8.))Pk,$29.Pr,$4.Pw9,(2.&40.)Pw10,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(6.(7.(8.$4.$4.)(9.$4.$4.(:.(;.&40.Vsp,)+40.)(;.&40.Vsp,))(<.(8.$4.$4.)))Vm,R13.)P,(=.$>.Vm,R14.)P,(?.$>.R15.)P,(10.$>.R16.(:.(;.&40.Vsp,)+40.)(11.Vra,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,))P,(12.$>.R17.Vlo,(:.(;.&40.Vsp,)+40.))P,(10.$>.R18.VAa,(7.$24.(25.(19.&40.VpA,))(7.$24.(26.VsAw,)(7.$24.(26.(19.&40.VnA,))(7.$24.(27.VpadA,)(<.$24.))))))P,(20.$>.R19.VpB,(21.Vzs,))P,(16.$29.(2:.R18.)R19.)P,(5.(15.+1.R19.)(15.R19.VnB,))P,(16.$4.(2;.Vzs,VnB,)(2;.Vzs,R1:.))P,(16.(2.&40.)R1:.(19.&40.R1;.))P,(16.(2.&40.)R1:.(19.&40.(:.(1:.VpB,(23.+4.R1<.))+4.)))(28.$>.VFQ,(17.(18.Vra,(19.&40.(:.(;.&40.Vsp,)+40.))Vgp,Vtp,R1:.R19.R18.(19.&40.VX,)R1<.R1;.R17.R16.R15.R14.R13.R12.R11.(19.&40.VBa,)(19.&40.VAa,)Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(19.&40.+1?=4<.)Vfc,(1;.(2.&40.))R1?.(1<.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros mz k. induction k as [|k IH]; intros r w9 w10 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MU WM MIz FRz STz CAz BZ Hk Hr INV -> ->; [exfalso; clear - Hk Hr; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ CAz) as ABND. cbn [cells_size csize Nat.add] in ABND.
    destruct (nth_error zs (Z.to_nat (r - 1))) as [wz|] eqn:NZ; [| apply nth_error_None in NZ; exfalso; clear - NZ Hr LENB; lia].
    pose proof (u32ro_read psegs mz pB zs (r - 1) wz _ BZ NZ ltac:(clear - Hr; lia) eq_refl) as RDZ.
    zstep. clear RDZ. pose proof (limb32_of_read zs r wz NZ) as LZr.
    pose proof (Z.mod_pos_bound (bv_unsigned wz) (2^32) ltac:(clear; lia)) as Bz.
    zstep. if_cases K1; zify_cond K1; rewrite ?bv_unsigned_sx32 in K1.
    - (* [comment removed for export] *)
      assert (NZL : limb32 zs (Z.to_nat (r - 1)) <> 0) by (rewrite LZr; intros E; apply K1; rewrite E; reflexivity).
      eapply front_tail; try eassumption. split; [clear - Hr; lia|]. split; [exact INV|]. right. apply lval_top_nonzero; [clear - Hr; lia| exact NZL].
    - apply (proj1 (sxz_zero_iff _ Bz)) in K1.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + eapply (IH (r - 1)); try eassumption; [clear - Hk; lia| clear - K2 Hr; lia| rewrite INV; apply lval_drop_zero; [clear - Hr; lia| rewrite LZr; exact K1]| f_equal; clear; lia| f_equal; clear; lia].
      + (* [comment removed for export] *)
        replace (Z_to_bv 64 (r + -1)) with (Z_to_bv 64 0) by (f_equal; clear - K2 Hr; lia).
        zstep. rewrite zx16_small by (clear - NRA; lia). zstep. zstep. zstep.
        apply evt_done. unfold FQ, sub_front_post. dexists mz, 0.
        split; [exact MU|]. split; [exact WM|]. split; [exact MIz|]. split; [exact FRz|]. split; [exact STz|].
        split. { split; [clear - NRB; lia|]. split; [| left; reflexivity]. rewrite INV, (lval_drop_zero zs r) by (first [clear - Hr; lia | rewrite LZr; exact K1]). replace (r - 1) with 0 by (clear - K2 Hr; lia). reflexivity. }
        left. deexists 16. split; [clear - NRA; lia| reflexivity].
  Qed.

  #[using="pA pB sAw sBw padA padB CA CB BV LENB NRA NRB AS BS ST SLO LO0 MI"] Lemma sub_front_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)(28.$>.VFQ,(17.(18.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(19.&40.VX,)(19.&40.VAa,)(19.&40.VBa,)R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(19.&40.+1?=04.)Vfc,(1;.(2.&40.))Vm,(1<.$>.)))")
(* [comment removed for export] *).
  Proof.
    intros. pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (rw_cells_bound _ _ _ _ CB) as BBND. cbn [cells_size csize Nat.add] in BBND.
    destruct (Z.le_gt_cases 1 nB) as [NB1|NB1]; [ddestruct (BV NB1) as (BZ & PB0 & PBAL & PBS)|].
    all: carve_frame 64%nat ST.
    all: do 9 zstep.
    all: zstep; zstep; zstep; rewrite zx16_small by (clear - NRB; lia); zstep; zstep; if_cases K0; zify_cond K0.
    all: replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in * by (clear; lia).
    - (* [comment removed for export] *) exfalso. clear - K0 NB1. lia.
    - (* [comment removed for export] *) zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4.
      eapply (front_loop _ (Z.to_nat nB) nB); try eassumption; try reflexivity; [clear - NB1; lia| f_equal; clear; lia].
    - (* [comment removed for export] *) eapply (front_tail _ nB); try eassumption. split; [clear - NRB; lia|]. split; [reflexivity| left; exact K0].
    - exfalso. clear - K0 NB1 NRB. lia.
  Qed.
End Front.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma P_layout_roimg : ltac2:(CDefT.buildp (gd_tbl_P_mpi_sub_abs ()) "Psp0,(2.&40.)Pa,$4.P,(16.$2<.(2=.$>.(2>.R1.))$2?.)P,(5.(15.=R2.)(1=.R2.(30.+2.+40.)))(5.(15.(31.(32.R4.))R3.)(1=.R3.(33.(32.R4.))))")
(* [comment removed for export] *).
Proof.
  intros sp0 a H Ha. unfold ro_addr in H. unfold wa in H. rewrite unsigned_lit in H by lia.
  cbn -[Z.leb Z.add andb negb] in H.
  repeat match type of H with context [if ?c then _ else _] => destruct c eqn:?E end;
    rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff, ?Z.leb_le, ?Z.leb_gt in *; cbn in *; try discriminate; try lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Spec.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HFREE : hl_free L = P_FREE.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP psegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis ROIMG : forall a, ro_addr psegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem P_mpi_sub_abs_spec_o : forall MSF, MSF = P_MEMSET_FUNC -> mpi_sub_abs_stmt' psegs L HI P_MPI_SUB_ABS MSF.
  Proof.
    intros MSF MSFE. unfold mpi_sub_abs_stmt', mpi_binop_stmt', P_MPI_SUB_ABS. intros until lo.
    intros HH MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST SLO ACL HTOP SPA DHI TP MI SOK CA -> -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct (opnd_raw _ _ _ _ _ MA ltac:(intros EO; pose proof (opnd_view _ _ _ _ _ MA) as [(_ & _ & _ & _ & _ & OW) _]; rewrite EO in OW; ddestruct OW as (_ & IN & _);
               pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CA0 & ABY & LENA & NRA & SGA & ABA & PBA).
    destruct (opnd_raw _ _ _ _ _ MB ltac:(intros EO; pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]; rewrite EO in OW; ddestruct OW as (_ & IN & _);
               pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (R0 & _); exact R0)) as (CB0 & BBY & LENB & NRB & SGB & ABB & PBB).
    pose proof (opnd_view _ _ _ _ _ MA) as [(_ & _ & A0 & _) _]. pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & B0 & _) _].
    dpose OA as (OA1 & OA2 & OA3 & OA4 & OA5). dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    dpose XW as (XCW & XD & XP).
    pose proof (client_wrange_where L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    eapply aevtM_cut_evt; [exact MK| |].
    { eapply (sub_front_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m (md_addr dX) (md_addr dA) (md_addr dB)
                (md_p dA) (md_p dB) (md_n dA) (md_n dB) lo (Z_to_bv 64 (md_sg dA)) (Z_to_bv 64 (md_sg dB)) (md_pad dA) (md_pad dB) (md_limbs dB));
        try eassumption.
      - intros H1. split; [exact BBY|]. destruct PBB as [Z0|[P0 PAL]]; [exfalso; clear - Z0 H1; lia|]. split; [exact P0|]. split; [exact PAL|].
        apply OB5. pose proof (opnd_view _ _ _ _ _ MB) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); [destruct OW; exfalso; clear - H1 H0; lia| discriminate| discriminate].
      - clear - SLO HLS. lia.
      - clear - ACL ACP. lia. }
    cbv beta. intros ms' FQ. unfold sub_front_post in FQ.
    ddestruct FQ as (m1 & n & MU1 & WM1 & MI1 & FR1 & ST1 & SB & CASES).
    (* [comment removed for export] *)
    assert (HH1 : HEAP psegs L HI h LB m1 mo).
    { eapply (Asn1AuxA.HEAP_munch psegs L HI) with (SP := lo); [exact HH| exact ACL| exact MU1| exact WM1|].
      intros a Ha NO. cbn in NO. left. clear - NO HTOP SLO HLS. lia. }
    assert (SOK1 : statics_ok psegs L m1).
    { eapply statics_ok_munch; [exact SOK| exact MU1|]. intros a Hd NW. cbn. split; [clear - Hd DHI ACL SLO HLS; lia| exact I]. }
    assert (HPX1 : heap_presx psegs L LB (bv_unsigned sp) (mpd_ivs dX) m m1).
    { eapply heap_presx_of_munch; [exact MU1| exact WM1|]. intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [C|[[C1 C2]|([q k] & Hq & R)]]; [clear - C; lia| clear - C1 DHI ACL SLO HLS; lia|]. cbn in R.
      pose proof (proj1 (Forall_forall _ _) HBR _ Hq) as (_ & _ & _ & R3 & _). cbn in R3. clear - R R3 ACL SLO HLS. lia. }
    assert (OPM : forall d, mpd_at psegs m LB d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> mpd_at psegs m1 LB d).
    { intros d Md D1 D2. eapply mpd_at_munch_any; [exact Md| exact MU1| exact WM1| cbn; split; [clear - D1 SLO HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO HLS; lia| exact I]. }
    pose proof (OPM _ MX XS XLS) as MX1.
    assert (OPM' : forall d, opnd_at psegs m LB (bv_unsigned sp) d -> (md_addr d + 16 <= lo \/ bv_unsigned sp <= md_addr d) ->
                  (md_own d <> LNull -> md_p d + 4 * md_n d <= lo \/ bv_unsigned sp <= md_p d) -> opnd_at psegs m1 LB (bv_unsigned sp) d).
    { intros d Md D1 D2. eapply opnd_at_munch_any; [exact Md| exact MU1| exact WM1| cbn; split; [clear - D1 SLO HLS; lia| exact I]|].
      intros ON. cbn. split; [destruct (D2 ON); clear - H SLO HLS; lia| exact I]. }
    pose proof (OPM' _ MA OA4 OA5) as MA1. pose proof (OPM' _ MB OB4 OB5) as MB1.
    destruct CASES as [(raj & t0' & t1' & t2' & a0' & a1' & a3' & a4' & a5' & a6' & a7' & s4j & t3' & t4' & t5' & t6' & NLE & ->)
                      |(t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & NGT & ->)].
    - (* [comment removed for export] *)
      eapply (sub_J1_proof L HI); try eassumption.
      intros n'. eapply (sub_C1_proof L HI); eassumption.
    - (* [comment removed for export] *)
      apply aevtM_done. unfold mpi_binop_post. deexists 14. dexists m1, mo, h, LB, dX, MBEDTLS_ERR_MPI_NEGATIVE_VALUE.
      split; [reflexivity|]. split; [exact MI1|].
      split; [unfold sub_frame in FR1; release_frame FR1 ST1 (bv_unsigned sp); exact ST1|].
      split; [apply mo_frame_refl|]. split; [reflexivity|]. split; [exact HH1|]. split; [exact MX1|].
      split; [apply mpd_out_refl; exact NST|]. split; [exact HPX1|]. split; [exact SOK1|].
      split; [| split; [reflexivity| split; [reflexivity| split; [intros b Hb; left; exact Hb| reflexivity]]]].
      right; right. split; [reflexivity|].
      dpose SB as (SB1 & SB2 & SB3). destruct SB3 as [Z0|LOW]; [exfalso; clear - Z0 NGT NRA; lia|].
      rewrite !mpd_abs_lval by assumption. rewrite SB2.
      pose proof (lval_range (md_limbs dA) (md_n dA) ltac:(clear - NRA; lia)) as RA. pose proof (pow32_le (md_n dA) (n - 1) ltac:(clear - NRA NGT; lia)) as PW.
      clear - RA PW LOW. lia.
  Qed.

  #[using="HFREE HCALLOC HLS SW DIMG HND ROIMG"] Theorem P_mpi_sub_abs_spec : forall MSF, MSF = P_MEMSET_FUNC -> mpi_sub_abs_stmt psegs L HI P_MPI_SUB_ABS MSF.
  Proof. intros MSF E. apply mpi_binop_stmt_of_prime. exact (P_mpi_sub_abs_spec_o MSF E). Qed.
End Spec.
