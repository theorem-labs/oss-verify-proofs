(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_memcpy_base U_memcpy_al U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_memcpy_mis () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.at_"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.U.U_memcpy_base.memk"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.keeps"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.land"].


Section MIS.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  #[local] Notation MK := (memk mem0 dst bs).
  #[local] Notation SB := (sb_ bs).
  #[local] Notation B := (b_ bs).
  Let Hn0 : (0 <= n < 2 ^ 64)%Z := Hn _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := Hnws _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac mlw F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lw _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (MK ?a) _) _ =>
                     first [constr_eq a kk | replace (MK a) with (MK kk) by (f_equal; lia)] end.
  Ltac msw F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sw _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].
  Ltac msb F D kk valtac :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | valtac | lia | lia]
      | step_simpl].

  (* [comment removed for export] *)
  Ltac cond :=
    rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; rewrite ?u_andi by lia; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge];
    rewrite ?land_3 by lia; lia.
  Ltac mk_eq := match goal with |- context [mkst _ _ (MK ?a) _] =>
                  match goal with |- msteps _ _ (mkst _ _ (MK ?b) _) => replace (MK a) with (MK b) by (f_equal; lia) end end.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity; try solve_keeps.
  Ltac sbp := apply sb_val_plain.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma b4_blk : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pa2,(1.&40.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))R4.)P,(8.=R6.)P,(8.(9.R7.+4.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+46==4.$6.)(10.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+46>00.$6.)(10.Vmem0,Vdst,Vbs,(9.R9.+4.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R9.+4.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R9.+4.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))R8.)(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_43688 D_43688 k. mlbu F_4368c D_4368c (k+1)%Z. mlbu F_43690 D_43690 (k+2)%Z. mlbu F_43694 D_43694 (k+3)%Z.
      stepn F_43698 D_43698.                            (* [comment removed for export] *)
      stepn F_4369c D_4369c.                            (* [comment removed for export] *)
      msb F_436a0 D_436a0 k ltac:(sbp). msb F_436a4 D_436a4 (k+1)%Z ltac:(sbp).
      msb F_436a8 D_436a8 (k+2)%Z ltac:(sbp). msb F_436ac D_436ac (k+3)%Z ltac:(sbp).
      stepn F_436b0 D_436b0.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b8_blk : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pa2,(1.&40.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))R4.)P,(8.=R6.)P,(8.(9.R7.+8.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+46=80.$6.)(10.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+46=<<.$6.)(10.Vmem0,Vdst,Vbs,(9.R9.+8.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R9.+8.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R9.+8.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))R8.)(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_43634 D_43634 k. mlbu F_43638 D_43638 (k+1)%Z. mlbu F_4363c D_4363c (k+2)%Z. mlbu F_43640 D_43640 (k+3)%Z.
      mlbu F_43644 D_43644 (k+4)%Z. mlbu F_43648 D_43648 (k+5)%Z. mlbu F_4364c D_4364c (k+6)%Z. mlbu F_43650 D_43650 (k+7)%Z.
      stepn F_43654 D_43654.                            (* [comment removed for export] *)
      msb F_43658 D_43658 k ltac:(sbp). msb F_4365c D_4365c (k+1)%Z ltac:(sbp).
      msb F_43660 D_43660 (k+2)%Z ltac:(sbp). msb F_43664 D_43664 (k+3)%Z ltac:(sbp).
      stepn F_43668 D_43668.                            (* [comment removed for export] *)
      msb F_4366c D_4366c (k+4)%Z ltac:(sbp). msb F_43670 D_43670 (k+5)%Z ltac:(sbp).
      msb F_43674 D_43674 (k+6)%Z ltac:(sbp). msb F_43678 D_43678 (k+7)%Z ltac:(sbp).
      stepn F_4367c D_4367c.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b16_blk : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pa2,(1.&40.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))R4.)P,(8.=R6.)P,(8.(9.R7.+10.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+46<><.$6.)(10.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+46=78.$6.)(10.Vmem0,Vdst,Vbs,(9.R9.+10.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R9.+10.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R9.+10.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))R8.)(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_435a0 D_435a0 k. mlbu F_435a4 D_435a4 (k+1)%Z. mlbu F_435a8 D_435a8 (k+2)%Z. mlbu F_435ac D_435ac (k+3)%Z.
      mlbu F_435b0 D_435b0 (k+4)%Z. mlbu F_435b4 D_435b4 (k+5)%Z. mlbu F_435b8 D_435b8 (k+6)%Z. mlbu F_435bc D_435bc (k+7)%Z.
      msb F_435c0 D_435c0 k ltac:(sbp). msb F_435c4 D_435c4 (k+1)%Z ltac:(sbp).
      msb F_435c8 D_435c8 (k+2)%Z ltac:(sbp). msb F_435cc D_435cc (k+3)%Z ltac:(sbp).
      mlbu F_435d0 D_435d0 (k+8)%Z. mlbu F_435d4 D_435d4 (k+9)%Z. mlbu F_435d8 D_435d8 (k+10)%Z. mlbu F_435dc D_435dc (k+11)%Z.
      msb F_435e0 D_435e0 (k+4)%Z ltac:(sbp). msb F_435e4 D_435e4 (k+5)%Z ltac:(sbp).
      msb F_435e8 D_435e8 (k+6)%Z ltac:(sbp). msb F_435ec D_435ec (k+7)%Z ltac:(sbp).
      mlbu F_435f0 D_435f0 (k+12)%Z. mlbu F_435f4 D_435f4 (k+13)%Z. mlbu F_435f8 D_435f8 (k+14)%Z. mlbu F_435fc D_435fc (k+15)%Z.
      stepn F_43600 D_43600.                            (* [comment removed for export] *)
      msb F_43604 D_43604 (k+8)%Z ltac:(sbp). msb F_43608 D_43608 (k+9)%Z ltac:(sbp).
      msb F_4360c D_4360c (k+10)%Z ltac:(sbp). msb F_43610 D_43610 (k+11)%Z ltac:(sbp).
      stepn F_43614 D_43614.                            (* [comment removed for export] *)
      msb F_43618 D_43618 (k+12)%Z ltac:(sbp). msb F_4361c D_4361c (k+13)%Z ltac:(sbp).
      msb F_43620 D_43620 (k+14)%Z ltac:(sbp). msb F_43624 D_43624 (k+15)%Z ltac:(sbp).
      stepn F_43628 D_43628.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma t4_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+4.)=)(;.(3.$2.(16.R7.+4.)+4.)(8.(9.R8.+4.)Vn,)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+46::8.$6.)(10.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+46>00.$6.)(10.Vmem0,Vdst,Vbs,(9.R:.(16.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_4335c D_4335c.                          (* [comment removed for export] *)
        stepb_ft F_43360 D_43360 ltac:(cond).           (* [comment removed for export] *)
        stepn F_43364 D_43364.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46dd4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_4335c D_4335c.
          stepb_tk F_43360 D_43360 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b8_tail : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+4.)=)(;.(3.$2.(16.R7.+4.)+4.)(8.(9.R8.+4.)Vn,)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+46=<<.$6.)(10.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+46>00.$6.)(10.Vmem0,Vdst,Vbs,(9.R:.(16.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_43680 D_43680.                          (* [comment removed for export] *)
        stepb_tk F_43684 D_43684 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46dd4 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_43680 D_43680.
          stepb_ft F_43684 D_43684 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma t8_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+8.)=)(3.$2.(16.R7.+8.)+8.))P,(15.(3.$2.(16.R8.+4.)=)(3.$2.(16.R8.+4.)+4.))P,(8.(9.(9.R:.(16.R9.+8.))(16.R9.+4.))Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R>.(5.&40.+46::0.$6.)(10.Vmem0,Vdst,Vbs,R<.)Vrom,)(>.$?.R1.(5.&40.+46>00.$6.)(10.Vmem0,Vdst,Vbs,(9.(9.R<.(16.R;.+8.))(16.R;.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R=.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R;.))(11.R>.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46aa8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_43354 D_43354.                        (* [comment removed for export] *)
          stepb_ft F_43358 D_43358 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        ddestruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46d80 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_43354 D_43354.
          stepb_tk F_43358 D_43358 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x46dcc : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2 dd_H; ddestruct dd_H as (S1 & S11 & S13 & S12 & K2)).
          ddestruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma b16_tail : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+8.)=)(3.$2.(16.R7.+8.)+8.))P,(15.(3.$2.(16.R8.+4.)=)(3.$2.(16.R8.+4.)+4.))P,(8.(9.(9.R:.(16.R9.+8.))(16.R9.+4.))Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R>.(5.&40.+46=78.$6.)(10.Vmem0,Vdst,Vbs,R<.)Vrom,)(>.$?.R1.(5.&40.+46>00.$6.)(10.Vmem0,Vdst,Vbs,(9.(9.R<.(16.R;.+8.))(16.R;.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R=.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R;.))(11.R>.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46aa8 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_4362c D_4362c.                        (* [comment removed for export] *)
          stepb_tk F_43630 D_43630 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        ddestruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46d80 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_4362c D_4362c.
          stepb_ft F_43630 D_43630 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x46dcc : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2 dd_H; ddestruct dd_H as (S1 & S11 & S13 & S12 & K2)).
          ddestruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma t16_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_mis ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.+20.))P,(8.=R7.)P,(8.(9.(9.(9.R8.(16.R7.+10.))(16.R7.+8.))(16.R7.+4.))Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+46:98.$6.)(10.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+46>00.$6.)(10.Vmem0,Vdst,Vbs,(9.(9.(9.R:.(16.R9.+10.))(16.R9.+8.))(16.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.(9.(9.R:.(16.R9.+10.))(16.R9.+8.))(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.(9.(9.R:.(16.R9.+10.))(16.R9.+8.))(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    ddestruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46aa0 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_4334c D_4334c.                        (* [comment removed for export] *)
          stepb_ft F_43350 D_43350 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        ddestruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46cec : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_4334c D_4334c.
          stepb_tk F_43350 D_43350 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x46d78 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2 dd_H; ddestruct dd_H as (S1 & S11 & S13 & S12 & K2)).
          ddestruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
