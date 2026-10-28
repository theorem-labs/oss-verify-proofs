(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim
  RefMemcpyLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMemcpyBase AsanMemcpyAL Asan_code_memcpy.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMemcpyMIS () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMemcpyBase.memk"; "RocqVerifyHarness.AgentSubmission.ABoot.RefMemcpyLib.keeps"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.land"].


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
  #[using="HOK Hn0"] Lemma b4_blk : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pa2,(1.&40.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))R4.)P,(8.=R6.)P,(8.(9.R7.+4.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+>:=54.$6.)(10.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(10.Vmem0,Vdst,Vbs,(9.R9.+4.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R9.+4.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R9.+4.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))R8.)(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk4. eexists. split.
    - mlbu F_e79a4 D_e79a4 k. mlbu F_e79a8 D_e79a8 (k+1)%Z. mlbu F_e79ac D_e79ac (k+2)%Z. mlbu F_e79b0 D_e79b0 (k+3)%Z.
      stepn F_e79b4 D_e79b4.                            (* [comment removed for export] *)
      stepn F_e79b8 D_e79b8.                            (* [comment removed for export] *)
      msb F_e79bc D_e79bc k ltac:(sbp). msb F_e79c0 D_e79c0 (k+1)%Z ltac:(sbp).
      msb F_e79c4 D_e79c4 (k+2)%Z ltac:(sbp). msb F_e79c8 D_e79c8 (k+3)%Z ltac:(sbp).
      stepn F_e79cc D_e79cc.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma b8_blk : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pa2,(1.&40.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))R4.)P,(8.=R6.)P,(8.(9.R7.+8.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+>:=00.$6.)(10.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+>:=4<.$6.)(10.Vmem0,Vdst,Vbs,(9.R9.+8.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R9.+8.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R9.+8.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))R8.)(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk8. eexists. split.
    - mlbu F_e7950 D_e7950 k. mlbu F_e7954 D_e7954 (k+1)%Z. mlbu F_e7958 D_e7958 (k+2)%Z. mlbu F_e795c D_e795c (k+3)%Z.
      mlbu F_e7960 D_e7960 (k+4)%Z. mlbu F_e7964 D_e7964 (k+5)%Z. mlbu F_e7968 D_e7968 (k+6)%Z. mlbu F_e796c D_e796c (k+7)%Z.
      stepn F_e7970 D_e7970.                            (* [comment removed for export] *)
      msb F_e7974 D_e7974 k ltac:(sbp). msb F_e7978 D_e7978 (k+1)%Z ltac:(sbp).
      msb F_e797c D_e797c (k+2)%Z ltac:(sbp). msb F_e7980 D_e7980 (k+3)%Z ltac:(sbp).
      stepn F_e7984 D_e7984.                            (* [comment removed for export] *)
      msb F_e7988 D_e7988 (k+4)%Z ltac:(sbp). msb F_e798c D_e798c (k+5)%Z ltac:(sbp).
      msb F_e7990 D_e7990 (k+6)%Z ltac:(sbp). msb F_e7994 D_e7994 (k+7)%Z ltac:(sbp).
      stepn F_e7998 D_e7998.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma b16_blk : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pa2,(1.&40.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))R4.)P,(8.=R6.)P,(8.(9.R7.+10.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+>:<6<.$6.)(10.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+>:<?8.$6.)(10.Vmem0,Vdst,Vbs,(9.R9.+10.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R9.+10.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R9.+10.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))R8.)(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k a2 H1 H11 H13 H12 Hk Hk16. eexists. split.
    - mlbu F_e78bc D_e78bc k. mlbu F_e78c0 D_e78c0 (k+1)%Z. mlbu F_e78c4 D_e78c4 (k+2)%Z. mlbu F_e78c8 D_e78c8 (k+3)%Z.
      mlbu F_e78cc D_e78cc (k+4)%Z. mlbu F_e78d0 D_e78d0 (k+5)%Z. mlbu F_e78d4 D_e78d4 (k+6)%Z. mlbu F_e78d8 D_e78d8 (k+7)%Z.
      msb F_e78dc D_e78dc k ltac:(sbp). msb F_e78e0 D_e78e0 (k+1)%Z ltac:(sbp).
      msb F_e78e4 D_e78e4 (k+2)%Z ltac:(sbp). msb F_e78e8 D_e78e8 (k+3)%Z ltac:(sbp).
      mlbu F_e78ec D_e78ec (k+8)%Z. mlbu F_e78f0 D_e78f0 (k+9)%Z. mlbu F_e78f4 D_e78f4 (k+10)%Z. mlbu F_e78f8 D_e78f8 (k+11)%Z.
      msb F_e78fc D_e78fc (k+4)%Z ltac:(sbp). msb F_e7900 D_e7900 (k+5)%Z ltac:(sbp).
      msb F_e7904 D_e7904 (k+6)%Z ltac:(sbp). msb F_e7908 D_e7908 (k+7)%Z ltac:(sbp).
      mlbu F_e790c D_e790c (k+12)%Z. mlbu F_e7910 D_e7910 (k+13)%Z. mlbu F_e7914 D_e7914 (k+14)%Z. mlbu F_e7918 D_e7918 (k+15)%Z.
      stepn F_e791c D_e791c.                            (* [comment removed for export] *)
      msb F_e7920 D_e7920 (k+8)%Z ltac:(sbp). msb F_e7924 D_e7924 (k+9)%Z ltac:(sbp).
      msb F_e7928 D_e7928 (k+10)%Z ltac:(sbp). msb F_e792c D_e792c (k+11)%Z ltac:(sbp).
      stepn F_e7930 D_e7930.                            (* [comment removed for export] *)
      msb F_e7934 D_e7934 (k+12)%Z ltac:(sbp). msb F_e7938 D_e7938 (k+13)%Z ltac:(sbp).
      msb F_e793c D_e793c (k+14)%Z ltac:(sbp). msb F_e7940 D_e7940 (k+15)%Z ltac:(sbp).
      stepn F_e7944 D_e7944.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma t4_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+4.)=)(;.(3.$2.(16.R7.+4.)+4.)(8.(9.R8.+4.)Vn,)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+>::28.$6.)(10.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(10.Vmem0,Vdst,Vbs,(9.R:.(16.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_e7678 D_e7678.                          (* [comment removed for export] *)
        stepb_ft F_e767c D_e767c ltac:(cond).           (* [comment removed for export] *)
        stepn F_e7680 D_e7680.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead54 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7678 D_e7678.
          stepb_tk F_e767c D_e767c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma b8_tail : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+4.)=)(;.(3.$2.(16.R7.+4.)+4.)(8.(9.R8.+4.)Vn,)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+>:=4<.$6.)(10.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(10.Vmem0,Vdst,Vbs,(9.R:.(16.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.R:.(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL|[HL H4]].
    - eexists. split.
      + stepn F_e799c D_e799c.                          (* [comment removed for export] *)
        stepb_tk F_e79a0 D_e79a0 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead54 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e799c D_e799c.
          stepb_ft F_e79a0 D_e79a0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (b4_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma t8_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+8.)=)(3.$2.(16.R7.+8.)+8.))P,(15.(3.$2.(16.R8.+4.)=)(3.$2.(16.R8.+4.)+4.))P,(8.(9.(9.R:.(16.R9.+8.))(16.R9.+4.))Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R>.(5.&40.+>::20.$6.)(10.Vmem0,Vdst,Vbs,R<.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(10.Vmem0,Vdst,Vbs,(9.(9.R<.(16.R;.+8.))(16.R;.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R=.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R;.))(11.R>.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaa28 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7670 D_e7670.                        (* [comment removed for export] *)
          stepb_ft F_e7674 D_e7674 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead00 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7670 D_e7670.
          stepb_tk F_e7674 D_e7674 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead4c : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. replace (k + 8 + Z.land m 4)%Z with (k + 8 + Z.land m 4)%Z by lia.
          split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma b16_tail : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.(14.+2.+40.)))P,(8.=R7.)P,(15.(3.$2.(16.R7.+8.)=)(3.$2.(16.R7.+8.)+8.))P,(15.(3.$2.(16.R8.+4.)=)(3.$2.(16.R8.+4.)+4.))P,(8.(9.(9.R:.(16.R9.+8.))(16.R9.+4.))Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R>.(5.&40.+>:<?8.$6.)(10.Vmem0,Vdst,Vbs,R<.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(10.Vmem0,Vdst,Vbs,(9.(9.R<.(16.R;.+8.))(16.R;.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R=.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.(9.R<.(16.R;.+8.))(16.R;.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R;.))(11.R>.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk HL8 HL4 Hkn.
    assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    destruct HL8 as [HL8|HL8].
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaa28 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7948 D_e7948.                        (* [comment removed for export] *)
          stepb_tk F_e794c D_e794c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t4_run r1 ret k m R1 R11 R13 R12 Hm Hk ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL8, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead00 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7948 D_e7948.
          stepb_ft F_e794c D_e794c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead4c : word) (MK (k + 8)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 8) /\ getr r 13 = at_ dst (k + 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b8_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b8_tail r2 ret (k + 8)%Z m S1 S11 S13 S12 Hm ltac:(lia) ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL8. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma t16_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyMIS ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(7.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(12.&40.R4.))P,(;.(8.=R5.)(13.R5.+20.))P,(8.=R7.)P,(8.(9.(9.(9.R8.(16.R7.+10.))(16.R7.+8.))(16.R7.+4.))Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+>::18.$6.)(10.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(10.Vmem0,Vdst,Vbs,(9.(9.(9.R:.(16.R9.+10.))(16.R9.+8.))(16.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(9.(9.(9.R:.(16.R9.+10.))(16.R9.+8.))(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(9.(9.(9.R:.(16.R9.+10.))(16.R9.+8.))(16.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(12.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk Hkn.
    destruct (bits_lt32 m Hm) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land m 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land m 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land m 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaa20 : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7668 D_e7668.                        (* [comment removed for export] *)
          stepb_ft F_e766c D_e766c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run r1 ret k m R1 R11 R13 R12 ltac:(lia) Hk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eac6c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7668 D_e7668.
          stepb_tk F_e766c D_e766c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eacf8 : word) (MK (k + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
        * destruct (b16_blk r1 ret k _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail r2 ret (k + 16)%Z m S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

End MIS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
