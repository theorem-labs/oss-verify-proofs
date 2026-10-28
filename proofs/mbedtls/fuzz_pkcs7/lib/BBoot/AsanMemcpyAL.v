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
  RefMemcpyLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMemcpyBase Asan_code_memcpy.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMemcpyAL () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "RocqVerifyHarness.AgentSubmission.ABoot.RefMemcpyLib.keeps"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMemcpyBase.memk"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"].


Section AL.
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="mem0 n bs HOK Hn0"] Lemma al_entry : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pmem,P,(1.&40.)(2.(1.&8.))P,(3.(1.&40.)(4.R2.(5.&5.+:.$6.))Vdst,)P,(3.(1.&40.)(4.R3.(5.&5.+;.$6.))Vsrc,)P,(3.$7.(8.(9.&40.Vsrc,)+4.)=)P,(3.$7.(8.(9.&40.Vdst,)+4.)=)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R7.(5.&40.+>:9<0.$6.)R6.Vrom,)(>.$?.R1.(5.&40.+>::>0.$6.)R6.Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(10.Vdst,=))(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(10.Vsrc,=))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(4.R7.(5.&5.+<.$6.)))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))(4.R7.(5.&5.+1.$6.)))(11.R7.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs mem H10 H11 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    eexists. split.
    - stepn F_e7610 D_e7610.                       (* [comment removed for export] *)
      stepb_tk F_e7614 D_e7614                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      stepn F_e7724 D_e7724.                       (* [comment removed for export] *)
      stepn F_e7728 D_e7728.                       (* [comment removed for export] *)
      stepb_ft F_e772c D_e772c                     (* [comment removed for export] *)
        ltac:(rwH; unfold c_eq, bv_eqb; rewrite u_andi by lia; unorm; rewrite land_3 by lia; apply Z.eqb_eq; lia).
      apply mst_refl.
    - repeat split; gres; rwH; rewrite ?at_0; try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma b1_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$7.P,(12.R2.)P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(10.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(10.Vdst,R4.))P,(13.=R5.)P,(3.$7.(14.R6.+1.)Vn,)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R:.(5.&40.+>:=;8.$6.)(15.Vmem0,Vdst,Vbs,R8.)Vrom,)(>.$?.R1.R9.(15.Vmem0,Vdst,Vbs,Vn,)Vrom,))(11.R:.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_e7a08 D_e7a08 k.                      (* [comment removed for export] *)
      msb F_e7a0c D_e7a0c k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_e7a10 D_e7a10 ret ltac:(exact H1).
      apply mst_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma t2_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$7.Pm,$7.P,(12.R3.)P,(3.(1.&40.)(4.R5.(5.&5.+1.$6.))R4.)P,(3.(1.&40.)(4.R6.(5.&5.+;.$6.))(10.Vsrc,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+=.$6.))(10.Vdst,R5.))P,(3.(1.&40.)(4.R8.(5.&5.+<.$6.))(16.&40.R5.))P,(;.(13.=R6.)(17.R6.(18.+2.+40.)))P,(19.(3.$7.(1:.R7.+2.)=)(3.$7.(1:.R7.+2.)+2.))P,(19.(3.$7.(1:.R8.+1.)=)(3.$7.(1:.R8.+1.)+1.))P,(13.=R:.)P,(3.$7.(1;.Vn,R;.)(14.(1:.R:.+2.)(1:.R:.+1.)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R?.(5.&40.+>:=80.$6.)(15.Vmem0,Vdst,Vbs,R=.)Vrom,)(>.$?.R1.R>.(15.Vmem0,Vdst,Vbs,Vn,)Vrom,))(11.R?.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_e79d0 D_e79d0.                          (* [comment removed for export] *)
        stepb_ft F_e79d4 D_e79d4 ltac:(cond).           (* [comment removed for export] *)
        stepn F_e79d8 D_e79d8.                          (* [comment removed for export] *)
        stepb_ft F_e79dc D_e79dc ltac:(cond).           (* [comment removed for export] *)
        stepret F_e79e0 D_e79e0 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eadb8 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_e79d0 D_e79d0.
          stepb_ft F_e79d4 D_e79d4 ltac:(cond).
          stepn F_e79d8 D_e79d8.
          stepb_tk F_e79dc D_e79dc ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_e79d0 D_e79d0.
        stepb_tk F_e79d4 D_e79d4 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_e79e4 D_e79e4 k.                         (* [comment removed for export] *)
        mlbu F_e79e8 D_e79e8 (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_e79ec D_e79ec.                          (* [comment removed for export] *)
        stepn F_e79f0 D_e79f0.                          (* [comment removed for export] *)
        msb F_e79f4 D_e79f4 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb F_e79f8 D_e79f8 (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        stepn F_e79fc D_e79fc.                          (* [comment removed for export] *)
        stepn F_e7a00 D_e7a00.                          (* [comment removed for export] *)
        stepb_tk F_e7a04 D_e7a04 ltac:(cond).           (* [comment removed for export] *)
        stepret F_e79e0 D_e79e0 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eadb8 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_e79d0 D_e79d0.
          stepb_tk F_e79d4 D_e79d4 ltac:(cond).
          mlbu F_e79e4 D_e79e4 k.
          mlbu F_e79e8 D_e79e8 (k + 1)%Z.
          stepn F_e79ec D_e79ec.
          stepn F_e79f0 D_e79f0.
          msb F_e79f4 D_e79f4 k ltac:(apply sb_val_plain).
          msb F_e79f8 D_e79f8 (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_e79fc D_e79fc.
          stepn F_e7a00 D_e7a00.
          stepb_ft F_e7a04 D_e7a04 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. intros r1 (R1 & R11 & R13 & K1).
        destruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma al4_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$7.Pm,$7.P,(3.(1.&40.)(4.R4.(5.&5.+1.$6.))R3.)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))(10.Vsrc,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+=.$6.))(10.Vdst,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+<.$6.))(16.&40.R4.))P,(;.(13.=R5.)(17.R5.(18.+2.+40.)))P,(13.=R7.)P,(19.(3.$7.(1:.R7.+4.)=)(;.(3.$7.(1:.R7.+4.)+4.)(13.(14.R8.+4.)Vn,)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R<.(5.&40.+>:;3<.$6.)(15.Vmem0,Vdst,Vbs,R:.)Vrom,)(>.$?.R1.(5.&40.+>:=80.$6.)(15.Vmem0,Vdst,Vbs,(14.R:.(1:.R9.+4.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(10.Vsrc,(14.R:.(1:.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(10.Vdst,(14.R:.(1:.R9.+4.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(16.&40.R9.))(11.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_e778c D_e778c.                          (* [comment removed for export] *)
        stepb_tk F_e7790 D_e7790 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_e778c D_e778c.
        stepb_ft F_e7790 D_e7790 ltac:(cond).           (* [comment removed for export] *)
        mlw F_e7794 D_e7794 k.                          (* [comment removed for export] *)
        stepn F_e7798 D_e7798.                          (* [comment removed for export] *)
        msw F_e779c D_e779c k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        stepn F_e77a0 D_e77a0.                          (* [comment removed for export] *)
        stepn F_e77a4 D_e77a4.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma al8_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$7.Pm,$7.Pe8,$7.P,(3.(1.&40.)(4.R5.(5.&5.+1.$6.))R4.)P,(3.(1.&40.)(4.R6.(5.&5.+;.$6.))(10.Vsrc,R4.))P,(3.(1.&40.)(4.R7.(5.&5.+=.$6.))(10.Vdst,R5.))P,(3.(1.&40.)(4.R8.(5.&5.+<.$6.))(16.&40.R5.))P,(;.(13.=R6.)(17.R6.(18.+2.+40.)))P,(13.=R8.)P,(19.(;.(17.R8.+8.)(3.$7.R7.=))(;.(13.+8.R8.)(;.(3.$7.R7.+8.)(13.(14.R9.+8.)Vn,))))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R=.(5.&40.+>:;1<.$6.)(15.Vmem0,Vdst,Vbs,R;.)Vrom,)(>.$?.R1.(5.&40.+>:;3<.$6.)(15.Vmem0,Vdst,Vbs,(14.R;.R9.))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R<.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(10.Vsrc,(14.R;.R9.)))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(10.Vdst,(14.R;.R9.)))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(16.&40.R:.))(11.R=.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_e776c D_e776c.                          (* [comment removed for export] *)
        stepb_tk F_e7770 D_e7770 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_e776c D_e776c.
        stepb_ft F_e7770 D_e7770 ltac:(cond).
        mlw F_e7774 D_e7774 k.                          (* [comment removed for export] *)
        mlw F_e7778 D_e7778 (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_e777c D_e777c k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw F_e7780 D_e7780 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_e7784 D_e7784.                          (* [comment removed for export] *)
        stepn F_e7788 D_e7788.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma al_loop : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pq,$1<.Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$7.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(10.Vsrc,R2.))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(10.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(16.&40.(1;.Vn,R4.)))P,(3.(1.&40.)(4.R7.(5.&5.+>.$6.))(16.&40.+?.))P,(13.=R6.)P,(;.(13.(1=.+10.(14.(1>.R:.)+1.))(1;.Vn,R7.))(17.(1;.Vn,R7.)(14.(1=.+10.(14.(1>.R:.)+1.))+10.)))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R;.(5.&40.+>::><.$6.)(15.Vmem0,Vdst,Vbs,R9.)Vrom,)(>.$?.R1.(5.&40.+>:;1<.$6.)(15.Vmem0,Vdst,Vbs,(14.R9.(1=.+10.(14.(1>.R<.)+1.))))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(10.Vsrc,(14.R9.(1=.+10.(14.(1>.R<.)+1.)))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(10.Vdst,(14.R9.(1=.+10.(14.(1>.R<.)+1.)))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(16.&40.(1;.Vn,(14.R9.(1=.+10.(14.(1>.R<.)+1.))))))(11.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      eexists. split.
      + mlw F_e773c D_e773c k.                          (* [comment removed for export] *)
        mlw F_e7740 D_e7740 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_e7744 D_e7744 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_e7748 D_e7748 (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_e774c D_e774c.                          (* [comment removed for export] *)
        stepn F_e7750 D_e7750.                          (* [comment removed for export] *)
        msw F_e7754 D_e7754 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw F_e7758 D_e7758 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_e775c D_e775c (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_e7760 D_e7760 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_e7764 D_e7764.                          (* [comment removed for export] *)
        stepb_ft F_e7768 D_e7768 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaaec : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_e773c D_e773c k.
          mlw F_e7740 D_e7740 (k + 4)%Z.
          mlw F_e7744 D_e7744 (k + 8)%Z.
          mlw F_e7748 D_e7748 (k + 12)%Z.
          stepn F_e774c D_e774c.
          stepn F_e7750 D_e7750.
          msw F_e7754 D_e7754 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_e7758 D_e7758 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_e775c D_e775c (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_e7760 D_e7760 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_e7764 D_e7764.
          stepb_tk F_e7768 D_e7768 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma al16_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$7.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(10.Vsrc,R2.))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(10.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(16.&40.(1;.Vn,R4.)))P,(;.(13.=R5.)(13.R5.Vn,))(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R9.(5.&40.+>::>0.$6.)(15.Vmem0,Vdst,Vbs,R7.)Vrom,)(>.$?.R1.(5.&40.+>:;1<.$6.)(15.Vmem0,Vdst,Vbs,(1;.Vn,(8.(1;.Vn,R7.)+10.)))Vrom,))(;.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R8.)(;.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(10.Vsrc,(1;.Vn,(8.(1;.Vn,R7.)+10.))))(;.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(10.Vdst,(1;.Vn,(8.(1;.Vn,R7.)+10.))))(;.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(16.&40.(8.(1;.Vn,R7.)+10.)))(11.R9.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_e7730 D_e7730.                          (* [comment removed for export] *)
        stepb_tk F_e7734 D_e7734 ltac:(cond).           (* [comment removed for export] *)
        replace (n - (n - k) mod 16)%Z with k by (rewrite Z.mod_small; lia).
        apply mst_refl.
      + rewrite (Z.mod_small (n - k) 16) by lia. replace (n - (n - k))%Z with k by lia.
        repeat split; gres; rwH; try reflexivity. solve_keeps.
    - set (q := Z.to_nat ((n - k) / 16 - 1)).
      assert (Hq : (16 * (Z.of_nat q + 1) <= n - k < 16 * (Z.of_nat q + 1) + 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 16 ltac:(lia)). lia. }
      assert (Hk' : (k + 16 * (Z.of_nat q + 1) = n - (n - k) mod 16)%Z).
      { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
        pose proof (Z.div_mod (n - k) 16 ltac:(lia)). lia. }
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaaec : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7730 D_e7730.                        (* [comment removed for export] *)
          stepb_ft F_e7734 D_e7734 ltac:(cond).         (* [comment removed for export] *)
          stepn F_e7738 D_e7738.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & K1).
        destruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Theorem memcpy_aligned : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyAL ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)P,(12.R1.)P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+:.$6.))Vdst,)P,(3.(1.&40.)(4.R5.(5.&5.+;.$6.))Vsrc,)P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(16.&40.Vn,))P,(3.$7.(8.(9.&40.Vsrc,)+4.)=)P,(3.$7.(8.(9.&40.Vdst,)+4.)=)(:.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.(<.$=.(>.$?.R:.(5.&40.+>:9<0.$6.)Vmem0,Vrom,)(>.$?.R1.R9.(1?.Vmem0,Vdst,Vbs,)Vrom,))(11.R:.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros regs ret Hret H1 H10 H11 H12 Hs4 Hd4.
    pose proof (u64_range src). pose proof (u64_range dst).
    rewrite <- (memk_n _ _ _ _ _ HOK). change mem0 with (MK 0).
    set (m := (n mod 16)%Z).
    pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as Hm16.
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (Hl16 : Z.land m 16 = 0%Z).
    { destruct B16 as [E|E]; [exact E|]. exfalso.
      pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaae0 : word) (MK 0) rom)
             (fun r => getr r 13 = at_ dst 0 /\ getr r 11 = at_ src 0 /\ getr r 12 = Z_to_bv 64 (n - 0) /\ getr r 1 = ret /\ keeps regs r)).
    { destruct (al_entry regs (MK 0) H10 H11 Hs4 Hd4) as (r & R & P). exists r. split; [exact R|].
      decompose [and] P. rewrite Z.sub_0_r. repeat split; try assumption; congruence. }
    cbv beta. intros r1 (R13 & R11 & R12 & R1 & K1).
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eab1c : word) (MK (n - m)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m) /\ getr r 13 = at_ dst (n - m) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al16_run r1 ret 0 R1 R11 R13 R12 ltac:(lia)) as (r & R & P). exists r.
      subst m. rewrite Z.sub_0_r in R, P. split; [exact R|]. decompose [and] P. repeat split; try assumption.
      eapply keeps_trans; eassumption. }
    cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eab3c : word) (MK (n - m + Z.land m 8)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8) /\ getr r 13 = at_ dst (n - m + Z.land m 8) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al8_run r2 ret (n - m) m (Z.land m 8) S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 4). pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r3 (T1 & T11 & T13 & T12 & K3).
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun r => mkst r (0x0ead80 : word) (MK (n - m + Z.land m 8 + Z.land m 4)) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ src (n - m + Z.land m 8 + Z.land m 4) /\ getr r 13 = at_ dst (n - m + Z.land m 8 + Z.land m 4) /\ getr r 12 = Z_to_bv 64 m /\ keeps regs r)).
    { destruct (al4_run r3 ret (n - m + Z.land m 8) m T1 T11 T13 T12 ltac:(lia)) as (r & R & P).
      { pose proof (Z.land_nonneg m 8). lia. }
      { pose proof (Z.land_nonneg m 2). pose proof (Z.land_nonneg m 1). pose proof (Z.land_nonneg m 8). lia. }
      exists r. split; [exact R|]. decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption. }
    cbv beta. intros r4 (U1 & U11 & U13 & U12 & K4).
    (* [comment removed for export] *)
    destruct (t2_run r4 ret (n - m + Z.land m 8 + Z.land m 4) m Hret U1 U11 U13 U12 ltac:(lia) B2 B1) as (r & R & P).
    { pose proof (Z.land_nonneg m 8). pose proof (Z.land_nonneg m 4). lia. }
    { lia. }
    exists r. split; [exact R | eapply keeps_trans; eassumption].
  Qed.

End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
