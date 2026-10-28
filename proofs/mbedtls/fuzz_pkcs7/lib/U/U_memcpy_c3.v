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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_memcpy_base U_memcpy_al U_memcpy_mis U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_memcpy_c3 () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.at_"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.U.U_memcpy_base.memk"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.LWv"; "RocqVerifyHarness.AgentSubmission.U.U_memcpy_base.sb_"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.keeps"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.land"].


Section C3.
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
  Ltac m8 := eapply (merge_s8 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c3_pro : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_c3 ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(7.Vsrc,R2.))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(7.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(8.&40.(9.Vn,R4.)))P,(3.(1.&40.)(4.R7.(5.&5.+?.$6.))(8.&40.+3.))P,(:.=R6.)P,(:.+20.(9.Vn,R7.))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R;.(5.&40.+46:;4.$6.)(11.Vmem0,Vdst,Vbs,R9.)Vrom,)(?.$10.R1.(5.&40.+46;><.$6.)(11.Vmem0,Vdst,Vbs,(12.R9.+1.))Vrom,))(<.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(<.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(12.R9.+10.)))(<.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(12.R9.+1.)))(<.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(8.&40.(9.Vn,(12.R9.+1.))))(<.(3.(1.&40.)(4.R1.(5.&5.+>.$6.))(13.(14.Vbs,R9.#4.)))(<.(3.(1.&40.)(4.R1.(5.&5.+?.$6.))(8.&40.+12.))(15.R;.R1.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_43368 D_43368 k.                            (* [comment removed for export] *)
      stepn F_4336c D_4336c.                            (* [comment removed for export] *)
      stepb_tk F_43370 D_43370 ltac:(cond).             (* [comment removed for export] *)
      msb F_4348c D_4348c k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      stepn F_43490 D_43490.                            (* [comment removed for export] *)
      stepn F_43494 D_43494.                            (* [comment removed for export] *)
      stepn F_43498 D_43498.                            (* [comment removed for export] *)
      stepn F_4349c D_4349c.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c3_loop : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_c3 ()) "Pq,$16.Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pkk,$2.Pja,$2.Pjw,$2.P,(3.(1.&40.)(4.R5.(5.&5.+1.$6.))R4.)P,(3.(1.&40.)(4.R6.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R7.(5.&5.+=.$6.))(7.Vdst,R5.))P,(3.(1.&40.)(4.R8.(5.&5.+<.$6.))(8.&40.(9.Vn,R6.)))P,(3.(1.&40.)(4.R9.(5.&5.+>.$6.))(13.(14.Vbs,R5.#4.)))P,(3.(1.&40.)(4.R:.(5.&5.+?.$6.))(8.&40.+12.))P,(3.$2.R8.(12.R9.+?.))P,(3.$2.R8.(9.R:.+1.))P,(:.+1.R;.)P,(<.(:.(12.(17.+10.(12.(18.R?.)+1.))+3.)(9.Vn,R<.))(19.(9.Vn,R<.)(12.(17.+10.(12.(18.R?.)+1.))+13.)))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R10.(5.&40.+46;><.$6.)(11.Vmem0,Vdst,Vbs,R>.)Vrom,)(?.$10.R1.(5.&40.+46<4<.$6.)(11.Vmem0,Vdst,Vbs,(12.R>.(17.+10.(12.(18.R11.)+1.))))Vrom,))(<.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R?.)(<.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(12.(12.R>.(17.+10.(12.(18.R11.)+1.)))+?.)))(<.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(12.R>.(17.+10.(12.(18.R11.)+1.)))))(<.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(8.&40.(9.Vn,(12.R>.(17.+10.(12.(18.R11.)+1.))))))(15.R10.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_434a0 D_434a0.                          (* [comment removed for export] *)
        mlw F_434a4 D_434a4 (kk + 3)%Z.                 (* [comment removed for export] *)
        mlw F_434a8 D_434a8 (kk + 7)%Z.                 (* [comment removed for export] *)
        mlw F_434ac D_434ac (kk + 11)%Z.                (* [comment removed for export] *)
        mlw F_434b0 D_434b0 (kk + 15)%Z.                (* [comment removed for export] *)
        stepn F_434b4 D_434b4. stepn F_434b8 D_434b8. stepn F_434bc D_434bc.
        stepn F_434c0 D_434c0. stepn F_434c4 D_434c4. stepn F_434c8 D_434c8.
        stepn F_434cc D_434cc. stepn F_434d0 D_434d0. stepn F_434d4 D_434d4.
        stepn F_434d8 D_434d8. stepn F_434dc D_434dc.
        stepn F_434e0 D_434e0.                          (* [comment removed for export] *)
        msw F_434e4 D_434e4 kk ltac:(m8).
        msw F_434e8 D_434e8 (kk + 4)%Z ltac:(m8).
        msw F_434ec D_434ec (kk + 8)%Z ltac:(m8).
        msw F_434f0 D_434f0 (kk + 12)%Z ltac:(m8).
        stepn F_434f4 D_434f4.                          (* [comment removed for export] *)
        stepn F_434f8 D_434f8.                          (* [comment removed for export] *)
        stepb_ft F_434fc D_434fc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46bec : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 15) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 15) 4)
                         /\ getr r 15 = Z_to_bv 64 18 /\ keeps regs r)).
      + eexists. split.
        * stepn F_434a0 D_434a0.
          mlw F_434a4 D_434a4 (kk + 3)%Z.
          mlw F_434a8 D_434a8 (kk + 7)%Z.
          mlw F_434ac D_434ac (kk + 11)%Z.
          mlw F_434b0 D_434b0 (kk + 15)%Z.
          stepn F_434b4 D_434b4. stepn F_434b8 D_434b8. stepn F_434bc D_434bc.
          stepn F_434c0 D_434c0. stepn F_434c4 D_434c4. stepn F_434c8 D_434c8.
          stepn F_434cc D_434cc. stepn F_434d0 D_434d0. stepn F_434d4 D_434d4.
          stepn F_434d8 D_434d8. stepn F_434dc D_434dc.
          stepn F_434e0 D_434e0.
          msw F_434e4 D_434e4 kk ltac:(m8).
          msw F_434e8 D_434e8 (kk + 4)%Z ltac:(m8).
          msw F_434ec D_434ec (kk + 8)%Z ltac:(m8).
          msw F_434f0 D_434f0 (kk + 12)%Z ltac:(m8).
          stepn F_434f4 D_434f4.
          stepn F_434f8 D_434f8.
          stepb_tk F_434fc D_434fc ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & R14 & R15 & K1)).
        ddestruct (IH r1 ret (kk + 16)%Z (kk + 16 + 15)%Z (kk + 15)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK"] Lemma c3_exit : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_c3 ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pkk,$2.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(7.Vsrc,(12.R2.+?.)))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(7.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(8.&40.(9.Vn,R4.)))P,(:.=R5.)P,(19.(9.Vn,R6.)+20.)P,(:.R7.Vn,)Zm,$2.(9.Vn,R8.)(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R<.(5.&40.+46<4<.$6.)(11.Vmem0,Vdst,Vbs,R:.)Vrom,)(?.$10.R1.(5.&40.+46>00.$6.)(11.Vmem0,Vdst,Vbs,(12.(12.(12.R:.(1:.R2.+10.))(1:.R2.+8.))(1:.R2.+4.)))Vrom,))(<.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(<.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(12.(12.(12.R:.(1:.R2.+10.))(1:.R2.+8.))(1:.R2.+4.))))(<.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(12.(12.(12.R:.(1:.R2.+10.))(1:.R2.+8.))(1:.R2.+4.))))(<.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(8.&40.R2.))(15.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    ddestruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46aa0 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_43500 D_43500.                        (* [comment removed for export] *)
          stepn F_43504 D_43504.                        (* [comment removed for export] *)
          stepb_tk F_43508 D_43508 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46cec : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_43500 D_43500.
          stepn F_43504 D_43504.
          stepb_ft F_43508 D_43508 ltac:(cond).
          stepn F_4350c D_4350c.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & K1)).
        eapply (runs_trans RSEGS _ (fun r => mkst r (0x46d78 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. (intros r2 dd_H; ddestruct dd_H as (S1 & S11 & S13 & S12 & K2)).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c3_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_c3 ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(7.Vsrc,R2.))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(7.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(8.&40.(9.Vn,R4.)))P,(3.(1.&40.)(4.R7.(5.&5.+?.$6.))(8.&40.+3.))P,(:.=R6.)P,(:.+20.(9.Vn,R7.))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.$2.Lm,$2.(<.(=.$>.(?.$10.R<.(5.&40.+46:;4.$6.)(11.Vmem0,Vdst,Vbs,R:.)Vrom,)(?.$10.R2.(5.&40.+46>00.$6.)(11.Vmem0,Vdst,Vbs,(9.Vn,(12.(1:.R1.+2.)(1:.R1.+1.))))Vrom,))(<.(<.(:.=R1.)(19.R1.+20.))(<.(3.(1.&40.)(4.R2.(5.&5.+1.$6.))R;.)(<.(3.(1.&40.)(4.R2.(5.&5.+;.$6.))(7.Vsrc,(9.Vn,(12.(1:.R1.+2.)(1:.R1.+1.)))))(<.(3.(1.&40.)(4.R2.(5.&5.+=.$6.))(7.Vdst,(9.Vn,(12.(1:.R1.+2.)(1:.R1.+1.)))))(<.(3.(1.&40.)(4.R2.(5.&5.+<.$6.))(8.&40.R1.))(15.R<.R2.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 3 <= n - (k + 1) < 16 * (Z.of_nat q + 1) + 19)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 1 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    ddestruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    ddestruct (c3_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    ddestruct (c3_loop q r1 ret (k + 1)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    ddestruct (c3_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    dexists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
