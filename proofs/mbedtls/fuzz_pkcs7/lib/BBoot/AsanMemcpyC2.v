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
  RefMemcpyLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMemcpyBase AsanMemcpyAL AsanMemcpyMIS Asan_code_memcpy.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMemcpyC2 () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMemcpyBase.memk"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.ABoot.RefMemcpyLib.LWv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMemcpyBase.sb_"; "RocqVerifyHarness.AgentSubmission.ABoot.RefMemcpyLib.keeps"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.land"].


Section C2.
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
  Ltac m16 := eapply (merge_s16 _ _ _ _ _ HOK); [reflexivity | lia | lia | lia | lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c2_pro : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyC2 ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(7.Vsrc,R2.))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(7.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(8.&40.(9.Vn,R4.)))P,(3.(1.&40.)(4.R7.(5.&5.+?.$6.))(8.&40.+2.))P,(:.=R6.)P,(:.+20.(9.Vn,R7.))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R;.(5.&40.+>::34.$6.)(11.Vmem0,Vdst,Vbs,R9.)Vrom,)(?.$10.R1.(5.&40.+>::64.$6.)(11.Vmem0,Vdst,Vbs,(12.R9.+2.))Vrom,))(<.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R:.)(<.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(12.R9.+10.)))(<.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(12.R9.+2.)))(<.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(8.&40.(9.Vn,(12.R9.+2.))))(<.(3.(1.&40.)(4.R1.(5.&5.+>.$6.))(13.(14.Vbs,R9.#4.)))(<.(3.(1.&40.)(4.R1.(5.&5.+?.$6.))(8.&40.+11.))(15.R;.R1.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk. eexists. split.
    - mlw F_e7684 D_e7684 k.                            (* [comment removed for export] *)
      stepn F_e7688 D_e7688.                            (* [comment removed for export] *)
      stepb_ft F_e768c D_e768c ltac:(cond).             (* [comment removed for export] *)
      stepn F_e7690 D_e7690.                            (* [comment removed for export] *)
      stepb_ft F_e7694 D_e7694 ltac:(cond).             (* [comment removed for export] *)
      stepn F_e7698 D_e7698.                            (* [comment removed for export] *)
      stepn F_e769c D_e769c.                            (* [comment removed for export] *)
      msb F_e76a0 D_e76a0 k ltac:(eapply (sb_val_word0' _ _ _ _ _ HOK); lia).        (* [comment removed for export] *)
      msb F_e76a4 D_e76a4 (k + 1)%Z ltac:(eapply (sb_val_srli8 _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
      stepn F_e76a8 D_e76a8.                            (* [comment removed for export] *)
      stepn F_e76ac D_e76ac.                            (* [comment removed for export] *)
      stepn F_e76b0 D_e76b0.                            (* [comment removed for export] *)
      mk_eq. apply mst_refl.
    - post. unfold v_addi. unorm. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c2_loop : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyC2 ()) "Pq,$16.Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pkk,$2.Pja,$2.Pjw,$2.P,(3.(1.&40.)(4.R5.(5.&5.+1.$6.))R4.)P,(3.(1.&40.)(4.R6.(5.&5.+;.$6.))(7.Vsrc,R3.))P,(3.(1.&40.)(4.R7.(5.&5.+=.$6.))(7.Vdst,R5.))P,(3.(1.&40.)(4.R8.(5.&5.+<.$6.))(8.&40.(9.Vn,R6.)))P,(3.(1.&40.)(4.R9.(5.&5.+>.$6.))(13.(14.Vbs,R5.#4.)))P,(3.(1.&40.)(4.R:.(5.&5.+?.$6.))(8.&40.+11.))P,(3.$2.R8.(12.R9.+>.))P,(3.$2.R8.(9.R:.+2.))P,(:.+2.R;.)P,(<.(:.(12.(17.+10.(12.(18.R?.)+1.))+2.)(9.Vn,R<.))(19.(9.Vn,R<.)(12.(17.+10.(12.(18.R?.)+1.))+12.)))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R10.(5.&40.+>::64.$6.)(11.Vmem0,Vdst,Vbs,R>.)Vrom,)(?.$10.R1.(5.&40.+>::<4.$6.)(11.Vmem0,Vdst,Vbs,(12.R>.(17.+10.(12.(18.R11.)+1.))))Vrom,))(<.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R?.)(<.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(12.(12.R>.(17.+10.(12.(18.R11.)+1.)))+>.)))(<.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(12.R>.(17.+10.(12.(18.R11.)+1.)))))(<.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(8.&40.(9.Vn,(12.R>.(17.+10.(12.(18.R11.)+1.))))))(15.R10.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    induction q as [|q IH]; intros regs ret kk ja jw H1 H11 H13 H12 H14 H15 Hja Hjw Hkk Hq; subst ja jw.
    - eexists. split.
      + stepn F_e76b4 D_e76b4.                          (* [comment removed for export] *)
        mlw F_e76b8 D_e76b8 (kk + 2)%Z.                 (* [comment removed for export] *)
        mlw F_e76bc D_e76bc (kk + 6)%Z.                 (* [comment removed for export] *)
        mlw F_e76c0 D_e76c0 (kk + 10)%Z.                (* [comment removed for export] *)
        mlw F_e76c4 D_e76c4 (kk + 14)%Z.                (* [comment removed for export] *)
        stepn F_e76c8 D_e76c8. stepn F_e76cc D_e76cc. stepn F_e76d0 D_e76d0.   (* [comment removed for export] *)
        stepn F_e76d4 D_e76d4. stepn F_e76d8 D_e76d8. stepn F_e76dc D_e76dc.   (* [comment removed for export] *)
        stepn F_e76e0 D_e76e0. stepn F_e76e4 D_e76e4. stepn F_e76e8 D_e76e8.   (* [comment removed for export] *)
        stepn F_e76ec D_e76ec. stepn F_e76f0 D_e76f0.                          (* [comment removed for export] *)
        stepn F_e76f4 D_e76f4.                          (* [comment removed for export] *)
        msw F_e76f8 D_e76f8 kk ltac:(m16).              (* [comment removed for export] *)
        msw F_e76fc D_e76fc (kk + 4)%Z ltac:(m16).      (* [comment removed for export] *)
        msw F_e7700 D_e7700 (kk + 8)%Z ltac:(m16).      (* [comment removed for export] *)
        msw F_e7704 D_e7704 (kk + 12)%Z ltac:(m16).     (* [comment removed for export] *)
        stepn F_e7708 D_e7708.                          (* [comment removed for export] *)
        stepn F_e770c D_e770c.                          (* [comment removed for export] *)
        stepb_ft F_e7710 D_e7710 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + post. unfold v_addi. unorm. f_equal. lia.
    - eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaa64 : word) (MK (kk + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16 + 14) /\ getr r 13 = at_ dst (kk + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (kk + 16)) /\ getr r 14 = LWv (SB (kk + 14) 4)
                         /\ getr r 15 = Z_to_bv 64 17 /\ keeps regs r)).
      + eexists. split.
        * stepn F_e76b4 D_e76b4.
          mlw F_e76b8 D_e76b8 (kk + 2)%Z.
          mlw F_e76bc D_e76bc (kk + 6)%Z.
          mlw F_e76c0 D_e76c0 (kk + 10)%Z.
          mlw F_e76c4 D_e76c4 (kk + 14)%Z.
          stepn F_e76c8 D_e76c8. stepn F_e76cc D_e76cc. stepn F_e76d0 D_e76d0.
          stepn F_e76d4 D_e76d4. stepn F_e76d8 D_e76d8. stepn F_e76dc D_e76dc.
          stepn F_e76e0 D_e76e0. stepn F_e76e4 D_e76e4. stepn F_e76e8 D_e76e8.
          stepn F_e76ec D_e76ec. stepn F_e76f0 D_e76f0.
          stepn F_e76f4 D_e76f4.
          msw F_e76f8 D_e76f8 kk ltac:(m16).
          msw F_e76fc D_e76fc (kk + 4)%Z ltac:(m16).
          msw F_e7700 D_e7700 (kk + 8)%Z ltac:(m16).
          msw F_e7704 D_e7704 (kk + 12)%Z ltac:(m16).
          stepn F_e7708 D_e7708.
          stepn F_e770c D_e770c.
          stepb_tk F_e7710 D_e7710 ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. post. unfold v_addi. unorm. f_equal. lia.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & R14 & R15 & K1).
        destruct (IH r1 ret (kk + 16)%Z (kk + 16 + 14)%Z (kk + 14)%Z R1 R11 R13 R12 R14 R15
                     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. replace (kk + 16 * (Z.of_nat (S q) + 1))%Z with (kk + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
        split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c2_exit : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyC2 ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pkk,$2.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(7.Vsrc,(12.R2.+>.)))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(7.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(8.&40.(9.Vn,R4.)))P,(:.=R5.)P,(19.(9.Vn,R6.)+20.)P,(:.R7.Vn,)Zm,$2.(9.Vn,R8.)(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R<.(5.&40.+>::<4.$6.)(11.Vmem0,Vdst,Vbs,R:.)Vrom,)(?.$10.R1.(5.&40.+>:=80.$6.)(11.Vmem0,Vdst,Vbs,(12.(12.(12.R:.(1:.R2.+10.))(1:.R2.+8.))(1:.R2.+4.)))Vrom,))(<.(3.(1.&40.)(4.R1.(5.&5.+1.$6.))R;.)(<.(3.(1.&40.)(4.R1.(5.&5.+;.$6.))(7.Vsrc,(12.(12.(12.R:.(1:.R2.+10.))(1:.R2.+8.))(1:.R2.+4.))))(<.(3.(1.&40.)(4.R1.(5.&5.+=.$6.))(7.Vdst,(12.(12.(12.R:.(1:.R2.+10.))(1:.R2.+8.))(1:.R2.+4.))))(<.(3.(1.&40.)(4.R1.(5.&5.+<.$6.))(8.&40.R2.))(15.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret kk H1 H11 H13 H12 Hkk Hm Hkn m. subst m.
    destruct (bits_lt32 (n - kk) ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    assert (0 <= Z.land (n - kk) 8)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 4)%Z by (apply Z.land_nonneg; lia).
    assert (0 <= Z.land (n - kk) 2)%Z by (apply Z.land_nonneg; lia). assert (0 <= Z.land (n - kk) 1)%Z by (apply Z.land_nonneg; lia).
    destruct B16 as [HL16|HL16].
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eaa20 : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7714 D_e7714.                        (* [comment removed for export] *)
          stepn F_e7718 D_e7718.                        (* [comment removed for export] *)
          stepb_tk F_e771c D_e771c ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        destruct (t8_run _ _ _ _ _ rom HOK r1 ret kk (n - kk) R1 R11 R13 R12 ltac:(lia) Hkk B8 B4 ltac:(lia)) as (r2 & RUN & P).
        exists r2. rewrite HL16, Z.add_0_r. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
    - (* [comment removed for export] *)
      eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eac6c : word) (MK kk) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src kk /\ getr r 13 = at_ dst kk /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
      + eexists. split.
        * stepn F_e7714 D_e7714.
          stepn F_e7718 D_e7718.
          stepb_ft F_e771c D_e771c ltac:(cond).         (* [comment removed for export] *)
          stepn F_e7720 D_e7720.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. post.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & K1).
        eapply (runs_trans ASEGS _ (fun r => mkst r (0x0eacf8 : word) (MK (kk + 16)) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = at_ src (kk + 16) /\ getr r 13 = at_ dst (kk + 16) /\ getr r 12 = Z_to_bv 64 (n - kk) /\ keeps regs r)).
        * destruct (b16_blk _ _ _ _ _ rom HOK r1 ret kk _ R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
          exists r2. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
        * cbv beta. intros r2 (S1 & S11 & S13 & S12 & K2).
          destruct (b16_tail _ _ _ _ _ rom HOK r2 ret (kk + 16)%Z (n - kk) S1 S11 S13 S12 ltac:(lia) ltac:(lia) B8 B4 ltac:(lia)) as (r3 & RUN & P).
          exists r3. rewrite HL16. split; [exact RUN|]. decompose [and] P. post. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma c2_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyC2 ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(3.(1.&40.)(4.R3.(5.&5.+1.$6.))R2.)P,(3.(1.&40.)(4.R4.(5.&5.+;.$6.))(7.Vsrc,R2.))P,(3.(1.&40.)(4.R5.(5.&5.+=.$6.))(7.Vdst,R3.))P,(3.(1.&40.)(4.R6.(5.&5.+<.$6.))(8.&40.(9.Vn,R4.)))P,(3.(1.&40.)(4.R7.(5.&5.+?.$6.))(8.&40.+2.))P,(:.=R6.)P,(:.+20.(9.Vn,R7.))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(;.$2.Lm,$2.(<.(=.$>.(?.$10.R<.(5.&40.+>::34.$6.)(11.Vmem0,Vdst,Vbs,R:.)Vrom,)(?.$10.R2.(5.&40.+>:=80.$6.)(11.Vmem0,Vdst,Vbs,(9.Vn,(12.(1:.R1.+2.)(1:.R1.+1.))))Vrom,))(<.(<.(:.=R1.)(19.R1.+20.))(<.(3.(1.&40.)(4.R2.(5.&5.+1.$6.))R;.)(<.(3.(1.&40.)(4.R2.(5.&5.+;.$6.))(7.Vsrc,(9.Vn,(12.(1:.R1.+2.)(1:.R1.+1.)))))(<.(3.(1.&40.)(4.R2.(5.&5.+=.$6.))(7.Vdst,(9.Vn,(12.(1:.R1.+2.)(1:.R1.+1.)))))(<.(3.(1.&40.)(4.R2.(5.&5.+<.$6.))(8.&40.R1.))(15.R<.R2.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k H1 H11 H13 H12 H15 Hk Hnk.
    set (q := Z.to_nat ((n - k - 4) / 16 - 1)).
    assert (Hq : (16 * (Z.of_nat q + 1) + 2 <= n - (k + 2) < 16 * (Z.of_nat q + 1) + 18)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod (n - k - 4) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k - 4) 16 ltac:(lia)). lia. }
    set (kk := (k + 2 + 16 * (Z.of_nat q + 1))%Z).
    set (m := (n - kk)%Z).
    destruct (bits_lt32 m ltac:(lia)) as (B16 & B8 & B4 & B2 & B1 & Bsum).
    destruct (c2_pro regs ret k H1 H11 H13 H12 H15 Hk Hnk) as (r1 & RUN1 & P1 & P11 & P13 & P12 & P14 & P15 & K1).
    destruct (c2_loop q r1 ret (k + 2)%Z (k + 16)%Z k P1 P11 P13 P12 P14 P15 ltac:(lia) ltac:(lia) ltac:(lia) Hq)
      as (r2 & RUN2 & Q1 & Q11 & Q13 & Q12 & K2).
    fold kk in RUN2, Q11, Q13, Q12.
    destruct (c2_exit r2 ret kk Q1 Q11 Q13 Q12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r3 & RUN3 & S1 & S11 & S13 & S12 & K3).
    fold m in RUN3, S11, S13, S12.
    exists r3, m.
    assert (E : (kk + Z.land m 16 + Z.land m 8 + Z.land m 4 = n - (Z.land m 2 + Z.land m 1))%Z) by lia.
    rewrite E in RUN3, S11, S13.
    split; [| split; [lia | repeat split; try assumption]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - eapply keeps_trans; [| exact K3]. eapply keeps_trans; eassumption.
  Qed.

End C2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
