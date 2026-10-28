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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_memcpy_base U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_memcpy_al () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.at_"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.U.U_memcpy_base.memk"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.keeps"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.modulo"].


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
  
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma b1_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_al ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(3.R2.)P,(4.(1.&40.)(5.R4.(6.&5.+1.$7.))R3.)P,(4.(1.&40.)(5.R5.(6.&5.+;.$7.))(8.Vsrc,R3.))P,(4.(1.&40.)(5.R6.(6.&5.+=.$7.))(8.Vdst,R4.))P,(9.=R5.)P,(4.$2.(:.R6.+1.)Vn,)(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R:.(6.&40.+46>38.$7.)(11.Vmem0,Vdst,Vbs,R8.)Vrom,)(?.$10.R1.R9.(11.Vmem0,Vdst,Vbs,Vn,)Vrom,))(12.R:.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k Hret H1 H11 H13 Hk Hkn.
    eexists. split.
    - mlbu F_436ec D_436ec k.                      (* [comment removed for export] *)
      msb F_436f0 D_436f0 k ltac:(apply sb_val_plain).   (* [comment removed for export] *)
      replace (k + 1)%Z with n by lia.
      stepret F_436f4 D_436f4 ret ltac:(exact H1).
      apply mst_refl.
    - solve_keeps.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma t2_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_al ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(3.R3.)P,(4.(1.&40.)(5.R5.(6.&5.+1.$7.))R4.)P,(4.(1.&40.)(5.R6.(6.&5.+;.$7.))(8.Vsrc,R4.))P,(4.(1.&40.)(5.R7.(6.&5.+=.$7.))(8.Vdst,R5.))P,(4.(1.&40.)(5.R8.(6.&5.+<.$7.))(13.&40.R5.))P,(<.(9.=R6.)(14.R6.(15.+2.+40.)))P,(16.(4.$2.(17.R7.+2.)=)(4.$2.(17.R7.+2.)+2.))P,(16.(4.$2.(17.R8.+1.)=)(4.$2.(17.R8.+1.)+1.))P,(9.=R:.)P,(4.$2.(18.Vn,R;.)(:.(17.R:.+2.)(17.R:.+1.)))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R?.(6.&40.+46>00.$7.)(11.Vmem0,Vdst,Vbs,R=.)Vrom,)(?.$10.R1.R>.(11.Vmem0,Vdst,Vbs,Vn,)Vrom,))(12.R?.R1.)))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m Hret H1 H11 H13 H12 Hm [HL2|HL2] [HL1|HL1] Hk Hrem.
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_436b4 D_436b4.                          (* [comment removed for export] *)
        stepb_ft F_436b8 D_436b8 ltac:(cond).           (* [comment removed for export] *)
        stepn F_436bc D_436bc.                          (* [comment removed for export] *)
        stepb_ft F_436c0 D_436c0 ltac:(cond).           (* [comment removed for export] *)
        stepret F_436c4 D_436c4 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46e38 : word) (MK k) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k /\ keeps regs r)).
      + eexists. split.
        * stepn F_436b4 D_436b4.
          stepb_ft F_436b8 D_436b8 ltac:(cond).
          stepn F_436bc D_436bc.
          stepb_tk F_436c0 D_436c0 ltac:(cond).         (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; exact H11 | gres; exact H13 | solve_keeps].
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & K1)).
        ddestruct (b1_run r1 ret k Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_436b4 D_436b4.
        stepb_tk F_436b8 D_436b8 ltac:(cond).           (* [comment removed for export] *)
        mlbu F_436c8 D_436c8 k.                         (* [comment removed for export] *)
        mlbu F_436cc D_436cc (k + 1)%Z.                 (* [comment removed for export] *)
        stepn F_436d0 D_436d0.                          (* [comment removed for export] *)
        stepn F_436d4 D_436d4.                          (* [comment removed for export] *)
        msb F_436d8 D_436d8 k ltac:(apply sb_val_plain).          (* [comment removed for export] *)
        msb F_436dc D_436dc (k + 1)%Z ltac:(apply sb_val_plain).  (* [comment removed for export] *)
        stepn F_436e0 D_436e0.                          (* [comment removed for export] *)
        stepn F_436e4 D_436e4.                          (* [comment removed for export] *)
        stepb_tk F_436e8 D_436e8 ltac:(cond).           (* [comment removed for export] *)
        stepret F_436c4 D_436c4 ret ltac:(exact H1).
        mk_eq. apply mst_refl.
      + solve_keeps.
    - (* [comment removed for export] *)
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46e38 : word) (MK (k + 2)) rom)
                (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 2) /\ getr r 13 = at_ dst (k + 2) /\ keeps regs r)).
      + eexists. split.
        * stepn F_436b4 D_436b4.
          stepb_tk F_436b8 D_436b8 ltac:(cond).
          mlbu F_436c8 D_436c8 k.
          mlbu F_436cc D_436cc (k + 1)%Z.
          stepn F_436d0 D_436d0.
          stepn F_436d4 D_436d4.
          msb F_436d8 D_436d8 k ltac:(apply sb_val_plain).
          msb F_436dc D_436dc (k + 1)%Z ltac:(apply sb_val_plain).
          stepn F_436e0 D_436e0.
          stepn F_436e4 D_436e4.
          stepb_ft F_436e8 D_436e8 ltac:(cond).         (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; [gres; exact H1 | gres; rwH; rewrite ?at_addi; reflexivity
                                 | gres; rwH; rewrite ?at_addi; reflexivity | solve_keeps].
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & K1)).
        ddestruct (b1_run r1 ret (k + 2)%Z Hret R1 R11 R13 ltac:(lia) ltac:(lia)) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply keeps_trans; eassumption].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma al4_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_al ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.P,(4.(1.&40.)(5.R4.(6.&5.+1.$7.))R3.)P,(4.(1.&40.)(5.R5.(6.&5.+;.$7.))(8.Vsrc,R3.))P,(4.(1.&40.)(5.R6.(6.&5.+=.$7.))(8.Vdst,R4.))P,(4.(1.&40.)(5.R7.(6.&5.+<.$7.))(13.&40.R4.))P,(<.(9.=R5.)(14.R5.(15.+2.+40.)))P,(9.=R7.)P,(16.(4.$2.(17.R7.+4.)=)(<.(4.$2.(17.R7.+4.)+4.)(9.(:.R8.+4.)Vn,)))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R<.(6.&40.+46;;<.$7.)(11.Vmem0,Vdst,Vbs,R:.)Vrom,)(?.$10.R1.(6.&40.+46>00.$7.)(11.Vmem0,Vdst,Vbs,(:.R:.(17.R9.+4.)))Vrom,))(<.(4.(1.&40.)(5.R1.(6.&5.+1.$7.))R;.)(<.(4.(1.&40.)(5.R1.(6.&5.+;.$7.))(8.Vsrc,(:.R:.(17.R9.+4.))))(<.(4.(1.&40.)(5.R1.(6.&5.+=.$7.))(8.Vdst,(:.R:.(17.R9.+4.))))(<.(4.(1.&40.)(5.R1.(6.&5.+<.$7.))(13.&40.R9.))(12.R<.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m H1 H11 H13 H12 Hm Hk [HL4|[HL4 Hk4]].
    - eexists. split.
      + stepn F_43470 D_43470.                          (* [comment removed for export] *)
        stepb_tk F_43474 D_43474 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_43470 D_43470.
        stepb_ft F_43474 D_43474 ltac:(cond).           (* [comment removed for export] *)
        mlw F_43478 D_43478 k.                          (* [comment removed for export] *)
        stepn F_4347c D_4347c.                          (* [comment removed for export] *)
        msw F_43480 D_43480 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).   (* [comment removed for export] *)
        stepn F_43484 D_43484.                          (* [comment removed for export] *)
        stepn F_43488 D_43488.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK"] Lemma al8_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_al ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.Pm,$2.Pe8,$2.P,(4.(1.&40.)(5.R5.(6.&5.+1.$7.))R4.)P,(4.(1.&40.)(5.R6.(6.&5.+;.$7.))(8.Vsrc,R4.))P,(4.(1.&40.)(5.R7.(6.&5.+=.$7.))(8.Vdst,R5.))P,(4.(1.&40.)(5.R8.(6.&5.+<.$7.))(13.&40.R5.))P,(<.(9.=R6.)(14.R6.(15.+2.+40.)))P,(9.=R8.)P,(16.(<.(14.R8.+8.)(4.$2.R7.=))(<.(9.+8.R8.)(<.(4.$2.R7.+8.)(9.(:.R9.+8.)Vn,))))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R=.(6.&40.+46;9<.$7.)(11.Vmem0,Vdst,Vbs,R;.)Vrom,)(?.$10.R1.(6.&40.+46;;<.$7.)(11.Vmem0,Vdst,Vbs,(:.R;.R9.))Vrom,))(<.(4.(1.&40.)(5.R1.(6.&5.+1.$7.))R<.)(<.(4.(1.&40.)(5.R1.(6.&5.+;.$7.))(8.Vsrc,(:.R;.R9.)))(<.(4.(1.&40.)(5.R1.(6.&5.+=.$7.))(8.Vdst,(:.R;.R9.)))(<.(4.(1.&40.)(5.R1.(6.&5.+<.$7.))(13.&40.R:.))(12.R=.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k m e8 H1 H11 H13 H12 Hm Hk [[HL8 He]|[HL8 [He Hk8]]]; subst e8.
    - eexists. split.
      + stepn F_43450 D_43450.                          (* [comment removed for export] *)
        stepb_tk F_43454 D_43454 ltac:(cond).           (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; try (f_equal; lia); try reflexivity. solve_keeps.
    - eexists. split.
      + stepn F_43450 D_43450.
        stepb_ft F_43454 D_43454 ltac:(cond).
        mlw F_43458 D_43458 k.                          (* [comment removed for export] *)
        mlw F_4345c D_4345c (k + 4)%Z.                  (* [comment removed for export] *)
        msw F_43460 D_43460 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).         (* [comment removed for export] *)
        msw F_43464 D_43464 (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_43468 D_43468.                          (* [comment removed for export] *)
        stepn F_4346c D_4346c.                          (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity. solve_keeps.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma al_loop : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_al ()) "Pq,$19.Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(4.(1.&40.)(5.R3.(6.&5.+1.$7.))R2.)P,(4.(1.&40.)(5.R4.(6.&5.+;.$7.))(8.Vsrc,R2.))P,(4.(1.&40.)(5.R5.(6.&5.+=.$7.))(8.Vdst,R3.))P,(4.(1.&40.)(5.R6.(6.&5.+<.$7.))(13.&40.(18.Vn,R4.)))P,(4.(1.&40.)(5.R7.(6.&5.+>.$7.))(13.&40.+?.))P,(9.=R6.)P,(<.(9.(1:.+10.(:.(1;.R:.)+1.))(18.Vn,R7.))(14.(18.Vn,R7.)(:.(1:.+10.(:.(1;.R:.)+1.))+10.)))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R;.(6.&40.+46;6<.$7.)(11.Vmem0,Vdst,Vbs,R9.)Vrom,)(?.$10.R1.(6.&40.+46;9<.$7.)(11.Vmem0,Vdst,Vbs,(:.R9.(1:.+10.(:.(1;.R<.)+1.))))Vrom,))(<.(4.(1.&40.)(5.R1.(6.&5.+1.$7.))R:.)(<.(4.(1.&40.)(5.R1.(6.&5.+;.$7.))(8.Vsrc,(:.R9.(1:.+10.(:.(1;.R<.)+1.)))))(<.(4.(1.&40.)(5.R1.(6.&5.+=.$7.))(8.Vdst,(:.R9.(1:.+10.(:.(1;.R<.)+1.)))))(<.(4.(1.&40.)(5.R1.(6.&5.+<.$7.))(13.&40.(18.Vn,(:.R9.(1:.+10.(:.(1;.R<.)+1.))))))(12.R;.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    induction q as [|q IH]; intros regs ret k H1 H11 H13 H12 H14 Hk Hq.
    - (* [comment removed for export] *)
      eexists. split.
      + mlw F_43420 D_43420 k.                          (* [comment removed for export] *)
        mlw F_43424 D_43424 (k + 4)%Z.                  (* [comment removed for export] *)
        mlw F_43428 D_43428 (k + 8)%Z.                  (* [comment removed for export] *)
        mlw F_4342c D_4342c (k + 12)%Z.                 (* [comment removed for export] *)
        stepn F_43430 D_43430.                          (* [comment removed for export] *)
        stepn F_43434 D_43434.                          (* [comment removed for export] *)
        msw F_43438 D_43438 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).          (* [comment removed for export] *)
        msw F_4343c D_4343c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_43440 D_43440 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).  (* [comment removed for export] *)
        msw F_43444 D_43444 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia). (* [comment removed for export] *)
        stepn F_43448 D_43448.                          (* [comment removed for export] *)
        stepb_ft F_4344c D_4344c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
        mk_eq. apply mst_refl.
      + repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
        * unfold v_addi. unorm. f_equal. lia.
        * solve_keeps.
    - eapply (runs_trans RSEGS _ (fun r => mkst r (0x46b6c : word) (MK (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 16) /\ getr r 13 = at_ dst (k + 16)
                         /\ getr r 12 = Z_to_bv 64 (n - (k + 16)) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * mlw F_43420 D_43420 k.
          mlw F_43424 D_43424 (k + 4)%Z.
          mlw F_43428 D_43428 (k + 8)%Z.
          mlw F_4342c D_4342c (k + 12)%Z.
          stepn F_43430 D_43430.
          stepn F_43434 D_43434.
          msw F_43438 D_43438 k ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_4343c D_4343c (k + 4)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_43440 D_43440 (k + 8)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          msw F_43444 D_43444 (k + 12)%Z ltac:(apply (sw_val_plain _ _ _ _ _ HOK); lia).
          stepn F_43448 D_43448.
          stepb_tk F_4344c D_4344c ltac:(unfold v_addi; cond).   (* [comment removed for export] *)
          mk_eq. apply mst_refl.
        * cbv beta. repeat split; gres; rwH; rewrite ?at_addi; try (f_equal; lia); try reflexivity.
          -- unfold v_addi. unorm. f_equal. lia.
          -- solve_keeps.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & R14 & K1)).
        ddestruct (IH r1 ret (k + 16)%Z R1 R11 R13 R12 R14 ltac:(lia) ltac:(lia)) as (r2 & RUN & P).
        exists r2. split.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * replace (k + 16 * (Z.of_nat (S q) + 1))%Z with (k + 16 + 16 * (Z.of_nat q + 1))%Z by lia.
          decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  (* [comment removed for export] *)
  #[using="HOK Hn0"] Lemma al16_run : ltac2:(CDefT.buildp (gd_tbl_P_memcpy_al ()) "Pregs,(0.&5.(1.&40.))Pret,(1.&40.)Pk,$2.P,(4.(1.&40.)(5.R3.(6.&5.+1.$7.))R2.)P,(4.(1.&40.)(5.R4.(6.&5.+;.$7.))(8.Vsrc,R2.))P,(4.(1.&40.)(5.R5.(6.&5.+=.$7.))(8.Vdst,R3.))P,(4.(1.&40.)(5.R6.(6.&5.+<.$7.))(13.&40.(18.Vn,R4.)))P,(<.(9.=R5.)(9.R5.Vn,))(;.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(<.(=.$>.(?.$10.R9.(6.&40.+46;60.$7.)(11.Vmem0,Vdst,Vbs,R7.)Vrom,)(?.$10.R1.(6.&40.+46;9<.$7.)(11.Vmem0,Vdst,Vbs,(18.Vn,(1<.(18.Vn,R7.)+10.)))Vrom,))(<.(4.(1.&40.)(5.R1.(6.&5.+1.$7.))R8.)(<.(4.(1.&40.)(5.R1.(6.&5.+;.$7.))(8.Vsrc,(18.Vn,(1<.(18.Vn,R7.)+10.))))(<.(4.(1.&40.)(5.R1.(6.&5.+=.$7.))(8.Vdst,(18.Vn,(1<.(18.Vn,R7.)+10.))))(<.(4.(1.&40.)(5.R1.(6.&5.+<.$7.))(13.&40.(1<.(18.Vn,R7.)+10.)))(12.R9.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret k H1 H11 H13 H12 Hk.
    destruct (Z.lt_ge_cases (n - k) 16) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      eexists. split.
      + stepn F_43414 D_43414.                          (* [comment removed for export] *)
        stepb_tk F_43418 D_43418 ltac:(cond).           (* [comment removed for export] *)
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
      eapply (runs_trans RSEGS _ (fun r => mkst r (0x46b6c : word) (MK k) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src k /\ getr r 13 = at_ dst k
                         /\ getr r 12 = Z_to_bv 64 (n - k) /\ getr r 14 = Z_to_bv 64 15 /\ keeps regs r)).
      + eexists. split.
        * stepn F_43414 D_43414.                        (* [comment removed for export] *)
          stepb_ft F_43418 D_43418 ltac:(cond).         (* [comment removed for export] *)
          stepn F_4341c D_4341c.                        (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_keeps.
      + cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R11 & R13 & R12 & R14 & K1)).
        ddestruct (al_loop q r1 ret k R1 R11 R13 R12 R14 ltac:(lia) Hq) as (r2 & RUN & P).
        exists r2. rewrite <- Hk'. replace ((n - k) mod 16)%Z with (n - (k + 16 * (Z.of_nat q + 1)))%Z by lia.
        decompose [and] P. repeat split; try assumption. eapply keeps_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  
End AL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
