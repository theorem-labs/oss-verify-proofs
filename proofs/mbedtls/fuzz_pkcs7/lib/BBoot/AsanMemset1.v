(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import MemsetLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMemset_code.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMemset1 () : Init.string Init.list := ["LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMemset_code.ms_base"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.cfill"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.cbyte"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.ms_agree"; "Stdlib.ZArith.BinInt.Z.le"; "Walk.L2"; "Walk.L6"; "Walk.L8"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Walk.Aligned.LC"; "Stdlib.ZArith.BinInt.Z.lt"; "Walk.Aligned.LB"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.c32"; "Walk.Aligned.LD"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.ABoot.MemsetLib.c64"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.option"].


(* [comment removed for export] *)
#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
(* [comment removed for export] *)
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
(* [comment removed for export] *)
#[local] Ltac cond :=
  rwH; unfold c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
(* [comment removed for export] *)
#[local] Ltac pclits :=
  repeat match goal with
         | |- context [Z_to_bv 64 (ms_base + ?o)%Z] => wlit_replace (Z_to_bv 64 (ms_base + o)%Z)
         end.
(* [comment removed for export] *)
#[local] Ltac stepat L F D vv tac :=
  chain_step; [reflexivity | eapply L with (v := vv); [exact F | reflexivity | exact D | reflexivity | tac] | step_simpl].

Section Walk.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

  (* [comment removed for export] *)
  #[local] Ltac msb F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sb MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | lia | lia]
      | step_simpl].
  #[local] Ltac msw F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sw MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb4_c32
        | lia | lia]
      | step_simpl].
  #[local] Ltac msd F D oo :=
    chain_step; [reflexivity
      | eapply (cf_sd MSEGS mem0 d n cv Hnw Hok) with (o := oo);
        [exact F | reflexivity | exact D
        | gres; rwH; rewrite ?at_addi; reflexivity
        | imm_norm; lia
        | gres; rwH; reflexivity
        | apply wleb8_c64
        | lia | lia]
      | step_simpl].
  (* [comment removed for export] *)
  #[local] Ltac mret := stepret Fo_0f4 Do_0f4 ret ltac:(rwH; reflexivity).
  (* [comment removed for export] *)
  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; solve_ms_agree.

  (* [comment removed for export] *)
  Definition L2 : list (Z * Z) := [(n-1,1); (0,1)]%Z.
  Definition L6 : list (Z * Z) := [(n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.
  Definition L8 : list (Z * Z) := [(n-4,1); (3,1); (n-2,1); (n-3,1); (2,1); (1,1); (n-1,1); (0,1)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hn Hret"] Lemma A_exit0 : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+1.$5.))Vret,)P,(2.$8.Vn,=)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R7.(7.&40.(?.$10.=))(11.Vmem0,Vd,Vn,(12.Vcv,)(13.(14.$8.$8.)))Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)(13.(14.$8.$8.)))Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R7.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_tk Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  #[using="Hn Hnw Hok Hret"] Lemma A_exit2 : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+1.$5.))Vret,)P,(:.(16.+1.Vn,)(16.Vn,+2.))(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R7.(7.&40.(?.$10.=))(11.Vmem0,Vd,Vn,(12.Vcv,)(13.(14.$8.$8.)))Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)$17.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R7.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).          (* [comment removed for export] *)
      msb Fo_004 Do_004 0%Z.                         (* [comment removed for export] *)
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
      stepn Fo_00c Do_00c.                           (* [comment removed for export] *)
      msb Fo_010 Do_010 (n-1)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_014 Do_014 ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  #[using="Hn Hnw Hok Hret"] Lemma A_exit6 : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+1.$5.))Vret,)P,(:.(16.+3.Vn,)(16.Vn,+6.))(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R7.(7.&40.(?.$10.=))(11.Vmem0,Vd,Vn,(12.Vcv,)(13.(14.$8.$8.)))Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)$18.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R7.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.                         (* [comment removed for export] *)
      msb Fo_01c Do_01c 2%Z.                         (* [comment removed for export] *)
      stepn Fo_020 Do_020.                           (* [comment removed for export] *)
      msb Fo_024 Do_024 (n-3)%Z.                     (* [comment removed for export] *)
      msb Fo_028 Do_028 (n-2)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_02c Do_02c ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  #[using="Hn Hnw Hok Hret"] Lemma A_exit8 : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+1.$5.))Vret,)P,(:.(16.+7.Vn,)(16.Vn,+8.))(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R7.(7.&40.(?.$10.=))(11.Vmem0,Vd,Vn,(12.Vcv,)(13.(14.$8.$8.)))Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)$19.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R7.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_ft Fo_02c Do_02c ltac:(cond).
      msb Fo_030 Do_030 3%Z.                         (* [comment removed for export] *)
      stepn Fo_034 Do_034.                           (* [comment removed for export] *)
      msb Fo_038 Do_038 (n-4)%Z.                     (* [comment removed for export] *)
      stepb_tk Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      mret.
      apply mst_refl.
    - post.
  Qed.

  #[using="Hn Hnw Hok"] Lemma A_cont : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R7.(7.&40.(?.$10.=))(11.Vmem0,Vd,Vn,(12.Vcv,)(13.(14.$8.$8.)))Vrom,)(=.$>.R1.(7.&40.(?.$10.+40.))(11.Vmem0,Vd,Vn,(12.Vcv,)$19.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(:.(2.(1.&40.)(3.R1.(4.&5.+;.$5.))Vcv,)(:.(2.(1.&40.)(3.R1.(4.&5.+<.$5.))(7.&40.Vn,))(:.(2.(1.&40.)(3.R1.(4.&5.+=.$5.))(6.Vd,Vn,))(:.(2.(1.&40.)(3.R1.(4.&5.+?.$5.))(7.&40.+9.))(:.(2.(1.&40.)(3.R1.(4.&5.+1.$5.))Vret,)(15.R7.R1.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros regs H10 H11 H12 H1 Hc. pose proof (u64_range d) as Hd. pclits.
    eexists. split.
    - stepb_ft Fo_000 Do_000 ltac:(cond).
      msb Fo_004 Do_004 0%Z.
      stepiv Fo_008 Do_008 (at_ d n) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).
      stepn Fo_00c Do_00c.
      msb Fo_010 Do_010 (n-1)%Z.
      stepb_ft Fo_014 Do_014 ltac:(cond).
      msb Fo_018 Do_018 1%Z.
      msb Fo_01c Do_01c 2%Z.
      stepn Fo_020 Do_020.
      msb Fo_024 Do_024 (n-3)%Z.
      msb Fo_028 Do_028 (n-2)%Z.
      stepb_ft Fo_02c Do_02c ltac:(cond).
      msb Fo_030 Do_030 3%Z.
      stepn Fo_034 Do_034.
      msb Fo_038 Do_038 (n-4)%Z.
      stepb_ft Fo_03c Do_03c ltac:(cond).          (* [comment removed for export] *)
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section Aligned.
    Variables k n1 : Z.
    Hypothesis Hk : (0 <= k <= 3)%Z.
    Hypothesis Hn1 : (n - k - 3 <= n1 <= n - k)%Z.
    Hypothesis Hkv : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 k.
    Hypothesis Hn1v : v_andi (Z_to_bv 64 (n - k)) (-4) = Z_to_bv 64 n1.

    Definition LB : list (Z * Z) := ((k+n1-4,4) :: (k,4) :: L8)%Z.
    Definition LC : list (Z * Z) := ((k+n1-8,4) :: (k+n1-12,4) :: (k+8,4) :: (k+4,4) :: LB)%Z.
    Definition LD (s4 : Z) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "(1:.(14.$8.$8.)(1;.$8.$8.(1<.(?.Vk,Vn1,)+10.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(1<.(?.Vk,Vn1,)+14.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(1<.(?.Vk,Vn1,)+18.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(1<.(?.Vk,Vn1,)+1<.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(?.Vk,+18.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(?.Vk,+14.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(?.Vk,+10.)+4.)(1:.(14.$8.$8.)(1;.$8.$8.(?.Vk,+<.)+4.)$1=.))))))))")
(* [comment removed for export] *).

    #[local] Ltac blockB :=
      stepn Fo_040 Do_040;                           (* [comment removed for export] *)
      stepn Fo_044 Do_044;                           (* [comment removed for export] *)
      stepn Fo_048 Do_048;                           (* [comment removed for export] *)
      stepiv Fo_04c Do_04c (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; rewrite at_0; exact Hkv);   (* [comment removed for export] *)
      stepn Fo_050 Do_050;                           (* [comment removed for export] *)
      stepiv Fo_054 Do_054 (Z_to_bv 64 (n - k)) ltac:(gres; rwH; apply ms_v_sub_ZZ; lia);          (* [comment removed for export] *)
      stepiv Fo_058 Do_058 (at_ d k) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia);  (* [comment removed for export] *)
      stepn Fo_05c Do_05c;                           (* [comment removed for export] *)
      stepiv Fo_060 Do_060 (Z_to_bv 64 n1) ltac:(gres; rwH; imm_norm; exact Hn1v);              (* [comment removed for export] *)
      stepat ms_step_mulhu_at Fo_064 Do_064 (c32 cv) ltac:(gres; rwH; apply mulhu_c32; unorm; reflexivity);  (* [comment removed for export] *)
      msw Fo_068 Do_068 k;                           (* [comment removed for export] *)
      stepiv Fo_06c Do_06c (at_ d (k + n1)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; reflexivity);  (* [comment removed for export] *)
      msw Fo_070 Do_070 (k + n1 - 4)%Z.              (* [comment removed for export] *)

    #[using="Hnw Hok Hret Hk Hn1 Hkv Hn1v"] Lemma B_exit : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+=.$5.))(6.Vd,Vn,))P,(2.(1.&40.)(3.R5.(4.&5.+?.$5.))(7.&40.+9.))P,(2.(1.&40.)(3.R6.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(1>.Vn1,+9.)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R:.(7.&40.(?.$10.+40.))(11.Vmem0,Vd,Vn,(12.Vcv,)$19.)Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)$1?.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R:.R1.))))")
(* [comment removed for export] *).
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_tk Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        mret.
        apply mst_refl.
      - post.
    Qed.

    #[using="Hnw Hok Hk Hn1 Hkv Hn1v"] Lemma B_cont : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))Vcv,)P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(7.&40.Vn,))P,(2.(1.&40.)(3.R4.(4.&5.+=.$5.))(6.Vd,Vn,))P,(2.(1.&40.)(3.R5.(4.&5.+?.$5.))(7.&40.+9.))P,(2.(1.&40.)(3.R6.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(16.+9.Vn1,)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R:.(7.&40.(?.$10.+40.))(11.Vmem0,Vd,Vn,(12.Vcv,)$19.)Vrom,)(=.$>.R1.(7.&40.(?.$10.+78.))(11.Vmem0,Vd,Vn,(12.Vcv,)$1?.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(:.(2.(1.&40.)(3.R1.(4.&5.+;.$5.))(6.Vd,Vk,))(:.(2.(1.&40.)(3.R1.(4.&5.+<.$5.))(20.Vcv,))(:.(2.(1.&40.)(3.R1.(4.&5.+=.$5.))(6.Vd,(?.Vk,Vn1,)))(:.(2.(1.&40.)(3.R1.(4.&5.+>.$5.))(7.&40.Vn1,))(:.(2.(1.&40.)(3.R1.(4.&5.+1.$5.))Vret,)(15.R:.R1.)))))))))")
(* [comment removed for export] *).
    Proof.
      intros regs H10 H11 H12 H13 H15 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockB.
        stepb_ft Fo_074 Do_074 ltac:(cond).        (* [comment removed for export] *)
        apply mst_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    #[local] Ltac blockC :=
      msw Fo_078 Do_078 (k + 4)%Z;                   (* [comment removed for export] *)
      msw Fo_07c Do_07c (k + 8)%Z;                   (* [comment removed for export] *)
      stepn Fo_080 Do_080;                           (* [comment removed for export] *)
      msw Fo_084 Do_084 (k + n1 - 12)%Z;             (* [comment removed for export] *)
      msw Fo_088 Do_088 (k + n1 - 8)%Z.              (* [comment removed for export] *)

    #[using="Hnw Hok Hret Hk Hn1"] Lemma C_exit : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))(6.Vd,Vk,))P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(20.Vcv,))P,(2.(1.&40.)(3.R4.(4.&5.+=.$5.))(6.Vd,(?.Vk,Vn1,)))P,(2.(1.&40.)(3.R5.(4.&5.+>.$5.))(7.&40.Vn1,))P,(2.(1.&40.)(3.R6.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(16.+<.Vn1,)P,(1>.Vn1,+19.)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R;.(7.&40.(?.$10.+78.))(11.Vmem0,Vd,Vn,(12.Vcv,)$1?.)Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)$1=.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R;.R1.))))")
(* [comment removed for export] *).
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_tk Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        mret.
        apply mst_refl.
      - post.
    Qed.

    #[using="Hnw Hok Hk Hn1"] Lemma C_cont : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))(6.Vd,Vk,))P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(20.Vcv,))P,(2.(1.&40.)(3.R4.(4.&5.+=.$5.))(6.Vd,(?.Vk,Vn1,)))P,(2.(1.&40.)(3.R5.(4.&5.+>.$5.))(7.&40.Vn1,))P,(2.(1.&40.)(3.R6.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(16.+19.Vn1,)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R:.(7.&40.(?.$10.+78.))(11.Vmem0,Vd,Vn,(12.Vcv,)$1?.)Vrom,)(=.$>.R1.(7.&40.(?.$10.+90.))(11.Vmem0,Vd,Vn,(12.Vcv,)$1=.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(:.(2.(1.&40.)(3.R1.(4.&5.+;.$5.))(6.Vd,Vk,))(:.(2.(1.&40.)(3.R1.(4.&5.+<.$5.))(20.Vcv,))(:.(2.(1.&40.)(3.R1.(4.&5.+=.$5.))(6.Vd,(?.Vk,Vn1,)))(:.(2.(1.&40.)(3.R1.(4.&5.+>.$5.))(7.&40.Vn1,))(:.(2.(1.&40.)(3.R1.(4.&5.+1.$5.))Vret,)(15.R:.R1.)))))))))")
(* [comment removed for export] *).
    Proof.
      intros regs H10 H11 H12 H13 H14 H1 Hn9 Hc. pose proof (u64_range d) as Hd. pclits.
      eexists. split.
      - blockC.
        stepb_ft Fo_08c Do_08c ltac:(cond).        (* [comment removed for export] *)
        apply mst_refl.
      - post.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)

    Section D.
      Variable s4 : Z.
      Hypothesis Hs4 : (s4 = 0 \/ s4 = 4)%Z.
      Hypothesis Hs4v : v_andi (at_ d k) 4 = Z_to_bv 64 s4.

      #[local] Ltac blockD :=
        msw Fo_090 Do_090 (k + 12)%Z;                (* [comment removed for export] *)
        msw Fo_094 Do_094 (k + 16)%Z;                (* [comment removed for export] *)
        msw Fo_098 Do_098 (k + 20)%Z;                (* [comment removed for export] *)
        msw Fo_09c Do_09c (k + 24)%Z;                (* [comment removed for export] *)
        stepiv Fo_0a0 Do_0a0 (Z_to_bv 64 s4) ltac:(gres; rwH; imm_norm; exact Hs4v);          (* [comment removed for export] *)
        stepn Fo_0a4 Do_0a4;                         (* [comment removed for export] *)
        stepiv Fo_0a8 Do_0a8 (Z_to_bv 64 (s4 + 24)) ltac:(gres; rwH; imm_norm; apply ms_v_addi_Z; lia);  (* [comment removed for export] *)
        stepiv Fo_0ac Do_0ac (Z_to_bv 64 (n1 - s4 - 24)) ltac:(gres; rwH; rewrite ms_v_sub_ZZ by lia; f_equal; lia);  (* [comment removed for export] *)
        msw Fo_0b0 Do_0b0 (k + n1 - 28)%Z;           (* [comment removed for export] *)
        msw Fo_0b4 Do_0b4 (k + n1 - 24)%Z;           (* [comment removed for export] *)
        msw Fo_0b8 Do_0b8 (k + n1 - 20)%Z;           (* [comment removed for export] *)
        msw Fo_0bc Do_0bc (k + n1 - 16)%Z.           (* [comment removed for export] *)

      #[using="Hnw Hok Hret Hk Hn1 Hs4 Hs4v"] Lemma D_exit : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))(6.Vd,Vk,))P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(20.Vcv,))P,(2.(1.&40.)(3.R4.(4.&5.+=.$5.))(6.Vd,(?.Vk,Vn1,)))P,(2.(1.&40.)(3.R5.(4.&5.+>.$5.))(7.&40.Vn1,))P,(2.(1.&40.)(3.R6.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(16.+1<.Vn1,)P,(1>.(1<.(1<.Vn1,Vs4,)+18.)+20.)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R;.(7.&40.(?.$10.+90.))(11.Vmem0,Vd,Vn,(12.Vcv,)$1=.)Vrom,)(=.$>.R1.Vret,(11.Vmem0,Vd,Vn,(12.Vcv,)(21.Vs4,))Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(15.R;.R1.))))")
(* [comment removed for export] *).
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_tk Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          mret.
          apply mst_refl.
        - post.
      Qed.

      #[using="Hnw Hok Hk Hn1 Hs4 Hs4v"] Lemma D_cont : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))P,(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R2.(4.&5.+;.$5.))(6.Vd,Vk,))P,(2.(1.&40.)(3.R3.(4.&5.+<.$5.))(20.Vcv,))P,(2.(1.&40.)(3.R4.(4.&5.+=.$5.))(6.Vd,(?.Vk,Vn1,)))P,(2.(1.&40.)(3.R5.(4.&5.+>.$5.))(7.&40.Vn1,))P,(2.(1.&40.)(3.R6.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(16.+1<.Vn1,)P,(16.+20.(1<.(1<.Vn1,Vs4,)+18.))(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R;.(7.&40.(?.$10.+90.))(11.Vmem0,Vd,Vn,(12.Vcv,)$1=.)Vrom,)(=.$>.R1.(7.&40.(?.$10.+<4.))(11.Vmem0,Vd,Vn,(12.Vcv,)(21.Vs4,))Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(:.(2.(1.&40.)(3.R1.(4.&5.+;.$5.))(6.Vd,Vk,))(:.(2.(1.&40.)(3.R1.(4.&5.+<.$5.))(20.Vcv,))(:.(2.(1.&40.)(3.R1.(4.&5.+>.$5.))(7.&40.(1<.(1<.Vn1,Vs4,)+18.)))(:.(2.(1.&40.)(3.R1.(4.&5.+?.$5.))(7.&40.(?.Vs4,+18.)))(:.(2.(1.&40.)(3.R1.(4.&5.+1.$5.))Vret,)(15.R;.R1.)))))))))")
(* [comment removed for export] *).
      Proof.
        intros regs H10 H11 H12 H13 H14 H1 Hn9 Hn1' Hc. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - blockD.
          stepb_ft Fo_0c0 Do_0c0 ltac:(cond).      (* [comment removed for export] *)
          apply mst_refl.
        - post.
      Qed.

      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (* [comment removed for export] *)

      #[using="Hs4"] Lemma E_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))PL,(22.(14.$8.$8.))P,(2.(1.&40.)(3.R2.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R3.(4.&5.+;.$5.))(6.Vd,Vk,))P,(2.(1.&40.)(3.R4.(4.&5.+<.$5.))(20.Vcv,))P,(2.(1.&40.)(3.R5.(4.&5.+>.$5.))(7.&40.(1<.(1<.Vn1,Vs4,)+18.)))P,(2.(1.&40.)(3.R6.(4.&5.+?.$5.))(7.&40.(?.Vs4,+18.)))P,(2.(1.&40.)(3.R7.(4.&5.+1.$5.))Vret,)P,(16.+9.Vn,)P,(16.+1<.Vn1,)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R;.(7.&40.(?.$10.+<4.))(11.Vmem0,Vd,Vn,(12.Vcv,)R:.)Vrom,)(=.$>.R1.(7.&40.(?.$10.+=8.))(11.Vmem0,Vd,Vn,(12.Vcv,)R:.)Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(:.(2.(1.&40.)(3.R1.(4.&5.+;.$5.))(6.Vd,(?.(?.Vk,Vs4,)+18.)))(:.(2.(1.&40.)(3.R1.(4.&5.+<.$5.))(23.Vcv,))(:.(2.(1.&40.)(3.R1.(4.&5.+=.$5.))(7.&40.+1?.))(:.(2.(1.&40.)(3.R1.(4.&5.+>.$5.))(7.&40.(1<.(1<.Vn1,Vs4,)+18.)))(:.(2.(1.&40.)(3.R1.(4.&5.+1.$5.))Vret,)(15.R;.R1.)))))))))")
(* [comment removed for export] *).
      Proof.
        intros regs L H10 H11 H12 H14 H15 H1 Hn9 Hn1'. pose proof (u64_range d) as Hd. pclits.
        eexists. split.
        - stepiv Fo_0c4 Do_0c4 (c32h cv) ltac:(gres; rwH; imm_norm; apply slli32_c32).             (* [comment removed for export] *)
          stepiv Fo_0c8 Do_0c8 (at_ d (k + s4 + 24)) ltac:(gres; rwH; rewrite ms_v_add_at_Z by lia; f_equal; lia).  (* [comment removed for export] *)
          stepiv Fo_0cc Do_0cc (c32 cv) ltac:(gres; rwH; imm_norm; apply srli32_c32h);             (* [comment removed for export] *)
          stepat ms_step_or_at Fo_0d0 Do_0d0 (c64 cv) ltac:(gres; rwH; apply or_c64).                 (* [comment removed for export] *)
          stepn Fo_0d4 Do_0d4.                       (* [comment removed for export] *)
          apply mst_refl.
        - post.
      Qed.
    End D.
  End Aligned.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Ltac ms_cov_eq :=
    intros i Hi; rewrite !ms_cov_cons;
    match goal with |- _ = ?rhs => match rhs with context [ms_cov ?L i] => destruct (ms_cov L i) end end;
    rewrite ?orb_true_r, ?orb_false_r; [reflexivity|];
    apply eq_true_iff_eq; rewrite !orb_true_iff, !ms_inb_true; lia.

  (* [comment removed for export] *)
  #[using="Hnw Hok"] Lemma loop_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pq,$24.Pregs,(0.&5.(1.&40.))PL,(22.(14.$8.$8.))Pa,$8.Pr,$8.P,(2.(1.&40.)(3.R4.(4.&5.+:.$5.))(6.Vd,=))P,(2.(1.&40.)(3.R5.(4.&5.+;.$5.))(6.Vd,R3.))P,(2.(1.&40.)(3.R6.(4.&5.+<.$5.))(23.Vcv,))P,(2.(1.&40.)(3.R7.(4.&5.+=.$5.))(7.&40.+1?.))P,(2.(1.&40.)(3.R8.(4.&5.+>.$5.))(7.&40.R5.))P,(2.(1.&40.)(3.R9.(4.&5.+1.$5.))Vret,)P,(16.=R8.)P,(16.(?.R9.R8.)Vn,)P,(:.(16.(25.+20.(?.(26.R=.)+1.))R9.)(1>.R9.(?.(25.+20.(?.(26.R=.)+1.))+20.)))(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R>.(7.&40.(?.$10.+=8.))(11.Vmem0,Vd,Vn,(12.Vcv,)R=.)Vrom,)(=.$>.R1.(7.&40.(?.$10.+?4.))(11.Vmem0,Vd,Vn,(12.Vcv,)(1:.(14.$8.$8.)(1;.$8.$8.R<.(25.+20.(?.(26.R?.)+1.)))R=.))Vrom,))(:.(2.(1.&40.)(3.R1.(4.&5.+:.$5.))(6.Vd,=))(:.(2.(1.&40.)(3.R1.(4.&5.+1.$5.))Vret,)(15.R>.R1.)))))")
(* [comment removed for export] *).
  Proof.
    induction q as [|q IH]; intros regs L a r H10 H11 H12 H13 H14 H1 Ha Har Hq;
      pose proof (u64_range d) as Hd; pclits.
    - (* [comment removed for export] *)
      eexists. split.
      + msd Fo_0d8 Do_0d8 a.                         (* [comment removed for export] *)
        msd Fo_0dc Do_0dc (a + 8)%Z.                 (* [comment removed for export] *)
        msd Fo_0e0 Do_0e0 (a + 16)%Z.                (* [comment removed for export] *)
        msd Fo_0e4 Do_0e4 (a + 24)%Z.                (* [comment removed for export] *)
        stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).  (* [comment removed for export] *)
        stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).               (* [comment removed for export] *)
        stepb_ft Fo_0f0 Do_0f0 ltac:(cond).        (* [comment removed for export] *)
        replace (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z
          with (CF ((a, 32 * (Z.of_nat 0 + 1))%Z :: L)) by (apply cfill_ext; ms_cov_eq).
        apply mst_refl.
      + post.
    - eapply (runs_trans MSEGS _
                (fun rg => mkst rg (PC 0xd8) (CF ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L))%Z rom)
                (fun rg => getr rg 10 = at_ d 0 /\ getr rg 11 = at_ d (a + 32) /\ getr rg 12 = c64 cv
                           /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32) /\ getr rg 1 = ret
                           /\ ms_agree regs rg)).
      + cbv beta. pclits. eexists. split.
        * msd Fo_0d8 Do_0d8 a.
          msd Fo_0dc Do_0dc (a + 8)%Z.
          msd Fo_0e0 Do_0e0 (a + 16)%Z.
          msd Fo_0e4 Do_0e4 (a + 24)%Z.
          stepiv Fo_0e8 Do_0e8 (Z_to_bv 64 (r - 32)) ltac:(gres; rwH; imm_norm; rewrite ms_v_addi_Z by lia; f_equal; lia).
          stepiv Fo_0ec Do_0ec (at_ d (a + 32)) ltac:(gres; rwH; imm_norm; rewrite at_addi; reflexivity).
          stepb_tk Fo_0f0 Do_0f0 ltac:(cond).      (* [comment removed for export] *)
          apply mst_refl.
        * post.
      + cbv beta. intros r1 (R10 & R11 & R12 & R13 & R14 & R1 & AG).
        destruct (IH r1 ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z (a + 32)%Z (r - 32)%Z
                    R10 R11 R12 R13 R14 R1 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P10 & P1 & AG2).
        exists r2. split.
        * replace (CF ((a, 32 * (Z.of_nat (S q) + 1))%Z :: L))
            with (CF ((a + 32, 32 * (Z.of_nat q + 1))%Z :: ((a + 24, 8) :: (a + 16, 8) :: (a + 8, 8) :: (a, 8) :: L)%Z))
            by (apply cfill_ext; ms_cov_eq).
          revert RUN. pclits. intros RUN. exact RUN.
        * repeat split; try assumption. eapply ms_agree_trans; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Hret"] Lemma ret_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemset1 ()) "Pregs,(0.&5.(1.&40.))PM,P,(1.&40.)(27.(1.&8.))P,(2.(1.&40.)(3.R2.(4.&5.+1.$5.))Vret,)(9.(0.&5.(1.&40.))Lregs',(0.&5.(1.&40.))(:.(;.$<.(=.$>.R4.(7.&40.(?.$10.+?4.))R3.Vrom,)(=.$>.R1.Vret,R3.Vrom,))(2.(0.&5.(1.&40.))R1.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros regs M H1. pclits. eexists. split.
    - mret. apply mst_refl.
    - reflexivity.
  Qed.

End Walk.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
