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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SumsLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import Sums2_code AsanIMemset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanIStrncpy () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a920"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a924"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a928"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a92c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a930"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a934"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a938"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a93c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a940"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a944"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a948"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a94c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a950"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a954"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a958"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a95c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a960"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a964"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a968"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a96c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a970"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a974"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a978"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a97c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a980"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a984"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a988"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums2_code.W_7a98c"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "ISTRNCPY.MZ"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.regs_agree"; "Stdlib.Lists.List.In"; "istrncpy_clob"; "RocqVerifyHarness.AgentSubmission.ABoot.SumsLib.memk"; "sealed8"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "strncpy_sealed_bytes"; "Corelib.Init.Datatypes.option"; "asan_sealed_src"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "asan_istrncpy_entry"].


(* [comment removed for export] *)
Definition istrncpy_words : list (bv 32) := ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "(0.(1.&20.)$2.(0.(1.&20.)$3.(0.(1.&20.)$4.(0.(1.&20.)$5.(0.(1.&20.)$6.(0.(1.&20.)$7.(0.(1.&20.)$8.(0.(1.&20.)$9.(0.(1.&20.)$:.(0.(1.&20.)$;.(0.(1.&20.)$<.(0.(1.&20.)$=.(0.(1.&20.)$>.(0.(1.&20.)$?.(0.(1.&20.)$10.(0.(1.&20.)$11.(0.(1.&20.)$12.(0.(1.&20.)$13.(0.(1.&20.)$14.(0.(1.&20.)$15.(0.(1.&20.)$16.(0.(1.&20.)$17.(0.(1.&20.)$18.(0.(1.&20.)$19.(0.(1.&20.)$1:.(0.(1.&20.)$1;.(0.(1.&20.)$1<.(0.(1.&20.)$1=.(1>.(1.&20.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition istrncpy_clob : list reg := [11; 12; 13; 14; 15].

(* [comment removed for export] *)
Definition sealed8 : list byte := ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "(0.(1.&8.)(1?.&8.+3<.)(0.(1.&8.)(1?.&8.+73.)(0.(1.&8.)(1?.&8.+65.)(0.(1.&8.)(1?.&8.+61.)(0.(1.&8.)(1?.&8.+6<.)(0.(1.&8.)(1?.&8.+65.)(0.(1.&8.)(1?.&8.+64.)(0.(1.&8.)(1?.&8.+3>.)(1>.(1.&8.))))))))))")
(* [comment removed for export] *).
Definition strncpy_sealed_bytes : list byte := sealed8 ++ zeros 4087.

Lemma length_strncpy_sealed_bytes : length strncpy_sealed_bytes = 4095%nat.
Proof. unfold strncpy_sealed_bytes. rewrite length_app, length_zeros. reflexivity. Qed.

Lemma sealed8_nz : forall j, (0 <= j < 8)%Z -> bv_unsigned (b_ sealed8 j) <> 0%Z.
Proof.
  intros j Hj.
  assert (E : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%Z) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst j; cbv; discriminate.
Qed.

(* [comment removed for export] *)
Lemma align15_4087 : forall d : word, align15 4087 d <> 0%Z.
Proof.
  intros d H. unfold align15 in H. rewrite Z.land_lor_distr_l in H.
  apply Z.lor_eq_0_iff in H as [H _]. cbv in H. discriminate.
Qed.

Section ISTRNCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 istrncpy_words.
  (* [comment removed for export] *)
  Hypothesis Hsrc : rdn segs mem0 src 8%nat = Some sealed8.
  Hypothesis Hnul : rdn segs mem0 (at_ src 8) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis Hsnw : (bv_unsigned src + 9 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Hok : store_ok segs mem0 dst 4095%nat = true.
  Hypothesis Hnw : (bv_unsigned dst + 4095 < 2 ^ 64)%Z.
  Hypothesis Hdisj : (bv_unsigned dst + 4095 <= bv_unsigned src \/ bv_unsigned src + 9 <= bv_unsigned dst)%Z.

  #[local] Abbreviation CL := (fun r => In r istrncpy_clob).

  (* [comment removed for export] *)
  Ltac condv :=
    rwH; rewrite ?at_addi; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
    first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; unorm; lia.

  (* [comment removed for export] *)
  #[using="Hsrc Hsnw Hok Hnw Hdisj"] Lemma HMC : cpyH segs mem0 dst src 8 sealed8.
  Proof.
    pose proof (u64_range dst). pose proof (u64_range src).
    apply CPYH.
    - lia.
    - reflexivity.
    - exact Hsrc.
    - cbn [length]. eapply (store_ok_sub segs mem0 dst dst 4095%nat 8%nat); [lia | exact Hok | lia | cbn; lia].
    - lia.
    - lia.
    - lia.
  Qed.

  #[local] Abbreviation MK := (memk mem0 dst sealed8).
  (* [comment removed for export] *)
  Definition MZ (k : Z) : word -> option byte := msetk (MK 8) (at_ dst 8) (Z_to_bv 8 0) k.

  #[using="Type"] Lemma MZ_0 : MZ 0 = MK 8.
  Proof. reflexivity. Qed.

  #[using="segs src Hsrc Hsnw Hok Hnw Hdisj"] Lemma MZ_final : MZ 4087 = wbytes mem0 dst strncpy_sealed_bytes.
  Proof.
    unfold MZ, msetk, strncpy_sealed_bytes, zeros. rewrite (memk_n _ _ _ _ _ _ HMC).
    rewrite wbytes_app. reflexivity.
  Qed.

  #[using="Hok Hnw"] Lemma MK8_ok : store_ok segs (MK 8) (at_ dst 8) (Z.to_nat 4087) = true.
  Proof.
    unfold memk. pose proof (u64_range dst).
    apply (store_ok_at segs mem0 dst 4095%nat); [lia | exact Hok | lia | cbn; lia].
  Qed.

  #[using="Hnw"] Lemma at8_nw : (bv_unsigned (at_ dst 8) + 4087 < 2 ^ 64)%Z.
  Proof. pose proof (u64_range dst). rewrite at_u by lia. lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at istrncpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60
                    & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HMC) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac mk_at kk := match goal with |- msteps _ (mkst _ _ (memk _ _ _ ?a) _) _ =>
                     first [constr_eq a kk | replace (memk mem0 dst sealed8 a) with (memk mem0 dst sealed8 kk) by (f_equal; lia)] end.
  Ltac msb F D kk :=
    mk_at kk;
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HMC) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; first [reflexivity | f_equal; lia] | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac mz_at kk := match goal with |- msteps _ (mkst _ _ (MZ ?a) _) _ =>
                     first [constr_eq a kk | replace (MZ a) with (MZ kk) by (f_equal; lia)] end.
  Ltac mzsb F D kk :=
    mz_at kk; unfold MZ;
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ (at_ dst 8) kk) (v := Z_to_bv 64 0) (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs (MK 8) (at_ dst 8) 4087 (Z_to_bv 8 0) ltac:(lia) at8_nw MK8_ok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 (MK 8) (at_ dst 8) (Z_to_bv 8 0) kk) by lia; fold (MZ (kk + 1)); vn.

  (* [comment removed for export] *)
  #[using="src HCODE Hsnw Hok Hnw"] Lemma fill_loop : ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "Pi,$20.Pregs,(21.&5.(1.&40.))Pret,(1.&40.)Pk,$22.P,(23.R2.)P,(24.(1.&40.)(25.R4.(26.&5.+1.$27.))R3.)P,(24.(1.&40.)(25.R5.(26.&5.+;.$27.))(28.Vdst,(29.+8.R3.)))P,(24.(1.&40.)(25.R6.(26.&5.+<.$27.))(28.Vdst,+???.))P,(2:.=R5.)P,(2;.(29.+8.R6.)+???.)P,(24.$22.(2<.R:.)(2=.(2=.(2=.+???.+8.)R7.)+1.))(2>.(21.&5.(1.&40.))Lregs',(21.&5.(1.&40.))(2?.(30.Vsegs,(31.$32.R;.(28.Vbase,+44.)(33.R9.)Vrom,)(31.$32.R1.R:.(33.+??7.)Vrom,))(34.Lr,(1.&5.)(35.(1.&5.)R1.$36.)R;.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H12 Hk Hkn Hi.
    - eexists. split.
      + mzsb C68 D_7a964 k.                                (* [comment removed for export] *)
        an C72 D_7a968.                                    (* [comment removed for export] *)
        ab_ft C76 D_7a96c ltac:(condz).                    (* [comment removed for export] *)
        an C80 D_7a970.                                    (* [comment removed for export] *)
        aret C108 D_7a98c ret.
        mz_at 4087%Z. apply mst_refl.
      + unfold istrncpy_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + (k + 1)) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
      + eexists. split.
        * mzsb C68 D_7a964 k.
          an C72 D_7a968.
          ab_tk C76 D_7a96c ltac:(condz).                  (* [comment removed for export] *)
          mz_at (k + 1)%Z. apply mst_refl.
        * post. unfold istrncpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="HCODE Hsrc Hsnw Hok Hnw Hdisj"] Lemma copy_iter : ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "Pregs,(21.&5.(1.&40.))Pj,$22.P,(24.(1.&40.)(25.R2.(26.&5.+:.$27.))Vdst,)P,(24.(1.&40.)(25.R3.(26.&5.+;.$27.))Vsrc,)P,(24.(1.&40.)(25.R4.(26.&5.+<.$27.))(1?.&40.+???.))P,(24.(1.&40.)(25.R5.(26.&5.+=.$27.))(1?.&40.R4.))P,(2?.(2:.=R5.)(2;.R5.+8.))(2>.(21.&5.(1.&40.))Lregs',(21.&5.(1.&40.))(2?.(30.Vsegs,(31.$32.R8.(28.Vbase,+8.)(37.Vmem0,Vdst,$38.R7.)Vrom,)(31.$32.R1.(28.Vbase,+8.)(37.Vmem0,Vdst,$38.(29.R7.+1.))Vrom,))(2?.(24.(1.&40.)(25.R1.(26.&5.+:.$27.))Vdst,)(2?.(24.(1.&40.)(25.R1.(26.&5.+;.$27.))Vsrc,)(2?.(24.(1.&40.)(25.R1.(26.&5.+<.$27.))(1?.&40.+???.))(2?.(24.(1.&40.)(25.R1.(26.&5.+=.$27.))(1?.&40.(29.R7.+1.)))(34.Lr,(1.&5.)(35.(1.&5.)R1.$36.)R8.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs j H10 H11 H12 H13 Hj. pose proof (u64_range dst). pose proof (u64_range src).
    eexists. split.
    - av C8 D_7a928 (at_ src j) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
      mlbu C12 D_7a92c j.                                              (* [comment removed for export] *)
      ab_ft C16 D_7a930
        ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; pose proof (u8_range (b_ sealed8 j));
              rewrite (u_Z2bv (bv_unsigned (b_ sealed8 j))) by lia; rewrite (u_Z2bv 0) by lia;
              apply sealed8_nz; lia).                                  (* [comment removed for export] *)
      av C20 D_7a934 (at_ dst j) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
      an C24 D_7a938.                                                  (* [comment removed for export] *)
      msb C28 D_7a93c j.                                               (* [comment removed for export] *)
      ab_tk C32 D_7a940 ltac:(condv).                                  (* [comment removed for export] *)
      mk_at (j + 1)%Z. apply mst_refl.
    - post; try (unfold istrncpy_clob; solve_regs_agree). unfold v_addi. unorm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="HCODE Hsrc Hsnw Hok Hnw Hdisj"] Lemma copy8 : ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "Pregs0,(21.&5.(1.&40.))Prr,(21.&5.(1.&40.))P,(34.Lr,(1.&5.)(35.(1.&5.)R1.$36.)R2.R1.)P,(24.(1.&40.)(25.R2.(26.&5.+:.$27.))Vdst,)P,(24.(1.&40.)(25.R3.(26.&5.+;.$27.))Vsrc,)P,(24.(1.&40.)(25.R4.(26.&5.+<.$27.))(1?.&40.+???.))P,(24.(1.&40.)(25.R5.(26.&5.+=.$27.))(1?.&40.=))(2>.(21.&5.(1.&40.))Lregs',(21.&5.(1.&40.))(2?.(30.Vsegs,(31.$32.R7.(28.Vbase,+8.)(37.Vmem0,Vdst,$38.=)Vrom,)(31.$32.R1.(28.Vbase,+8.)(37.Vmem0,Vdst,$38.+8.)Vrom,))(2?.(24.(1.&40.)(25.R1.(26.&5.+:.$27.))Vdst,)(2?.(24.(1.&40.)(25.R1.(26.&5.+;.$27.))Vsrc,)(2?.(24.(1.&40.)(25.R1.(26.&5.+<.$27.))(1?.&40.+???.))(2?.(24.(1.&40.)(25.R1.(26.&5.+=.$27.))(1?.&40.+8.))(34.Lr,(1.&5.)(35.(1.&5.)R1.$36.)R8.R1.)))))))")
(* [comment removed for export] *).
  Proof.
    intros regs0 rr K A B C D.
    Ltac cp_iter :=
      match goal with
      | K : regs_agree _ ?regs0 ?rr, A : getr ?rr 10 = _, B : getr ?rr 11 = _, C : getr ?rr 12 = _, D : getr ?rr 13 = Z_to_bv 64 ?v |- _ =>
        let jj := eval vm_compute in v in
        let jj1 := eval vm_compute in (v + 1)%Z in
        change (Z_to_bv 64 v) with (Z_to_bv 64 jj) in D;
        try change (memk mem0 dst sealed8 v) with (memk mem0 dst sealed8 jj);
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK jj1) rom)
                 (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                           /\ getr r 13 = Z_to_bv 64 jj1 /\ regs_agree CL regs0 r));
        [ destruct (copy_iter rr jj A B C D ltac:(lia)) as (r' & RUN & B10 & B11 & B12 & B13 & K');
          exists r'; split; [exact RUN | repeat split; try assumption; eapply regs_agree_trans; [exact K | exact K']]
        | cbv beta; clear rr K A B C D; intros rr (A & B & C & D & K) ]
      end.
    do 8 cp_iter.
    exists rr. split; [apply mst_refl | repeat split; assumption].
  Qed.

  #[using="HCODE Hsrc Hnul Hsnw Hok Hnw Hdisj"] Theorem istrncpy_run : ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "Pregs,(21.&5.(1.&40.))Pret,(1.&40.)P,(23.R1.)P,(24.(1.&40.)(25.R3.(26.&5.+1.$27.))R2.)P,(24.(1.&40.)(25.R4.(26.&5.+:.$27.))Vdst,)P,(24.(1.&40.)(25.R5.(26.&5.+;.$27.))Vsrc,)P,(24.(1.&40.)(25.R6.(26.&5.+<.$27.))(1?.&40.+???.))(2>.(21.&5.(1.&40.))Lregs',(21.&5.(1.&40.))(2?.(30.Vsegs,(31.$32.R8.(28.Vbase,=)Vmem0,Vrom,)(31.$32.R1.R7.(39.Vmem0,Vdst,$3:.)Vrom,))(34.Lr,(1.&5.)(35.(1.&5.)R1.$36.)R8.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs.
    rewrite <- MZ_final.
    change (mkst regs (at_ base 0) mem0 rom) with (mkst regs (at_ base 0) (MK 0) rom).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 0) rom)
             (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                       /\ getr r 13 = Z_to_bv 64 0 /\ regs_agree CL regs r)).
    { eexists. split.
      - ab_ft C0 D_7a920 ltac:(condz).                                  (* [comment removed for export] *)
        an C4 D_7a924.                                                   (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold istrncpy_clob. solve_regs_agree. }
    cbv beta. intros r0 (A10 & A11 & A12 & A13 & K0).
    (* [comment removed for export] *)
    destruct (copy8 regs r0 K0 A10 A11 A12 A13) as (r8 & RUN8 & L10 & L11 & L12 & L13 & K8).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MK 8) rom)
             (fun r => getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 4095
                       /\ getr r 13 = Z_to_bv 64 8 /\ regs_agree CL regs r)).
    { exists r8. split; [exact RUN8 | repeat split; assumption]. }
    cbv beta. clear r8 RUN8 L10 L11 L12 L13 K8. intros r8 (L10 & L11 & L12 & L13 & K8).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 68) (MZ 0) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = at_ dst (8 + 0) /\ getr r 12 = at_ dst 4095 /\ regs_agree CL regs r)).
    { eexists. split.
      - av C8 D_7a928 (at_ src 8) ltac:(apply v_add_at; lia).         (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 0);
            [exact C12 | reflexivity | exact D_7a92c
            | gres; rwH; imm_norm; rewrite at_addi; replace (at_ src (8 + 0)) with (at_ src 8) by (f_equal; lia);
              unfold memk; change (firstn (Z.to_nat 8) sealed8) with sealed8;
              rewrite rdn_wbytes_out;
              [ exact Hnul
              | change (length sealed8) with 8%nat; rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | rewrite at_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | change (length sealed8) with 8%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ] ]
          | step_simpl]; vn.                                             (* [comment removed for export] *)
        ab_tk C16 D_7a930 ltac:(condz).                                (* [comment removed for export] *)
        change (memk mem0 dst sealed8 8) with (MZ 0).
        av C40 D_7a948 (at_ dst 8) ltac:(apply v_add_at; lia).          (* [comment removed for export] *)
        an C44 D_7a94c.                                                  (* [comment removed for export] *)
        (* [comment removed for export] *)
        an C48 D_7a950.
        av C52 D_7a954 (Z_to_bv 64 (align15 4087 (at_ dst 8)))
           ltac:(rewrite <- (u_align15 4087 (at_ dst 8)) by lia; symmetry; apply Z_to_bv_bv_unsigned).
        pose proof (align15_4087 (at_ dst 8)) as HA. pose proof (align15_range 4087 (at_ dst 8) ltac:(lia)) as HAR.
        ab_ft C56 D_7a958 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; rewrite !u_Z2bv by lia; exact HA).
        ab_ft C60 D_7a95c ltac:(condz).                                 (* [comment removed for export] *)
        av C64 D_7a960 (at_ dst 4095) ltac:(apply v_add_at; lia).       (* [comment removed for export] *)
        apply mst_refl.
      - post.
        + rewrite <- H1. apply K8. unfold istrncpy_clob. cbn. intros [X|[X|[X|[X|[X|[]]]]]]; discriminate.
        + unfold istrncpy_clob in *. ra_chain. }
    cbv beta. intros r9 (M1 & M11 & M12 & K9).
    destruct (fill_loop (Z.to_nat 4086) r9 ret 0 Hret M1 M11 M12 ltac:(lia) ltac:(lia) ltac:(lia)) as (r10 & RUN & K10).
    exists r10. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End ISTRNCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_istrncpy_entry : word := 0x7ae84.
Definition asan_sealed_src : Z := 0x11d57. (* [comment removed for export] *)

Lemma asan_istrncpy_code :
  code_at AsanUbsan.M.loaded_segments asan_istrncpy_entry 0 istrncpy_words.
Proof. unfold istrncpy_words. code_at_vm. Qed.

(* [comment removed for export] *)
Lemma asan_sealed_src_img : ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "Pmem,Px,(1.&40.)(3;.(1.&8.))P,Pi,$22.P,(2?.(2:.$3<.R1.)(2;.R1.(29.$3<.+9.)))(24.(3;.(1.&8.))A1.R3.(1?.&40.R2.)(3=.(1.&8.)))(2?.(24.(3;.(3>.(1.&8.)))(3?.$40.R2.(1?.&40.$3<.)#8.)(41.(3>.(1.&8.))$38.))(24.(3;.(3>.(1.&8.)))(3?.$40.R2.(28.(1?.&40.$3<.)+8.)#1.)(41.(3>.(1.&8.))(0.(1.&8.)(1?.&8.=)(1>.(1.&8.))))))")
(* [comment removed for export] *).
Proof.
  intros mem Hnone. unfold asan_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; cbn; lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.

Theorem asan_istrncpy_sealed : ltac2:(CDefT.buildp (gd_tbl_AsanIStrncpy ()) "Pmem0,Px,(1.&40.)(3;.(1.&8.))Pdst,(1.&40.)Prom,P,(1.&40.)(3;.(1.&8.))Pregs,(21.&5.(1.&40.))Pret,(1.&40.)P,Pi,$22.P,(2?.(2:.$3<.R1.)(2;.R1.(29.$3<.+9.)))(24.(3;.(1.&8.))A1.R7.(1?.&40.R2.)(3=.(1.&8.)))P,(24.$42.(43.$40.R6.R5.#???.)$44.)P,(2;.(29.(45.&40.R6.)+???.)(46.+2.+40.))P,(47.(2:.(29.(45.&40.R7.)+???.)$3<.)(2:.(29.$3<.+9.)(45.&40.R7.)))P,(23.R5.)P,(24.(1.&40.)(25.R7.(26.&5.+1.$27.))R6.)P,(24.(1.&40.)(25.R8.(26.&5.+:.$27.))R:.)P,(24.(1.&40.)(25.R9.(26.&5.+;.$27.))(1?.&40.$3<.))P,(24.(1.&40.)(25.R:.(26.&5.+<.$27.))(1?.&40.+???.))(2>.(21.&5.(1.&40.))Lregs',(21.&5.(1.&40.))(2?.(30.$40.(31.$32.R<.$48.R?.R=.)(31.$32.R1.R;.(39.R?.R>.$3:.)R=.))(34.Lr,(1.&5.)(35.(1.&5.)R1.$36.)R<.R1.)))")
(* [comment removed for export] *).
Proof.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (asan_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite <- (at_0 asan_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 asan_sealed_src) rom asan_istrncpy_code Hs Hn); try assumption;
    unfold asan_sealed_src in *; u_norm; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
