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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SumsLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import Sums_code.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanIMemset () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a4f4"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a4f8"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a4fc"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a500"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a504"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a508"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a50c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a510"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a514"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a518"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a51c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a520"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a524"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a528"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a52c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a530"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a534"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a538"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a53c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a540"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a544"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a548"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a54c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7a550"; "Corelib.Init.Datatypes.nil"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_andi"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_or"; "stdpp.bitvector.definitions.Z_to_bv"; "align15"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "RocqVerifyHarness.AgentSubmission.ABoot.SumsLib.msetk"; "cbyte_"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.regs_agree"; "Stdlib.Lists.List.In"; "imemset_clob"; "cpat_"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.not"; "asan_imemset_entry"].


(* [comment removed for export] *)
Definition imemset_words : list (bv 32) := ltac2:(CDefT.buildp (gd_tbl_AsanIMemset ()) "(0.(1.&20.)$2.(0.(1.&20.)$3.(0.(1.&20.)$4.(0.(1.&20.)$5.(0.(1.&20.)$6.(0.(1.&20.)$7.(0.(1.&20.)$8.(0.(1.&20.)$9.(0.(1.&20.)$:.(0.(1.&20.)$;.(0.(1.&20.)$<.(0.(1.&20.)$=.(0.(1.&20.)$>.(0.(1.&20.)$?.(0.(1.&20.)$10.(0.(1.&20.)$11.(0.(1.&20.)$12.(0.(1.&20.)$13.(0.(1.&20.)$14.(0.(1.&20.)$15.(0.(1.&20.)$16.(0.(1.&20.)$17.(0.(1.&20.)$18.(0.(1.&20.)$19.(1:.(1.&20.))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition imemset_clob : list reg := [11; 12; 13].

(* [comment removed for export] *)
Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.

Lemma land15_range : forall x, (0 <= x)%Z -> (0 <= Z.land x 15 < 16)%Z.
Proof.
  intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : forall n s, (0 <= n)%Z -> (0 <= align15 n s < 16)%Z.
Proof.
  intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : ltac2:(CDefT.buildp (gd_tbl_AsanIMemset ()) "Pn,$1;.Ps,(1.&40.)P,(1<.(1=.=R2.)(1>.R2.(1?.+2.+40.)))(20.$1;.(21.&40.(22.(23.(24.&40.R3.)R2.)+?.))(25.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros n s Hn. pose proof (u64_range s) as Hs.
  pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
  unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
  rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
  change (bv_wrap 64 15) with 15%Z.
  pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
  apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : forall n s, (0 <= n)%Z -> align15 n s = 0%Z -> (n mod 16 = 0)%Z.
Proof.
  intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
  change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).

Lemma cpat_bytes : forall c : word, (bv_unsigned c < 256)%Z ->
  word_to_le_bytes 8 (cpat_ c) = repeat (cbyte_ c) 8.
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.

Section IMEMSET.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables s c : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemset_words.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.
  (* [comment removed for export] *)
  Hypothesis HC256 : align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z.

  #[local] Abbreviation cbyte := (cbyte_ c).
  #[local] Abbreviation cpat := (cpat_ c).
  #[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
  #[local] Abbreviation CL := (fun r => In r imemset_clob).

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).

  (* [comment removed for export] *)
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

  (* [comment removed for export] *)
  Ltac msd F D kk :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ s kk) (v := cpat);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (cpat_bytes c) by lia;
    rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE Hn Hnw Hok"] Lemma bl_loop : ltac2:(CDefT.buildp (gd_tbl_AsanIMemset ()) "Pi,$26.Pregs,(27.&5.(1.&40.))Pret,(1.&40.)Pk,$1;.P,(28.R2.)P,(20.(1.&40.)(29.R4.(2:.&5.+1.$2;.))R3.)P,(20.(1.&40.)(29.R5.(2:.&5.+;.$2;.))Vc,)P,(20.(1.&40.)(29.R6.(2:.&5.+=.$2;.))(2<.Vs,R4.))P,(20.(1.&40.)(29.R7.(2:.&5.+<.$2;.))(2<.Vs,Vn,))P,(1<.(1=.=R6.)(1>.R6.Vn,))P,(20.$1;.(2=.R:.)(2>.(2>.Vn,+1.)R7.))(2?.(27.&5.(1.&40.))Lregs',(27.&5.(1.&40.))(1<.(30.Vsegs,(31.$32.R;.(2<.Vbase,+18.)(33.Vmem0,Vs,(34.Vc,)R9.)Vrom,)(31.$32.R1.R:.(33.Vmem0,Vs,(34.Vc,)Vn,)Vrom,))(35.Lr,(1.&5.)(36.(1.&5.)R1.$37.)R;.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - eexists. split.
      + msb C24 D_7a50c k.                        (* [comment removed for export] *)
        an C28 D_7a510.                           (* [comment removed for export] *)
        ab_ft C32 D_7a514 ltac:(condz).           (* [comment removed for export] *)
        an C36 D_7a518.                           (* [comment removed for export] *)
        aret C92 D_7a550 ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msb C24 D_7a50c k.
          an C28 D_7a510.
          ab_tk C32 D_7a514 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE Hn Hnw Hok"] Lemma al_loop : ltac2:(CDefT.buildp (gd_tbl_AsanIMemset ()) "Pi,$26.Pregs,(27.&5.(1.&40.))Pret,(1.&40.)Pk,$1;.P,(28.R2.)P,(20.(1.&40.)(29.R4.(2:.&5.+1.$2;.))R3.)P,(20.(1.&40.)(29.R5.(2:.&5.+;.$2;.))(38.Vc,))P,(20.(1.&40.)(29.R6.(2:.&5.+=.$2;.))(2<.Vs,R4.))P,(20.(1.&40.)(29.R7.(2:.&5.+<.$2;.))(2<.Vs,Vn,))P,(1=.=R6.)P,(1=.(39.R7.+10.)Vn,)P,(20.$1;.(3:.(2=.R;.)+10.)(2>.(2>.Vn,R8.)+10.))P,(1>.(21.&40.Vc,)+100.)(2?.(27.&5.(1.&40.))Lregs',(27.&5.(1.&40.))(1<.(30.Vsegs,(31.$32.R=.(2<.Vbase,+4<.)(33.Vmem0,Vs,(34.Vc,)R;.)Vrom,)(31.$32.R1.R<.(33.Vmem0,Vs,(34.Vc,)Vn,)Vrom,))(35.Lr,(1.&5.)(36.(1.&5.)R1.$37.)R=.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
    - eexists. split.
      + msd C76 D_7a540 k.                        (* [comment removed for export] *)
        msd C80 D_7a544 (k + 8)%Z.                (* [comment removed for export] *)
        an C84 D_7a548.                           (* [comment removed for export] *)
        ab_ft C88 D_7a54c ltac:(condz).           (* [comment removed for export] *)
        aret C92 D_7a550 ret.
        replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msd C76 D_7a540 k.
          msd C80 D_7a544 (k + 8)%Z.
          an C84 D_7a548.
          ab_tk C88 D_7a54c ltac:(condz).         (* [comment removed for export] *)
          replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE Hn Hnw Hok HC256"] Theorem imemset_run : ltac2:(CDefT.buildp (gd_tbl_AsanIMemset ()) "Pregs,(27.&5.(1.&40.))Pret,(1.&40.)P,(28.R1.)P,(20.(1.&40.)(29.R3.(2:.&5.+1.$2;.))R2.)P,(20.(1.&40.)(29.R4.(2:.&5.+:.$2;.))Vs,)P,(20.(1.&40.)(29.R5.(2:.&5.+;.$2;.))Vc,)P,(20.(1.&40.)(29.R6.(2:.&5.+<.$2;.))(24.&40.Vn,))(2?.(27.&5.(1.&40.))Lregs',(27.&5.(1.&40.))(1<.(30.Vsegs,(31.$32.R8.(2<.Vbase,=)Vmem0,Vrom,)(31.$32.R1.R7.(3;.Vmem0,Vs,(3<.(1.&8.)(34.Vc,)(3=.Vn,)))Vrom,))(35.Lr,(1.&5.)(36.(1.&5.)R1.$37.)R8.R1.)))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    pose proof (align15_range n s Hn) as HA.
    change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
                       /\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_7a4f4.                            (* [comment removed for export] *)
        av C4 D_7a4f8 (Z_to_bv 64 (align15 n s))
           ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).  (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold imemset_clob. solve_regs_agree. }
    cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
    destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_tk C8 D_7a4fc ltac:(condz).          (* [comment removed for export] *)
          ab_tk C40 D_7a51c ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_7a550 ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + pose proof (HC256 HA0 Hnz) as Hc256.
        pose proof (align15_n16 n s Hn HA0) as Hn16.
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_tk C8 D_7a4fc ltac:(condz).       (* [comment removed for export] *)
             ab_ft C40 D_7a51c ltac:(condz).      (* [comment removed for export] *)
             av C44 D_7a520 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             av C48 D_7a524 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).  (* [comment removed for export] *)
             av_or C52 D_7a528 (Z_to_bv 64 (bv_unsigned c * 257))
               ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).                        (* [comment removed for export] *)
             av C56 D_7a52c (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C60 D_7a530 (Z_to_bv 64 (bv_unsigned c * 16843009))
               ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).                 (* [comment removed for export] *)
             av C64 D_7a534 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C68 D_7a538 (cpat_ c)
               ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia). (* [comment removed for export] *)
             an C72 D_7a53c.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
          assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
          destruct Hi as (i & Hi).
          destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_ft C8 D_7a4fc ltac:(condz).          (* [comment removed for export] *)
          ab_tk C12 D_7a500 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_7a550 ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C8 D_7a4fc ltac:(condz).       (* [comment removed for export] *)
             ab_ft C12 D_7a500 ltac:(condz).      (* [comment removed for export] *)
             av C16 D_7a504 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             an C20 D_7a508.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMSET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_imemset_entry : word := 0x7aa58.

Lemma asan_imemset_code :
  code_at AsanUbsan.M.loaded_segments asan_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem asan_imemset : ltac2:(CDefT.buildp (gd_tbl_AsanIMemset ()) "Pmem0,P,(1.&40.)(3>.(1.&8.))Ps,(1.&40.)Pc,(1.&40.)Pn,$1;.Prom,P,(1.&40.)(3>.(1.&8.))Pregs,(27.&5.(1.&40.))Pret,(1.&40.)P,(1=.=R4.)P,(1>.(39.(21.&40.R7.)R5.)(1?.+2.+40.))P,(20.$3?.(40.$41.R9.R8.(3=.R6.))$42.)P,P,(20.$1;.(25.R7.R9.)=)P,(43.(20.$1;.R8.=))(1>.(21.&40.R:.)+100.)P,(28.R5.)P,(20.(1.&40.)(29.R7.(2:.&5.+1.$2;.))R6.)P,(20.(1.&40.)(29.R8.(2:.&5.+:.$2;.))R<.)P,(20.(1.&40.)(29.R9.(2:.&5.+;.$2;.))R<.)P,(20.(1.&40.)(29.R:.(2:.&5.+<.$2;.))(24.&40.R<.))(2?.(27.&5.(1.&40.))Lregs',(27.&5.(1.&40.))(1<.(30.$41.(31.$32.R<.$44.R11.R=.)(31.$32.R1.R;.(3;.R11.R10.(3<.(1.&8.)(24.&8.(21.&40.R?.))(3=.R>.)))R=.))(35.Lr,(1.&5.)(36.(1.&5.)R1.$37.)R<.R1.)))")
(* [comment removed for export] *).
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 asan_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
