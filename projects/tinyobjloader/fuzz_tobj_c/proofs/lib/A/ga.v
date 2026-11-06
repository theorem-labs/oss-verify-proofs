(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_046.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq fz ft fu fw.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR.

(* [comment removed for export] *)
Module FpsU_a6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "nat"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st"; "T7b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_U"; "SUF_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs"; "SUFA_U"; "tailBR_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsB"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs.
Import ListNotations.
Open Scope Z_scope.

Lemma okBR_6 : ltac2:(tb__ "0|0|
S4S1SdS0S0SbS8S9R1Z0SaScS7A7Ln;S5S2S0SeS6U43U7A2A4A3S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End FpsU_a6.

(* [comment removed for export] *)
Module FpsC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_C"; "SUF_NL"; "Posts_fps"; "FTA"; "T8"; "tailA_ok"; "@Corelib.Init.Datatypes"; "length"; "nat"; "bool"; "true"; "list"; "Some"; "option"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "lt"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st"; "Pre"; "T7s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA"; "MSGb"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs"; "tailB_out"; "SUFA_C"; "tailB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "FdEntry"; "FdChannel"; "Model"; "event"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsC_mod.FpsC_cert"; "T7b"; "T7s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsS"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs"; "T8C"; "tailC_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymEntail SymCFG SymSummary SymObj SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv StrBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ft.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsC_mod OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.FpsC_b0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.FpsC_b1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.FpsC_a0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.FpsC_a1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ft.FpsC_a2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fu.FpsC_a3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ft.FpsC_a4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fu.FpsC_a5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fw.FpsC_a6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fw.FpsC_a7.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.

Lemma In_seqZ : ltac2:(tb__ "0|1|
S1S9S9S15SfS10R2A1M0R3A2S12R3S11G0S10R1A1A2A2A2S2fS1R4S31S9S1S10S32R3R2A2A4A3F_;Fcnt;Flo;Fn;").
Proof. intros n lo cnt H. apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia. Qed.

Lemma okA_pickn : ltac2:(tb__ "0|0|
S1SaF_;ScS1A1S1S14SaS30S1R3R2A3SbA3S2fS1R2R3A3S14SaR5R3A1SbA3F_;F_;Fn;Fns;Fg;").
Proof. intros g ns n H Hn. exact (proj1 (forallb_forall _ _) H n Hn). Qed.

Lemma okA_C : ltac2:(tb__ "0|2|
S1S1S15SfZ0R2A2M0SfR2Z3eA2A2S15G0SfR2Z3A2A2S14SaS7S5R4R3S2dA3S2S3R4S11S11S10S8S1S2A2A1M1R4A2S10S8S1S3A2A1A2S6G1R4R3S2eS2dA5A6SbA3F_;F_;Fr;Fn;").
Proof.
  intros n r Hn Hr. change (Z.of_nat (length PRE_C)) with 17. change (Z.of_nat (length SUF_NL)) with 1. replace (17 + n + 1) with (18 + n) by lia.
  change FpsC_cert.T7s with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s.
  assert (HR : In r [0; 1; 2; 3]) by (cbn; lia).
  set (g := fun n => tailA_n (FPA n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) (fun r => FQA n r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) PRE_C SUF_NL n (18 + n) (fun r => T8 17 n r factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) [0; 1; 2; 3]).
  assert (Hg : g n = true).
  { destruct (Z_lt_le_dec n 8);  [apply (okA_pickn g _ n okA_0); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 16); [apply (okA_pickn g _ n okA_1); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 24); [apply (okA_pickn g _ n okA_2); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 32); [apply (okA_pickn g _ n okA_3); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 40); [apply (okA_pickn g _ n okA_4); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 48); [apply (okA_pickn g _ n okA_5); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 56); [apply (okA_pickn g _ n okA_6); apply In_seqZ; cbn; lia|].
    apply (okA_pickn g _ n okA_7); apply In_seqZ; cbn; lia. }
  exact (tailA_n_sound (FPA n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) (fun r => FQA n r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) PRE_C SUF_NL n (18 + n) 17 factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s [0; 1; 2; 3] r
           ltac:(unfold FPA; discriminate) Hg HR).
Qed.

Section C.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S36ScS13Q40A1A1ScS28A1S27VJ0;R4R3R2R1A4S14SeS25A1S29S2aR2A1S2bA2SdS25S26S2bA1A2A3F_;Fmd;Ftr;Ft;Fr;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis HFN : FirstNul rho.
Let n : Z := bv_unsigned (rw rho 16).
Let str : list byte := firstn (Z.to_nat n) (rl rho 3).
Let Kwr : ltac2:(tb__ "0|0|
S9S1dFk;") := ltac2:(tb__ "0|0|
S1aVJ0;S2S3Vstr;A4").
Hypothesis HokK : ltac2:(tb__ "0|0|
S9S1eS0Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S9S37S0Vok;VKwr;R1A1A3Fk;").
Lemma preC1 : (1 <= length PRE_C)%nat. Proof. cbn. lia. Qed.

Theorem fpsC_small : ltac2:(tb__ "0|0|
SfVn;Z3eA2S24S0Vok;S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsC_sum.fpsA_sound_S ok J0 PRE_C SUF_NL preC1 Hst0 Hfd2 rho tp HFN HokK HokP (FTA n (bv_unsigned (eval rho sX) mod 4) FpsC_cert.T7s)); [unfold n in *; lia | cbn [length PRE_C SUF_NL Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  apply okA_C; [unfold n in *; lia | pose proof (Z.mod_pos_bound (bv_unsigned (eval rho sX)) 4 ltac:(lia)); lia].
Qed.

Theorem fpsC_small_ex : ltac2:(tb__ "0|0|
SfVn;Z3eA2S23S0S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsC_sum.fpsA_sound_S_ex J0 PRE_C SUF_NL preC1 Hst0 Hfd2 rho tp HFN (FTA n (bv_unsigned (eval rho sX) mod 4) FpsC_cert.T7s)); [unfold n in *; lia | cbn [length PRE_C SUF_NL Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  apply okA_C; [unfold n in *; lia | pose proof (Z.mod_pos_bound (bv_unsigned (eval rho sX)) 4 ltac:(lia)); lia].
Qed.

Lemma okC_C : ltac2:(tb__ "0|1|
S14SaS35S2S3S10S8S1S2A2A1M0S33S2cA1S34G0S2cA2A5SbA3").
Proof. change (Z.of_nat (length PRE_C)) with 17. change FpsC_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7b. exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.FpsC_b0.okC. Qed.

Theorem fpsC_big : ltac2:(tb__ "0|0|
SfZ40Vn;A2S24S0Vok;S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsC_sum.fpsC_sound_C ok J0 PRE_C SUF_NL preC1 Hst0 Hfd2 rho tp HFN HokK HokP);
    [unfold n in *; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply okC_C].
Qed.

Theorem fpsC_big_ex : ltac2:(tb__ "0|0|
SfZ40Vn;A2S23S0S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsC_sum.fpsC_sound_C_ex J0 PRE_C SUF_NL preC1 Hst0 Hfd2 rho tp HFN);
    [unfold n in *; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply okC_C].
Qed.

Lemma okB_C : ltac2:(tb__ "0|0|
S1S15SfZ0R1A2SfR1Z3A2A2S16S20S20S14SeS20A1S22S2S3Z3fR3S21S2eS18A7SdS20R1A2A3Lo;A2F_;Fr;").
Proof.
  intros r Hr.
  assert (Hg : tailB_ok PRE_C SUF_NL 63 r SUFA_C factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s = true).
  { apply (okA_pickn (fun r => tailB_ok PRE_C SUF_NL 63 r SUFA_C factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) [0; 1; 2; 3] r okB_1). cbn. lia. }
  unfold tailB_ok in Hg. destruct (tailB PRE_C SUF_NL 63 r SUFA_C factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s) as [o|]; [exists o; reflexivity | discriminate].
Qed.
Theorem fpsC_63 : ltac2:(tb__ "0|0|
S14S1Vn;Z3fA3S24S0Vok;S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. pose proof (Z.mod_pos_bound (bv_unsigned (eval rho sX)) 4 ltac:(lia)) as HrA.
  destruct (okB_C (bv_unsigned (eval rho sX) mod 4) ltac:(lia)) as [o Hcert].
  apply (FpsC_sum.fps_sound_S_gen ok J0 PRE_C SUF_NL preC1 Hst0 rho tp HFN HokK); [unfold n in *; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  unfold FpsC_sum.tail_stmt. change (Z.of_nat (length PRE_C)) with 17. change FpsC_cert.T7s with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s.
  intros Hstr_len HlT8 HnT8 rho7 Hag7. pose proof (urange (rw rho 16)) as R16. fold n str in Hstr_len. fold n. rewrite <- Hn in Hcert.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB.tailB_sound ok J0 PRE_C SUF_NL str Hst0 Hfd2 HokK HokP rho tp) with (sufa := SUFA_C) (o := o);
    [rewrite Hstr_len; reflexivity | rewrite Hstr_len; unfold n; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | exact preC1
    | cbn [length SUF_NL Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hcert | exact HlT8 | exact HnT8 | exact Hag7].
Qed.
Theorem fpsC_63_ex : ltac2:(tb__ "0|0|
S14S1Vn;Z3fA3S23S0S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. pose proof (Z.mod_pos_bound (bv_unsigned (eval rho sX)) 4 ltac:(lia)) as HrA.
  destruct (okB_C (bv_unsigned (eval rho sX) mod 4) ltac:(lia)) as [o Hcert].
  apply (FpsC_sum.fps_sound_S_gen_ex J0 PRE_C SUF_NL preC1 Hst0 rho tp HFN); [unfold n in *; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  unfold FpsC_sum.tail_stmt_ex. change (Z.of_nat (length PRE_C)) with 17. change FpsC_cert.T7s with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsC_st.T7s.
  intros Hstr_len HlT8 HnT8 rho7 Hag7. pose proof (urange (rw rho 16)) as R16. fold n str in Hstr_len. fold n. rewrite <- Hn in Hcert.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB.tailB_sound_ex J0 PRE_C SUF_NL str Hst0 Hfd2 rho tp) with (sufa := SUFA_C) (o := o);
    [rewrite Hstr_len; reflexivity | rewrite Hstr_len; unfold n; lia | cbn [length PRE_C Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | exact preC1
    | cbn [length SUF_NL Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hcert | exact HlT8 | exact HnT8 | exact Hag7].
Qed.
Theorem fpsC_all : ltac2:(tb__ "0|0|
S24S0Vok;S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A4").
Proof.
  destruct (Z_lt_le_dec n 63); [apply fpsC_small; lia|]. destruct (Z.eq_dec n 63); [apply fpsC_63; lia|]. apply fpsC_big; lia.
Qed.
Theorem fpsC_all_ex : ltac2:(tb__ "0|0|
S23S0S1cS0VJ0;S17Vrho;Vtp;A5S1bS0VKwr;S8S13Q8A1S19S2S3Vstr;A3A2A1S1fVrho;Vtp;S4A6A3").
Proof.
  destruct (Z_lt_le_dec n 63); [apply fpsC_small_ex; lia|]. destruct (Z.eq_dec n 63); [apply fpsC_63_ex; lia|]. apply fpsC_big_ex; lia.
Qed.
End C.
End FpsC.

(* [comment removed for export] *)
Module FpsD.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "nat"; "bool"; "length"; "list"; "true"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_D"; "SUF_NL"; "Posts_fps"; "FTA"; "T8"; "tailA_ok"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "add"; "le"; "lt"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "FdEntry"; "FdChannel"; "Model"; "event"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsD_mod.FpsD_cert"; "T7s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st"; "Pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA"; "MSGb"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymEntail SymCFG SymSummary SymObj SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv StrBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsD_mod OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.FpsD_a0.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.

Lemma In_seqZ : ltac2:(tb__ "0|1|
S0S4S4S3S13S11R2A1M0R3A2S14R3S12G0S11R1A1A2A2A2S26S0R4S28S4S0S11S29R3R2A2A4A3F_;Fcnt;Flo;Fn;").
Proof. intros n lo cnt H. apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia. Qed.

Lemma okA_pickn : ltac2:(tb__ "0|0|
S0S5F_;S7S0A1S0S2S5S27S0R3R2A3S8A3S26S0R2R3A3S2S5R5R3A1S8A3F_;F_;Fn;Fns;Fg;").
Proof. intros g ns n H Hn. exact (proj1 (forallb_forall _ _) H n Hn). Qed.

Lemma okA_D : ltac2:(tb__ "0|1|
S0S0S2S0R2Z1A3S3S13Z0R2A2S13R2Z3A2A2S2S5S10SeR4R3S1dA3SbScR4S12S12S11S6S0SbA2A1M0R4A2S11S6S0ScA2A1A2SfG0R4R3S2aS1dA5A6S8A3F_;F_;Fr;Fn;").
Proof.
  intros n r -> Hr. change (Z.of_nat (length PRE_D)) with 19. change (Z.of_nat (length SUF_NL)) with 1. change (19 + 1 + 1) with (20 + 1).
  change FpsD_cert.T7s with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s.
  assert (HR : In r [0; 1; 2; 3]) by (cbn; lia).
  set (g := fun n => tailA_n (FPA n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s) (fun r => FQA n r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s) PRE_D SUF_NL n (20 + n) (fun r => T8 19 n r factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s) [0; 1; 2; 3]).
  assert (Hg : g 1 = true) by (apply (okA_pickn g _ 1 okA_0); left; reflexivity).
  exact (tailA_n_sound (FPA 1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s) (fun r => FQA 1 r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s) PRE_D SUF_NL 1 (20 + 1) 19 factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsD_st.T7s [0; 1; 2; 3] r
           ltac:(unfold FPA; discriminate) Hg HR).
Qed.

Section D.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S2dS7S15Q40A1A1S7S19A1S18VJ0;R4R3R2R1A4S2SaS16A1S1aS1bR2A1S1cA2S9S16S17S1cA1A2A3F_;Fmd;Ftr;Ft;Fr;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis HFN : FirstNul rho.
Let n : Z := bv_unsigned (rw rho 16).
Let str : list byte := firstn (Z.to_nat n) (rl rho 3).
Let Kwr : ltac2:(tb__ "0|0|
S4S23Fk;") := ltac2:(tb__ "0|0|
S20VJ0;SbScVstr;A4").
Hypothesis HokK : ltac2:(tb__ "0|0|
S4S24S1Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S4S2eS1Vok;VKwr;R1A1A3Fk;").
Lemma preD1 : (1 <= length PRE_D)%nat. Proof. cbn. lia. Qed.

Theorem fpsD_small : ltac2:(tb__ "0|0|
S2S0Vn;Z1A3S2cS1Vok;S22S1VJ0;S1eVrho;Vtp;A5S21S1VKwr;S6S15Q8A1S1fSbScVstr;A3A2A1S25Vrho;Vtp;SdA6A4F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsD_sum.fpsA_sound_S ok J0 PRE_D SUF_NL preD1 Hst0 Hfd2 rho tp HFN HokK HokP (FTA n (bv_unsigned (eval rho sX) mod 4) FpsD_cert.T7s)); [unfold n in *; lia | cbn [length PRE_D SUF_NL Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  apply okA_D; [exact Hn | pose proof (Z.mod_pos_bound (bv_unsigned (eval rho sX)) 4 ltac:(lia)); lia].
Qed.

Theorem fpsD_small_ex : ltac2:(tb__ "0|0|
S2S0Vn;Z1A3S2bS1S22S1VJ0;S1eVrho;Vtp;A5S21S1VKwr;S6S15Q8A1S1fSbScVstr;A3A2A1S25Vrho;Vtp;SdA6A3F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsD_sum.fpsA_sound_S_ex J0 PRE_D SUF_NL preD1 Hst0 Hfd2 rho tp HFN (FTA n (bv_unsigned (eval rho sX) mod 4) FpsD_cert.T7s)); [unfold n in *; lia | cbn [length PRE_D SUF_NL Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  apply okA_D; [exact Hn | pose proof (Z.mod_pos_bound (bv_unsigned (eval rho sX)) 4 ltac:(lia)); lia].
Qed.
End D.
End FpsD.

(* [comment removed for export] *)
Module FpsU.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "PRE_U"; "SUF_U"; "Posts_fps"; "FTA"; "T8"; "tailA_ok"; "@Stdlib.ZArith.BinInt.Z"; "le"; "of_nat"; "add"; "lt"; "modulo"; "@Corelib.Init.Datatypes"; "length"; "bool"; "nat"; "true"; "Some"; "list"; "option"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st"; "Pre"; "T7b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA"; "MSGb"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsU_mod.FpsU_cert"; "T7b"; "T7s"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs"; "tailBR_out"; "SUFA_U"; "tailBR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Fps_tailR"; "tailR_out"; "tailAR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "factsB"; "factsS"; "sX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "FdEntry"; "FdChannel"; "Model"; "event"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "zvar"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs"; "T8C"; "tailC_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymEntail SymCFG SymSummary SymObj SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv StrBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Fps_tailR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Fps_tailR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_prefix OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.FpsU_mod OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fr.Fps_tailCdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.FpsU_b0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Fps_tailBdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fu.FpsU_a0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fw.FpsU_a1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.FpsU_a2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.FpsU_a3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fu.FpsU_a4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.FpsU_a5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsU_a6.
Import ListNotations.
Close Scope bv_scope. Open Scope Z_scope.

Lemma In_seqZ : ltac2:(tb__ "0|1|
S1SfSfS17S8S9R2A1M0R3A2SbR3SaG0S9R1A1A2A2A2S35S1R4S37SfS1S9S38R3R2A2A4A3F_;Fcnt;Flo;Fn;").
Proof. intros n lo cnt H. apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia. Qed.

Lemma okA_pickn : ltac2:(tb__ "0|0|
S1SeF_;S12S1A1S1S16SeS36S1R3R2A3S10A3S35S1R2R3A3S16SeR5R3A1S10A3F_;F_;Fn;Fns;Fg;").
Proof. intros g ns n H Hn. exact (proj1 (forallb_forall _ _) H n Hn). Qed.

Lemma okA_U : ltac2:(tb__ "0|2|
S1S17S8Z0M0R1A2S8R1Z3fA2A2S16SeS7S5R2G0S25A3S2S3R2SaSaS9SdS1S2A2A1M1R2A2S9SdS1S3A2A1A2S6G1R2G0S2cS25A5A6S10A3F_;Fn;").
Proof.
  intros n Hn. change (Z.of_nat (length PRE_U)) with 7. change (Z.of_nat (length SUF_U)) with 7. replace (7 + n + 7) with (14 + n) by lia.
  change FpsU_cert.T7s with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s.
  assert (HR : In 0 [0]) by (left; reflexivity).
  set (g := fun n => tailA_n (FPA n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s) (fun r => FQA n r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s) PRE_U SUF_U n (14 + n) (fun r => T8 7 n r factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s) [0]).
  assert (Hg : g n = true).
  { destruct (Z_lt_le_dec n 16); [apply (okA_pickn g _ n okA_0); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 32); [apply (okA_pickn g _ n okA_1); apply In_seqZ; cbn; lia|].
    destruct (Z_lt_le_dec n 48); [apply (okA_pickn g _ n okA_2); apply In_seqZ; cbn; lia|].
    apply (okA_pickn g _ n okA_3); apply In_seqZ; cbn; lia. }
  exact (tailA_n_sound (FPA n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s) (fun r => FQA n r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s) PRE_U SUF_U n (14 + n) 7 factsS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7s [0] 0
           ltac:(unfold FPA; discriminate) Hg HR).
Qed.

Lemma okA_U64 : ltac2:(tb__ "0|2|
S1S16S1R1Z40A3S16SeS7S5R2Z0M0S24A3S2S3R2SaSaS9SdS1S2A2A1M1R2A2S9SdS1S3A2A1A2S6G1R2G0S2bS24A5A6S10A3F_;Fn;").
Proof.
  intros n ->. change (Z.of_nat (length PRE_U)) with 7. change (Z.of_nat (length SUF_U)) with 7. change (7 + 64 + 7) with (14 + 64).
  change FpsU_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b.
  assert (HR : In 0 [0]) by (left; reflexivity).
  set (g := fun n => tailA_n (FPA n OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) (fun r => FQA n r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) PRE_U SUF_U n (14 + n) (fun r => T8 7 n r factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) [0]).
  assert (Hg : g 64 = true) by (apply (okA_pickn g _ 64 okA_4); left; reflexivity).
  exact (tailA_n_sound (FPA 64 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) (fun r => FQA 64 r OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) PRE_U SUF_U 64 (14 + 64) 7 factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b [0] 0
           ltac:(unfold FPA; discriminate) Hg HR).
Qed.

Section U.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S3dS12S14Q40A1A1S12S31A1S30VJ0;R4R3R2R1A4S16S13S2eA1S32S33R2A1S34A2S11S2eS2fS34A1A2A3F_;Fmd;Ftr;Ft;Fr;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis HFN : FirstNul rho.
Let n : Z := bv_unsigned (rw rho 16).
Let str : list byte := firstn (Z.to_nat n) (rl rho 3).
Let Kwr : ltac2:(tb__ "0|0|
SfS1fFk;") := ltac2:(tb__ "0|0|
S1cVJ0;S2S3Vstr;A4").
Hypothesis Hal : ltac2:(tb__ "0|0|
S16S1ScS15Q40S3cVrho;S2dA2A2Z4A2Z0A3").
Hypothesis HokK : ltac2:(tb__ "0|0|
SfS20S0Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
SfS3eS0Vok;VKwr;R1A1A3Fk;").
Lemma preU1 : (1 <= length PRE_U)%nat. Proof. cbn. lia. Qed.

Theorem fpsU_small : ltac2:(tb__ "0|0|
S8Vn;Z3fA2S23S0Vok;S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsU_sum.fpsA_sound_S ok J0 PRE_U SUF_U preU1 Hst0 Hfd2 rho tp HFN HokK HokP (FTA n 0 FpsU_cert.T7s)); [unfold n in *; lia | cbn [length PRE_U SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  rewrite Hal. apply okA_U. unfold n in *; lia.
Qed.

Theorem fpsU_small_ex : ltac2:(tb__ "0|0|
S8Vn;Z3fA2S22S0S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsU_sum.fpsA_sound_S_ex J0 PRE_U SUF_U preU1 Hst0 Hfd2 rho tp HFN (FTA n 0 FpsU_cert.T7s)); [unfold n in *; lia | cbn [length PRE_U SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  rewrite Hal. apply okA_U. unfold n in *; lia.
Qed.

Lemma okC_U : ltac2:(tb__ "0|1|
S16SeS3bS2S3S9SdS1S2A2A1M0S39S24A1S3aG0S24A2A5S10A3").
Proof. change (Z.of_nat (length PRE_U)) with 7. change FpsU_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b. exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fv.FpsU_b0.okC. Qed.

Theorem fpsU_big : ltac2:(tb__ "0|0|
S8Z4aVn;A2S23S0Vok;S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsU_sum.fpsC_sound_C ok J0 PRE_U SUF_U preU1 Hst0 Hfd2 rho tp HFN HokK HokP);
    [unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply okC_U].
Qed.

Theorem fpsU_big_ex : ltac2:(tb__ "0|0|
S8Z4aVn;A2S22S0S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. pose proof (urange (rw rho 16)) as R16.
  apply (FpsU_sum.fpsC_sound_C_ex J0 PRE_U SUF_U preU1 Hst0 Hfd2 rho tp HFN);
    [unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; lia | apply okC_U].
Qed.

Theorem fpsU_64 : ltac2:(tb__ "0|0|
S16S1Vn;Z40A3S23S0Vok;S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn.
  apply (FpsU_sum.fpsA_sound_B ok J0 PRE_U SUF_U preU1 Hst0 Hfd2 rho tp HFN HokK HokP (FTA n 0 FpsU_cert.T7b)); [unfold n in *; lia | cbn [length PRE_U SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  rewrite Hal. apply okA_U64. exact Hn.
Qed.
Theorem fpsU_64_ex : ltac2:(tb__ "0|0|
S16S1Vn;Z40A3S22S0S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn.
  apply (FpsU_sum.fpsA_sound_B_ex J0 PRE_U SUF_U preU1 Hst0 Hfd2 rho tp HFN (FTA n 0 FpsU_cert.T7b)); [unfold n in *; lia | cbn [length PRE_U SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  rewrite Hal. apply okA_U64. exact Hn.
Qed.

Lemma okR_U : ltac2:(tb__ "0|0|
S1S17S8Z41R1A2S8R1Z42A2A2S18S29S29S16S13S29A1S2aS2S3Z7R3Z0S2bS1aA7S11S29R1A2A3Lo;A2F_;Fm;").
Proof.
  intros m Hm.
  assert (Hg : tailAR_ok PRE_U SUF_U 7 m 0 factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b = true).
  { apply (okA_pickn (fun m => tailAR_ok PRE_U SUF_U 7 m 0 factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) [65; 66] m okR_5).
    destruct (Z.eq_dec m 65) as [->|]; [left; reflexivity | right; left; lia]. }
  unfold tailAR_ok in Hg. destruct (tailAR PRE_U SUF_U 7 m 0 factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) as [o|]; [exists o; reflexivity | discriminate].
Qed.
Theorem fpsU_6566 : ltac2:(tb__ "0|0|
S17S8Z41Vn;A2S8Vn;Z42A2A2S23S0Vok;S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. destruct (okR_U n Hn) as [o Hcert].
  apply (FpsU_sum.fps_sound_B_gen ok J0 PRE_U SUF_U preU1 Hst0 rho tp HFN HokK); [unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  unfold FpsU_sum.tail_stmt. change (Z.of_nat (length PRE_U)) with 7. change FpsU_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b. rewrite Hal.
  intros Hstr_len HlT8 HnT8 rho7 Hag7. pose proof (urange (rw rho 16)) as R16. fold n str in Hstr_len.
  apply (Fps_tailR.tailAR_sound ok J0 PRE_U SUF_U str Hst0 Hfd2 HokK HokP rho tp) with (len := 7 + n + 7) (o := o);
    [rewrite Hstr_len; reflexivity | rewrite Hstr_len; unfold n; lia | cbn [length PRE_U SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
    | exact preU1 | exact Hcert | exact HlT8 | exact HnT8 | exact Hag7].
Qed.
Theorem fpsU_6566_ex : ltac2:(tb__ "0|0|
S17S8Z41Vn;A2S8Vn;Z42A2A2S22S0S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. destruct (okR_U n Hn) as [o Hcert].
  apply (FpsU_sum.fps_sound_B_gen_ex J0 PRE_U SUF_U preU1 Hst0 rho tp HFN); [unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  unfold FpsU_sum.tail_stmt_ex. change (Z.of_nat (length PRE_U)) with 7. change FpsU_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b. rewrite Hal.
  intros Hstr_len HlT8 HnT8 rho7 Hag7. pose proof (urange (rw rho 16)) as R16. fold n str in Hstr_len.
  apply (Fps_tailR.tailAR_sound_ex J0 PRE_U SUF_U str Hst0 Hfd2 rho tp) with (len := 7 + n + 7) (o := o);
    [rewrite Hstr_len; reflexivity | rewrite Hstr_len; unfold n; lia | cbn [length PRE_U SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
    | exact preU1 | exact Hcert | exact HlT8 | exact HnT8 | exact Hag7].
Qed.

Lemma okBR_U : ltac2:(tb__ "0|0|
S1S17S8Z43R1A2S8R1Z49A2A2S18S26S26S16S13S26A1S28S2S3R3Z0S27S2bS1aA7S11S26R1A2A3Lo;A2F_;Fm;").
Proof.
  intros m Hm.
  assert (Hg : tailBR_ok PRE_U SUF_U m 0 SUFA_U factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b = true).
  { apply (okA_pickn (fun m => tailBR_ok PRE_U SUF_U m 0 SUFA_U factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) _ m okBR_6). apply In_seqZ. cbn. lia. }
  unfold tailBR_ok in Hg. destruct (tailBR PRE_U SUF_U m 0 SUFA_U factsB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b) as [o|]; [exists o; reflexivity | discriminate].
Qed.
Theorem fpsU_6773 : ltac2:(tb__ "0|0|
S17S8Z43Vn;A2S8Vn;Z49A2A2S23S0Vok;S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A4F_;").
Proof.
  intros Hn. destruct (okBR_U n Hn) as [o Hcert].
  apply (FpsU_sum.fps_sound_B_gen ok J0 PRE_U SUF_U preU1 Hst0 rho tp HFN HokK); [unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  unfold FpsU_sum.tail_stmt. change (Z.of_nat (length PRE_U)) with 7. change FpsU_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b. rewrite Hal.
  intros Hstr_len HlT8 HnT8 rho7 Hag7. pose proof (urange (rw rho 16)) as R16. fold n str in Hstr_len.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB.tailBR_sound ok J0 PRE_U SUF_U str Hst0 Hfd2 HokK HokP rho tp) with (sufa := SUFA_U) (o := o);
    [rewrite Hstr_len; reflexivity | rewrite Hstr_len; unfold n; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | exact preU1
    | cbn [length SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hcert | exact HlT8 | exact HnT8 | exact Hag7].
Qed.
Theorem fpsU_6773_ex : ltac2:(tb__ "0|0|
S17S8Z43Vn;A2S8Vn;Z49A2A2S22S0S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A3F_;").
Proof.
  intros Hn. destruct (okBR_U n Hn) as [o Hcert].
  apply (FpsU_sum.fps_sound_B_gen_ex J0 PRE_U SUF_U preU1 Hst0 rho tp HFN); [unfold n in *; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia |].
  unfold FpsU_sum.tail_stmt_ex. change (Z.of_nat (length PRE_U)) with 7. change FpsU_cert.T7b with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.FpsU_st.T7b. rewrite Hal.
  intros Hstr_len HlT8 HnT8 rho7 Hag7. pose proof (urange (rw rho 16)) as R16. fold n str in Hstr_len.
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fz.Fps_tailB.tailBR_sound_ex J0 PRE_U SUF_U str Hst0 Hfd2 rho tp) with (sufa := SUFA_U) (o := o);
    [rewrite Hstr_len; reflexivity | rewrite Hstr_len; unfold n; lia | cbn [length PRE_U Z.of_nat Pos.of_succ_nat Pos.succ]; unfold n in *; lia | exact preU1
    | cbn [length SUF_U Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Hcert | exact HlT8 | exact HnT8 | exact Hag7].
Qed.
Theorem fpsU_all : ltac2:(tb__ "0|0|
S23S0Vok;S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A4").
Proof.
  destruct (Z_lt_le_dec n 64); [apply fpsU_small; lia|]. destruct (Z.eq_dec n 64); [apply fpsU_64; lia|].
  destruct (Z_lt_le_dec n 67); [apply fpsU_6566; lia|]. destruct (Z_lt_le_dec n 74); [apply fpsU_6773; lia|]. apply fpsU_big; lia.
Qed.
Theorem fpsU_all_ex : ltac2:(tb__ "0|0|
S22S0S1eS0VJ0;S19Vrho;Vtp;A5S1dS0VKwr;SdS14Q8A1S1bS2S3Vstr;A3A2A1S21Vrho;Vtp;S4A6A3").
Proof.
  destruct (Z_lt_le_dec n 64); [apply fpsU_small_ex; lia|]. destruct (Z.eq_dec n 64); [apply fpsU_64_ex; lia|].
  destruct (Z_lt_le_dec n 67); [apply fpsU_6566_ex; lia|]. destruct (Z_lt_le_dec n 74); [apply fpsU_6773_ex; lia|]. apply fpsU_big_ex; lia.
Qed.
End U.
End FpsU.

(* [comment removed for export] *)
Module FpsSite_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "nil"; "true"; "prod"; "option"; "list"; "Some"; "bool"; "app"; "length"; "negb"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "axst"; "mkLeafA"; "la_state"; "ax_setS"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "ss_objs"; "ss_pc"; "cell"; "odefault"; "DList"; "SAlu"; "mkObj"; "mkSS"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_regs"; "ss_resv"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states"; "CUTS_S"; "C_C"; "C_D"; "C_U"; "Pre_rde"; "Pre_use"; "R_C"; "R_D"; "R_U"; "s_C"; "s_D"; "s_U"; "V_C"; "V_D"; "V_U"; "XB"; "XL"; "X_C"; "X_D"; "X_U"; "sXc"; "CX_C"; "CX_D"; "CX_U"; "E_C"; "E_D"; "E_U"; "N_fps"; "O_strX"; "T_C"; "T_D"; "T_U"; "XO"; "exU_sel"; "fps_u1"; "imfr"; "istr"; "setregA"; "splitsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "list_set"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "exit_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "T_after"; "ax_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "ex_okb"; "selA"; "app_objs"; "ex_fin"; "firstA"; "mergeA"; "splitA"; "x4set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "Pre_co"; "facts_fps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "P_fps"; "Posts_fps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM"; "S_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "locate"; "sp0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states"; "E_copen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_dstates"; "D_rde"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "apply_axforms"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface"; "fp_entry"; "fp_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lc_obj"; "lcarve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sprop_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@Stdlib.Lists.List"; "filter"; "fold_right"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA SummaryA EntailA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvJ DrvIfaceT DrvIfaceR DrvIfaceM DrvM_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR_facts DrvR_tfacts DrvR_dstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFpIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_tfacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_dstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import PFAddr TAddr RAddr MAddr. Open Scope Z_scope.

Definition CUTS_S : list Z := ltac2:(tb__ "0|0|
S0SeS7bS0SeS5eS0SeS7cS3SeA1A3A3A3").
Definition runS (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S6S7S10A1M0A1G0Lx;S11S32Vfuel;S33VA;S4A5G0R1Ll;S3S10A1X6x2").
Definition osum (o : sobj) : ltac2:(tb__ "0|0|
S5S5S5S5S18S18A2S18A2S1A2S1fA2") := ltac2:(tb__ "0|2|
S2S5S5S5S18S18A2M0S18A2M1S1A2S1fS2G1S1S2G0S18S2S18S18S24Vo;A1S28Vo;A1A4S27Vo;A1A4SbS1eS25Vo;A1A2A4S26Vo;A1A4").

Definition XB : sv := SAlu Instr.ALU_AND sp0 (SLit (-64)).
Definition XE : sv := ltac2:(tb__ "0|0|
S21S7aS75S75S72S7dA2S19Z3fA1A2S19N40A1A3").
Definition XL : sv := SAlu Instr.ALU_SUB XE XB.
Definition XO (p : sv) : sv := SAlu Instr.ALU_SUB p XB.
Definition sXc (p : sv) : sv := add XB (XO p).

Definition N_fps : list lcarve := ltac2:(tb__ "0|d|
S0S5S5SeSeA2M0S7S5S5SeS1A2M1SeA2M2A1M3A2M4S2G0G3S2SeSeZf20d8M5Zf20daA4S0G2S2G1SeS2SeS1G5U1M6A4Z1M7A4S0G2S2G1SeS2SeS1Zf20d9G6A4G7A4S3G2A1M8A3A3A4S0G4S2G0G3S2SeSeZf20e0M9Zf20f8A4S0G2S2G1SeS2SeS1G9U8MaA4Z7fffffffffffA4S0G2S2G1SeS2SeS1Zf20e8GaA4Z0MbA4S0G2S2G1SeS2SeS1Zf20f0GaA4GbA4G8A3A3A3A4S0G4S2G0G3S2SeSeZe9ae8McZe9af8A4S0G2S2G1SeS2SeS1GcGaA4Zddf74A4S0G2S2G1SeS2SeS1Ze9af0GaA4Zde378A4G8A3A3A4S3G4A1A3A3A3").
Definition setregA (A : axst) (k : nat) (v : sv) : axst := ltac2:(tb__ "0|1|
S16VA;S23S1dS12VA;A1M0A1S5bS18S2eG0A1Vk;Vv;A4S2bG0A1S2aG0A1S2fG0A1S1cG0A1S29G0A1S2dG0A1S2cG0A1A9A2").
Definition istr (p : sv) (A : axst) : nat := ltac2:(tb__ "0|0|
S71S1cS12VA;A1A1Vp;S19Z0A1A3").
Definition O_strX (p n : sv) : sobj := ltac2:(tb__ "0|0|
S22S47Vp;A1S19Z0A1Vn;S3S1eA1S20P3A1A5").

Definition s_fps (l n p : sv) (C Pre : axst) : wsub := ltac2:(tb__ "0|1|
SaS5SfS18A2M0S0G0S2SfS18P10Vl;A4S0G0S2SfS18P11Vn;A4S0G0S2SfS18P12S42A4S0G0S2SfS18P13S43A4S0G0S2SfS18P14S53Vp;A1A4S3G0A1A3A3A3A3A3S81P1S12VC;A1S12VPre;A1A3A3").
Definition sfacts_of (s : wsub) : list sprop := ltac2:(tb__ "0|1|
S87S7S1aA1M0S1aS1aG0S6S1aA1G0Lx;S82Vs;R2A2S1aS0S1aR1R2A3Lf';R1X6x2Lacc;Lf;S3S1aA1S6aA5").

Fixpoint splitsA (cuts : list (nat * Z)) (A : axst) : axst :=
  match cuts with [] => A | (i, z) :: r => splitsA r (splitA i (SLit z) A) end.
Definition fps_site1 (cuts : list (nat * Z)) (p n : sv) (E : axst) : axst := ltac2:(tb__ "0|0|
S59Vcuts;S68S19S7eA1VE;A2A2S13S63S5cS80S1bS7fS4eA4S58S16R1S85S12R1A1S57Vp;R1A2S4fVp;Vn;A2A3A2UcS47Vp;A1A3A2TA3;").
Definition fps_site2 (fblk flen : Z) (sf : list sprop) (A : axst) : axst := ltac2:(tb__ "0|1|
S83Vsf;S84VA;S0S5S18S18A2M0S2S18S18S19Vfblk;A1S19Vflen;A1A4S0G0S2S18S18S42S43A4S17VA;A1A3A3A2A2").

Definition fps_u1 (n : nat) : list nat := ltac2:(tb__ "0|2|
SaS1S0S1U0S0S1U1S0S1U2S0S1U5S0S1U6S3S1A1M0A3A3A3A3A3SaS1S5dU8M1S6fVn;G1A2A2S0S1U3S0S1U4S0S1U7G0A3A3A3A3A3").
Definition fps_undo (T : axst) : axst := ltac2:(tb__ "0|0|
SbS1bS1cS12VT;A1A1A2S1S65S6fR1U3A2S62S55R1A1VT;A2A2Tn;").

Definition run_C1__R : option (list leafA) := ltac2:(tb__ "0|0|
S11S32U3cS33S73S4A5").
Local Strategy expand [run_C1__R].
Definition LV_C1 : list leafA := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) run_C1__R).
Definition E_C : axst := Eval vm_compute in nthA E_copen LV_C1 0.
Lemma run_C1 : ltac2:(tb__ "0|1|
S30S6S7S10A1M0A1S11S32U3cS33S73S4A5S8G0S0S10S14S4bS5aA2S3S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_C1__R <: run_C1__R = Some [mkLeafA E_C RsCut]). Qed.
Definition cuts_C : list (nat * Z) := ltac2:(tb__ "0|1|
S0S5S1SeA2M0S2S1SeU0N15a0A4S0G0S2S1SeU1N80A4S3G0A1A3A3").
Definition C1_C : axst := Eval vm_compute in fps_site1 cuts_C vA1 vL3 E_C.
Definition s_C : wsub := Eval vm_compute in s_fps vL1 vL3 vA1 (fps_site2 0x1eec0 0x80 [] C1_C) Pre_co.
Definition sf_C : list sprop := Eval vm_compute in sfacts_of s_C.
Definition C_C : axst := Eval vm_compute in fps_site2 0x1eec0 0x80 sf_C C1_C.
Definition R_C : list sobj := Eval vm_compute in optR (entails_frA C_C Pre_co s_C).
Lemma fr_C : ltac2:(tb__ "0|1|
S30S6S7S1bA1M0A1S6eS34S69S3cA3S8G0S39A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_C : ltac2:(tb__ "0|0|
S30S9S6dS34S69S3cS39S5cS10S13S15S6cA4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_C : axst := Eval vm_compute in T_after Pre_co C_C s_C R_C P_fps.
Lemma T_C_eq : ltac2:(tb__ "0|0|
S30S13S5fS69S34S3cS39S6bA5S50A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition V_C : axst := Eval vm_compute in fps_undo T_C.
Definition run_C2__R : option (list leafA) := ltac2:(tb__ "0|0|
S11S32U28S33S3fS4A5").
Local Strategy expand [run_C2__R].
Definition LV_C2 : list leafA := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) run_C2__R).
Definition X_C : axst := Eval vm_compute in nthA V_C LV_C2 0.
Lemma run_C2 : ltac2:(tb__ "0|1|
S30S6S7S10A1M0A1S11S32U28S33S3fS4A5S8G0S0S10S14S44S5aA2S3S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_C2__R <: run_C2__R = Some [mkLeafA X_C RsCut]). Qed.
Definition CX_C : axst := Eval vm_compute in ex_siteD (-1024) X_C.
Lemma ex_C : ltac2:(tb__ "0|0|
S31S30SeS1dS12S44A1A1S5eA3S30S9S61Z0S48A2S4A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Pre_rde : axst := Pre_fps FMT_RDERR 0x1eec0 0x80.
Definition run_D1__R : option (list leafA) := ltac2:(tb__ "0|0|
S11S32U3cS33S74S4A5").
Local Strategy expand [run_D1__R].
Definition LV_D1 : list leafA := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) run_D1__R).
Definition E_D : axst := Eval vm_compute in nthA D_rde LV_D1 0.
Lemma run_D1 : ltac2:(tb__ "0|1|
S30S6S7S10A1M0A1S11S32U3cS33S74S4A5S8G0S0S10S14S4cS5aA2S3S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_D1__R <: run_D1__R = Some [mkLeafA E_D RsCut]). Qed.
Definition cuts_D : list (nat * Z) := ltac2:(tb__ "0|1|
S0S5S1SeA2M0S2S1SeU0N15a0A4S3G0A1A3").
Definition C1_D : axst := Eval vm_compute in fps_site1 cuts_D vA1 vL3 E_D.
Definition s_D : wsub := Eval vm_compute in s_fps vL1 vL3 vA1 (fps_site2 0x1eec0 0x80 [] C1_D) Pre_rde.
Definition sf_D : list sprop := Eval vm_compute in sfacts_of s_D.
Definition C_D : axst := Eval vm_compute in fps_site2 0x1eec0 0x80 sf_D C1_D.
Definition R_D : list sobj := Eval vm_compute in optR (entails_frA C_D Pre_rde s_D).
Lemma fr_D : ltac2:(tb__ "0|1|
S30S6S7S1bA1M0A1S6eS35S37S3dA3S8G0S3aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_D : ltac2:(tb__ "0|0|
S30S9S6dS35S37S3dS3aS5cS10S13S15S6cA4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_D : axst := Eval vm_compute in T_after Pre_rde C_D s_D R_D P_fps.
Lemma T_D_eq : ltac2:(tb__ "0|0|
S30S13S5fS37S35S3dS3aS6bA5S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition V_D : axst := Eval vm_compute in fps_undo T_D.
Definition run_D2__R : option (list leafA) := ltac2:(tb__ "0|0|
S11S32U28S33S40S4A5").
Local Strategy expand [run_D2__R].
Definition LV_D2 : list leafA := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) run_D2__R).
Definition X_D : axst := Eval vm_compute in nthA V_D LV_D2 0.
Lemma run_D2 : ltac2:(tb__ "0|1|
S30S6S7S10A1M0A1S11S32U28S33S40S4A5S8G0S0S10S14S45S5aA2S3S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_D2__R <: run_D2__R = Some [mkLeafA X_D RsCut]). Qed.
Definition CX_D : axst := Eval vm_compute in ex_siteD (-1024) X_D.
Lemma ex_D : ltac2:(tb__ "0|0|
S31S30SeS1dS12S45A1A1S5eA3S30S9S61Z0S49A2S4A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition Pre_use : axst := Pre_fps FMT_USAGE 0x16080 0x80.
Definition run_U1__R : option (list leafA) := ltac2:(tb__ "0|0|
S11S32U50S33S70S4A5").
Local Strategy expand [run_U1__R].
Definition LV_U1 : list leafA := Eval vm_compute in ((fun ro5__ : option (list leafA) => (match ro5__ with Some l => l | None => [] end)) run_U1__R).
Definition E_U : axst := Eval vm_compute in nthA S_U LV_U1 0.
Lemma run_U1 : ltac2:(tb__ "0|1|
S30S6S7S10A1M0A1S11S32U50S33S70S4A5S8G0S0S10S14S4dS5aA2S3S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_U1__R <: run_U1__R = Some [mkLeafA E_U RsCut]). Qed.
Definition cuts_U : list (nat * Z) := ltac2:(tb__ "0|1|
S0S5S1SeA2M0S2S1SeU0N15a0A4S0G0S2S1SeU1N80A4S3G0A1A3A3").
Definition C1_U : axst := Eval vm_compute in fps_site1 cuts_U vA0 vL2 E_U.
Definition s_U : wsub := Eval vm_compute in s_fps vL0 vL2 vA0 (fps_site2 0x16080 0x80 [] C1_U) Pre_use.
Definition sf_U : list sprop := Eval vm_compute in sfacts_of s_U.
Definition C_U : axst := Eval vm_compute in fps_site2 0x16080 0x80 sf_U C1_U.
Definition R_U : list sobj := Eval vm_compute in optR (entails_frA C_U Pre_use s_U).
Lemma fr_U : ltac2:(tb__ "0|1|
S30S6S7S1bA1M0A1S6eS36S38S3eA3S8G0S3bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_U : ltac2:(tb__ "0|0|
S30S9S6dS36S38S3eS3bS5cS10S13S15S6cA4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_U : axst := Eval vm_compute in T_after Pre_use C_U s_U R_U P_fps.
Lemma T_U_eq : ltac2:(tb__ "0|0|
S30S13S5fS38S36S3eS3bS6bA5S52A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition V_U : axst := Eval vm_compute in fps_undo T_U.
Definition run_U2__R : option (list leafA) := ltac2:(tb__ "0|0|
S11S32U3cS33S41S4A5").
Local Strategy expand [run_U2__R].
Definition LV_U2 : list leafA := Eval vm_compute in ((fun ro6__ : option (list leafA) => (match ro6__ with Some l => l | None => [] end)) run_U2__R).
Definition X_U : axst := Eval vm_compute in nthA V_U LV_U2 0.
Lemma run_U2 : ltac2:(tb__ "0|1|
S30S6S7S10A1M0A1S11S32U3cS33S41S4A5S8G0S0S10S14S46S5aA2S3S10A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run_U2__R <: run_U2__R = Some [mkLeafA X_U RsCut]). Qed.

Definition imfr (A : axst) : nat := ltac2:(tb__ "0|0|
S71S1cS12VA;A1A1S72S19N80A1A3").
Definition exU_sel (A : axst) : list nat := ltac2:(tb__ "0|1|
SbS1bS1cS12VA;A1A1A2S1S56VA;A1S1SaS1S0S1U0M0S0S1R1S3S1A1A3A3S86S1S1SdScS79R1G0A2A1ScS79R1R2A2A1A2Lk;S5dG0R2A2A3A3Ti;Tn;").
Definition ex_siteU (E : axst) : axst := ltac2:(tb__ "0|1|
S60S78VE;S0S76S77U0M0A1S3S76A1A3A2VE;A2S13S64S67G0S19N430A1S66G0S62S54R1A1R1A2A2A3A1TE1;").
Definition XU1 : axst := Eval vm_compute in ax_of (apply_axforms X_U [AXRebase 0]) X_U.
Definition XU2 : axst := Eval vm_compute in selA (exU_sel XU1) XU1.
Definition XU3 : axst := Eval vm_compute in mergeA 0 XU2.
Definition CX_U : axst := Eval vm_compute in ex_siteU X_U.
Lemma ex_U : ltac2:(tb__ "0|0|
S31S30SeS1dS12S46A1A1S5eA3S30S9S61Z0S4aA2S4A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End FpsSite_states.

(* [comment removed for export] *)
Module FpsSite.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "True"; "or"; "not"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "true"; "bool"; "nil"; "cons"; "prod"; "app"; "Some"; "option"; "length"; "andb"; "nat"; "pair"; "orb"; "false"; "fst"; "snd"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "FdChannel"; "fd_lookup"; "WriteEv"; "ExitEv"; "m_fds"; "m_fs"; "VmState"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "div"; "of_nat"; "sub"; "to_nat"; "lt"; "modulo"; "mul"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "rw"; "sv"; "SLit"; "sobj"; "SVar"; "ss_next"; "SPUle"; "ss_facts"; "rl"; "ss_objs"; "SAlu"; "sprop_eqb"; "sv_eqb"; "eval"; "sprop_below"; "holds"; "DList"; "cell"; "mkObj"; "ss_lenient"; "SPEq"; "swf"; "SPAlign"; "rm"; "sstate"; "SPBranch"; "SPNot"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "mkLeafA"; "sym_runA"; "ax_X"; "ax_base"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "tcons"; "w_tr"; "assn"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA"; "Kwr"; "MSGb"; "EVS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail"; "SUF_NL"; "Posts_fps"; "PRE_C"; "PRE_D"; "PRE_U"; "SUF_U"; "P_fps"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "nth_error"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SUB"; "ALU_OR"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa"; "BX0"; "KV_T"; "SH0"; "CST_drv"; "HKVrng_T"; "KP_T"; "HCSTKV_T"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "TP"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vTP"; "N_ex"; "locate"; "sp0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR"; "KcG"; "SHR"; "SHRZ"; "BXk"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXUnbase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ"; "lcarve"; "lc_obj"; "JAK"; "JA_carve"; "JA_uncarve"; "carve_okb"; "tv_bandfree"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite"; "sfl"; "XBe"; "XLe"; "siteI3"; "splits_okb"; "layout_okb"; "XEe"; "d4_okb"; "P0C"; "P0Us"; "nd_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "IMG_HI"; "SHADOW_OFF"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states"; "N_fps"; "CUTS_S"; "E_U"; "XB"; "XL";
"fps_u1"; "sXc"; "E_C"; "splitsA"; "C1_C"; "C1_U"; "C_C"; "C_U"; "O_strX"; "Pre_rde"; "Pre_use"; "XO"; "setregA"; "sf_C"; "sf_D"; "sf_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_tv"; "JA"; "nd_below"; "JAi"; "ANone"; "NDA"; "amode"; "keptFA"; "nd_am"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "SHR2"; "ZARG"; "Uv"; "SHRZ2"; "TOPV"; "CST_drv2"; "P0Z"; "SLK1"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre"; "Pre_fps"; "FMT_COPEN"; "FMT_RDERR"; "FMT_USAGE"; "Pre_co"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "Pre_exit0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates"; "s_exR"; "x4_okb"; "ex_img_okb"; "ex_img"; "splitA"; "x4set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "with_vm"; "AE_A"; "alloc_contractsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit"; "ch1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_dstates"; "D_rde"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts"; "carve_chk"; "carve_st"; "nd_Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states"; "T_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "HKV_K"; "HKP_K"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite.SiteC"; "CX"; "S1"; "S4"; "Tq"; "V"; "A2"; "B0"; "C"; "Rx"; "Xl"; "d4"; "s"; "A3"; "B3"; "C1"; "R"; "cuts"; "xsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite.SiteD"; "CX"; "E1"; "S4"; "D2"; "S1"; "SD1"; "Tq"; "V"; "A2"; "A3"; "B0"; "Rx"; "Xl"; "d4"; "dD1"; "s"; "A5"; "B3"; "C"; "C1"; "D1"; "R"; "cuts"; "iE"; "xsD"; "xsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite.SiteU"; "CX"; "S1"; "S4"; "Tq"; "V"; "A2"; "B0"; "C"; "Rx"; "Xl"; "d4"; "s"; "A3"; "B3"; "C1"; "R"; "cuts"; "xsE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st"; "sX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM"; "S_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states"; "E_copen"; "nd_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvRGlue"; "pub_lit_okb2"; "pub_sym_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.StrBytes"; "nthb"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "path_eqb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "dot_path"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt";
"vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bxt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymCall SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV MuslWL ListObj StrBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceEx GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform MuslWLA DrvGlueA DrvGlueB.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvFw DrvIfaceT DrvIfaceR DrvIfaceM DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR_facts DrvR_tfacts DrvR_dstates DrvM_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require g3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fx.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvSiteEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.DrvJRe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g7.DrvRGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g6.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_tfacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR_dstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.g3.DrvM_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fp.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fy.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations. Import PFAddr TAddr RAddr MAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition XBe : sv := SAlu ALU_AND sp0 (SLit (-64)).
Definition XEe : sv := ltac2:(tb__ "0|0|
S3cS7eS3cS7dS3cS7dS8fSdaA3S34Z3fA1A3S34N40A1A3").
Definition XLe : sv := SAlu ALU_SUB XEe XBe.

Definition sfl (p l n : positive) : list sprop := ltac2:(tb__ "0|9|
SdS31S38S34Z7fff7ffff000A1S3cS7dS36P1A1M0S34N80A1A3M1A2SdS31S38G1S34Z7ffffffffff0A1A2SdS31S4cS4bS81S3cS7eS3cS80S34Z28A1S3cS7dG0S34N998A1A3A3S34ZfA1A3S34Z0A1A3A1SdS31S38S3cS7dS36Vl;A1M2S34Z8A1M3A3S36Vn;A1M4A2SdS31S38G3G4A2SdS31S38G4S34Z4000000000000000A1M5A2SdS31S38S34Z1A1M6S36Vp;A1M7A2SdS31S38G7G5A2SdS31S38S3cS7dS3cS7fG7Sa3A3M8G4A3Sa4A2SdS31S38G8Sa4A2SdS31S38G4Sa4A2SdS31S38Sa4S34Z10000000000A1A2SdS31S38S34Z10007fff8000A1Sa3A2SdS31S38Sa8S34Z800000000000A1A2SdS31S38Sa3S34Z7fffffffffc0A1A2SdS31S38S3cS7dG7G6A3Sa8A2SdS31S38G2S34Z1ffffA1A2SdS31S38G1G7A2SdS31S38S3cS7dG2S34Z10A1A3G4A2ScS31A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Lemma sf_eqs : ltac2:(tb__ "0|2|
S1S0S9S31A1M0Sc4Sa2P8P9PaA3M1A3S1S0G0Sc5G1A3S0G0Sc6Sa2P4P5PcA3A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section SFL.
Variable rho : valuation.
Variables p l n : positive.
Let S := bv_unsigned (rw rho 1). Let AL := bv_unsigned (rw rho 11).
Let A := bv_unsigned (rw rho p). Let L := bv_unsigned (rw rho l). Let N := bv_unsigned (rw rho n).

Hypothesis HS : ltac2:(tb__ "0|0|
S1S24Z7fff80000000VS;A2S24VS;S29S26Z2Z2fA2Ze0A2A2A2").
Hypothesis HA : S + 24 <= A.
Hypothesis HAN : ltac2:(tb__ "0|0|
S24S25VA;VN;A2S25VS;VAL;A2A2").
Hypothesis HAL : ltac2:(tb__ "0|1|
S1S24S25VS;VAL;A2S26Z2M0Z2fA2A2S24VAL;S26G0Z17A2A2A2").
Hypothesis HLN : ltac2:(tb__ "0|0|
S1S24S25VL;Z11A2VN;A2S1S24VN;S26Z2Z16A2A2S24VL;Z1ffffA2A2A2").

Let XB := S - S mod 64.
Let XE : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
S29S25S25VS;VAL;A2Z3fA2M0S2cG0Z40A2A2").

Lemma U_sp0m : ltac2:(tb__ "0|0|
S7S1S24N1000R1A2S24R1Z0A2A2S0S7S53Q40S3fVrho;S3cS7dS36P1A1S34R2A1A3A2A2S25VS;R2A2A3F_;Fc;").
Proof. intros c Hc. apply (U_addc rho (SVar 1) c S); [reflexivity | unfold S in *; lia | lia]. Qed.
Lemma U_XBe : ltac2:(tb__ "0|0|
S0S7S53Q40S3fVrho;Sa3A2A2VXB;A3").
Proof. unfold XBe, sp0. rewrite (U_and_hmask rho (SVar 1) (-64) 64 eq_refl). reflexivity. Qed.
Lemma U_XEe : ltac2:(tb__ "0|0|
S0S7S53Q40S3fVrho;Sa8A2A2VXE;A3").
Proof.
  unfold XEe, sp0, vAL. rewrite (U_and_hmask rho _ (-64) 64 eq_refl).
  assert (E1 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 1) (SVar 11))) = S + AL).
  { apply (U_add2 rho (SVar 1) (SVar 11)); [reflexivity | reflexivity | unfold S, AL in *; pose proof (urange (rw rho 1)); pose proof (urange (rw rho 11)); lia]. }
  rewrite (U_addc rho _ 63 (S + AL) E1); [reflexivity | unfold S, AL in *; pose proof (urange (rw rho 1)); pose proof (urange (rw rho 11)); lia | lia].
Qed.
Lemma XB_facts : ltac2:(tb__ "0|0|
S1S24VXB;VS;A2S1S24S29VS;Z3fA2VXB;A2S0S7S2cVXB;Z40A2Z0A3A2A2").
Proof.
  subst XB. pose proof (Z.mod_pos_bound S 64 ltac:(lia)). pose proof (Z.div_mod S 64 ltac:(lia)).
  assert (M : (S - S mod 64) mod 64 = 0). { replace (S - S mod 64) with ((S / 64) * 64) by lia. apply Z_mod_mult. }
  repeat split; lia.
Qed.
Lemma XE_facts : ltac2:(tb__ "0|1|
S1S24S25VS;VAL;A2M0VXE;A2S1S24VXE;S25G0Z3fA2A2S24VXE;S26Z2Z2fA2A2A2A2").
Proof.
  subst XE. pose proof (Z.mod_pos_bound (S + AL + 63) 64 ltac:(lia)). pose proof (Z.div_mod (S + AL + 63) 64 ltac:(lia)).
  destruct HAL as [H1 H2].

  assert ((S + AL + 63) / 64 < 2 ^ 41 + 1) by (apply Z.div_lt_upper_bound; lia).
  repeat split; lia.
Qed.
Lemma U_XLe : ltac2:(tb__ "0|0|
S0S7S53Q40S3fVrho;Sa4A2A2S29VXE;VXB;A2A3").
Proof.
  unfold XLe. pose proof XB_facts. pose proof XE_facts. pose proof (urange (rw rho 11)) as R11. change (bv_unsigned (rw rho 11)) with AL in R11.
  apply (U_sub2 rho XEe XBe XE XB U_XEe U_XBe). lia.
Qed.
Lemma U_pXB : ltac2:(tb__ "0|0|
S0S7S53Q40S3fVrho;S3cS7fS36Vp;A1Sa3A3A2A2S29VA;VXB;A2A3").
Proof. pose proof XB_facts. apply (U_sub2 rho (SVar p) XBe A XB eq_refl U_XBe). lia. Qed.

Lemma sfl_holds : ltac2:(tb__ "0|0|
S6eS31S41Vrho;A1Sa2Vp;Vl;Vn;A3A3").
Proof.
  pose proof XB_facts as (B1 & B2 & B3). pose proof XE_facts as (E1 & E2 & E3). destruct HAL as [AL1 AL2]. destruct HLN as (LN1 & LN2 & LN3).
  pose proof (urange (rw rho p)) as RA. pose proof (urange (rw rho l)) as RL. pose proof (urange (rw rho n)) as RN.
  assert (UpN : bv_unsigned (eval rho (SAlu ALU_ADD (SAlu ALU_SUB (SVar p) XBe) (SVar n))) = A - XB + N).
  { apply (U_add2 rho _ (SVar n) (A - XB) N U_pXB eq_refl). unfold A, N in *. lia. }
  assert (Ul8 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar l) (SLit 8))) = L + 8) by (apply (U_addc rho (SVar l) 8 L eq_refl); unfold L in *; lia).
  assert (Ul16 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar l) (SLit 16))) = L + 16) by (apply (U_addc rho (SVar l) 16 L eq_refl); unfold L in *; lia).
  assert (Up1 : bv_unsigned (eval rho (SAlu ALU_ADD (SVar p) (SLit 1))) = A + 1) by (apply (U_addc rho (SVar p) 1 A eq_refl); unfold A in *; lia).
  unfold sfl.
  repeat (apply Forall_cons); try apply Forall_nil; cbn [holds];
    rewrite ?U_sp0m, ?UpN, ?U_pXB, ?U_XLe, ?U_XBe, ?U_XEe, ?Ul8, ?Ul16, ?Up1 by lia;
    rewrite ?(U_lit64 rho) by lia;
    try (change (eval rho (SVar p)) with (rw rho p)); try (change (eval rho (SVar l)) with (rw rho l)); try (change (eval rho (SVar n)) with (rw rho n));
    try (subst S AL A L N XB XE; lia).

  apply ms16_shape_holds.
Qed.
End SFL.

Lemma eval_sXc : ltac2:(tb__ "0|0|
S30S33S0S54Q40A1S3fR2Sb8R1A1A2S3fR2R1A2A3Fp;Frho;").
Proof.
  intros rho p. unfold sXc, XO, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.add. cbn [eval]. unfold alu64, alu. apply bv_eq.
  rewrite bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap. rewrite !two64.
  pose proof (urange (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB)). pose proof (urange (eval rho p)).
  rewrite ?Zmod_mod, Zplus_mod_idemp_r. replace (bv_unsigned (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB) + (bv_unsigned (eval rho p) - bv_unsigned (eval rho OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB)))
    with (bv_unsigned (eval rho p)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma ZARG_pclK : ltac2:(tb__ "0|2|
S7S7S7S24Z7fff80000000R3A2S24S25R4R3A2S26Z2Z2fA2M0A2S1S24S2dS27SaeR5A1Z8M1A2G1A2R3A2S2bR3S25S2dS27SaeS29S25R5R4A2Z1A2A1G1A2G1A2G1A2A2A2S6S7S7S1S24Z0R1A2S1S1S24S29R7Z40A2R1A2S2bR1G0A2A2S0S7R5SaeR1A1A3A2A2Lx;A2F_;F_;F_;Fz;Fal;Fsp;").
Proof.
  intros sp al z Hsp Hal Hz. unfold Sh, SHADOW_OFF in *.
  pose proof (Z.div_mod (sp / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sp / 8 + 2147450880) 8 ltac:(lia)).
  pose proof (Z.div_mod sp 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp 8 ltac:(lia)).
  assert (U : (sp + al - 1) / 8 <= 2 ^ 44 - 1).
  { replace (2 ^ 44 - 1) with ((2 ^ 47 - 1) / 8) by reflexivity. apply Z.div_le_mono; lia. }
  assert (U2 : ((sp + al - 1) / 8 + 2147450880) / 8 <= (2 ^ 44 - 1 + 2147450880) / 8) by (apply Z.div_le_mono; lia).
  change ((2 ^ 44 - 1 + 2147450880) / 8) with (2 ^ 41 + 268431359) in U2.
  exists (8 * (z - 2147450880)). split; [lia|]. split; [lia|].
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma div8_of_m64 : ltac2:(tb__ "0|2|
S7S24Z0R1A2S0S7S27S29R2S2cR2Z40M0A2A2Z8M1A2S2dG1S27R2G0A2A2A3F_;Fx;").
Proof.
  intros x Hx. pose proof (Z.div_mod x 64 ltac:(lia)). pose proof (Z.mod_pos_bound x 64 ltac:(lia)).
  symmetry. apply (Z.div_unique _ 8 _ 0); lia.
Qed.
Lemma div8_8 : ltac2:(tb__ "0|1|
S7S24Z0R1A2S0S7S27S27R2Z8M0A2G0A2S27R2Z40A2A3F_;Fx;").
Proof. intros x Hx. rewrite (Zdiv_Zdiv x 8 8) by lia. reflexivity. Qed.
Lemma div_add_off : ltac2:(tb__ "0|1|
S7S24Z0R1A2S0S7S27S25S27R2Z8M0A2Z7fff8000A2G0A2S25S27R2Z40A2Zffff000A2A3F_;Fx;").
Proof.
  intros x Hx. pose proof (Z.div_mod (x / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x / 8) 8 ltac:(lia)).
  rewrite <- (div8_8 x Hx). symmetry. apply (Z.div_unique _ 8 _ ((x / 8) mod 8)); lia.
Qed.
Lemma div64_p63 : ltac2:(tb__ "0|2|
S7S24Z1M0R1A2S0S7S27S25R2Z3fA2Z40M1A2S25S27S29R2G0A2G1A2G0A2A3F_;Fx;").
Proof.
  intros x Hx. pose proof (Z.div_mod (x - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (x - 1) 64 ltac:(lia)).
  symmetry. apply (Z.div_unique _ 64 _ ((x - 1) mod 64)); lia.
Qed.
Lemma zarg_hull : ltac2:(tb__ "0|6|
S7S7S7S24Z0R3A2M0G0S24Z1M1S25R5R4A2A2S1S24S25S27S29R6S2cR6Z40M2A2A2Z8M3A2Z7fff8000M4A2R4A2S2bR4S25S27S29S25S25R6R5A2Z3fA2M5S2cG5G2A2A2G3A2G4A2A2A2S1S24S2dS27S25S27R7G3A2G4A2G3A2G3A2R5A2S2bR5S25S2dS27S25S27S29S25R7R6A2G1A2G3A2G4A2G3A2G3A2G3A2A2A2F_;F_;F_;F_;Fz;FAL;FS;").
Proof.
  intros S AL z HS HAL H1 Hz.
  rewrite (div8_of_m64 S) in Hz by lia. rewrite (div8_of_m64 (S + AL + 63)) in Hz by lia.
  rewrite (div_add_off S) by lia. rewrite (div_add_off (S + AL - 1)) by lia.
  rewrite (div64_p63 (S + AL)) in Hz by lia. lia.
Qed.

Lemma firstn_succ_split {A} : ltac2:(tb__ "0|2|
S9VA;A1M0G0VA;S0G0S6cVA;Sb1S12VA;R3A2U1A2R2A3SfVA;R3SdVA;R1ScVA;A1A3A3A3S1S0G0S6cVA;S12VA;R4A2M1R3A3R4A3S0S11VA;A1S7bVA;R3G1A3S10VA;R2A2A3A2F_;Fx;Fl;Fs;").
Proof.
  induction s as [|a s IH]; intros l x H.
  - cbn in H |- *. destruct l; [discriminate|]. cbn in H. injection H as ->. split; reflexivity.
  - destruct l as [|b l]; [discriminate|]. cbn in H. injection H as -> H'. destruct (IH l x H') as [H1 H2].
    cbn. rewrite H1, H2. split; reflexivity.
Qed.

Lemma FirstNul_of_firstn : ltac2:(tb__ "0|6|
S9S54Q8M0A1M1A1M2G2S0G2S6cG1Sb1S12G1R1A2U1A2R2A3SfG1R1SdG1S55G0Z0M3A2M4ScG1A1A3A3A3S5S7cG1G4R2A3A1S1S0S7S147R4S28S12G1R3A2M5A1A2G3A3S1S7S1S24G3R1A2S2bR1S28S12G1R4A2A1A2A2S5S0S7S147R6R2A2G3A3A1F_;Fi;S0G2S6cG1G5R4A3R3A3A2A2F_;F_;Fstr;FL;").
Proof.
  intros L str H Hn. destruct (firstn_succ_split str L _ H) as [H1 H2]. unfold nthb. rewrite Nat2Z.id.
  split; [|split; [|exact H1]].
  - rewrite (nth_error_nth _ _ _ H2). reflexivity.
  - intros i Hi E. apply Hn. rewrite <- H1.
    assert (Hlt : (Z.to_nat i < length str)%nat) by lia.
    assert (EQ : nth (Z.to_nat i) L (Z_to_bv 8 0) = Z_to_bv 8 0).
    { apply bv_eq. rewrite E. reflexivity. }
    assert (EQ' : nth (Z.to_nat i) (firstn (length str) L) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { rewrite nth_firstn. rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) Hlt). exact EQ. }
    rewrite <- EQ'. apply nth_In. rewrite length_firstn. pose proof (f_equal (@length byte) H1) as EL. rewrite length_firstn in EL. lia.
Qed.

Lemma FirstNul_len : ltac2:(tb__ "0|4|
S30S9S54Q8A1M0A1M1SadR2A1S0G1S6cG0S2aS53Q40M2S32R3P10M3A2A2A1S3aR3P3A2A3R2A3S0S7S53G2S32R4G3A2A2S28S12G0R3A2A1A3F_;F_;Fstr;Frho;").
Proof.
  intros rho str [_ HN] Hs. pose proof (urange (rw rho 16)) as R16.
  set (n := bv_unsigned (rw rho 16)) in *. set (L := rl rho 3) in *.
  pose proof (f_equal (@length byte) Hs) as EL. rewrite length_firstn in EL.
  destruct (Nat.le_gt_cases (Z.to_nat n) (length L)) as [Hle|Hgt]; [lia|].
  exfalso. apply (HN (Z.of_nat (length L))); [lia|]. unfold nthb. rewrite Nat2Z.id. rewrite nth_overflow; [reflexivity | lia].
Qed.

Lemma triple_preK : ltac2:(tb__ "0|1|
S66OF_;S6bOS6bS66R4R1A1R4F_;Fw;R3S68S2fR6R5R3A4M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.
Lemma etriple_preK : ltac2:(tb__ "0|2|
S66OF_;M0OG0S66R4R1A1R4F_;Fw;R3S67S2fR5R3A3M1F_;G1F_;F_;FQ;FX;FP;").
Proof. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.

Lemma splitsA_cons : ltac2:(tb__ "0|1|
S14S7S9SeS14S7A2M0A1S57S0S57SbaSdG0S15S14S7R4R3A4R2A3R1A2SbaR2SeaR4S34R3A1R1A3A2A3FA;Fr;Fz;Fi;").
Proof. reflexivity. Qed.

Fixpoint splits_okb (cuts : list (nat * Z)) (A : axst) : bool :=
  match cuts with
  | [] => true
  | (i, z) :: r => match split_obj_at (ax_S A) i (SLit z) with Some S' => splits_okb r (ax_setS A S') | None => false end
  end.
Lemma SPA_splits : ltac2:(tb__ "0|0|
S62S9SeS14S7A2A1S30S57S9S54Q40A1A1S66S0SbSa6R5R3A2SaA3S61S2fR7R4R5R3R2A6S61S2fR8SbaR7R5A2R6R4R3A6F_;F_;Fw;Ftp;FA;Frho;Fcuts;FJ;").
Proof.
  intros J cuts. induction cuts as [|[i z] r IH]; intros rho A tp w Hok HS; [exact HS|].
  cbn [splits_okb] in Hok. destruct (split_obj_at (ax_S A) i (SLit z)) as [S'|] eqn:E; [|discriminate].
  rewrite splitsA_cons. unfold splitA, optS. rewrite E. apply IH; [exact Hok|]. apply (SPA_split segs J rho A i (SLit z) S' tp w E HS).
Qed.

Section FPSTAIL.
Variable AInv : ltac2:(tb__ "0|0|
Sf5S30S9S54Q40A1A1S1bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S7S99VCST;R1A2S1S24Z0R2A2S2bR2SafA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S7S99VXGL;R1A2S1S24Z0R2A2S2bR2SafA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S7S99S85R1A2S99VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis HCSTdrv2 : ltac2:(tb__ "0|0|
S7S99Sd7R1A2S99VCST;R2A2F_;Fz;").
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S62S30S9S54Q40A1A1S9S1aA1S1bR5R4R3R2R1A4S69VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S65S2fVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S62S30S9S54Q40A1A1S9S1aA1S1bR5R4R3R2R1A4S69VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Se4S2fVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
Sf4S2fSf3VAInv;VCST;VXGL;A5").

Variable T0 : list event.
Variable MDX : Model -> Prop.
Hypothesis HMDXvm : ltac2:(tb__ "0|0|
S1bS23VMDX;R2A1VMDX;Sf2R2R3A2A1F_;Fv;Fmd;").
Variable fds : list (word * FdEntry).
Hypothesis Hfds1 : ltac2:(tb__ "0|0|
S0S11S1cA1S1eVfds;Sf6A2S10S1cS1dSf6A1A2A3").
Hypothesis Hfds2 : ltac2:(tb__ "0|0|
S0S11S1cA1S1eVfds;S60A2S10S1cS1dS60A1A2A3").
Variable EV0 : list event.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0SH : ltac2:(tb__ "0|0|
S30VP0f;R1A1S84R2A1F_;Fr;").
Hypothesis HP0ZA : ltac2:(tb__ "0|0|
S30VP0f;R1A1S1Sd3R2A1Sd2R2A1A2F_;Fr;").
Hypothesis HP0R : ltac2:(tb__ "0|0|
S30VP0f;R1A1S91R2A1F_;Fr;").
Variable PA : AA -> Prop.

Variables (vp vl vn : positive) (lX : positive) (str : list byte).
Hypothesis Hvars : ltac2:(tb__ "0|0|
S1S8bVvp;S5fA2S1S8bVvl;S5fA2S8bVvn;S5fA2A2A2").
Hypothesis HP0str : ltac2:(tb__ "0|7|
S30VP0f;R1A1S1S0S9S54Q8M0A1M1A1M2S6cG1Sb1S12G1Vstr;A2M3U1A2S3aR2VlX;A2M4A3SfG1Vstr;SdG1S55G0Z0A2ScG1A1A3A3A3S1S0S7S53Q40M5S32R2Vvl;A2A2M6S28G3A1A3S1S0G2S3aR2P3A2G4A3S24S25G6Z11A2S53G5S32R2Vvn;A2A2A2A2A2A2F_;Fr;").
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) str.

Variables pre suf : list Z.
Variables (fmt fblk flen : Z).
Let Pre : axst := ltac2:(tb__ "0|0|
SdbVfmt;Vfblk;Vflen;A3").
Let msg : list byte := MSGb pre suf str.
Hypothesis HSPECm : ltac2:(tb__ "0|0|
S1bVMDX;R1A1VSpec;SfS1aVT0;SfS1aVEV0;SfS1aS6dS54Q8A1S1aS1fS60A1Vmsg;A4SdS1aS20S55Q40Z2A2S22R2A1A2ScS1aA1A3A3A3A3A1F_;Fmd;").

Variable PX : Z -> Prop.
Hypothesis HSUM : ltac2:(tb__ "0|6|
S66OF_;S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1VPX;S53G0S3fR3S13dA2A2A1S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vstr;A2A1A3S14S65S2fRaS6fR9Vpre;Vsuf;S6cG3S2aS53G0S32R6G2A2A2A1S3aR6P3M4A2A3R1A5A3Fk;S14Se4S2fRbS6fRaVpre;Vsuf;S6cG3S2aS53G0S32R7G2A2A2A1S3aR7G4A2A3M5R1A5A3Fk;S68S2fRbS61S2fRaVPre;R7R6A5S63S2fS6fRaVpre;Vsuf;G5S12G3S70Vpre;Vsuf;G5A3A2A5S5fR7R6S73A6A4F_;F_;F_;F_;F_;Ftp;Frho;F_;F_;FJ0;Fok';").

Hypothesis HSUMX : ltac2:(tb__ "0|5|
S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1VPX;S53G0S3fR3S13dA2A2A1S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vstr;A2A1A3S67S2fS61S2fR8VPre;R5R4A5S63S2fS6fR8Vpre;Vsuf;S6cG3S2aS53G0S32R5G2A2A2A1S3aR5P3A2A3M4S12G3S70Vpre;Vsuf;G4A3A2A5S5fR5R4S73A6A3F_;F_;F_;Ftp;Frho;F_;F_;FJ0;").

Hypothesis Htop0 : TOPV rho0.
Let Kc : KcA := ltac2:(tb__ "0|0|
S90VT0;VMDX;Vfds;VEV0;A4").
Let Kc' : KcA := ltac2:(tb__ "0|0|
S90VT0;VMDX;Vfds;SfS1aVEV0;S6dS54Q8A1S1aS1fS60A1Vmsg;A4A3A4").
Let JK (K : KcA) (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
ScaVAInv;VCST;VXGL;S5fVK;Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;Vnd;Ac").
Lemma KcG_okK : ltac2:(tb__ "0|0|
S9S1aA1Sf1S90VT0;VMDX;Vfds;R1A4A1Fevs;"). Proof. intros evs. apply KcG_ok. exact HMDXvm. Qed.

Variable nd : ndesc.
Hypothesis Hndam : nd_am nd = ANone.
Variables (E E1 : axst) (fuel1 : nat).
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S0S11S9S58A1M0A1S5bS2fVfuel1;Sb3VE;SaA5S10G0SdS58S5aVE1;Se2A2ScS58A1A3A2A3").
Hypothesis HnE : ltac2:(tb__ "0|2|
S1S0SbS8aS5fS37S56VE;A1M0A1M1A2SaA3S1S0SbS45G0A1S17A3S0SbScbG1Vnd;A2SaA3A2A2").

Variable cuts : list (nat * Z).
Let A2 : axst := splitsA cuts E1.
Hypothesis Hspl : ltac2:(tb__ "0|0|
S0SbSa6Vcuts;VE1;A2SaA3").
Variable i3 : nat.
Hypothesis Hi3 : ltac2:(tb__ "0|0|
S0S11S35A1S7bS35S3bS56VA2;A1A1Vi3;A3S10S35S44S36Vvp;A1S34Z0A1S36Vvn;A1ScS43A1S42VlX;A1A5A2A3").
Let A3 : axst := ltac2:(tb__ "0|0|
S59VA2;S141S56VA2;A1Vi3;S44S36Vvp;A1S34Z0A1S36Vvn;A1ScS43A1S42P3A1A5A3A2").
Hypothesis HA3s : ltac2:(tb__ "0|0|
S0SbSedS56VA2;A1S56VA3;A1A2SaA3").
Variable S4 : sstate.
Variable d4 : list (sv * sv).
Hypothesis HS4w : swf S4 = true.
Hypothesis HS4d : ltac2:(tb__ "0|3|
S0S11SeS9SeS33S33A2A1M0S9S31A1M1A2M2A1SecS56VA3;A1VS4;A2S10G2S15G0G1Vd4;ScS31A1A4A2A3").
Hypothesis HS4n : ltac2:(tb__ "0|1|
S1S0S8S37VS4;A1S37S56VA3;A1A1M0A3S0S8G0S37S56VE1;A1A1A3A2").
Hypothesis HS4f : ltac2:(tb__ "0|0|
S0S9S31A1S39VS4;A1S39S56VE1;A1A1A3").
Hypothesis Hd4 : ltac2:(tb__ "0|6|
S0SbS7aSeS33S33A2M0G0S16S16S16S13S3eS18S33S33R1A3M1S8cA2S3eS19S33S33R1A3M2S34S89A1M3A2A2S13S3eG1G3A2S3eG2S8cA2A2A2S13S3eG1S36Vvp;A1M4A2S3eG2Sb8G4A1M5A2A2A2S13S3eG1G5A2S3eG2G4A2A2A2Lpr;Vd4;A3SaA3").
Hypothesis Htpf : ltac2:(tb__ "0|0|
S0SbS79S31S3dS46S8cS34S89A1A2A1S39S56VE1;A1A1A3SaA3").
Let A4 : axst := ax_setS A3 S4.

Let C1 : axst := ltac2:(tb__ "0|0|
S59VA4;Sf9VS4;Sb2A2A2").
Hypothesis HC1 : ltac2:(tb__ "0|0|
S0SbSf8VA4;Sc9Vnd;A1Sb2A3SaA3").

Let A5 : axst := ltac2:(tb__ "0|0|
Sc7VC1;SdSeS33S33A2S15S33S33Sb5Sb6A4S5cVC1;A1A3A2").
Hypothesis Hpubs : ltac2:(tb__ "0|0|
S0SbS145VC1;Sc9Vnd;A1Sb5Sb6Z7fff7fffffc0S26Z2Z2fA2A6SaA3").
Let A6 : axst := ltac2:(tb__ "0|0|
Sc7VA5;SdSeS33S33A2S15S33S33S34Vfblk;A1S34Vflen;A1A4S5cVA5;A1A3A2").
Hypothesis Hpubl : ltac2:(tb__ "0|0|
S0SbS144VA5;Sc9Vnd;A1Vfblk;Vflen;A4SaA3").
Hypothesis Hfblk : ltac2:(tb__ "0|0|
S7S1S24SaeVfblk;A1R1A2S2bR1SaeS25Vfblk;Vflen;A2A1A2A2S4S92R2A1Sd5R2A1A2F_;Fz;").
Let C : axst := ltac2:(tb__ "0|0|
S146Sa2Vvp;Vvl;Vvn;A3VA6;A2").
Hypothesis HsfB : ltac2:(tb__ "0|0|
S0SbS7aS31S40S37S56VE1;A1A1A1Sa2Vvp;Vvl;Vvn;A3A3SaA3").

Hypothesis Hlayout : ltac2:(tb__ "0|8|
S30S6eS31S41R1A1S39S56VE1;A1A1A3S1S1S24Z7fff80000000S53Q40M0S32R2P1A2A2M1A2S24G1S29S26Z2M2Z2fA2M3Ze0A2A2A2S1S24S25G1Z18A2S53G0S32R2Vvp;A2A2M4A2S1S24S25G4S53G0S32R2Vvn;A2A2M5A2S25G1S53G0S32R2PbA2A2M6A2M7A2S1S24G7G3A2S1S24G6S26G2Z17A2A2S1S24G5S26G2Z16A2A2S24S53G0S32R2Vvl;A2A2Z1ffffA2A2A2A2A2A2A2F_;Frho;").

Variables (s : wsub) (R : list sobj).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S0S11S9S35A1M0A1SefVC;VPre;Vs;A3S10G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S0SbSeeVC;VPre;Vs;VR;S6dS58S57S5eS73A4A5SaA3").
Hypothesis Hs16 : ltac2:(tb__ "0|0|
S0S33Se0Vs;P10A2S36Vvl;A1A3").
Hypothesis Hs18 : ltac2:(tb__ "0|0|
S1S0S33Se0Vs;P12A2Sb5A3S0S33Se0Vs;P14A2Sc2S36Vvp;A1A1A3A2").
Hypothesis HPX : ltac2:(tb__ "0|0|
S30S6eS31S41R1A1S39S56VE1;A1A1A3VPX;S53Q40S32R2Vvp;A2A2A1F_;Frho;").
Hypothesis HnC : ltac2:(tb__ "0|2|
S1S0SbS8aS5fS37S56VC;A1M0A1M1A2SaA3S1S0SbScbG1Vnd;A2SaA3S0SbS7aS31S40G1A1S39G0A1A3SaA3A2A2").

Variable Tq : axst.
Hypothesis HTq : ltac2:(tb__ "0|0|
S0S57SfbVPre;VC;Vs;VR;S78A5VTq;A3").
Variables (S1 V : axst).
Hypothesis HS1 : ltac2:(tb__ "0|0|
S0S11S57A1S96VTq;SdS95S97Sb7S12S35S3bS56VTq;A1A1A2A1A1ScS95A1A3A2S10S57VS1;A2A3").
Hypothesis HS1o : ltac2:(tb__ "0|2|
S1S0S9S35A1S3bS56VS1;A1M0A1SfS35S3bS56VV;A1A1M1S6dS9aS35S9bSb2A4A3A3S0S57S59VS1;Se3G0G1A2A2VV;A3A2").
Hypothesis HnbS1 : ltac2:(tb__ "0|0|
S0SbScbS37S56VS1;A1A1Vnd;A2SaA3").

Variables (Xl : axst) (fuel2 : nat).
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S0S11S9S58A1M0A1S5bS2fVfuel2;Sb3VV;SaA5S10G0SdS58S5aVXl;Se2A2ScS58A1A3A2A3").
Hypothesis HnV : ltac2:(tb__ "0|2|
S1S0SbS8aS5fS37S56VV;A1M0A1M1A2SaA3S1S0SbS45G0A1S17A3S0SbScbG1Vnd;A2SaA3A2A2").

Variable xsE : list axform.
Variable B0 : axst.
Hypothesis HB0 : ltac2:(tb__ "0|0|
S0S11S57A1S96VXl;VxsE;A2S10S57VB0;A2A3").
Let B1 : axst := ax_setX B0 [].
Let B2 : axst := ex_img B1.
Hypothesis Himg : ex_img_okb B1 = true.
Let B3 : axst := ltac2:(tb__ "0|0|
S59VB2;Sf9S56VB2;A1S8dA2A2").
Hypothesis HB3 : ltac2:(tb__ "0|0|
S0SbSf8VB2;Sc9Vnd;A1S8dA3SaA3").
Let CX : axst := x4set (SLit TP) B3.
Hypothesis Hx4 : ltac2:(tb__ "0|0|
S0SbSe7VB3;S34S89A1A2SaA3").
Variable Rx : list sobj.
Hypothesis HnX : ltac2:(tb__ "0|2|
S1S0SbS8aS5fS37S56VCX;A1M0A1M1A2SaA3S1S0SbScbG1Vnd;A2SaA3S0SbS7aS31S40G1A1S39G0A1A3SaA3A2A2").
Hypothesis Hfrx : ltac2:(tb__ "0|2|
S0S11S9S35A1M0A1SefVCX;Se5Z0M1Z2A2Se6G1VCX;A2A3S10G0VRx;A2A3").
Hypothesis Hccx : ltac2:(tb__ "0|1|
S0SbSeeVCX;Se5Z0M0Z2A2Se6G0VCX;A2VRx;ScS57A1A5SaA3").

Lemma JK_parts : ltac2:(tb__ "0|3|
Sf0Sc8Sf5S7S30S9S54Q40A1A1S9S1aA1S1bSccVAInv;VCST;VXGL;S5fR8Vrho0;VP0f;ScSeS7S7A2M0A1M1ScSeG0S7A2A1M2S82VPA;R7R6R5R4R3R2R1A12S1S14bS5fVrho0;R5A3S1R9R3R2A2S1Sd0VCST;VXGL;Vrho0;G1G2S49Vrho0;A1S49R5A1A7VP0f;Vrho0;A1A2A2A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd';FK;").
Proof. intros K nd' Ai kc rho tp tr md (Hav & Hk & _ & _ & _ & _ & _ & _ & HK0 & HP0 & _). split; [exact Hav|]. split; [exact Hk|]. split; [exact HK0 | exact HP0]. Qed.

Lemma ZX_nowK : ltac2:(tb__ "0|1|
Sf0Sc8Sf5S7S30S9S54Q40A1A1S9S1aA1S1bSccVAInv;VCST;VXGL;S5fR8Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;R7R6R5R4R3R2R1A12S1Sd3R5A1S1Sd2R5A1S91R5A1A2A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd';FK;").
Proof.
  intros K nd' Ai kc rho tp tr md HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  destruct (HP0ZA _ HP0) as [(Z1 & Z2 & HZA) HS2]. pose proof (HP0R _ HP0) as [[HZ HP] HZR]. destruct HK0 as [K1 _].
  assert (KEPT : forall lo len z, In (lo, len) CST_drv \/ In (lo, len) CST_drv2 -> Sh lo <= z < Sh (lo + len) -> lo mod 8 = 0 -> 0 <= lo -> lo + len <= 0x646000 -> (lo + len <= 0x624510 \/ 0x624518 <= lo) -> rm rho0 (Z_to_bv 64 z) <> None ->
            rm rho (Z_to_bv 64 z) = rm rho0 (Z_to_bv 64 z)).
  { intros lo len z Hin Hz Hm Hlo Hhi Hne Hdef. unfold Sh, SHADOW_OFF in Hz. apply (K1 z ltac:(lia)).
    right. split; [|exact Hdef]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
    - left. right. left. split; [destruct Hin as [Hin|Hin]; [apply HCSTdrv | apply HCSTdrv2]; exists lo, len; split; [exact Hin | unfold SHADOW_OFF; lia | exact Hin | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
    - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  unfold ZARG, SHR2, SHR, SH0, Uv in *.
  rewrite <- (proj1 Hav 1%positive ltac:(unfold NF; lia)), <- (proj1 Hav 11%positive ltac:(unfold NF; lia)).
  split; [|split].
  - split; [exact Z1|]. split; [exact Z2|]. intros z Hz. rewrite <- (HZA z Hz). apply (K1 z).
    + destruct (ZARG_pclK _ _ z Z1 Z2 Hz) as (x & Hx0 & Hx & ->). unfold Sh, SHADOW_OFF in *. lia.
    + right. split; [|intro HcN; pose proof (HZA z Hz) as HcE; congruence]. destruct (ZARG_pclK _ _ z Z1 Z2 Hz) as (x & Hx0 & Hx & Ez). exists x. split; [exact Hx0|]. split; [left; left | exact Ez].
      unfold TobjJV.T0. cbn [Contract.V_TOP Malloc.Contract.V_TOP] in *. change (rw rho0 _) with (rw rho0 30%positive) at 1.
      unfold TOPV, Uv in Htop0. lia.
  - intros z Hz. destruct Hz as [Hz|Hz].
    + rewrite (KEPT 0x16080 0x40 z); [exact (HS2 z (or_introl Hz)) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HS2 z (or_introl Hz)) as HcE; congruence].
    + rewrite (KEPT 0x1eec0 0x80 z); [exact (HS2 z (or_intror Hz)) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HS2 z (or_intror Hz)) as HcE; congruence].
  - split; [split|].
    + intros a Ha. rewrite (KEPT 0x644ca8 0x450 a); [exact (HZ a Ha) | cbn; tauto | unfold Sh, SHADOW_OFF; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZ a Ha) as HcE; congruence].
    + intros a Ha. destruct Ha as [Ha|Ha].
      * rewrite (KEPT 0x22b80 0xf00 a); [exact (HP a (or_introl Ha)) | cbn; tauto | unfold Sh, SHADOW_OFF; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HP a (or_introl Ha)) as HcE; congruence].
      * rewrite (KEPT 0xec540 0x1800 a); [exact (HP a (or_intror Ha)) | cbn; tauto | unfold Sh, SHADOW_OFF; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HP a (or_intror Ha)) as HcE; congruence].
    + intros z Hz. destruct Hz as [Hz|[Hz|Hz]].
      * rewrite (KEPT 0x21440 0x80 z); [exact (HZR z (or_introl Hz)) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_introl Hz)) as HcE; congruence].
      * destruct (Z_lt_le_dec z (Sh 0x160c0)) as [Zlo|Zhi].
        -- rewrite (KEPT 0x16080 0x40 z); [exact (HZR z (or_intror (or_introl Hz))) | cbn; tauto | unfold Sh, SHADOW_OFF in *; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_intror (or_introl Hz))) as HcE; congruence].
        -- rewrite (KEPT 0x160c0 0x40 z); [exact (HZR z (or_intror (or_introl Hz))) | cbn; tauto | unfold Sh, SHADOW_OFF in *; lia | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_intror (or_introl Hz))) as HcE; congruence].
      * rewrite (KEPT 0x1a7c0 0x80 z); [exact (HZR z (or_intror (or_intror Hz))) | cbn; tauto | exact Hz | reflexivity | lia | lia | unfold Sh, SHADOW_OFF in *; lia | intro HcN; pose proof (HZR z (or_intror (or_intror Hz))) as HcE; congruence].
Qed.

Lemma JK_tv_bandfree : ltac2:(tb__ "0|0|
Sf0Sc8S30S9S54Q40A1A1S9S1aA1S1bVJK;R6R5R4R3R2R1A6Sa0R5Sc9R6A1A2F_;Fmd;Ftr;Ftp;Frho;Fnd';FK;").
Proof.
  intros K nd' rho tp tr md (Ai & kc & HJ) t Ht Hz a Ha.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _).
  destruct (proj1 (Forall_forall _ _) HN t Ht Hz) as (Hpos & Hlive & _).
  unfold TobjJV.tvv in Hpos, Hlive. cbn [fst snd] in Hpos, Hlive.
  pose proof (law_client_app _ _ _ ALA Ai rho tp md a HM) as X. pose proof (topG_range (aa_geom Ai)) as TG.
  assert (HC : client_addrA CST Ai a).
  { left. right. left. exists (uval rho (fst t)), (uval rho (snd t)). split; [exact Hlive | exact Ha]. }
  specialize (X HC). clear - X TG Ha.
  unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Let carveK (K : KcA) : ltac2:(tb__ "0|3|
Sc8S57S30S9S54Q40A1A1S66S9S9aA1S8S61S2fS9cVAInv;VCST;VXGL;S5fVrho0;VP0f;ScSeS7S7A2M0A1M1ScSeG0S7A2A1M2S82VPA;VK;R7AcR6R5R4R3A6S56R7A1S4aS4dS50R1A1S51R1A1S4fR1A1S4eR1A1S52R1A1SfS35S3bR1A1S6dS9aS35S9bR4A4A3S39R1A1R3S45R1A1A9S4aS0SbS47R1A1SaA3S0SbS8aS37R3A1R5A2SaA3S0S33S5dRbA1S34Sb0A1A3S0SbS9fS39R5A1S3bR5A1S5cRcA1S83S87Sc9RdA1R8A7SaA3S61S2fS9cVAInv;VCST;VXGL;S5fVrho0;VP0f;G1G2S82VPA;VK;ReAcS59RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;") := ltac2:(tb__ "0|1|
S9dVAInv;VCST;VXGL;VALA;S5fVrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;S83SfdVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AcS86S87SfeVAInv;VCST;VXGL;VHCSTdrv;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AaVK;A11").
Let uncarveK (K : KcA) : ltac2:(tb__ "0|5|
Sc8S57S30S9S54Q40A1A1S9S1aA1M0S149S1bS9S35A1M1S9S9aA1Sf1VK;A1S0G1S3bS56R9A1A1SfS35R3S6dS9aS35S9bR2A4A3A3S0SbSa1S83R3A2SaA3S0ScfSd1RcA1ScdA3S0SbScbS37S56RcA1A1RdA2SaA3S61S2fS9cVAInv;VCST;VXGL;S5fVrho0;VP0f;ScSeS7S7A2M2A1M3ScSeG2S7A2A1M4S82VPA;VK;ReAcRdRcRbS15G0S142RaS143R9R8A2A4A6S61S2fS9cVAInv;VCST;VXGL;S5fVrho0;VP0f;G3G4S82VPA;VK;RfAcS59ReSe3S56ReA1R8A2A2Se1RdS6dS9aS35S9bR7A4S14cR9RcRaA3A3RcS15G0S142RbS143RaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;") := ltac2:(tb__ "0|1|
S9eVAInv;VCST;VXGL;VALA;VHLV;S5fVrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;S83SfdVAInv;VCST;VXGL;VALA;VHCSTdrv;VHLPP;VKc;Vrho0;VP0f;VHP0SH;VPA;VPA;AcS86S88VAInv;VCST;VHCSTok;VHLPP;A4VK;A11").

Lemma Kwr_JK : ltac2:(tb__ "0|2|
S9S1aA1M0Sc8S30S14S30S9S54Q40A1A1M1G0S1bS6fS30G1G0S1bVJK;S90VT0;VMDX;Vfds;RcA4RbRaR3R2R1A6Lmd;Ltr;Lt;L_;Vpre;Vsuf;Vstr;R5R4R3R2R1A9VJK;S90VT0;VMDX;Vfds;SfS1aR9S71Vpre;Vsuf;Vstr;R6A4A3A4R8R7R4R3R2A6F_;Fmd';Ftr';Ft;FrhoL;Fk;Frho1;Fnd';Fevs;").
Proof.
  intros evs nd' rho1 k rhoL t tr' md' (tr0 & HJ & ->).
  destruct HJ as (Ai & kc & Hav & (Htr & Hfd & HX) & REST). exists Ai, kc. split; [exact Hav|]. split; [|exact REST].
  split; [rewrite Htr, <- !app_assoc; reflexivity|]. split; [exact Hfd | exact HX].
Qed.

Lemma msg_prefix_tcons : ltac2:(tb__ "0|0|
S14S1bVMDX;R1A1S69VSpec;SfS1aSfS1aVT0;VEV0;A3S71Vpre;Vsuf;Vstr;R3A4A3A2F_;Fmd;Fk;").
Proof.
  intros k md HX. exists (T0 ++ EV0 ++ map (WriteEv ch2) msg ++ [ExitEv (Z_to_bv 64 2) (m_fs md)]). split; [exact (HSPECm md HX)|].
  rewrite <- app_assoc. apply is_prefix_app_mono. apply is_prefix_app_mono. unfold EVS, msg. rewrite <- firstn_map. apply is_prefix_firstn.
Qed.

Lemma Kc_tcons : ltac2:(tb__ "0|0|
S9S1aA1S1bVKc;R2R1A2S69VSpec;R3A2F_;Fmd;Ftr;").
Proof. intros tr md (-> & _ & HX). pose proof (msg_prefix_tcons 0%nat md HX) as X. unfold EVS in X. cbn [firstn map] in X. rewrite app_nil_r in X. exact X. Qed.
Lemma Kce_tcons : ltac2:(tb__ "0|0|
S14S9S1aA1S1bS90VT0;VMDX;Vfds;SfS1aVEV0;S71Vpre;Vsuf;Vstr;R3A4A3R2R1A6S69VSpec;R3A2F_;Fmd;Ftr;Fk;").
Proof. intros k tr md (-> & _ & HX). rewrite app_assoc. exact (msg_prefix_tcons k md HX). Qed.

Theorem fps_tail_safe : ltac2:(tb__ "0|0|
S30S9S54Q40A1A1S68S2fVok;S61S2fVJK;VKc;Vnd;A2VE;R2R1A5S66S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp.
  destruct HnE as (N1 & N2 & N3). destruct HS4n as [HS4n1 HS4n2]. destruct HnC as (C1n & C2 & C3). destruct HnV as (V1 & V2 & V3). destruct HnX as (X1 & X2 & X3).

  eapply (JK_run AInv CST XGL ALA ok Spec HOKJ Kc (KcG_okK EV0) rho0 P0f Kc_tcons PA nd);
    [exact Hrun1 | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].

  unfold carve_chk in HC1. apply andb_prop in HC1 as [HC1 Cb]. apply andb_prop in HC1 as [Cw Cc]. apply sv_eqb_sound in Cb.
  eapply (triple_conseq (P := SPA segs (JK Kc nd) C rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof HS as [[Hsm1 _] (Ai & kc & HJi)]. pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HF1.
    pose proof (JK_parts _ _ _ _ _ _ _ _ HJi) as (Hav & HKc & HK0 & HP00).
    destruct (ZX_nowK _ _ _ _ _ _ _ _ HJi) as (HZA & HS2 & HSR).
    destruct (HP0str _ HP00) as (Sfirst & Slen & Srl & Sslk).

    apply (SPA_splits _ cuts rho1 E1 tp w Hspl) in HS. change (splitsA cuts E1) with A2 in HS.

    apply (SPA_relist _ rho1 A2 i3 (SVar vp) (SLit 0) (SVar vn) lX 3%positive tp w Hi3 HA3s) in HS;
      [| rewrite <- (proj2 Hav 3%positive), <- (proj2 Hav lX); exact Srl].
    change (ax_setS A2 _) with A3 in HS.

    assert (HS4 : SPA segs (JK Kc nd) A4 rho1 tp w).
    { apply (SPA_restate segs _ rho1 A3 S4 tp w d4 [] HS4w HS4d HS4n1); [| constructor | exact HS].
      assert (Htp : eval rho1 vTP = eval rho1 (SLit TP)).
      { pose proof (holds_mem _ _ _ HF1 Htpf) as X. cbn [holds] in X. exact X. }
      unfold diffs_ok. apply Forall_forall. intros [a b] Hab. cbn [fst snd].
      pose proof (proj1 (forallb_forall _ _) Hd4 (a, b) Hab) as QQ. cbn [fst snd] in QQ.
      apply orb_prop in QQ as [QQ|QQ]; [apply orb_prop in QQ as [QQ|QQ]; [apply orb_prop in QQ as [QQ|QQ]|]|];
        apply andb_prop in QQ as [Qa Qb]; apply sv_eqb_sound in Qa; apply sv_eqb_sound in Qb; subst a b;
        [exact Htp | symmetry; exact Htp | symmetry; apply eval_sXc | apply eval_sXc]. }
    clear HS.

    assert (HS5 : SPA segs (JK Kc nd) C1 rho1 tp w).
    { exact (carveK Kc nd A4 rho1 tp w N_fps (ss_next S4) HS4 Cw (Pos.leb_refl _) Cb Cc). }
    clear HS4.

    pose proof (Hlayout rho1 HF1) as (LS & LA & LAN & LAL1 & LAL2 & LN2 & LL3).
    pose proof (proj1 Hav vl (proj1 (proj2 Hvars))) as Evl. pose proof (proj1 Hav vn (proj2 (proj2 Hvars))) as Evn.
    assert (Sslk1 : bv_unsigned (rw rho1 vl) + 17 <= bv_unsigned (rw rho1 vn)) by (rewrite <- Evl, <- Evn; exact Sslk).
    pose proof (XB_facts rho1 vp vl vn LS) as (XB1 & XB2 & XB3). pose proof (XE_facts rho1 vp vl vn LS (conj LAL1 LAL2)) as (XE1 & XE2 & XE3).
    pose proof (U_XBe rho1) as UXB. pose proof (U_XLe rho1 vp vl vn LS (conj LAL1 LAL2)) as UXL.
    change XBe with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB in UXB. change XLe with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XL in UXL.
    pose proof (urange (rw rho1 11)) as R11. pose proof (urange (rw rho1 vn)) as Rvn.
    set (Sz := bv_unsigned (rw rho1 1)) in *. set (ALz := bv_unsigned (rw rho1 11)) in *.
    assert (HS6 : SPA segs (JK Kc nd) A5 rho1 tp w).
    { apply (SPA_publish_sym _ rho1 C1 (nd_tv nd) tp w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XL 0x7fff7fffffc0 (2 ^ 47) Hpubs (JK_tv_bandfree _ _ _ _ _ _ (proj2 HS5)));
        rewrite ?UXB, ?UXL; [lia | lia | exact XB3 | | lia | | exact HS5].
      -
        pose proof (Z.div_mod (Sz + ALz + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (Sz + ALz + 63) 64 ltac:(lia)).
        pose proof (Z.div_mod Sz 64 ltac:(lia)). pose proof (Z.mod_pos_bound Sz 64 ltac:(lia)).
        replace (Sz + ALz + 63 - (Sz + ALz + 63) mod 64 - (Sz - Sz mod 64)) with (((Sz + ALz + 63) / 64 - Sz / 64) * 64) by lia. apply Z_mod_mult.
      -
        intros z Hz. destruct HZA as (_ & _ & HZ). apply HZ. unfold Uv. fold Sz ALz.
        replace (Sz - Sz mod 64 + (Sz + ALz + 63 - (Sz + ALz + 63) mod 64 - (Sz - Sz mod 64))) with (Sz + ALz + 63 - (Sz + ALz + 63) mod 64) in Hz by lia.
        unfold Sh, SHADOW_OFF in *. apply (zarg_hull Sz ALz z); lia. }
    clear HS5.

    assert (HS7 : SPA segs (JK Kc nd) A6 rho1 tp w).
    { apply (SPA_publish_lit2 _ rho1 A5 (nd_tv nd) tp w fblk flen Hpubl (JK_tv_bandfree _ _ _ _ _ _ (proj2 HS6))); [|exact HS6].
      intros z Hz. destruct (Hfblk z Hz) as [Zz|Zz]; [exact (proj2 HSR z Zz) | exact (HS2 z Zz)]. }
    clear HS6.

    unfold C. apply (SPA_add_facts _ rho1 tp (sfl vp vl vn) A6 w); [| | exact HS7].
    - apply (sfl_holds rho1 vp vl vn LS LA LAN (conj LAL1 LAL2) (conj Sslk1 (conj LN2 LL3))).
    - change (ss_next (ax_S A6)) with (ss_next S4). rewrite HS4n1, HS4n2. exact HsfB. }

  set (Jfp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
                JK Kc nd rho1 t tr md /\ (FirstNul r /\ firstn (Z.to_nat (bv_unsigned (rw r 16))) (rl r 3) = str /\ PX (bv_unsigned (eval r sX)))).
  assert (Jfp_stable : stableA segs NF Jfp).
  { intros r r' t tr md md' Hag Hme [HJ (HFN & Hstr & HPXr)]. unfold Jfp. split; [|split; [|split]].
    - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0f [] [] BX0 PA (KcG_okK EV0) ALA (ss_next (ax_S C)) nd Ai kc rho1 rho1 t tr md md' ltac:(apply Pos.leb_le; exact C1n) C2 (agree_below_refl _ _) Hme HJ').
    - eapply (FirstNul_agree NF); [unfold NF; cbv; reflexivity | exact Hag | exact HFN].
    - destruct Hag as (Aw & Al & _). rewrite <- (Aw 16%positive ltac:(unfold NF; lia)), <- (Al 3%positive). exact Hstr.
    - destruct Hag as (Aw & Al & _). unfold sX, vXB, vXO in HPXr |- *. cbn [eval] in HPXr |- *.
      rewrite <- (Aw 18%positive ltac:(unfold NF; lia)), <- (Aw 20%positive ltac:(unfold NF; lia)). exact HPXr. }
  assert (JfpK : forall r t tr md, Jfp r t tr md -> tr = T0 ++ EV0 /\ m_fds md = fds /\ MDX md).
  { intros r t tr md [(Ai & kc & _ & HKc & _) _]. exact HKc. }
  assert (Kwr_tcons : forall k r t tr md, Kwr Jfp pre suf str k r t tr md -> tcons Spec tr).
  { intros k r t tr md (tr0 & HJ & ->). destruct (JfpK _ _ _ _ HJ) as (-> & _ & HX). first [exact (msg_prefix_tcons k md HX) | rewrite <- app_assoc; exact (msg_prefix_tcons k md HX) | rewrite app_assoc; exact (msg_prefix_tcons k md HX)]. }

  assert (HSTR : forall tr ms md, smatchA segs rho1 tp C (tr, mkCfg ms md) -> JK Kc nd rho1 tp tr md ->
            Jfp (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) tp tr md).
  { intros tr ms md Hsm HJ. split; [exact HJ|].
    destruct HJ as (Ai & kc & HJi). pose proof (JK_parts _ _ _ _ _ _ _ _ HJi) as (Hav & _ & _ & HP00).
    destruct (HP0str _ HP00) as (Sfirst & Slen & Srl & _).
    destruct Hav as [Aw Al].
    assert (E16 : rw (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) 16%positive = rw rho0 vl).
    { cbn [rho_sub rw]. rewrite Hs16. cbn [eval rho_absorb rw]. symmetry. apply Aw. exact (proj1 (proj2 Hvars)). }
    assert (E3 : rl (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) 3%positive = rl rho0 lX).
    { cbn [rho_sub rho_absorb rl]. rewrite <- (Al 3%positive). exact Srl. }
    destruct (FirstNul_of_firstn _ _ Sfirst Hnonul) as (F1 & F2 & F3).
    unfold FirstNul. rewrite E16, E3, Slen. split; [split; [exact F1 | exact F2]|]. split; [rewrite Nat2Z.id; exact F3|].

    destruct Hs18 as [S18 S20].
    assert (EsX : eval (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) sX = eval rho1 (SVar vp)).
    { rewrite <- eval_subst. transitivity (eval (rho_absorb rho1 R (vms md tp ms)) (SVar vp)); [| apply eval_absorb].
      unfold sX, vXB, vXO. cbn [sv_subst]. rewrite S18, S20, mk_alu_sound. apply eval_sXc. }
    rewrite EsX. cbn [eval]. apply HPX.
    pose proof (smatchA_facts segs _ _ _ _ Hsm) as HFC. unfold C in HFC. unfold ax_add_facts in HFC. cbn [ax_S ss_facts add_facts] in HFC.
    apply Forall_app in HFC as [_ HF6]. change (ss_facts (ax_S A6)) with (ss_facts S4) in HF6. rewrite HS4f in HF6. exact HF6. }
  apply (pure_callJ AInv CST XGL ALA NF rho0 P0f [] [] BX0 PA ok Kc Kc' C Pre s R Posts_fps rho1 tp nd Jfp (Kwr Jfp pre suf str (length msg)) (fun _ => False) (KcG_okK _)).
  -
    intros rho2 tp2. apply (triple_preK _ _ (FirstNul rho2 /\ firstn (Z.to_nat (bv_unsigned (rw rho2 16))) (rl rho2 3) = str /\ PX (bv_unsigned (eval rho2 sX)))).
    { intros w [_ [_ HX]]. exact HX. }
    intros (HFN2 & Hstr2 & HPX2).
    pose proof (HSUM ok Jfp Jfp_stable ltac:(intros r t tr md HJ; destruct (JfpK _ _ _ _ HJ) as (_ & Hfd & _); rewrite Hfd; exact Hfds2) rho2 tp2 HFN2 HPX2 (FirstNul_len rho2 str HFN2 Hstr2)) as X.
    rewrite Hstr2 in X. apply X; intros k; [apply HOKJ | apply HOKP]; intros r t tr md; apply Kwr_tcons.
  - exact Hfr.
  - exact Hcc.
  - exact C1n.
  - exact C2.
  - exact C3.
  -   exact HSTR.
  -   intros rhoL tr' md' (tr0 & [HJ _] & ->).
    destruct HJ as (Ai & kc & Hav & (Htr & Hfd & HX) & REST). exists Ai, kc. split; [exact Hav|]. split; [|exact REST].
    split; [| split; [exact Hfd | exact HX]]. rewrite Htr. unfold EVS. rewrite firstn_all. rewrite <- !app_assoc. reflexivity.
  -
    intros Lf rho2 HinL Hag2. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C)) (import_postA s Pre P_fps C R)) with (T_after Pre C s R P_fps). rewrite HTq.
    set (evs := EV0 ++ map (WriteEv ch2) msg).
    assert (HtcK' : forall tr md, Kc' tr md -> tcons Spec tr).
    { intros tr md (-> & _ & HX). exists (T0 ++ EV0 ++ map (WriteEv ch2) msg ++ [ExitEv (Z_to_bv 64 2) (m_fs md)]). split; [exact (HSPECm md HX)|].
      unfold evs. rewrite ?app_assoc. rewrite <- ?app_assoc. apply is_prefix_app_mono. apply is_prefix_app_mono. apply is_prefix_app. }

    destruct HS1o as [HS1a HS1b].
    eapply (triple_conseq (P := fun w => exists rho3, SPA segs (JK Kc' nd) V rho3 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      apply (SPA_axforms segs _ _ rho2 Tq S1 tp _ HS1) in HS.
      pose proof (uncarveK Kc' nd S1 rho2 tp tr ms md (ss_objs (ax_S V)) N_fps (KcG_okK _) HS1a ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hndam HnbS1 HS) as HS2.
      rewrite HS1b in HS2. eexists. exact HS2. }
    apply triple_ex. intros rho3.
    eapply (JK_run AInv CST XGL ALA ok Spec HOKJ Kc' (KcG_okK _) rho0 P0f HtcK' PA nd); [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lx rho4 [<-|[]] Hag4. cbn [la_state].

    unfold carve_chk in HB3. apply andb_prop in HB3 as [HB3a Xb]. apply andb_prop in HB3a as [Xw Xc]. apply sv_eqb_sound in Xb.
    eapply (triple_conseq (P := SPA segs (JK Kc' nd) CX rho4 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
    { apply (SPA_axforms segs _ _ rho4 Xl B0 tp _ HB0) in HS.
      apply (SPA_x_sub segs _ rho4 B0 [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HS. change (ax_setX B0 []) with B1 in HS.
      apply (SPA_img_cell segs _ rho4 B1 _ _ _ _ tp w Himg) in HS. change (ax_setS B1 _) with B2 in HS.
      assert (HS3 : SPA segs (JK Kc' nd) B3 rho4 tp w).
      { exact (carveK Kc' nd B2 rho4 tp w N_ex (ss_next (ax_S B2)) HS Xw (Pos.leb_refl _) Xb Xc). }
      clear HS. apply (SPA_x4set _ rho4 B3 (SLit TP) tp w Hx4) in HS3. exact HS3. }

    apply (X_exit_call AInv CST XGL ALA ok Spec HOKJ HOKP Hokh Kc' (KcG_okK _) rho0 P0f PA false nd 0 2 CX (s_exR 0 CX) Rx X1 X2 Hfrx Hccx X3).
    + cbn. tauto.
    + intros tr md (-> & Hfd & HX). unfold evs. cbn [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface.PEND map]. rewrite <- !app_assoc. cbn [app]. exact (HSPECm md HX).
    + intros tr md (_ & Hfd & _). rewrite Hfd. exact Hfds1.
Qed.

Theorem fps_tail_ex : ltac2:(tb__ "0|1|
S66OF_;S66S1bVMDX;R1A1S0S9S1aA1S6aR3A1SfS1aVT0;SfS1aVEV0;SfS1aS6dS54Q8A1S1aS1fS60A1Vmsg;A4SdS1aS20S55Q40M0Z2A2S22R2A1A2ScS1aA1A3A3A3A3A3R5R4A1F_;F_;Fmd;Fw;S30S9S54G0A1A1S67S2fS61S2fVJK;VKc;Vnd;A2VE;R2R1A5R4A3Ftp;Frho;F_;FQ;").
Proof.
  intros Q HQ rho tp.
  destruct HnE as (N1 & N2 & N3). destruct HS4n as [HS4n1 HS4n2]. destruct HnC as (C1n & C2 & C3). destruct HnV as (V1 & V2 & V3). destruct HnX as (X1 & X2 & X3).

  eapply (JK_erun AInv CST XGL ALA Kc (KcG_okK EV0) rho0 P0f PA nd);
    [exact Hrun1 | exact N2 | exact N1 | exact N3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].

  unfold carve_chk in HC1. apply andb_prop in HC1 as [HC1 Cb]. apply andb_prop in HC1 as [Cw Cc]. apply sv_eqb_sound in Cb.
  eapply (etriple_conseq (P := SPA segs (JK Kc nd) C rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { pose proof HS as [[Hsm1 _] (Ai & kc & HJi)]. pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HF1.
    pose proof (JK_parts _ _ _ _ _ _ _ _ HJi) as (Hav & HKc & HK0 & HP00).
    destruct (ZX_nowK _ _ _ _ _ _ _ _ HJi) as (HZA & HS2 & HSR).
    destruct (HP0str _ HP00) as (Sfirst & Slen & Srl & Sslk).

    apply (SPA_splits _ cuts rho1 E1 tp w Hspl) in HS. change (splitsA cuts E1) with A2 in HS.

    apply (SPA_relist _ rho1 A2 i3 (SVar vp) (SLit 0) (SVar vn) lX 3%positive tp w Hi3 HA3s) in HS;
      [| rewrite <- (proj2 Hav 3%positive), <- (proj2 Hav lX); exact Srl].
    change (ax_setS A2 _) with A3 in HS.

    assert (HS4 : SPA segs (JK Kc nd) A4 rho1 tp w).
    { apply (SPA_restate segs _ rho1 A3 S4 tp w d4 [] HS4w HS4d HS4n1); [| constructor | exact HS].
      assert (Htp : eval rho1 vTP = eval rho1 (SLit TP)).
      { pose proof (holds_mem _ _ _ HF1 Htpf) as X. cbn [holds] in X. exact X. }
      unfold diffs_ok. apply Forall_forall. intros [a b] Hab. cbn [fst snd].
      pose proof (proj1 (forallb_forall _ _) Hd4 (a, b) Hab) as QQ. cbn [fst snd] in QQ.
      apply orb_prop in QQ as [QQ|QQ]; [apply orb_prop in QQ as [QQ|QQ]; [apply orb_prop in QQ as [QQ|QQ]|]|];
        apply andb_prop in QQ as [Qa Qb]; apply sv_eqb_sound in Qa; apply sv_eqb_sound in Qb; subst a b;
        [exact Htp | symmetry; exact Htp | symmetry; apply eval_sXc | apply eval_sXc]. }
    clear HS.

    assert (HS5 : SPA segs (JK Kc nd) C1 rho1 tp w).
    { exact (carveK Kc nd A4 rho1 tp w N_fps (ss_next S4) HS4 Cw (Pos.leb_refl _) Cb Cc). }
    clear HS4.

    pose proof (Hlayout rho1 HF1) as (LS & LA & LAN & LAL1 & LAL2 & LN2 & LL3).
    pose proof (proj1 Hav vl (proj1 (proj2 Hvars))) as Evl. pose proof (proj1 Hav vn (proj2 (proj2 Hvars))) as Evn.
    assert (Sslk1 : bv_unsigned (rw rho1 vl) + 17 <= bv_unsigned (rw rho1 vn)) by (rewrite <- Evl, <- Evn; exact Sslk).
    pose proof (XB_facts rho1 vp vl vn LS) as (XB1 & XB2 & XB3). pose proof (XE_facts rho1 vp vl vn LS (conj LAL1 LAL2)) as (XE1 & XE2 & XE3).
    pose proof (U_XBe rho1) as UXB. pose proof (U_XLe rho1 vp vl vn LS (conj LAL1 LAL2)) as UXL.
    change XBe with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB in UXB. change XLe with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XL in UXL.
    pose proof (urange (rw rho1 11)) as R11. pose proof (urange (rw rho1 vn)) as Rvn.
    set (Sz := bv_unsigned (rw rho1 1)) in *. set (ALz := bv_unsigned (rw rho1 11)) in *.
    assert (HS6 : SPA segs (JK Kc nd) A5 rho1 tp w).
    { apply (SPA_publish_sym _ rho1 C1 (nd_tv nd) tp w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ga.FpsSite_states.XL 0x7fff7fffffc0 (2 ^ 47) Hpubs (JK_tv_bandfree _ _ _ _ _ _ (proj2 HS5)));
        rewrite ?UXB, ?UXL; [lia | lia | exact XB3 | | lia | | exact HS5].
      -
        pose proof (Z.div_mod (Sz + ALz + 63) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (Sz + ALz + 63) 64 ltac:(lia)).
        pose proof (Z.div_mod Sz 64 ltac:(lia)). pose proof (Z.mod_pos_bound Sz 64 ltac:(lia)).
        replace (Sz + ALz + 63 - (Sz + ALz + 63) mod 64 - (Sz - Sz mod 64)) with (((Sz + ALz + 63) / 64 - Sz / 64) * 64) by lia. apply Z_mod_mult.
      -
        intros z Hz. destruct HZA as (_ & _ & HZ). apply HZ. unfold Uv. fold Sz ALz.
        replace (Sz - Sz mod 64 + (Sz + ALz + 63 - (Sz + ALz + 63) mod 64 - (Sz - Sz mod 64))) with (Sz + ALz + 63 - (Sz + ALz + 63) mod 64) in Hz by lia.
        unfold Sh, SHADOW_OFF in *. apply (zarg_hull Sz ALz z); lia. }
    clear HS5.

    assert (HS7 : SPA segs (JK Kc nd) A6 rho1 tp w).
    { apply (SPA_publish_lit2 _ rho1 A5 (nd_tv nd) tp w fblk flen Hpubl (JK_tv_bandfree _ _ _ _ _ _ (proj2 HS6))); [|exact HS6].
      intros z Hz. destruct (Hfblk z Hz) as [Zz|Zz]; [exact (proj2 HSR z Zz) | exact (HS2 z Zz)]. }
    clear HS6.

    unfold C. apply (SPA_add_facts _ rho1 tp (sfl vp vl vn) A6 w); [| | exact HS7].
    - apply (sfl_holds rho1 vp vl vn LS LA LAN (conj LAL1 LAL2) (conj Sslk1 (conj LN2 LL3))).
    - change (ss_next (ax_S A6)) with (ss_next S4). rewrite HS4n1, HS4n2. exact HsfB. }

  set (Jfp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
                JK Kc nd rho1 t tr md /\ (FirstNul r /\ firstn (Z.to_nat (bv_unsigned (rw r 16))) (rl r 3) = str /\ PX (bv_unsigned (eval r sX)))).
  assert (Jfp_stable : stableA segs NF Jfp).
  { intros r r' t tr md md' Hag Hme [HJ (HFN & Hstr & HPXr)]. unfold Jfp. split; [|split; [|split]].
    - destruct HJ as (Ai & kc & HJ'). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF _ rho0 P0f [] [] BX0 PA (KcG_okK EV0) ALA (ss_next (ax_S C)) nd Ai kc rho1 rho1 t tr md md' ltac:(apply Pos.leb_le; exact C1n) C2 (agree_below_refl _ _) Hme HJ').
    - eapply (FirstNul_agree NF); [unfold NF; cbv; reflexivity | exact Hag | exact HFN].
    - destruct Hag as (Aw & Al & _). rewrite <- (Aw 16%positive ltac:(unfold NF; lia)), <- (Al 3%positive). exact Hstr.
    - destruct Hag as (Aw & Al & _). unfold sX, vXB, vXO in HPXr |- *. cbn [eval] in HPXr |- *.
      rewrite <- (Aw 18%positive ltac:(unfold NF; lia)), <- (Aw 20%positive ltac:(unfold NF; lia)). exact HPXr. }
  assert (JfpK : forall r t tr md, Jfp r t tr md -> tr = T0 ++ EV0 /\ m_fds md = fds /\ MDX md).
  { intros r t tr md [(Ai & kc & _ & HKc & _) _]. exact HKc. }
  assert (Kwr_tcons : forall k r t tr md, Kwr Jfp pre suf str k r t tr md -> tcons Spec tr).
  { intros k r t tr md (tr0 & HJ & ->). destruct (JfpK _ _ _ _ HJ) as (-> & _ & HX). first [exact (msg_prefix_tcons k md HX) | rewrite <- app_assoc; exact (msg_prefix_tcons k md HX) | rewrite app_assoc; exact (msg_prefix_tcons k md HX)]. }

  assert (HSTR : forall tr ms md, smatchA segs rho1 tp C (tr, mkCfg ms md) -> JK Kc nd rho1 tp tr md ->
            Jfp (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) tp tr md).
  { intros tr ms md Hsm HJ. split; [exact HJ|].
    destruct HJ as (Ai & kc & HJi). pose proof (JK_parts _ _ _ _ _ _ _ _ HJi) as (Hav & _ & _ & HP00).
    destruct (HP0str _ HP00) as (Sfirst & Slen & Srl & _).
    destruct Hav as [Aw Al].
    assert (E16 : rw (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) 16%positive = rw rho0 vl).
    { cbn [rho_sub rw]. rewrite Hs16. cbn [eval rho_absorb rw]. symmetry. apply Aw. exact (proj1 (proj2 Hvars)). }
    assert (E3 : rl (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) 3%positive = rl rho0 lX).
    { cbn [rho_sub rho_absorb rl]. rewrite <- (Al 3%positive). exact Srl. }
    destruct (FirstNul_of_firstn _ _ Sfirst Hnonul) as (F1 & F2 & F3).
    unfold FirstNul. rewrite E16, E3, Slen. split; [split; [exact F1 | exact F2]|]. split; [rewrite Nat2Z.id; exact F3|].

    destruct Hs18 as [S18 S20].
    assert (EsX : eval (rho_sub (rho_absorb rho1 R (vms md tp ms)) s) sX = eval rho1 (SVar vp)).
    { rewrite <- eval_subst. transitivity (eval (rho_absorb rho1 R (vms md tp ms)) (SVar vp)); [| apply eval_absorb].
      unfold sX, vXB, vXO. cbn [sv_subst]. rewrite S18, S20, mk_alu_sound. apply eval_sXc. }
    rewrite EsX. cbn [eval]. apply HPX.
    pose proof (smatchA_facts segs _ _ _ _ Hsm) as HFC. unfold C in HFC. unfold ax_add_facts in HFC. cbn [ax_S ss_facts add_facts] in HFC.
    apply Forall_app in HFC as [_ HF6]. change (ss_facts (ax_S A6)) with (ss_facts S4) in HF6. rewrite HS4f in HF6. exact HF6. }
  apply (pure_callJ_ex AInv CST XGL ALA NF rho0 P0f [] [] BX0 PA Kc Kc' C Pre s R Posts_fps rho1 tp nd Jfp (Kwr Jfp pre suf str (length msg)) Q (KcG_okK _)).
  -
    intros rho2 tp2. apply (etriple_preK _ (FirstNul rho2 /\ firstn (Z.to_nat (bv_unsigned (rw rho2 16))) (rl rho2 3) = str /\ PX (bv_unsigned (eval rho2 sX)))).
    { intros w [_ [_ HX]]. exact HX. }
    intros (HFN2 & Hstr2 & HPX2).
    pose proof (HSUMX Jfp Jfp_stable ltac:(intros r t tr md HJ; destruct (JfpK _ _ _ _ HJ) as (_ & Hfd & _); rewrite Hfd; exact Hfds2) rho2 tp2 HFN2 HPX2 (FirstNul_len rho2 str HFN2 Hstr2)) as X.
    rewrite Hstr2 in X. exact X.
  - exact Hfr.
  - exact Hcc.
  - exact C1n.
  - exact C2.
  - exact C3.
  -   exact HSTR.
  -   intros rhoL tr' md' (tr0 & [HJ _] & ->).
    destruct HJ as (Ai & kc & Hav & (Htr & Hfd & HX) & REST). exists Ai, kc. split; [exact Hav|]. split; [|exact REST].
    split; [| split; [exact Hfd | exact HX]]. rewrite Htr. unfold EVS. rewrite firstn_all. rewrite <- !app_assoc. reflexivity.
  -
    intros Lf rho2 HinL Hag2. destruct HinL as [<-|[]]. cbn [la_state].
    change (ax_add_facts (ss_facts (ax_S C)) (import_postA s Pre P_fps C R)) with (T_after Pre C s R P_fps). rewrite HTq.
    set (evs := EV0 ++ map (WriteEv ch2) msg).
    assert (HtcK' : forall tr md, Kc' tr md -> tcons Spec tr).
    { intros tr md (-> & _ & HX). exists (T0 ++ EV0 ++ map (WriteEv ch2) msg ++ [ExitEv (Z_to_bv 64 2) (m_fs md)]). split; [exact (HSPECm md HX)|].
      unfold evs. rewrite ?app_assoc. rewrite <- ?app_assoc. apply is_prefix_app_mono. apply is_prefix_app_mono. apply is_prefix_app. }

    destruct HS1o as [HS1a HS1b].
    eapply (etriple_conseq (P := fun w => exists rho3, SPA segs (JK Kc' nd) V rho3 tp w)); [intros w HS | intros w' Hw'; exact Hw' |].
    { destruct w as [tr [ms md]].
      apply (SPA_axforms segs _ _ rho2 Tq S1 tp _ HS1) in HS.
      pose proof (uncarveK Kc' nd S1 rho2 tp tr ms md (ss_objs (ax_S V)) N_fps (KcG_okK _) HS1a ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hndam HnbS1 HS) as HS2.
      rewrite HS1b in HS2. eexists. exact HS2. }
    apply etriple_ex. intros rho3.
    eapply (JK_erun AInv CST XGL ALA Kc' (KcG_okK _) rho0 P0f PA nd); [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros Lx rho4 [<-|[]] Hag4. cbn [la_state].

    unfold carve_chk in HB3. apply andb_prop in HB3 as [HB3a Xb]. apply andb_prop in HB3a as [Xw Xc]. apply sv_eqb_sound in Xb.
    eapply (etriple_conseq (P := SPA segs (JK Kc' nd) CX rho4 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
    { apply (SPA_axforms segs _ _ rho4 Xl B0 tp _ HB0) in HS.
      apply (SPA_x_sub segs _ rho4 B0 [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HS. change (ax_setX B0 []) with B1 in HS.
      apply (SPA_img_cell segs _ rho4 B1 _ _ _ _ tp w Himg) in HS. change (ax_setS B1 _) with B2 in HS.
      assert (HS3 : SPA segs (JK Kc' nd) B3 rho4 tp w).
      { exact (carveK Kc' nd B2 rho4 tp w N_ex (ss_next (ax_S B2)) HS Xw (Pos.leb_refl _) Xb Xc). }
      clear HS. apply (SPA_x4set _ rho4 B3 (SLit TP) tp w Hx4) in HS3. exact HS3. }

    apply (X_exit_call_ex AInv CST XGL ALA Kc' (KcG_okK _) rho0 P0f PA false nd 0 2 CX (s_exR 0 CX) Rx X1 X2 Hfrx).
    + cbn. tauto.
    + intros tr md (_ & Hfd & _). rewrite Hfd. exact Hfds1.
    + intros w tr md (-> & Hfd & HX) Hw. apply (HQ w md HX). rewrite Hw. unfold evs. cbn [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface.PEND map]. rewrite <- !app_assoc. reflexivity.
Qed.
End FPSTAIL.

Definition layout_okb (facts : list sprop) (vp vl vn : positive) : bool := ltac2:(tb__ "0|8|
S13S13S13S13S13S13S13SfcVfacts;A1S16S79S31S3dS38S3cS7dS36P1A1M0S34Z18A1A3S36Vvp;A1M1A2A1Vfacts;A3S79S31S3dS38S3cS7dG0S34Z20A1A3G1A2A1Vfacts;A3A2A2S79S31S3dS38S3cS7dG1S36Vvn;A1M2A3S3cS7dG0S36PbA1M3A3M4A2A1Vfacts;A3A2S79S31S3dS38G4S34S26Z2M5Z2fA2A1M6A2A1Vfacts;A3A2S79S31S3dS38G3S34S26G5Z17A2A1A2A1Vfacts;A3A2S79S31S3dS38G2S34S26G5Z16A2A1A2A1Vfacts;A3A2S16S79S31S3dS38S36Vvl;A1M7S34Z1ffffA1A2A1Vfacts;A3S79S31S3dS38G7S34ZfffA1A2A1Vfacts;A3A2A2S79S31S3dS38G1G6A2A1Vfacts;A3A2").

Lemma layout_okb_sound : ltac2:(tb__ "0|8|
S9S31A1S8S8S8S30S0SbSa7R5R4R3R2A4SaA3S6eS31S41R2A1R6A3S1S1S24Z7fff80000000S53Q40M0S32R3P1A2A2M1A2S24G1S29S26Z2M2Z2fA2M3Ze0A2A2A2S1S24S25G1Z18A2S53G0S32R3R6A2A2M4A2S1S24S25G4S53G0S32R3R4A2A2M5A2S25G1S53G0S32R3PbA2A2M6A2M7A2S1S24G7G3A2S1S24G6S26G2Z17A2A2S1S24G5S26G2Z16A2A2S24S53G0S32R3R5A2A2Z1ffffA2A2A2A2A2A2A2F_;F_;Frho;Fvn;Fvl;Fvp;Ffacts;").
Proof.
  intros facts vp vl vn rho H HF. unfold layout_okb in H.
  apply andb_prop in H as [H F8]. apply andb_prop in H as [H F7]. apply andb_prop in H as [H F6]. apply andb_prop in H as [H F5].
  apply andb_prop in H as [H F4]. apply andb_prop in H as [H F3]. apply andb_prop in H as [F1 F2].
  pose proof (proj1 (sp0_facts_sound rho facts HF F1)) as S1.
  pose proof (urange (rw rho 1)) as R1. pose proof (urange (rw rho 11)) as R11. pose proof (urange (rw rho vp)) as Rp.
  pose proof (urange (rw rho vn)) as Rn. pose proof (urange (rw rho vl)) as Rl.
  pose proof (holds_mem _ _ _ HF F8) as A8. cbn [holds eval] in A8. rewrite lit_unsigned in A8. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47) in A8.
  pose proof (holds_mem _ _ _ HF F4) as A4. cbn [holds] in A4. rewrite (U_lit64 rho (2 ^ 47)) in A4 by lia.
  pose proof (holds_mem _ _ _ HF F5) as A5. cbn [holds eval] in A5. rewrite (lit_unsigned) in A5. change ((2 ^ 23) mod 2 ^ 64) with (2 ^ 23) in A5.
  pose proof (holds_mem _ _ _ HF F6) as A6. cbn [holds eval] in A6. rewrite (lit_unsigned) in A6. change ((2 ^ 22) mod 2 ^ 64) with (2 ^ 22) in A6.
  rewrite (U_add2 rho (SVar 1) (SVar 11) _ _ eq_refl eq_refl) in A4 by (cbn [eval]; lia). cbn [eval] in A4.
  pose proof (holds_mem _ _ _ HF F3) as A3. cbn [holds] in A3.
  rewrite (U_add2 rho (SVar vp) (SVar vn) _ _ eq_refl eq_refl) in A3 by (cbn [eval]; lia).
  rewrite (U_add2 rho (SVar 1) (SVar 11) _ _ eq_refl eq_refl) in A3 by (cbn [eval]; lia). cbn [eval] in A3.
  assert (A2 : bv_unsigned (rw rho 1) + 24 <= bv_unsigned (rw rho vp)).
  { apply orb_prop in F2 as [F2|F2]; pose proof (holds_mem _ _ _ HF F2) as X; cbn [holds] in X;
      [rewrite (U_addc rho (SVar 1) 24 _ eq_refl) in X by (cbn [eval]; lia) | rewrite (U_addc rho (SVar 1) 32 _ eq_refl) in X by (cbn [eval]; lia)];
      cbn [eval] in X; lia. }
  assert (A7 : bv_unsigned (rw rho vl) <= 131071).
  { apply orb_prop in F7 as [F7|F7]; pose proof (holds_mem _ _ _ HF F7) as X; cbn [holds eval] in X; rewrite lit_unsigned in X;
      [change (131071 mod 2 ^ 64) with 131071 in X | change (4095 mod 2 ^ 64) with 4095 in X]; lia. }
  repeat split; lia.
Qed.

Definition d4_okb (vp : positive) (d : list (sv * sv)) : bool := ltac2:(tb__ "0|6|
S7aSeS33S33A2M0G0S16S16S16S13S3eS18S33S33R1A3M1S8cA2S3eS19S33S33R1A3M2S34S89A1M3A2A2S13S3eG1G3A2S3eG2S8cA2A2A2S13S3eG1S36Vvp;A1M4A2S3eG2Sb8G4A1M5A2A2A2S13S3eG1G5A2S3eG2G4A2A2A2Lpr;Vd;A3").

Definition siteA2 (cuts : list (nat * Z)) (E1 : axst) : axst := splitsA cuts E1.
Definition siteI3 (vp : positive) (A2 : axst) : nat := ltac2:(tb__ "0|0|
S8eS3bS56VA2;A1A1S36Vvp;A1S34Z0A1A3").
Definition siteA3 (vp vn : positive) (A2 : axst) : axst := ltac2:(tb__ "0|0|
S59VA2;S141S56VA2;A1Sa5Vvp;VA2;A2S44S36Vvp;A1S34Z0A1S36Vvn;A1ScS43A1S42P3A1A5A3A2").

Definition siteS4 (vp vn : positive) (A3 : axst) : sstate := ltac2:(tb__ "0|1|
SebS34S89A1VA3;A2S57S56Sc3S59R1S141S56R1A1Sa5Vvp;VA3;A2SbfS36Vvp;A1M0S36Vvn;A1A2A3A2UcSb8G0A1A3A1TA;").
Definition siteC1 (A3 : axst) (S4 : sstate) : axst := ltac2:(tb__ "0|0|
S59S59VA3;VS4;A2Sf9VS4;Sb2A2A2").
Definition siteA5 (C1 : axst) : axst := ltac2:(tb__ "0|0|
Sc7VC1;SdSeS33S33A2S15S33S33Sb5Sb6A4S5cVC1;A1A3A2").
Definition siteA6 (fblk flen : Z) (A5 : axst) : axst := ltac2:(tb__ "0|0|
Sc7VA5;SdSeS33S33A2S15S33S33S34Vfblk;A1S34Vflen;A1A4S5cVA5;A1A3A2").
Definition siteC (vp vl vn : positive) (A6 : axst) : axst := ltac2:(tb__ "0|0|
S146Sa2Vvp;Vvl;Vvn;A3VA6;A2").
Definition exB3 (B0 : axst) : axst := ltac2:(tb__ "0|0|
Se9Sc7VB0;ScSeS33S33A2A1A2A1S57S59R1Sf9S56R1A1S8dA2A2TB2;").
Definition exCX (B3 : axst) : axst := x4set (SLit TP) B3.

Module SiteC.
Definition cuts := cuts_C.
Definition A2 : axst := Eval vm_compute in siteA2 cuts E_C.
Definition A3 : axst := Eval vm_compute in siteA3 8 10 A2.
Definition S4 : sstate := Eval vm_compute in siteS4 8 10 A3.
Definition d4 : list (sv * sv) := Eval vm_compute in match state_diff (ax_S A3) S4 with Some (d, _) => d | None => [] end.
Definition C1 : axst := Eval vm_compute in siteC1 A3 S4.
Definition A5 : axst := Eval vm_compute in siteA5 C1.
Definition A6 : axst := Eval vm_compute in siteA6 0x1eec0 0x80 A5.
Definition C : axst := Eval vm_compute in siteC 8 9 10 A6.
Definition s : wsub := Eval vm_compute in s_fps vL1 vL3 vA1 C Pre_co.
Definition R : list sobj := Eval vm_compute in optR (entails_frA C Pre_co s).
Definition Tq : axst := Eval vm_compute in T_after Pre_co C s R P_fps.
Definition S1 : axst := Eval vm_compute in match apply_axforms Tq [AXSelect (fps_u1 (length (ss_objs (ax_S Tq))))] with Some x => x | None => Tq end.
Definition V : axst := Eval vm_compute in ax_setS S1 (set_objs (ax_S S1) (firstn (length (ss_objs (ax_S S1)) - 3) (ss_objs (ax_S S1)))).
Definition LV2 : list leafA := Eval vm_compute in runS 40 V.
Definition Xl : axst := Eval vm_compute in nthA V LV2 0.
Definition xsE : list axform := [AXSplit 0 (SLit (-1024))].
Definition B0 : axst := Eval vm_compute in match apply_axforms Xl xsE with Some x => x | None => Xl end.
Definition B3 : axst := Eval vm_compute in exB3 B0.
Definition CX : axst := Eval vm_compute in exCX B3.
Definition Rx : list sobj := Eval vm_compute in optR (entails_frA CX (Pre_exit0 0 2) (s_exR 0 CX)).

Lemma facts : ltac2:(tb__ "0|19|
S1S0S57S10dSbbA3S1S0S57S106SbdA3S1S0SbSa6S10fSb9A2SaA3S1S0S11S35A1S7bS35S3bS56S104A1M0A1Sa5P8M1S104A2A3S10S35S44S36G1A1S34Z0M2A1S36PaM3A1ScS43A1S42P3A1A5A2A3S1S0SbSedG0S56S10bA1M4A2SaA3S1S0SbS47S101A1SaA3S1S0S11SeS9SeS33S33A2M5A1M6S9S31A1M7A2M8A1SecG4S101A2S10G8S15G6G7S109ScS31A1A4A2A3S1S1S0S8S37S101A1S37G4A1M9A3S0S8G9S37S56Sb9A1MaA1MbA3A2S1S0SbSa9G1S109A2SaA3S1S0SbS79S31S3dS46S8cS34S89A1McA2A1S39GaA1MdA3SaA3S1S0SbS7aS31S40GbA1Sa2G1P9MeG3A3A3SaA3S1S0SbSa7GdG1GeG3A4SaA3S1S0S33Se0S10aP10A2S36GeA1A3S1S0S57SfbSdfS106S10aS10eS78A5S102A3S1S0S11S57A1MfS96S102SdS95S97Sb7S12S35S3bS56S102A1A1A2A1A1ScS95A1A3A2S10S57S100A2A3S1S1S0S9S35A1M10S3bS56S100A1M11A1SfS35S3bS56S103A1M12A1M13S6dS9aS35S9bSb2A4A3A3S0S57S59S100Se3G11G13A2A2S103A3A2S1S0S11S9S58A1M14A1S5bS2fU28Sb3S103SaA5S10G14SdS58S5aS108Se2A2ScS58A1A3A2A3S1S1S0SbS8aS5fS37G12A1A2SaA3S0SbS45G12A1S17A3A2S1S0GfS96S108S110A2S10S57S105A2A3S1S0SbSe8Sc7S105ScG5A1A2A1SaA3S1S0SbSe7S10cGcA2SaA3S1S1S0SbS8aS5fS37S56SffA1M15A1M16A2SaA3S0SbS7aS31S40G16A1S39G15A1A3SaA3A2S1S0S11G10A1SefSffSe5G2Z2A2M17Se6G2SffA2M18A3S10G10S107A2A3S0SbSeeSffG17G18S107ScS57A1A5SaA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SiteC.

Module SiteD.

Definition iE : nat := 6.
Definition oD : sobj := Eval vm_compute in match nth_error (ss_objs (ax_S D_rde)) iE with
  Some o => mkObj (SLit TP) (ob_lo o) (ob_hi o) (ob_cells o) (ob_dflt o) | None => mkObj (SLit 0) (SLit 0) (SLit 0) [] DUnknown end.
Definition SD1 : sstate := Eval vm_compute in set_obj_at (ax_S D_rde) iE oD.
Definition dD1 : list (sv * sv) := Eval vm_compute in match state_diff (ax_S D_rde) SD1 with Some (d, _) => d | None => [] end.
Definition D1 : axst := Eval vm_compute in ax_setS D_rde SD1.
Definition xsD : list axform := ltac2:(tb__ "0|0|
SdS95S98S128S2eS89A1A2ScS95A1A3").
Definition D2 : axst := Eval vm_compute in match apply_axforms D1 xsD with Some x => x | None => D1 end.
Definition LV1 : list leafA := Eval vm_compute in runS 60 D2.
Definition E1 : axst := Eval vm_compute in nthA D2 LV1 0.
Definition cuts := cuts_D.
Definition A2 : axst := Eval vm_compute in siteA2 cuts E1.
Definition A3 : axst := Eval vm_compute in siteA3 8 10 A2.
Definition S4 : sstate := Eval vm_compute in siteS4 8 10 A3.
Definition d4 : list (sv * sv) := Eval vm_compute in match state_diff (ax_S A3) S4 with Some (d, _) => d | None => [] end.
Definition C1 : axst := Eval vm_compute in siteC1 A3 S4.
Definition A5 : axst := Eval vm_compute in siteA5 C1.
Definition A6 : axst := Eval vm_compute in siteA6 0x1eec0 0x80 A5.
Definition C : axst := Eval vm_compute in siteC 8 9 10 A6.
Definition s : wsub := Eval vm_compute in s_fps vL1 vL3 vA1 C Pre_rde.
Definition R : list sobj := Eval vm_compute in optR (entails_frA C Pre_rde s).
Definition Tq : axst := Eval vm_compute in T_after Pre_rde C s R P_fps.
Definition S1 : axst := Eval vm_compute in match apply_axforms Tq [AXSelect (fps_u1 (length (ss_objs (ax_S Tq))))] with Some x => x | None => Tq end.
Definition V : axst := Eval vm_compute in ax_setS S1 (set_objs (ax_S S1) (firstn (length (ss_objs (ax_S S1)) - 3) (ss_objs (ax_S S1)))).
Definition LV2 : list leafA := Eval vm_compute in runS 40 V.
Definition Xl : axst := Eval vm_compute in nthA V LV2 0.
Definition xsE : list axform := [AXSplit 0 (SLit (-1024))].
Definition B0 : axst := Eval vm_compute in match apply_axforms Xl xsE with Some x => x | None => Xl end.
Definition B3 : axst := Eval vm_compute in exB3 B0.
Definition CX : axst := Eval vm_compute in exCX B3.
Definition Rx : list sobj := Eval vm_compute in optR (entails_frA CX (Pre_exit0 0 2) (s_exR 0 CX)).

Lemma pre_facts : ltac2:(tb__ "0|7|
S1S0SbS47S116A1SaA3S1S0S11SeS9SeS33S33A2M0A1M1S9S31A1M2A2M3A1SecS56Sf7A1M4S116A2S10G3S15G1G2S11fScS31A1A4A2A3S1S0S8S37S116A1S37G4A1A3S1S0G1S11fSdG0S15S33S33S8cS34S89A1M5A4ScG0A1A3A3S1S0SbS79S31S3dS46S8cG5A2A1S39G4A1A3SaA3S1S0S11S57A1S96S125S129A2S10S57S114A2A3S0S11S9S58A1M6A1S5bS2fU3cSb3S114SaA5S10G6SdS58S5aS112Se2A2ScS58A1A3A2A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma facts : ltac2:(tb__ "0|1c|
S1S0SbSa6S127S112A2SaA3S1S0S11S35A1S7bS35S3bS56S119A1M0A1Sa5P8M1S119A2A3S10S35S44S36G1A1S34Z0M2A1S36PaM3A1ScS43A1S42P3A1A5A2A3S1S0SbSedG0S56S11aA1M4A2SaA3S1S0SbS47S113A1SaA3S1S0S11SeS9SeS33S33A2M5A1M6S9S31A1M7A2M8A1SecG4S113A2S10G8S15G6G7S11eScS31A1A4A2A3S1S1S0S8S37S113A1S37G4A1M9A3S0S8G9S37S56S112A1MaA1MbA3A2S1S0SbSa9G1S11eA2SaA3S1S0SbS79S31S3dS46S8cS34S89A1McA2A1S39GaA1MdA3SaA3S1S0SbS7aS31S40GbA1Sa2G1P9MeG3A3A3SaA3S1S0SbSa7GdG1GeG3A4SaA3S1S0SbSf8S59S11aS113A2Sc9SfaA1MfSb2A3SaA3S1S0SbS145S124GfSb5Sb6Z7fff7fffffc0S26Z2M10Z2fA2A6SaA3S1S0SbS144S121GfZ1eec0Z80A4SaA3S1S0S33Se0S120P10A2S36GeA1A3S1S0S57SfbSc0S123S120S126S78A5S117A3S1S0S11S57A1M11S96S117SdS95S97Sb7S12S35S3bS56S117A1A1A2A1A1ScS95A1A3A2S10S57S115A2A3S1S1S0S9S35A1M12S3bS56S115A1M13A1SfS35S3bS56S118A1M14A1M15S6dS9aS35S9bSb2A4A3A3S0S57S59S115Se3G13G15A2A2S118A3A2S1S0S11S9S58A1M16A1S5bS2fU28Sb3S118SaA5S10G16SdS58S5aS11dSe2A2ScS58A1A3A2A3S1S1S0SbS8aS5fS37G14A1A2SaA3S0SbS45G14A1S17A3A2S1S0G11S96S11dS12aA2S10S57S11bA2A3S1S0SbSe8Sc7S11bScG5A1A2M17A1SaA3S1S0SbSf8Se9G17A1GfS8dA3SaA3S1S0SbSe7S122GcA2SaA3S1S1S0SbS8aS5fS37S56S111A1M18A1M19A2SaA3S0SbS7aS31S40G19A1S39G18A1A3SaA3A2S1S0S11G12A1SefS111Se5G2G10A2M1aSe6G2S111A2M1bA3S10G12S11cA2A3S0SbSeeS111G1aG1bS11cScS57A1A5SaA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SiteD.

Module SiteU.
Definition cuts := cuts_U.
Definition A2 : axst := Eval vm_compute in siteA2 cuts E_U.
Definition A3 : axst := Eval vm_compute in siteA3 4 12 A2.
Definition S4 : sstate := Eval vm_compute in siteS4 4 12 A3.
Definition d4 : list (sv * sv) := Eval vm_compute in match state_diff (ax_S A3) S4 with Some (d, _) => d | None => [] end.
Definition C1 : axst := Eval vm_compute in siteC1 A3 S4.
Definition A5 : axst := Eval vm_compute in siteA5 C1.
Definition A6 : axst := Eval vm_compute in siteA6 0x16080 0x80 A5.
Definition C : axst := Eval vm_compute in siteC 4 5 12 A6.
Definition s : wsub := Eval vm_compute in s_fps vL0 vL2 vA0 C Pre_use.
Definition R : list sobj := Eval vm_compute in optR (entails_frA C Pre_use s).
Definition Tq : axst := Eval vm_compute in T_after Pre_use C s R P_fps.
Definition S1 : axst := Eval vm_compute in match apply_axforms Tq [AXSelect (fps_u1 (length (ss_objs (ax_S Tq))))] with Some x => x | None => Tq end.
Definition V : axst := Eval vm_compute in ax_setS S1 (set_objs (ax_S S1) (firstn (length (ss_objs (ax_S S1)) - 3) (ss_objs (ax_S S1)))).
Definition LV2 : list leafA := Eval vm_compute in runS 60 V.
Definition Xl : axst := Eval vm_compute in nthA V LV2 0.
Definition XU1 : axst := Eval vm_compute in ax_of (apply_axforms Xl [AXRebase 0]) Xl.
Definition xsE : list axform := Eval vm_compute in [AXRebase 0; AXSelect (exU_sel XU1); AXMerge 0; AXSplit 0 (SLit (-1072))].
Definition B0 : axst := Eval vm_compute in match apply_axforms Xl xsE with Some x => x | None => Xl end.
Definition B3 : axst := Eval vm_compute in exB3 B0.
Definition CX : axst := Eval vm_compute in exCX B3.
Definition Rx : list sobj := Eval vm_compute in optR (entails_frA CX (Pre_exit0 0 2) (s_exR 0 CX)).

Lemma facts : ltac2:(tb__ "0|19|
S1S0S57S139SbcA3S1S0S57S132SbeA3S1S0SbSa6S13bSb4A2SaA3S1S0S11S35A1S7bS35S3bS56S130A1M0A1Sa5P4M1S130A2A3S10S35S44S36G1A1S34Z0M2A1S36PcM3A1ScS43A1S42P2A1A5A2A3S1S0SbSedG0S56S137A1M4A2SaA3S1S0SbS47S12dA1SaA3S1S0S11SeS9SeS33S33A2M5A1M6S9S31A1M7A2M8A1SecG4S12dA2S10G8S15G6G7S135ScS31A1A4A2A3S1S1S0S8S37S12dA1S37G4A1M9A3S0S8G9S37S56Sb4A1MaA1MbA3A2S1S0SbSa9G1S135A2SaA3S1S0SbS79S31S3dS46S8cS34S89A1McA2A1S39GaA1MdA3SaA3S1S0SbS7aS31S40GbA1Sa2G1P5MeG3A3A3SaA3S1S0SbSa7GdG1GeG3A4SaA3S1S0SbS79S31S3dS48G1Z3A2A1GdA3SaA3S1S0S33Se0S136P10A2S36GeA1A3S1S0S57SfbSc1S132S136S13aS78A5S12eA3S1S0S11S57A1MfS96S12eSdS95S97Sb7S12S35S3bS56S12eA1A1A2A1A1ScS95A1A3A2S10S57S12cA2A3S1S1S0S9S35A1M10S3bS56S12cA1M11A1SfS35S3bS56S12fA1M12A1M13S6dS9aS35S9bSb2A4A3A3S0S57S59S12cSe3G11G13A2A2S12fA3A2S1S0S11S9S58A1M14A1S5bS2fU3cSb3S12fSaA5S10G14SdS58S5aS134Se2A2ScS58A1A3A2A3S1S1S0SbS8aS5fS37G12A1A2SaA3S0SbS45G12A1S17A3A2S1S0GfS96S134S13cA2S10S57S131A2A3S1S0SbSe8Sc7S131ScG5A1A2A1SaA3S1S0SbSe7S138GcA2SaA3S1S1S0SbS8aS5fS37S56S12bA1M15A1M16A2SaA3S0SbS7aS31S40G16A1S39G15A1A3SaA3A2S1S0S11G10A1SefS12bSe5G2Z2A2M17Se6G2S12bA2M18A3S10G10S133A2A3S0SbSeeS12bG17G18S133ScS57A1A5SaA3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End SiteU.

Definition P0C (argv1 : list byte) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1S91Vr;A1S1S0S9S54Q8M0A1M1A1S6cG1Sb1S12G1Vargv1;A2M2U1A2S3aVr;P3A2A3SfG1Vargv1;SdG1S55G0Z0A2ScG1A1A3A3A3S1S0S7Sd4Vr;P9A2S28G2A1A3S1S1Sd3Vr;A1Sd2Vr;A1A2Sd9Vr;A1A2A2A2A2").
Definition P0Us (argv0 : list byte) (r : valuation) : Prop := ltac2:(tb__ "0|6|
S1S0S7Sd4Vr;P18A2S89A3S1S91Vr;A1S1S0S9S54Q8M0A1M1A1M2S6cG1Sb1S12G1Vargv0;A2M3U1A2S3aVr;P2A2M4A3SfG1Vargv0;SdG1S55G0Z0A2ScG1A1A3A3A3S1S0S7Sd4Vr;P5A2M5S28G3A1A3S1S1Sd3Vr;A1Sd2Vr;A1A2S1S0G2S3aVr;P3A2G4A3S24S25G5Z11A2Sd4Vr;PcA2A2A2A2A2A2A2A2").

Definition nd_U : ndesc := ltac2:(tb__ "0|0|
SceScSeS33S33A2A1ScSeSeS33S7A2S33A2A1ScS14dA1ScdA4").

Section INST.
Variable AInv : ltac2:(tb__ "0|0|
Sf5S30S9S54Q40A1A1S1bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S7S99S85R1A2S99VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis HCSTdrv2 : ltac2:(tb__ "0|0|
S7S99Sd7R1A2S99VCST;R2A2F_;Fz;").
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S62S30S9S54Q40A1A1S9S1aA1S1bR5R4R3R2R1A4S69VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S65S2fVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S62S30S9S54Q40A1A1S9S1aA1S1bR5R4R3R2R1A4S69VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Se4S2fVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Variable T0 : list event.
Variable MDX : Model -> Prop.
Hypothesis HMDXvm : ltac2:(tb__ "0|0|
S1bS23VMDX;R2A1VMDX;Sf2R2R3A2A1F_;Fv;Fmd;").
Variable fds : list (word * FdEntry).
Hypothesis Hfds1 : ltac2:(tb__ "0|0|
S0S11S1cA1S1eVfds;Sf6A2S10S1cS1dSf6A1A2A3").
Hypothesis Hfds2 : ltac2:(tb__ "0|0|
S0S11S1cA1S1eVfds;S60A2S10S1cS1dS60A1A2A3").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable PA : AA -> Prop.

Lemma TOPV_of_SPA : ltac2:(tb__ "0|1|
Sf0S14eSc8S57S30S9S54Q40A1A1S66S0SbSfcS39S56R4A1A1A1SaA3S61S2fScaVAInv;VCST;VXGL;S5fR8Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1R7VPA;R6AcR5R4R3R2A6Sd6Vrho0;A1F_;F_;Fw;Ftp;Frho;FA;Fnd;FBX;FK;").
Proof.
  intros K BX nd A rho tp w Hb [Hsm (Ai & kc & HJ)]. pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  pose proof (sp0_facts_sound rho _ HF Hb) as [_ H30]. destruct HJ as ([Aw _] & _).
  unfold TOPV, Uv. rewrite (Aw 1%positive ltac:(unfold NF; lia)), (Aw 30%positive ltac:(unfold NF; lia)). lia.
Qed.

Section C.
Variable argv1 : list byte.
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) argv1.
Hypothesis HP0 : ltac2:(tb__ "0|0|
S30VP0f;R1A1SaaVargv1;R2A2F_;Fr;").
Let JC : jpredA := ltac2:(tb__ "0|1|
ScaVAInv;VCST;VXGL;S5fS90VT0;VMDX;Vfds;ScS1aA1A4Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;S140Ac").

Lemma C_P0SH : ltac2:(tb__ "0|0|
S30VP0f;R1A1S84R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj1 (HP0 r Hr))). Qed.
Lemma C_P0ZA : ltac2:(tb__ "0|0|
S30VP0f;R1A1S1Sd3R2A1Sd2R2A1A2F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj2 (proj2 (proj2 (HP0 r Hr))))). Qed.
Lemma C_P0R : ltac2:(tb__ "0|0|
S30VP0f;R1A1S91R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (HP0 r Hr)). Qed.
Lemma C_P0str : ltac2:(tb__ "0|7|
S30VP0f;R1A1S1S0S9S54Q8M0A1M1A1M2S6cG1Sb1S12G1Vargv1;A2M3U1A2S3aR2P3A2M4A3SfG1Vargv1;SdG1S55G0Z0A2ScG1A1A3A3A3S1S0S7S53Q40M5S32R2P9A2A2M6S28G3A1A3S1S0G2G4G4A3S24S25G6Z11A2S53G5S32R2PaA2A2A2A2A2A2F_;Fr;").
Proof. intros r Hr. destruct (HP0 r Hr) as (_ & H1 & H2 & _ & H3). unfold SLK1, Uv in *. repeat split; assumption. Qed.
Lemma C_fblk : ltac2:(tb__ "0|1|
S7S1S24SaeZ1eec0M0A1R1A2S2bR1SaeS25G0Z80A2A1A2A2S4S92R2A1Sd5R2A1A2F_;Fz;").
Proof. intros z Hz. right. right. unfold Sh in *. lia. Qed.
Lemma C_layout : ltac2:(tb__ "0|8|
S30S6eS31S41R1A1S39S56Sb9A1A1A3S1S1S24Z7fff80000000S53Q40M0S32R2P1A2A2M1A2S24G1S29S26Z2M2Z2fA2M3Ze0A2A2A2S1S24S25G1Z18A2S53G0S32R2P8A2A2M4A2S1S24S25G4S53G0S32R2PaA2A2M5A2S25G1S53G0S32R2PbA2A2M6A2M7A2S1S24G7G3A2S1S24G6S26G2Z17A2A2S1S24G5S26G2Z16A2A2S24S53G0S32R2P9A2A2Z1ffffA2A2A2A2A2A2A2F_;Frho;").
Proof. intros rho HF. apply (layout_okb_sound (ss_facts (ax_S E_C)) 8 9 10 rho); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HF]. Qed.

Lemma C_sp0 : ltac2:(tb__ "0|0|
S0SbSfcS39S56S13fA1A1A1SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Hypothesis HSPEC : ltac2:(tb__ "0|1|
S1bVMDX;R1A1VSpec;SfS1aVT0;SfS1aScS1aA1M0SfS1aS6dS54Q8A1S1aS1fS60A1S70S74S72Vargv1;A3A4SdS1aS20S55Q40Z2A2S22R2A1A2G0A3A3A3A3A1F_;Fmd;").

Lemma C_sum : ltac2:(tb__ "0|6|
S66OF_;S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1S3S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vargv1;A2A1A3S14S65S2fRaS6fR9S74S72S6cG3S2aS53G0S32R6G2A2A2A1S3aR6P3M4A2A3R1A5A3Fk;S14Se4S2fRbS6fRaS74S72S6cG3S2aS53G0S32R7G2A2A2A1S3aR7G4A2A3M5R1A5A3Fk;S68S2fRbS61S2fRaSdbSdcZ1eec0Z80A3R7R6A5S63S2fS6fRaS74S72G5S12G3S70S74S72G5A3A2A5S5fR7R6S73A6A4F_;F_;F_;F_;F_;Ftp;Frho;F_;F_;FJ0;Fok';").
Proof. intros ok' J0 Hst Hfd rho tp HFN _ _ HK HP. exact (fpsC_all ok' J0 Hst Hfd rho tp HFN HK HP). Qed.
Lemma C_sumx : ltac2:(tb__ "0|5|
S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1S3S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vargv1;A2A1A3S67S2fS61S2fR8SdbSdcZ1eec0Z80A3R5R4A5S63S2fS6fR8S74S72S6cG3S2aS53G0S32R5G2A2A2A1S3aR5P3A2A3M4S12G3S70S74S72G4A3A2A5S5fR5R4S73A6A3F_;F_;F_;Ftp;Frho;F_;F_;FJ0;").
Proof. intros J0 Hst Hfd rho tp HFN _ _. exact (fpsC_all_ex J0 Hst Hfd rho tp HFN). Qed.

Theorem copen_tail_safe : ltac2:(tb__ "0|0|
S30S9S54Q40A1A1S68S2fVok;S61S2fVJC;S13fR2R1A5S66S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. apply (triple_preK _ _ (TOPV rho0)); [intros w HS; exact (TOPV_of_SPA (KcG T0 MDX fds []) BX0 nd_M E_copen rho tp w C_sp0 HS)|]. intros Htop0.
  unshelve (eapply (fps_tail_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 ok Spec HOKJ HOKP Hokh T0 MDX HMDXvm fds Hfds1 Hfds2 [] rho0 P0f
                      C_P0SH C_P0ZA C_P0R PA 8%positive 9%positive 10%positive 3%positive argv1 _ C_P0str Hnonul PRE_C SUF_NL FMT_COPEN 0x1eec0 0x80
                      HSPEC (fun _ => True) C_sum Htop0 nd_M eq_refl E_copen E_C 60%nat run_C1)
     with (cuts := cuts_C) (i3 := siteI3 8 SiteC.A2) (S4 := SiteC.S4) (d4 := SiteC.d4) (Hfblk := C_fblk) (Hlayout := C_layout)
          (s := SiteC.s) (R := SiteC.R) (HPX := fun _ _ => I) (Tq := SiteC.Tq) (S1 := SiteC.S1) (V := SiteC.V) (Xl := SiteC.Xl) (fuel2 := 40%nat)
          (xsE := SiteC.xsE) (B0 := SiteC.B0) (Rx := SiteC.Rx)).
  all: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.

Theorem copen_tail_ex : ltac2:(tb__ "0|2|
S66OF_;S66S1bVMDX;R1A1S0S9S1aA1S6aR3A1SfS1aVT0;SfS1aScS1aA1M0SfS1aS6dS54Q8A1S1aS1fS60A1S70S74S72Vargv1;A3A4SdS1aS20S55Q40M1Z2A2S22R2A1A2G0A3A3A3A3A3R5R4A1F_;F_;Fmd;Fw;S30S9S54G1A1A1S67S2fS61S2fVJC;S13fR2R1A5R4A3Ftp;Frho;F_;FQ;").
Proof.
  intros Q HQ rho tp. apply (etriple_preK _ (TOPV rho0)); [intros w HS; exact (TOPV_of_SPA (KcG T0 MDX fds []) BX0 nd_M E_copen rho tp w C_sp0 HS)|]. intros Htop0.
  unshelve (eapply (fps_tail_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 Spec T0 MDX HMDXvm fds Hfds1 Hfds2 [] rho0 P0f
                      C_P0SH C_P0ZA C_P0R PA 8%positive 9%positive 10%positive 3%positive argv1 _ C_P0str Hnonul PRE_C SUF_NL FMT_COPEN 0x1eec0 0x80
                      HSPEC (fun _ => True) C_sumx Htop0 nd_M eq_refl E_copen E_C 60%nat run_C1)
     with (cuts := cuts_C) (i3 := siteI3 8 SiteC.A2) (S4 := SiteC.S4) (d4 := SiteC.d4) (Hfblk := C_fblk) (Hlayout := C_layout)
          (s := SiteC.s) (R := SiteC.R) (HPX := fun _ _ => I) (Tq := SiteC.Tq) (S1 := SiteC.S1) (V := SiteC.V) (Xl := SiteC.Xl) (fuel2 := 40%nat)
          (xsE := SiteC.xsE) (B0 := SiteC.B0) (Rx := SiteC.Rx)).
  all: try exact HQ.
  all: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.
End C.

Section D.
Variable argv1 : list byte.
Hypothesis Hdot : ltac2:(tb__ "0|0|
S0SbS148Vargv1;S14aA2SaA3").
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) argv1.
Hypothesis HP0 : ltac2:(tb__ "0|0|
S30VP0f;R1A1Sd8Vargv1;R2A2F_;Fr;").
Let JD : jpredA := ltac2:(tb__ "0|1|
ScaVAInv;VCST;VXGL;S5fS90VT0;VMDX;Vfds;ScS1aA1A4Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S93S94A1VPA;SfaAc").
Let JD0 : jpredA := ltac2:(tb__ "0|1|
ScaVAInv;VCST;VXGL;S5fS90VT0;VMDX;Vfds;ScS1aA1A4Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;SfaAc").

Lemma D_P0SH : ltac2:(tb__ "0|0|
S30VP0f;R1A1S84R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj1 (proj2 (HP0 r Hr)))). Qed.
Lemma D_P0ZA : ltac2:(tb__ "0|0|
S30VP0f;R1A1S1Sd3R2A1Sd2R2A1A2F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj2 (proj2 (proj2 (proj2 (HP0 r Hr)))))). Qed.
Lemma D_P0R : ltac2:(tb__ "0|0|
S30VP0f;R1A1S91R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj2 (HP0 r Hr))). Qed.
Lemma D_P0str : ltac2:(tb__ "0|7|
S30VP0f;R1A1S1S0S9S54Q8M0A1M1A1M2S6cG1Sb1S12G1Vargv1;A2M3U1A2S3aR2P3A2M4A3SfG1Vargv1;SdG1S55G0Z0A2ScG1A1A3A3A3S1S0S7S53Q40M5S32R2P9A2A2M6S28G3A1A3S1S0G2G4G4A3S24S25G6Z11A2S53G5S32R2PaA2A2A2A2A2A2F_;Fr;").
Proof. intros r Hr. destruct (HP0 r Hr) as (_ & _ & H1 & H2 & _ & _ & H3). unfold SLK1, Uv in *. repeat split; assumption. Qed.
Lemma D_top : ltac2:(tb__ "0|0|
S30VP0f;R1A1Sd6R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HP0 r Hr))))))). Qed.
Lemma D_len : Z.of_nat (length argv1) = 1.
Proof. apply path_eqb_eq in Hdot. rewrite Hdot. reflexivity. Qed.
Lemma D_layout : ltac2:(tb__ "0|8|
S30S6eS31S41R1A1S39S56S112A1A1A3S1S1S24Z7fff80000000S53Q40M0S32R2P1A2A2M1A2S24G1S29S26Z2M2Z2fA2M3Ze0A2A2A2S1S24S25G1Z18A2S53G0S32R2P8A2A2M4A2S1S24S25G4S53G0S32R2PaA2A2M5A2S25G1S53G0S32R2PbA2A2M6A2M7A2S1S24G7G3A2S1S24G6S26G2Z17A2A2S1S24G5S26G2Z16A2A2S24S53G0S32R2P9A2A2Z1ffffA2A2A2A2A2A2A2F_;Frho;").
Proof. intros rho HF. apply (layout_okb_sound (ss_facts (ax_S SiteD.E1)) 8 9 10 rho); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HF]. Qed.

Lemma JAi_dropK : ltac2:(tb__ "0|3|
Sf0S7Sc8Sf5S7S30S9S54Q40A1A1S9S1aA1S1bS24Z0R8A2SccVAInv;VCST;VXGL;S5fRaVrho0;VP0f;ScSeS7S7A2M0A1M1ScSeG0S7A2A1M2S93R9A1VPA;R8R7R6R5R4R3R2A12SccVAInv;VCST;VXGL;S5fRbVrho0;VP0f;G1G2S82VPA;R9R8R7R6R5R4R3A12F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;Fk;FK;").
Proof.
  intros K k nd Ai kc rho tp tr md Hk HJ.
  destruct HJ as (Hav & HKc & HM & HT & HB & HFF & HN3 & HFR & HK & HP00 & HXA & HBU & HPA & HCK).
  split; [exact Hav|]. split; [exact HKc|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HP00|]. split; [exact HXA|]. split; [|split; [exact HPA | exact HCK]].
  pose proof HXA as Hkc. apply XA_kc_nonneg in Hkc. pose proof (apot_range (nd_am nd) rho) as APR.
  destruct HBU as (A1 & A2 & A3 & A4 & A5 & Hwf & Hnn & B1 & B2).
  unfold BUD. unfold bxa, BXk, BX0 in *. cbn [fst snd bx2] in *. repeat split; try assumption; lia.
Qed.

Hypothesis HSPEC : ltac2:(tb__ "0|1|
S1bVMDX;R1A1VSpec;SfS1aVT0;SfS1aScS1aA1M0SfS1aS6dS54Q8A1S1aS1fS60A1S70S75S72Vargv1;A3A4SdS1aS20S55Q40Z2A2S22R2A1A2G0A3A3A3A3A1F_;Fmd;").

Lemma D_sum : ltac2:(tb__ "0|6|
S66OF_;S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1S3S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vargv1;A2A1A3S14S65S2fRaS6fR9S75S72S6cG3S2aS53G0S32R6G2A2A2A1S3aR6P3M4A2A3R1A5A3Fk;S14Se4S2fRbS6fRaS75S72S6cG3S2aS53G0S32R7G2A2A2A1S3aR7G4A2A3M5R1A5A3Fk;S68S2fRbS61S2fRaSdbSddZ1eec0Z80A3R7R6A5S63S2fS6fRaS75S72G5S12G3S70S75S72G5A3A2A5S5fR7R6S73A6A4F_;F_;F_;F_;F_;Ftp;Frho;F_;F_;FJ0;Fok';").
Proof. intros ok' J0 Hst Hfd rho tp HFN _ Hlen HK HP. apply (fpsD_small ok' J0 Hst Hfd rho tp HFN HK HP). rewrite Hlen. exact D_len. Qed.
Lemma D_sumx : ltac2:(tb__ "0|5|
S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1S3S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vargv1;A2A1A3S67S2fS61S2fR8SdbSddZ1eec0Z80A3R5R4A5S63S2fS6fR8S75S72S6cG3S2aS53G0S32R5G2A2A2A1S3aR5P3A2A3M4S12G3S70S75S72G4A3A2A5S5fR5R4S73A6A3F_;F_;F_;Ftp;Frho;F_;F_;FJ0;").
Proof. intros J0 Hst Hfd rho tp HFN _ Hlen. apply (fpsD_small_ex J0 Hst Hfd rho tp HFN). rewrite Hlen. exact D_len. Qed.

Lemma D_pre : ltac2:(tb__ "0|0|
S30S9S54Q40A1A1S66S61S2fVJD;Sf7R3R2R1A6S1S61S2fVJD0;S114R4R3R2A6Sd6Vrho0;A1A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w [Hsm (Ai & kc & HJ)]. assert (HK0 : 0 <= K0) by (unfold K0, KU; pose proof DrvR.K_T_pos; lia).
  destruct SiteD.pre_facts as (Pw & Pd & Pn & Pdd & Ptp & Pax & _).
  split; [| destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HP00 & _); exact (D_top _ HP00)].
  assert (HS0 : SPA segs JD0 D_rde rho tp w).
  { split; [exact Hsm|]. exists Ai, kc. exact (JAi_dropK _ K0 nd_Z Ai kc rho tp _ _ HK0 HJ). }
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (HS1 : SPA segs JD0 SiteD.D1 rho tp w).
  { apply (SPA_restate segs _ rho D_rde SiteD.SD1 tp w SiteD.dD1 [] Pw Pd Pn); [| constructor | exact HS0].
    rewrite Pdd. unfold diffs_ok. constructor; [|constructor]. cbn [fst snd].
    pose proof (holds_mem _ _ _ HF Ptp) as X. cbn [holds] in X. exact X. }
  apply (SPA_axforms segs _ SiteD.xsD rho SiteD.D1 SiteD.D2 tp _ Pax) in HS1. exact HS1.
Qed.

Theorem rderr_tail_safe : ltac2:(tb__ "0|0|
S30S9S54Q40A1A1S68S2fVok;S61S2fVJD;Sf7R2R1A5S66S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. apply (triple_preK _ _ (TOPV rho0)); [intros w HS; exact (proj2 (D_pre rho tp w HS))|]. intros Htop0.
  eapply (triple_conseq (P := SPA segs JD0 SiteD.D2 rho tp)); [intros w HS; exact (proj1 (D_pre rho tp w HS)) | intros w' Hw'; exact Hw' |].
  destruct SiteD.pre_facts as (_ & _ & _ & _ & _ & _ & RUN1).
  unshelve (eapply (fps_tail_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 ok Spec HOKJ HOKP Hokh T0 MDX HMDXvm fds Hfds1 Hfds2 [] rho0 P0f
                      D_P0SH D_P0ZA D_P0R PA 8%positive 9%positive 10%positive 3%positive argv1 _ D_P0str Hnonul PRE_D SUF_NL FMT_RDERR 0x1eec0 0x80
                      HSPEC (fun _ => True) D_sum Htop0 nd_Z eq_refl SiteD.D2 SiteD.E1 60%nat RUN1)
     with (cuts := cuts_D) (i3 := siteI3 8 SiteD.A2) (S4 := SiteD.S4) (d4 := SiteD.d4) (Hfblk := C_fblk) (Hlayout := D_layout)
          (s := SiteD.s) (R := SiteD.R) (HPX := fun _ _ => I) (Tq := SiteD.Tq) (S1 := SiteD.S1) (V := SiteD.V) (Xl := SiteD.Xl) (fuel2 := 40%nat)
          (xsE := SiteD.xsE) (B0 := SiteD.B0) (Rx := SiteD.Rx)).
  all: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.

Theorem rderr_tail_ex : ltac2:(tb__ "0|2|
S66OF_;S66S1bVMDX;R1A1S0S9S1aA1S6aR3A1SfS1aVT0;SfS1aScS1aA1M0SfS1aS6dS54Q8A1S1aS1fS60A1S70S75S72Vargv1;A3A4SdS1aS20S55Q40M1Z2A2S22R2A1A2G0A3A3A3A3A3R5R4A1F_;F_;Fmd;Fw;S30S9S54G1A1A1S67S2fS61S2fVJD;Sf7R2R1A5R4A3Ftp;Frho;F_;FQ;").
Proof.
  intros Q HQ rho tp. apply (etriple_preK _ (TOPV rho0)); [intros w HS; exact (proj2 (D_pre rho tp w HS))|]. intros Htop0.
  eapply (etriple_conseq (P := SPA segs JD0 SiteD.D2 rho tp)); [intros w HS; exact (proj1 (D_pre rho tp w HS)) | intros w' Hw'; exact Hw' |].
  destruct SiteD.pre_facts as (_ & _ & _ & _ & _ & _ & RUN1).
  unshelve (eapply (fps_tail_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 Spec T0 MDX HMDXvm fds Hfds1 Hfds2 [] rho0 P0f
                      D_P0SH D_P0ZA D_P0R PA 8%positive 9%positive 10%positive 3%positive argv1 _ D_P0str Hnonul PRE_D SUF_NL FMT_RDERR 0x1eec0 0x80
                      HSPEC (fun _ => True) D_sumx Htop0 nd_Z eq_refl SiteD.D2 SiteD.E1 60%nat RUN1)
     with (cuts := cuts_D) (i3 := siteI3 8 SiteD.A2) (S4 := SiteD.S4) (d4 := SiteD.d4) (Hfblk := C_fblk) (Hlayout := D_layout)
          (s := SiteD.s) (R := SiteD.R) (HPX := fun _ _ => I) (Tq := SiteD.Tq) (S1 := SiteD.S1) (V := SiteD.V) (Xl := SiteD.Xl) (fuel2 := 40%nat)
          (xsE := SiteD.xsE) (B0 := SiteD.B0) (Rx := SiteD.Rx)).
  all: try exact HQ.
  all: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.
End D.

Section U.
Variable argv0 : list byte.
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) argv0.
Hypothesis HP0 : ltac2:(tb__ "0|0|
S30VP0f;R1A1SabVargv0;R2A2F_;Fr;").
Let JU : jpredA := ltac2:(tb__ "0|1|
ScaVAInv;VCST;VXGL;S5fS90VT0;VMDX;Vfds;ScS1aA1A4Vrho0;VP0f;ScSeS7S7A2M0A1ScSeG0S7A2A1S82VPA;SacAc").

Lemma U_P0SH : ltac2:(tb__ "0|0|
S30VP0f;R1A1S84R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj1 (proj2 (HP0 r Hr)))). Qed.
Lemma U_P0ZA : ltac2:(tb__ "0|0|
S30VP0f;R1A1S1Sd3R2A1Sd2R2A1A2F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj2 (proj2 (proj2 (proj2 (HP0 r Hr)))))). Qed.
Lemma U_P0R : ltac2:(tb__ "0|0|
S30VP0f;R1A1S91R2A1F_;Fr;"). Proof. intros r Hr. exact (proj1 (proj2 (HP0 r Hr))). Qed.
Lemma U_P0str : ltac2:(tb__ "0|7|
S30VP0f;R1A1S1S0S9S54Q8M0A1M1A1M2S6cG1Sb1S12G1Vargv0;A2M3U1A2S3aR2P2A2M4A3SfG1Vargv0;SdG1S55G0Z0A2ScG1A1A3A3A3S1S0S7S53Q40M5S32R2P5A2A2M6S28G3A1A3S1S0G2S3aR2P3A2G4A3S24S25G6Z11A2S53G5S32R2PcA2A2A2A2A2A2F_;Fr;").
Proof. intros r Hr. destruct (HP0 r Hr) as (_ & _ & H1 & H2 & _ & H3 & H4). unfold Uv in *. repeat split; assumption. Qed.
Lemma U_sp0 : ltac2:(tb__ "0|0|
S0SbSfcS39S56S13eA1A1A1SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma U_fblk : ltac2:(tb__ "0|1|
S7S1S24SaeZ16080M0A1R1A2S2bR1SaeS25G0Z80A2A1A2A2S4S92R2A1Sd5R2A1A2F_;Fz;").
Proof. intros z Hz. left. right. left. unfold Sh in *. lia. Qed.
Lemma U_layout : ltac2:(tb__ "0|8|
S30S6eS31S41R1A1S39S56Sb4A1A1A3S1S1S24Z7fff80000000S53Q40M0S32R2P1A2A2M1A2S24G1S29S26Z2M2Z2fA2M3Ze0A2A2A2S1S24S25G1Z18A2S53G0S32R2P4A2A2M4A2S1S24S25G4S53G0S32R2PcA2A2M5A2S25G1S53G0S32R2PbA2A2M6A2M7A2S1S24G7G3A2S1S24G6S26G2Z17A2A2S1S24G5S26G2Z16A2A2S24S53G0S32R2P5A2A2Z1ffffA2A2A2A2A2A2A2F_;Frho;").
Proof. intros rho HF. apply (layout_okb_sound (ss_facts (ax_S E_U)) 4 5 12 rho); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact HF]. Qed.
Lemma U_al4 : ltac2:(tb__ "0|0|
S0SbS79S31S3dS48P4Z3A2A1S39S56Sb4A1A1A3SaA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma U_PX : ltac2:(tb__ "0|0|
S30S6eS31S41R1A1S39S56Sb4A1A1A3S0S7S2cS53Q40S32R2P4A2A2Z4A2Z0A3F_;Frho;").
Proof.
  intros rho HF. pose proof (holds_mem _ _ _ HF U_al4) as H. cbn [holds] in H. destruct H as [_ H]. change (2 ^ 3) with 8 in H.
  apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|]. destruct H as [q Hq]. exists (2 * q). lia.
Qed.

Hypothesis HSPEC : ltac2:(tb__ "0|1|
S1bVMDX;R1A1VSpec;SfS1aVT0;SfS1aScS1aA1M0SfS1aS6dS54Q8A1S1aS1fS60A1S70S76S77Vargv0;A3A4SdS1aS20S55Q40Z2A2S22R2A1A2G0A3A3A3A3A1F_;Fmd;").

Lemma U_sum : ltac2:(tb__ "0|6|
S66OF_;S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1S0S7S2cS53G0S3fR3S13dA2A2Z4A2Z0A3S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vargv0;A2A1A3S14S65S2fRaS6fR9S76S77S6cG3S2aS53G0S32R6G2A2A2A1S3aR6P3M4A2A3R1A5A3Fk;S14Se4S2fRbS6fRaS76S77S6cG3S2aS53G0S32R7G2A2A2A1S3aR7G4A2A3M5R1A5A3Fk;S68S2fRbS61S2fRaSdbSdeZ16080Z80A3R7R6A5S63S2fS6fRaS76S77G5S12G3S70S76S77G5A3A2A5S5fR7R6S73A6A4F_;F_;F_;F_;F_;Ftp;Frho;F_;F_;FJ0;Fok';").
Proof. intros ok' J0 Hst Hfd rho tp HFN Hal _ HK HP. exact (fpsU_all ok' J0 Hst Hfd rho tp HFN Hal HK HP). Qed.
Lemma U_sumx : ltac2:(tb__ "0|5|
S62S64S2fS5fR1A3S30S9S54Q40M0A1A1M1S9S1aA1S1bR6R4R3R2R1A4S0S11S1cA1S1eS21R2A1S60A2S10S1cS1dS60A1A2A3F_;Fmd;Ftr;Ft;Fr;S30G1SadR2A1S0S7S2cS53G0S3fR3S13dA2A2Z4A2Z0A3S0S7S53G0S32R4P10M2A2A2S28S12S54Q8A1M3Vargv0;A2A1A3S67S2fS61S2fR8SdbSdeZ16080Z80A3R5R4A5S63S2fS6fR8S76S77S6cG3S2aS53G0S32R5G2A2A2A1S3aR5P3A2A3M4S12G3S70S76S77G4A3A2A5S5fR5R4S73A6A3F_;F_;F_;Ftp;Frho;F_;F_;FJ0;").
Proof. intros J0 Hst Hfd rho tp HFN Hal _. exact (fpsU_all_ex J0 Hst Hfd rho tp HFN Hal). Qed.

Theorem usage_tail_safe : ltac2:(tb__ "0|0|
S30S9S54Q40A1A1S68S2fVok;S61S2fVJU;S13eR2R1A5S66S2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. apply (triple_preK _ _ (TOPV rho0)); [intros w HS; exact (TOPV_of_SPA (KcG T0 MDX fds []) BX0 nd_U S_U rho tp w U_sp0 HS)|]. intros Htop0.
  unshelve (eapply (fps_tail_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 ok Spec HOKJ HOKP Hokh T0 MDX HMDXvm fds Hfds1 Hfds2 [] rho0 P0f
                      U_P0SH U_P0ZA U_P0R PA 4%positive 5%positive 12%positive 2%positive argv0 _ U_P0str Hnonul PRE_U SUF_U FMT_USAGE 0x16080 0x80
                      HSPEC (fun z => z mod 4 = 0) U_sum Htop0 nd_U eq_refl S_U E_U 80%nat run_U1)
     with (cuts := cuts_U) (i3 := siteI3 4 SiteU.A2) (S4 := SiteU.S4) (d4 := SiteU.d4) (Hfblk := U_fblk) (Hlayout := U_layout)
          (s := SiteU.s) (R := SiteU.R) (HPX := U_PX) (Tq := SiteU.Tq) (S1 := SiteU.S1) (V := SiteU.V) (Xl := SiteU.Xl) (fuel2 := 60%nat)
          (xsE := SiteU.xsE) (B0 := SiteU.B0) (Rx := SiteU.Rx)).
  all: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.

Theorem usage_tail_ex : ltac2:(tb__ "0|2|
S66OF_;S66S1bVMDX;R1A1S0S9S1aA1S6aR3A1SfS1aVT0;SfS1aScS1aA1M0SfS1aS6dS54Q8A1S1aS1fS60A1S70S76S77Vargv0;A3A4SdS1aS20S55Q40M1Z2A2S22R2A1A2G0A3A3A3A3A3R5R4A1F_;F_;Fmd;Fw;S30S9S54G1A1A1S67S2fS61S2fVJU;S13eR2R1A5R4A3Ftp;Frho;F_;FQ;").
Proof.
  intros Q HQ rho tp. apply (etriple_preK _ (TOPV rho0)); [intros w HS; exact (TOPV_of_SPA (KcG T0 MDX fds []) BX0 nd_U S_U rho tp w U_sp0 HS)|]. intros Htop0.
  unshelve (eapply (fps_tail_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 Spec T0 MDX HMDXvm fds Hfds1 Hfds2 [] rho0 P0f
                      U_P0SH U_P0ZA U_P0R PA 4%positive 5%positive 12%positive 2%positive argv0 _ U_P0str Hnonul PRE_U SUF_U FMT_USAGE 0x16080 0x80
                      HSPEC (fun z => z mod 4 = 0) U_sumx Htop0 nd_U eq_refl S_U E_U 80%nat run_U1)
     with (cuts := cuts_U) (i3 := siteI3 4 SiteU.A2) (S4 := SiteU.S4) (d4 := SiteU.d4) (Hfblk := U_fblk) (Hlayout := U_layout)
          (s := SiteU.s) (R := SiteU.R) (HPX := U_PX) (Tq := SiteU.Tq) (S1 := SiteU.S1) (V := SiteU.V) (Xl := SiteU.Xl) (fuel2 := 60%nat)
          (xsE := SiteU.xsE) (B0 := SiteU.B0) (Rx := SiteU.Rx)).
  all: try exact HQ.
  all: OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2.
Qed.
End U.
End INST.
End FpsSite.

