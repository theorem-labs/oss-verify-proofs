(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_read_binary.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_alloc_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_read_binary_stmt () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "MPI_RB_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "MPI_RB_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_read_binary.chars_to_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.mpd_writable"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "arl_need_rt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_tp"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "mpi_read_binary_postA"].


Definition A_MPI_READ_BINARY : Z := 0x09d308.
Notation A_MPI_READ_BINARY_STACK := 192 (only parsing).

(* [comment removed for export] *)
Definition arl_need_rt (R : art_layout) : Z :=
  Z.max (arl_need_malloc R) (Z.max (arl_need_free R) (arl_need_amem R)).

Lemma arl_need_rt_malloc : forall R, arl_need_malloc R <= arl_need_rt R.
Proof. intros; unfold arl_need_rt; lia. Qed.
Lemma arl_need_rt_free : forall R, arl_need_free R <= arl_need_rt R.
Proof. intros; unfold arl_need_rt; lia. Qed.
Lemma arl_need_rt_amem : forall R, arl_need_amem R <= arl_need_rt R.
Proof. intros; unfold arl_need_rt; lia. Qed.

(* [comment removed for export] *)
Definition MPI_RB_PHI (len : Z) : Z := 2 * len + 8 + 2 * AVOL_CALL.
(* [comment removed for export] *)
Definition MPI_RB_FR (d : Z) : Z := 2 * fr_charge d.
Lemma MPI_RB_FR_nonneg : forall d, 0 <= d -> 0 <= MPI_RB_FR d.
Proof. intros; unfold MPI_RB_FR, fr_charge; lia. Qed.

Lemma MPI_RB_PHI_mono : forall a b, a <= b -> MPI_RB_PHI a <= MPI_RB_PHI b.
Proof. intros; unfold MPI_RB_PHI; lia. Qed.

(* [comment removed for export] *)
Definition blk_eqb (a b : blk) : bool := Z.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
Lemma blk_eqb_eq : forall a b, blk_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold blk_eqb. cbn. rewrite Bool.andb_true_iff, !Z.eqb_eq. split; [intros [-> ->]; reflexivity| intros E; injection E; auto].
Qed.
Definition mpd_keep (LB : list blk) (d : mpd) : list blk :=
  match md_own d with LHeap => List.filter (fun b => negb (blk_eqb b (md_p d, 4 * md_n d))) LB | _ => LB end.

Lemma In_mpd_keep : forall LB d b, In b (mpd_keep LB d) -> In b LB.
Proof. intros LB d b. unfold mpd_keep. destruct (md_own d); [exact (fun H => H)| | exact (fun H => H)]. intros H. apply filter_In in H. exact (proj1 H). Qed.
Lemma In_mpd_keep_intro : forall LB d b, In b LB -> ~ In b (mpd_blk d) -> In b (mpd_keep LB d).
Proof.
  intros LB d b Hb Hn. unfold mpd_keep, mpd_blk in *. destruct (md_own d); [exact Hb| | exact Hb].
  apply filter_In. split; [exact Hb|]. destruct (blk_eqb b (md_p d, 4 * md_n d)) eqn:E; [| reflexivity].
  exfalso. apply Hn. left. symmetry. apply blk_eqb_eq, E.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fresh_apart_blocks_mono : ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary_stmt ()) "PR,$0.PLB,(1.$2.)PLB',(1.$2.)PLF,(1.$2.)PN,$3.Pk,$3.P,(4.R6.R5.R3.R2.R1.)P,Pb,$2.P,(5.$2.R1.R6.)(5.$2.R2.R8.)(4.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros R LB LB' LF N k dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros HI). split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
  intros B j Hb. apply F3. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HI, Hb| right; exact Hb].
Qed.
Lemma fresh_apart_keep : forall R LB LF d N k, fresh_apart R LB LF N k -> fresh_apart R (mpd_keep LB d) LF N k.
Proof. intros. eapply fresh_apart_blocks_mono; [eassumption| intros b Hb; eapply In_mpd_keep; exact Hb]. Qed.

Lemma mpd_keep_out : forall LB dX LB' dX' b, mpd_out LB dX LB' dX' -> In b (mpd_keep LB dX) -> In b LB'.
Proof.
  (intros LB dX LB' dX' b dd_H; ddestruct dd_H as (_ & _ & _ & HO & _); intros Hb). unfold mpd_keep in Hb.
  destruct (md_own dX) eqn:EO.
  - apply HO; [exact Hb|]. unfold mpd_blk. rewrite EO. intros [].
  - apply filter_In in Hb. destruct Hb as [Hb Hne]. apply HO; [exact Hb|]. unfold mpd_blk. rewrite EO.
    intros [E|[]]. rewrite <- E in Hne. unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
  - apply HO; [exact Hb|]. unfold mpd_blk. rewrite EO. intros [].
Qed.

Definition mpi_read_binary_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (dX : mpd) (LEN lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary_stmt ()) "Lc,$6.(7.(8.&40.)Lt0,(8.&40.)(7.(8.&40.)Lt1,(8.&40.)(7.(8.&40.)Lt2,(8.&40.)(7.(8.&40.)La1,(8.&40.)(7.(8.&40.)La2,(8.&40.)(7.(8.&40.)La3,(8.&40.)(7.(8.&40.)La4,(8.&40.)(7.(8.&40.)La5,(8.&40.)(7.(8.&40.)La6,(8.&40.)(7.(8.&40.)La7,(8.&40.)(7.(8.&40.)Lt3,(8.&40.)(7.(8.&40.)Lt4,(8.&40.)(7.(8.&40.)Lt5,(8.&40.)(7.(8.&40.)Lt6,(8.&40.)(7.P,(8.&40.)(9.(8.&8.))Lm',P,(8.&40.)(9.(8.&8.))(7.$:.Lmo',$:.(7.(;.O1>.O1=.O1<.)Lh',(;.O1>.O1=.O1<.)(7.(1.$2.)LLB',(1.$2.)(7.$<.LdX',$<.(7.$3.Lr,$3.(=.(>.$6.R15.(?.(10.(11.O18.O17.O16.O15.R14.R13.R12.O14.O13.(12.&40.R1.)R11.R10.R?.R>.R=.R<.R;.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R:.R9.R8.R7.)O8.(13.O18.)O7.(14.(8.&40.))R6.(15.O1>.))R5.))(=.(16.O1>.R6.)(=.(17.O1>.R6.O4.(18.&40.O17.))(=.(19.O1.R5.)(=.(1:.O1>.O1=.(1;.O1:.O6.)O19.(18.&40.O17.)(1<.O1=.)(1=.O1>.O1=.O1<.O1;.)(1>.(1?.$3.$3.)(20.$3.$3.(21.O6.)(22.(21.O6.)+10.))(23.(1?.$3.$3.)))O2.R6.)(=.(>.$3.(24.O1>.O1=.O1<.R4.)(24.O1>.O1=.O1<.O1;.))(=.(>.$3.(1=.O1>.O1=.O1<.R4.)(1=.O1>.O1=.O1<.O1;.))(=.(>.$3.(25.O1>.O1=.O1<.R4.)(25.O1>.O1=.O1<.O1;.))(=.(26.O1>.O1=.O1<.R4.R5.)(=.Px,$3.P,(27.O1>.O1=.O1<.O1;.R1.)(27.O1>.O1=.O1<.R6.R2.)(=.(28.(29.O1>.O1=.O1<.R4.)(22.(29.O1>.O1=.O1<.O1;.)(2:.O5.)))(=.(28.(2;.O1>.O1=.O1<.R4.)(22.(2;.O1>.O1=.O1<.O1;.)(2<.O3.)))(=.(2=.O1>.O1=.O1<.R4.R3.O19.R6.)(=.(2>.O1>.R6.R3.R2.)(=.(2?.O1:.O6.R3.R2.)(=.(30.(>.$3.R1.=)(>.$3.R1.$31.))(=.P,(>.$3.R1.=)(=.(>.$3.(32.R3.)+1.)(>.$3.(33.R3.)(34.O5.)))Pb,$2.P,(5.$2.R1.(35.R3.))(30.(5.$2.R2.(35.O6.))(4.O1=.(1;.O1:.O6.)O19.(36.$3.$3.R2.)(37.$3.$3.R2.))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Definition mpi_read_binary_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_read_binary_stmt ()) "Ph,(;.O4.O3.O2.)PLB,(1.$2.)PLF,(1.$2.)Pra,(8.&40.)Psp,(8.&40.)Pgp,(8.&40.)Ptp,(8.&40.)Pt0,(8.&40.)Pt1,(8.&40.)Pt2,(8.&40.)Ps0,(8.&40.)Ps1,(8.&40.)Pa0,(8.&40.)Pa1,(8.&40.)Pa2,(8.&40.)Pa3,(8.&40.)Pa4,(8.&40.)Pa5,(8.&40.)Pa6,(8.&40.)Pa7,(8.&40.)Ps2,(8.&40.)Ps3,(8.&40.)Ps4,(8.&40.)Ps5,(8.&40.)Ps6,(8.&40.)Ps7,(8.&40.)Ps8,(8.&40.)Ps9,(8.&40.)Ps10,(8.&40.)Ps11,(8.&40.)Pt3,(8.&40.)Pt4,(8.&40.)Pt5,(8.&40.)Pt6,(8.&40.)PF,(38.&5.(8.&40.))Pfc,(8.&20.)Pm,P,(8.&40.)(9.(8.&8.))Pmo,$:.PdX,$<.PB,$3.Pibs,(1.(8.&8.))Plo,$3.Pd,$3.P,(2=.O4.O3.O2.R2;.R2:.R29.R7.)P,(26.O4.O3.O2.R2<.R7.)P,(2>.O4.R9.R2<.R7.)P,(39.(>.$3:.(3;.R8.)$3<.))P,(3=.(3>.O3.)(3?.$2.R2>.(40.R2=.))(18.&40.R2;.)(24.O4.O3.O2.R2?.)R9.)P,(41.O4.R<.R9.R8.)P,(42.=R:.)P,(42.(22.R;.(43.(44.(8.&8.)R:.)))(45.+2.+3?.))P,(46.(3>.O3.)(3?.$2.R32.(40.R31.))R:.R<.(43.(44.(8.&8.)R;.)))P,(30.(28.(22.R=.(43.(44.(8.&8.)R<.)))(21.R>.))(28.(22.(21.R>.)+10.)R=.))P,P,(>.$3:.(3;.R?.)$47.)(30.(28.(22.R?.(43.(44.(8.&8.)R>.)))(48.R10.))(28.(22.(48.R10.)(49.+4.(33.R10.)))R?.))P,(30.(28.(22.R?.(43.(44.(8.&8.)R>.)))R=.)(28.(18.&40.R32.)R?.))P,(30.(>.$3.(43.(44.(8.&8.)R?.))=)(28.(22.(22.R10.(43.(44.(8.&8.)R?.)))+8.)(45.+2.+2?.)))P,(17.O4.R14.R?.(18.&40.R34.))P,(28.(1<.O3.)R10.)P,(28.R11.(4:.(4:.(18.&40.R36.)+<0.)(4;.O3.)))P,(28.(18.&40.R37.)(24.O4.O3.O2.R3;.))P,(>.$3.(4<.(18.&40.R38.)+10.)=)P,(>.(8.&40.)R37.(12.&40.(4=.O3.)))P,(16.O4.R1:.)P,(>.$3.(4<.(18.&40.R3<.)+2.)=)P,(4>.O4.(4?.O3.)(27.O4.O3.O2.R40.)R1<.(21.R1:.)+10.)P,(4>.O4.(4?.O3.)(27.O4.O3.O2.R41.)R1=.R1:.(43.(44.(8.&8.)R19.)))P,(28.(22.(29.O4.O3.O2.R42.)(2:.(43.(44.(8.&8.)R1:.))))$50.)P,(51.O3.(21.R1=.)+10.R19.)P,(28.(22.(2;.O4.O3.O2.R44.)(2<.R1:.))$52.)P,(>.(8.&40.)R39.(12.&40.(21.R1?.)))P,(>.(8.&40.)R39.(12.&40.R1?.))P,(>.(8.&40.)R39.(12.&40.(43.(44.(8.&8.)R1?.))))(53.O4.(54.O4.O3.O2.R48.R47.R46.R45.R44.R43.R42.R3>.R3=.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R26.R25.R22.(43.(44.(8.&8.)R20.))R1?.R1>.R24.R23.)(?.(10.(11.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R26.(12.&40.O1.)R25.(14.(8.&40.))R24.(15.O4.))R23.))")
(* [comment removed for export] *).
