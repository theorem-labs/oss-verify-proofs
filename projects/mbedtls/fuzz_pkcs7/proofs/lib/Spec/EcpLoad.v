(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux MpiWalkAux HeapIface Image.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_EcpLoad () : Init.string Init.list := ["Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.Lib.Mem.ro_bytes"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Image.ro_bytes_b"; "Stdlib.ZArith.BinInt.Z.pow"; "static_limbs"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Spec.RepEcp.mpdr_at"; "OSSVerify.KrLib.Spec.EcpCurves.smpd"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Lib.Cells.C4"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.Spec.EcpCurves.ca_P"; "OSSVerify.KrLib.Spec.EcpCurves.cP"; "OSSVerify.KrLib.Spec.EcpCurves.has_A"; "OSSVerify.KrLib.Spec.EcpCurves.ca_A"; "OSSVerify.KrLib.Spec.EcpCurves.cA"; "OSSVerify.KrLib.Spec.EcpCurves.is_sw"; "OSSVerify.KrLib.Spec.EcpCurves.ca_B"; "OSSVerify.KrLib.Spec.EcpCurves.cB"; "OSSVerify.KrLib.Spec.EcpCurves.ca_GX"; "OSSVerify.KrLib.Spec.EcpCurves.cGX"; "OSSVerify.KrLib.Spec.EcpCurves.ca_GY"; "OSSVerify.KrLib.Spec.EcpCurves.cGY"; "OSSVerify.KrLib.Spec.EcpCurves.ca_N"; "OSSVerify.KrLib.Spec.EcpCurves.cN"; "OSSVerify.KrLib.Spec.EcpCurves.curve_addrs"; "curve_statics"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Init.Logic.or"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.EcpCurves.ca_modp"; "mx_field"; "OSSVerify.KrLib.Lib.MpiCoreAux.core_bitlen"; "OSSVerify.KrLib.Spec.EcpCurves.mx_nbits"; "OSSVerify.KrLib.Spec.RepEcp.ecp_group_at"; "OSSVerify.KrLib.Spec.EcpCurves.grp_mxi"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.max"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.EcpCurves.heap1"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition static_limbs (segs : list Segment) (m : mem) (P : Z) (ws : list word) : Prop := ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "(0.(1.O4.O3.O2.(2.O1.))(0.Pi,$3.P,(0.(4.=R1.)(5.R1.(6.+4.(7.(8.(9.&40.)O1.)))))(:.$;.(<.O4.(=.(>.O2.R2.)))$?.)(0.(:.$3.(10.O2.+4.)=)(0.(5.=O2.)(0.(4.+1.(7.(8.(9.&40.)O1.)))(4.(7.(8.(9.&40.)O1.))+2710.))))))")
(* [comment removed for export] *).

Lemma ro_bytes_ro_addr : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pbs,(11.(9.&8.))Pa,$3.Pi,$3.P,(13.R4.R2.R3.)P,(0.(4.=R2.)(5.R2.(7.(8.(9.&8.)R4.))))(:.$;.(<.R6.(=.(>.R4.R3.)))$?.)")
(* [comment removed for export] *).
Proof.
  induction bs as [|b bs IH]; cbn [ro_bytes length]; intros a i H Hi; [lia|].
  destruct H as [[_ Hro] H]. destruct (Z.eq_dec i 0) as [->|NZ].
  - rewrite Z.add_0_r. exact Hro.
  - replace (a + i) with (a + 1 + (i - 1)) by lia. apply IH; [exact H| cbn in Hi; lia].
Qed.

(* [comment removed for export] *)
Lemma static_limbs_image : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))PP,$3.Pws,(11.(9.&40.))P,(15.R4.R3.)P,(:.$;.(16.R5.R3.(2.R2.))$?.)P,(:.$3.(10.R4.+4.)=)P,(5.=R5.)P,(4.(>.R6.(6.+4.(7.(8.(9.&40.)R5.))))(17.+2.+40.))P,(0.(4.+1.(7.(8.(9.&40.)R6.)))(4.(7.(8.(9.&40.)R6.))+2710.))(18.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs m P ws MI RB AL POS HB L1. pose proof (ro_bytes_b_sound segs _ _ RB) as RO.
  split; [| split; [| auto]].
  - apply ro_bytes_at; [exact MI| lia| rewrite u32s_length; lia| exact RO].
  - intros i Hi. eapply ro_bytes_ro_addr; [exact RO|]. rewrite u32s_length. lia.
Qed.

Lemma static_limbs_any_mem : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))Pm',P,(9.&40.)(14.(9.&8.))PP,$3.Pws,(11.(9.&40.))P,(18.R5.R4.R2.R1.)P,(15.R6.R5.)P,(15.R7.R5.)(18.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs m m' P ws (HB & RO & REST) MI MI'. split; [| split; [exact RO| exact REST]].
  eapply bytes_at_static; [exact MI| exact MI'| exact HB|]. rewrite u32s_length. intros i Hi. apply RO. lia.
Qed.

(* [comment removed for export] *)
Lemma smpd_at : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))PLB,(11.$19.)PA,$3.PP,$3.Pws,(11.(9.&40.))Ppad,(9.&40.)P,(1:.R7.R6.R4.(1;.R3.(1<.&40.+1.)(7.(8.(9.&40.)R2.))R1.))P,(:.$3.(10.R5.+8.)=)P,(5.=R6.)P,(18.R:.R9.R6.R5.)(1=.R;.R:.R9.(1>.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros segs m LB A P ws pad H AL POS (HB & RO & PAL & PP & L1).
  unfold mpdr_at, smpd, mpi_at; cbn -[mpi_cells rw_cells Z.of_nat Z.mul Z.pow u32s bytes_at Z.add Z.le Z.lt MPI_MAX_LIMBS].
  refine (conj H (conj AL (conj POS (conj eq_refl (conj _ _))))); [unfold MPI_MAX_LIMBS; lia|].
  split; [lia|]. split; [exact PAL|]. split; [exact PP|]. split; [exact HB|]. intros i Hi. apply RO. lia.
Qed.
Lemma smpd_mpd_at : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))PLB,(11.$19.)PA,$3.PP,$3.Pws,(11.(9.&40.))Ppad,(9.&40.)P,(1:.R7.R6.R4.(1;.R3.(1<.&40.+1.)(7.(8.(9.&40.)R2.))R1.))P,(:.$3.(10.R5.+8.)=)P,(5.=R6.)P,(18.R:.R9.R6.R5.)(1?.R;.R:.R9.(1>.R8.R7.R6.R5.))")
(* [comment removed for export] *).
Proof. intros. apply mpd_of_mpdr; [apply smpd_at; assumption| left; reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le2_low16 : forall z, le2 (Z_to_bv 64 z) = le2 (Z_to_bv 64 (z mod 2^16)).
Proof. intros z. rewrite !le2_of_Z. rewrite <- (Z_to_le_bytes_mod 2 z). reflexivity. Qed.

(* [comment removed for export] *)
Lemma mpi_cells_join : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))PX,$3.PP,$3.Ps,(9.&40.)Pn,$3.Ppad,(9.&40.)P,(1:.R7.R6.R5.(1;.R4.R3.R2.R1.))(1:.R8.R7.R6.(20.$21.(22.(1<.&40.R5.))(20.$21.(23.(1<.&40.(>.(10.(24.&40.R4.)(17.+2.+10.))(6.(17.+2.+10.)(24.&40.(1<.&40.R3.))))))(20.$21.(23.R2.)(25.$21.)))))")
(* [comment removed for export] *).
Proof. intros. apply (rw_cells_join_C2C2 segs m X [C8 (Z_to_bv 64 P)] s (Z_to_bv 64 n) [C4 pad]). exact H. Qed.

Lemma mpi_cells_of_sn : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))PX,$3.Pp,$3.Psn,$3.Ppad,(9.&40.)P,(1:.R6.R5.R4.(20.$21.(22.(1<.&40.R3.))(20.$21.(23.(1<.&40.R2.))(20.$21.(23.R1.)(25.$21.)))))P,(0.(4.=R3.)(5.R3.(17.+2.+20.)))(1:.R8.R7.R6.(1;.R5.(1<.&40.(10.R4.(17.+2.+10.)))(26.R4.(17.+2.+10.))R3.))")
(* [comment removed for export] *).
Proof.
  intros segs m X p sn pad H Hsn.
  pose proof (rw_cells_split_C4 segs m X [C8 (Z_to_bv 64 p)] (Z_to_bv 64 sn) [C4 pad] H) as H1. cbn [app] in H1.
  rewrite unsigned_lit in H1 by lia.
  eapply rw_cells_reshape; [exact H1| cbn; tauto|].
  unfold mpi_cells. cbn [cells_bytes cbytes app]. rewrite (le2_low16 sn). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition curve_statics (segs : list Segment) (ca : curve_addrs) (ONE : Z) (id : Z) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "(0.(18.O5.O1.(27.O4.)(28.O2.))(0.P,(:.$;.(29.O2.)$?.)(18.O5.O1.(2:.O4.)(2;.O2.))(0.P,(:.$;.(2<.O2.)$?.)(0.(18.O5.O1.(2=.O4.)(2>.O2.))(0.(18.O5.O1.(2?.O4.)(30.O2.))(18.O5.O1.(31.O4.)(32.O2.))))(0.(18.O5.O1.(33.O4.)(34.O2.))(18.O5.O1.O3.(20.(9.&40.)(1<.&40.+1.)(25.(9.&40.))))))))")
(* [comment removed for export] *).

Lemma curve_statics_any_mem : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pca,$35.PONE,$3.Pid,$3.Pm,P,(9.&40.)(14.(9.&8.))Pm',P,(9.&40.)(14.(9.&8.))P,(36.R6.R5.R4.R3.R2.)P,(15.R7.R3.)P,(15.R8.R3.)(36.R9.R8.R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs ca ONE id m m' (SP & SA & SW & SN & SO) MI MI'.
  split; [eapply static_limbs_any_mem; eauto|]. split; [intros H; eapply static_limbs_any_mem; eauto|].
  split; [intros H; destruct (SW H) as (S1 & S2 & S3); repeat split; eapply static_limbs_any_mem; eauto|].
  split; eapply static_limbs_any_mem; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grp_sw_at : forall segs MT m LB (ca : curve_addrs) ONE id A idpad pP pA pB pX pY pZ pN hpad,
  is_sw id = true -> 0 <= id < 2^31 ->
  curve_statics segs ca ONE id m ->
  (ca_modp ca = 0 \/ In (ca_modp ca, (ca_P ca, cP id)) MT) -> 0 <= ca_modp ca < 2^64 -> 0 <= ca_T ca < 2^64 ->
  rw_cells segs m A [C4 (Z_to_bv 64 id); C4 idpad] -> A mod 8 = 0 -> 0 < A ->
  rw_cells segs m (A + 8) (mpi_cells (ca_P ca) (Z_to_bv 64 1) (Z.of_nat (length (cP id))) pP) ->
  rw_cells segs m (A + 24) (mpi_cells (if has_A id then ca_A ca else 0) (Z_to_bv 64 1) (if has_A id then Z.of_nat (length (cA id)) else 0) pA) ->
  rw_cells segs m (A + 40) (mpi_cells (ca_B ca) (Z_to_bv 64 1) (Z.of_nat (length (cB id))) pB) ->
  rw_cells segs m (A + 56) (mpi_cells (ca_GX ca) (Z_to_bv 64 1) (Z.of_nat (length (cGX id))) pX) ->
  rw_cells segs m (A + 72) (mpi_cells (ca_GY ca) (Z_to_bv 64 1) (Z.of_nat (length (cGY id))) pY) ->
  rw_cells segs m (A + 88) (mpi_cells ONE (Z_to_bv 64 1) 1 pZ) ->
  rw_cells segs m (A + 104) (mpi_cells (ca_N ca) (Z_to_bv 64 1) (Z.of_nat (length (cN id))) pN) ->
  rw_cells segs m (A + 120) [C8 (Z_to_bv 64 (core_bitlen (cP id) (Z.of_nat (length (cP id))))); C8 (Z_to_bv 64 (core_bitlen (cN id) (Z.of_nat (length (cN id)))));
                             C4 (Z_to_bv 64 1); C4 hpad; C8 (Z_to_bv 64 (ca_modp ca)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                             C8 (Z_to_bv 64 (ca_T ca)); C8 (Z_to_bv 64 0)] ->
  ecp_group_at segs MT m LB A (grp_sw id ca ONE A idpad pP pA pB pX pY pZ pN hpad).
Proof.
  intros until hpad. intros SWC IDB (SP & SA & SWS & SN & SO) MODP MB TB HD AL POS HP HA HB HX HY HZ HN HT.
  destruct (SWS SWC) as (SB & SX & SY).
  pose proof (core_bitlen_range (cP id) (Z.of_nat (length (cP id))) ltac:(lia)) as R1.
  pose proof (core_bitlen_range (cN id) (Z.of_nat (length (cN id))) ltac:(lia)) as R2.
  pose proof SP as (_ & _ & _ & _ & LP). pose proof SN as (_ & _ & _ & _ & LN).
  unfold ecp_group_at, grp_sw, ecp_point_at; cbn -[mpdr_at smpd mpd_init rw_cells Z.pow Z.add Z.mul Z.le Z.lt Z.of_nat core_bitlen cP cN cA cB cGX cGY has_A length grp_free_mpds grp_kept_mpds grp_modp_ok].
  refine (conj HD (conj AL (conj POS _))).
  split; [reflexivity|]. split; [destruct (has_A id); reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply smpd_at; [exact HP| lia| lia| exact SP]|].
  split. { destruct (has_A id); [apply smpd_at; [exact HA| lia| lia| exact (SA eq_refl)]| apply mpdr_at_init; [exact HA| lia| lia]]. }
  split; [apply smpd_at; [exact HB| lia| lia| exact SB]|].
  split. { split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
           replace (A + 56 + 16) with (A + 72) by lia. replace (A + 56 + 32) with (A + 88) by lia.
           split; [apply smpd_at; [exact HX| lia| lia| exact SX]|]. split; [apply smpd_at; [exact HY| lia| lia| exact SY]|].
           apply (smpd_at segs m LB (A + 88) ONE [Z_to_bv 64 1] pZ); [exact HZ| lia| lia| exact SO]. }
  split; [apply smpd_at; [exact HN| lia| lia| exact SN]|].
  split; [exact HT|].
  repeat (split; [lia|]).
  split. { unfold grp_free_mpds; cbn. constructor. }
  split. { unfold grp_kept_mpds, grp_mpds, pt_mpds; cbn -[smpd mpd_init has_A]. repeat constructor; try (cbn; discriminate). destruct (has_A id); cbn; discriminate. }
  unfold grp_modp_ok; cbn -[cP In]. destruct MODP as [M0|MIN]; [left; exact M0| right]. exists (ca_P ca), (cP id). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mx_field (X : Z) (d : mpd) : Prop :=
  md_addr d = X /\ ((exists pad, d = mpd_init X pad) \/ (exists P w pad, d = heap1 X P w pad)).

Lemma mx_field_init : forall X pad, mx_field X (mpd_init X pad).
Proof. intros. split; [reflexivity| left; eauto]. Qed.
Lemma mx_field_heap1 : forall X P w pad, mx_field X (heap1 X P w pad).
Proof. intros. split; [reflexivity| right; eauto]. Qed.
Lemma mx_field_not_static : forall X d, mx_field X d -> md_own d <> LStatic.
Proof. intros X d [_ [[pad ->]|(P & w & pad & ->)]]; cbn; discriminate. Qed.
Lemma mx_field_sg : forall X d, mx_field X d -> md_sg d = 1.
Proof. intros X d [_ [[pad ->]|(P & w & pad & ->)]]; reflexivity. Qed.

Lemma grp_mxi_at : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)PMT,(11.(37.$3.(37.$3.(11.(9.&40.)))))Pm,P,(9.&40.)(14.(9.&8.))PLB,(11.$19.)Pca,$35.PONE,$3.Pid,$3.PA,$3.Pidpad,(9.&40.)PpP,(9.&40.)PpB,(9.&40.)PpY,(9.&40.)PpN,(9.&40.)Phpad,(9.&40.)PdA,$38.PdX,$38.PdZ,$38.P,(39.(:.$3.R;.+9.)(:.$3.R;.+=.))P,(36.R12.R>.R=.R<.R10.)P,(3:.(37.$3.(37.$3.(11.(9.&40.))))(3;.$3.(37.$3.(11.(9.&40.)))(3<.R?.)(3;.$3.(11.(9.&40.))(27.R?.)(28.R=.)))R12.)P,(0.(4.=(3<.R10.))(5.(3<.R10.)(17.+2.+40.)))P,(1:.R15.R13.R>.(20.$21.(23.(1<.&40.R?.))(20.$21.(23.R=.)(25.$21.))))P,(:.$3.(10.R?.+8.)=)P,(5.=R10.)P,(1:.R18.R16.(>.R11.+8.)(1;.(27.R14.)(1<.&40.+1.)(7.(8.(9.&40.)(28.R12.)))R?.))P,(1=.R19.R17.R16.R;.)P,(3=.(>.R13.+18.)R<.)P,(1:.R1;.R19.(>.R14.+28.)(1;.=(1<.&40.+1.)=R11.))P,(1=.R1<.R1:.R19.R=.)P,(3=.(>.R16.+38.)R>.)P,(1:.R1>.R1<.(>.R17.+48.)(1;.=(1<.&40.+1.)=R13.))P,(1=.R1?.R1=.R1<.R?.)P,(3=.(>.R19.+58.)R10.)P,(1:.R21.R1?.(>.R1:.+68.)(1;.(33.R1=.)(1<.&40.+1.)(7.(8.(9.&40.)(34.R1;.)))R15.))P,(1:.R22.R20.(>.R1;.+78.)(20.$21.(22.(1<.&40.(3>.(28.R1<.)(7.(8.(9.&40.)(28.R1<.))))))(20.$21.(22.(1<.&40.(3?.R1<.)))(20.$21.(23.(1<.&40.+2.))(20.$21.(23.R15.)(20.$21.(22.(1<.&40.(3<.R1>.)))(20.$21.(22.(1<.&40.=))(20.$21.(22.(1<.&40.=))(20.$21.(22.(1<.&40.=))(20.$21.(22.(1<.&40.=))(20.$21.(22.(1<.&40.=))(25.$21.))))))))))))(40.R23.R22.R21.R20.R1<.(41.R1=.R1?.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.))")
(* [comment removed for export] *).
Proof.
  intros until dZ. intros IDC (SP & _ & _ & SN & _) MODP MB HD AL POS HP MA FA HB MX FX HY MZ FZ HN HT.
  pose proof (core_bitlen_range (cP id) (Z.of_nat (length (cP id))) ltac:(lia)) as R1.
  pose proof SP as (_ & _ & _ & _ & LP). pose proof SN as (_ & _ & _ & _ & LN).
  pose proof FA as [EA _]. pose proof FX as [EX _]. pose proof FZ as [EZ _].
  unfold ecp_group_at, grp_mxi, ecp_point_at; cbn -[mpdr_at smpd mpd_init rw_cells Z.pow Z.add Z.mul Z.le Z.lt Z.of_nat core_bitlen cP cN length grp_free_mpds grp_kept_mpds grp_modp_ok mx_nbits].
  refine (conj HD (conj AL (conj POS _))).
  split; [reflexivity|]. split; [exact EA|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply smpd_at; [exact HP| lia| lia| exact SP]|].
  split; [exact MA|].
  split; [apply mpdr_at_init; [exact HB| lia| lia]|].
  split. { split; [exact EX|]. split; [cbn; lia|]. split; [rewrite EZ; lia|].
           split; [exact MX|]. split; [apply mpdr_at_init; [replace (A + 56 + 16) with (A + 72) by lia; exact HY| lia| lia]| exact MZ]. }
  split; [apply smpd_at; [exact HN| lia| lia| exact SN]|].
  split; [exact HT|].
  assert (0 <= mx_nbits id < 2^64) by (unfold mx_nbits; destruct (id =? 9); lia).
  repeat (split; [lia|]).
  split. { unfold grp_free_mpds; cbn -[mpd_init]. repeat constructor; cbn; try discriminate.
           - eapply mx_field_not_static; exact FA. - eapply mx_field_not_static; exact FX. - eapply mx_field_not_static; exact FZ. }
  split. { unfold grp_kept_mpds; cbn -[smpd]. repeat constructor; cbn; discriminate. }
  unfold grp_modp_ok; cbn -[cP In]. right. exists (ca_P ca), (cP id). auto.
Qed.

(* [comment removed for export] *)
Lemma mpdr_at_LB_mono : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Psegs,(11.$12.)Pm,P,(9.&40.)(14.(9.&8.))PLB,(11.$19.)PLB',(11.$19.)Pd,$38.P,(1=.R5.R4.R3.R1.)P,Pb,$19.P,(3:.$19.R1.R5.)(3:.$19.R2.R5.)(1=.R7.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros segs m LB LB' d (HR & HAL & HPOS & HL & HN & HO) S.
  split; [exact HR|]. split; [exact HAL|]. split; [exact HPOS|]. split; [exact HL|]. split; [exact HN|].
  destruct (md_own d); try exact HO. destruct HO as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [apply S; exact H2|]. split; [exact H3| exact H4].
Qed.

(* [comment removed for export] *)
Lemma lset_heap1 : ltac2:(CDefT.buildp (gd_tbl_EcpLoad ()) "Pd,$38.PX,$3.P,(:.$3.(42.R2.)(43.=+1.))P,(:.$44.(45.R3.)$46.)P,(47.(9.&40.)Lw0,(9.&40.)(:.(11.(9.&40.))(48.R5.)(20.(9.&40.)R1.(49.(9.&40.)(1<.&40.=)(4:.(4;.(42.R5.)+1.))))))P,(:.$3.(4<.R5.)+1.)P,(:.$3.(4=.R6.)R5.)(47.(9.&40.)Lw,(9.&40.)(:.$38.R8.(4>.R7.(4?.R8.)R1.(50.R8.))))")
(* [comment removed for export] *).
Proof.
  intros [a sg n p ls pd ow] X Hn Ho [w0 Hl] Hs Ha. cbn in Hn, Ho, Hl, Hs, Ha. subst a ow sg. rewrite Hn in Hl. cbn in Hl. subst ls.
  exists w0. unfold heap1. cbn. rewrite Hn. reflexivity.
Qed.
