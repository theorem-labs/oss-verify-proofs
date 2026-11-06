(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of kind_of_link1 on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat, the walk loop and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v; the contract and the branch lemmas are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/KindOfLink1.v, with its module paths and module names changed; 58 of its 174 lines of code are new or changed and 53 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/KindOfLink1.v, with its module paths and module names changed; 118 of its 150 lines of code are new or changed and 142 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require FindEntry CheckTable RoleOf ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntObsS1 DiscoYEntObsS2 DiscoYEntObsS3 DiscoYEntObsS4 DiscoYEntObsS5 DiscoYEntObsS7
DiscoYEntObsS8 DiscoYEntObsS9 DiscoYEntObsS10 DiscoYEntObsS9b2 DiscoYEntObsS6 DiscoYEntObsS9a2W.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma ob_in0 : forall cx h i n now op nb fr len Sg W c,
  obs_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg W c ->
  ob_c0 B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c.
Proof.
intros cx h i n now op nb fr len Sg W c H.
unfold obs_in, d_arm_at_pf, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & _ & HX & Hsp0 & Hbody).
destruct HX as (Hop & Hop2 & Hfrm & HSgl & HSg & HSf & HREC & (H360 & _) & Hlen & Hnb).
pose proof Hbody as (T & G & Lk & H & _ & _ & Hobjs & _).
destruct Hobjs as (HTl & HT & HTok & _).
unfold ob_c0, d_at.
exists fq, ly3, S3, regs, mem3, md3, k, acc.
split; [exact Hc|]. split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
exists T. split; [|exact H360].
exact (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj HrL (conj Hsp0 (conj Hfrm (conj HSgl (conj HSg (conj HSf
  (conj HREC (conj Hlen (conj Hnb (conj HTl (conj HT (conj HTok Hbody))))))))))))))))).
Qed.

Theorem ob_s9b_of : ob_seg9b1 B MT XM_LIB RLO RHI tfib_K -> ob_seg9b2 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg9b B MT XM_LIB RLO RHI tfib_K.
Proof.
intros S1 S2 cx h i n now op nb fr len Sg W c H.
eapply SRr_bind; [exact (S1 cx h i n now op nb fr len Sg _ _ W c H)|].
intros W1 c1 _ H1. exact (S2 cx h i n now op nb fr len Sg W1 c1 H1).
Qed.

Theorem ob_s9a_of : ob_seg9a1 B MT XM_LIB RLO RHI tfib_K -> ob_seg9a2 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg9a B MT XM_LIB RLO RHI tfib_K.
Proof.
intros S1 S2 cx h i n now op nb fr len Sg kmax accmax W c H.
eapply SRr_bind; [exact (S1 cx h i n now op nb fr len Sg kmax accmax W c H)|].
intros W1 c1 _ H1. exact (S2 cx h i n now op nb fr len Sg kmax accmax W1 c1 H1).
Qed.

Theorem obs_of_parts :
  ob_seg01 B MT XM_LIB RLO RHI tfib_K -> ob_seg12 B MT XM_LIB RLO RHI tfib_K -> ob_seg23 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg34 B MT XM_LIB RLO RHI tfib_K -> ob_seg45 B MT XM_LIB RLO RHI tfib_K -> ob_seg56 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg67 B MT XM_LIB RLO RHI tfib_K -> ob_seg78 B MT XM_LIB RLO RHI tfib_K -> ob_seg89 B MT XM_LIB RLO RHI tfib_K ->
  ob_seg9a B MT XM_LIB RLO RHI tfib_K -> ob_seg9b B MT XM_LIB RLO RHI tfib_K -> ob_seg10r B MT XM_LIB RLO RHI tfib_K ->
  obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros S01 S12 S23 S34 S45 S56 S67 S78 S89 S9a S9b S10r cx h i n now op nb fr len Sg W c H.
set (km := EV_HEAD i + 1). set (am := ACC_HEAD MT i + mo_malloc MT REC_MAX).
eapply SRr_bind; [exact (S01 cx h i n now op nb fr len Sg km am W c (ob_in0 cx h i n now op nb fr len Sg W c H))|].
intros W1 c1 _ H1.
eapply SRr_bind; [exact (S12 cx h i n now op nb fr len Sg km am W1 c1 H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (S23 cx h i n now op nb fr len Sg km am W2 c2 H2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (S34 cx h i n now op nb fr len Sg km am W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (S45 cx h i n now op nb fr len Sg km am W4 c4 H4)|]. intros W5 c5 _ H5.
eapply SRr_bind; [exact (S56 cx h i n now op nb fr len Sg km am W5 c5 H5)|]. intros W6 c6 _ H6.
eapply SRr_bind; [exact (S67 cx h i n now op nb fr len Sg km am W6 c6 H6)|]. intros W7 c7 _ [H7|[H9|H10]].
- eapply SRr_bind; [exact (S78 cx h i n now op nb fr len Sg km am W7 c7 H7)|]. intros W8 c8 _ H8.
  eapply SRr_bind; [exact (S89 cx h i n now op nb fr len Sg km am W8 c8 H8)|]. intros W9 c9 _ H9.
  eapply SRr_bind; [exact (S9a cx h i n now op nb fr len Sg km am W9 c9 H9)|]. intros W10 c10 _ H10.
  exact (S9b cx h i n now op nb fr len Sg W10 c10 H10).
- eapply SRr_bind; [exact (S9a cx h i n now op nb fr len Sg km am W7 c7 H9)|]. intros W10 c10 _ H10.
  exact (S9b cx h i n now op nb fr len Sg W10 c10 H10).
- exact (S10r cx h i n now op nb fr len Sg W7 c7 H10).
Qed.

Section p.
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
Context {PX : PAXcalls lib_both3_0_listing}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BTOBS : d_body_tobs_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BPCALL : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DCAN : d_can_hyps B tfib_K.
Hypothesis DRO : d_ro_hyps B.
Hypothesis TFIND : FindEntry.tfind_entry_spec B.
Hypothesis TCHK : CheckTable.tcheck_table_spec B.
Hypothesis TROLE : RoleOf.trole_of_spec B.
Hypothesis TTOBS : ReacDiscoTableObserve.treac_disco_table_observe_spec B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).

Theorem pb_obs_of_9a : ob_seg9a1 B MT XM_LIB RLO RHI tfib_K -> ob_seg9a2 B MT XM_LIB RLO RHI tfib_K ->
  obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof using PX LAWS TL MT_TRIV SEAT FACTS BRT BCK BTOBS BPCALL DCAN DRO TFIND TCHK TROLE TTOBS ABCMP.
intros S9a1 S9a2.
apply obs_of_parts.
- eapply ob_s01; eassumption.
- eapply ob_s12; eassumption.
- eapply (ob_s23 B MT XM_LIB XM_LIB RLO RHI tfib_K); eassumption.
- eapply ob_s34; eassumption.
- eapply ob_s45; eassumption.
- eapply ob_s56; eassumption.
- eapply ob_s67; eassumption.
- eapply ob_s78; eassumption.
- eapply ob_s89; eassumption.
- exact (ob_s9a_of S9a1 S9a2).
- apply ob_s9b_of; [eapply (ob_s9b1 B MT MT_TRIV XM_LIB XM_LIB RLO RHI tfib_K); eassumption |
    eapply (ob_s9b2 B MT XM_LIB XM_LIB RLO RHI tfib_K); eassumption].
- eapply ob_s10r; eassumption.
Qed.

Theorem pb_obs : obs_spec B MT XM_LIB RLO RHI tfib_K.
Proof using PX LAWS TL MT_TRIV SEAT FACTS BRT BCK BTOBS BPCALL DCAN DRO TFIND TCHK TROLE TTOBS ABCMP.
apply pb_obs_of_9a; [eapply (ob_s9a1 B MT XM_LIB XM_LIB RLO RHI tfib_K); eassumption | eapply ob_s9a2; eassumption].
Qed.
End p.

End h.
End f.
End d.
