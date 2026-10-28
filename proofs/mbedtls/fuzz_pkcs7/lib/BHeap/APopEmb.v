(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_APopEmb () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "ARUN_1.acct_set_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.fold_right"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.NoDup"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.csum"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.frozen"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_exh"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.epi"; "RocqVerifyHarness.AgentSubmission.BHeap.APopGen.null_h"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.EM"; "ARUN_1.emb_h"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

Definition acct_set_emb (a : acct) (d sz : Z) : acct := AC (a_sech a) d sz (a_exh a).
Definition emb_h (h : ahst) (d sz : Z) : ahst := ltac2:(CDefT.buildp (gd_tbl_APopEmb ()) "(0.(1.O3.)(2.O3.)(3.O3.)(4.O3.)(5.O3.)(6.O3.)(7.O3.)(8.O3.)(9.O3.)(:.O3.)(;.O3.)(<.O3.)(=.O3.)(>.(?.O3.)O2.O1.))")
(* [comment removed for export] *).


(* [comment removed for export] *)
#[using="Type"] Lemma fold_same : ltac2:(CDefT.buildp (gd_tbl_APopEmb ()) "Pf,P,$10.$10.Pg,P,$10.$10.Pl,(11.$10.)P,Pj,$10.P,(12.$10.R1.R2.)(13.$10.A1.R4.R2.A1.R5.R2.)(13.$10.(14.$10.$10.Lc,$10.Lacc,$10.(15.A1.R5.R2.R1.)=R2.)(14.$10.$10.Lc,$10.Lacc,$10.(15.A1.R6.R2.R1.)=R2.))")
(* [comment removed for export] *).
Proof. induction l as [|x l IH]; intros H; cbn; [reflexivity|]. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros j Hj. apply H. right. exact Hj. Qed.
#[using="Type"] Lemma fold_step : ltac2:(CDefT.buildp (gd_tbl_APopEmb ()) "Pf,P,$10.$10.Pg,P,$10.$10.Pc,$10.Pl,(11.$10.)P,(16.$10.R1.)P,(12.$10.R3.R2.)P,Pj,$10.P,(17.(13.$10.R1.R5.))(13.$10.A1.R7.R2.A1.R8.R2.)P,(13.$10.A1.R6.R5.(15.A1.R7.R5.+1.))(13.$10.(14.$10.$10.Lc,$10.Lacc,$10.(15.A1.R9.R2.R1.)=R5.)(15.(14.$10.$10.Lc,$10.Lacc,$10.(15.A1.R:.R2.R1.)=R5.)+1.))")
(* [comment removed for export] *).
Proof.
  induction l as [|x l IH]; intros ND HI HO HC; [destruct HI|]. inversion ND as [|? ? NI ND']; subst. cbn.
  destruct (Z.eq_dec x c) as [->|NE].
  - rewrite HC, (fold_same f g l); [lia|]. intros j Hj. apply HO. intros ->. exact (NI Hj).
  - destruct HI as [E|HI]; [exfalso; exact (NE E)|]. rewrite (HO x NE), (IH ND' HI HO HC). lia.
Qed.
#[using="Type"] Lemma csum_step : ltac2:(CDefT.buildp (gd_tbl_APopEmb ()) "Pf,P,$10.$10.Pg,P,$10.$10.Pc,$10.P,(18.(19.+1.R1.)(19.R1.+1?.))P,Pj,$10.P,(17.(13.$10.R1.R3.))(13.$10.A1.R5.R2.A1.R6.R2.)P,(13.$10.A1.R4.R3.(15.A1.R5.R3.+1.))(13.$10.(1:.R5.)(15.(1:.R6.)+1.))")
(* [comment removed for export] *).
Proof.
  intros f g c Hc HO HC. unfold csum. apply (fold_step f g c); [| | exact HO| exact HC]; unfold cls31.
  - apply Finite.Injective_map_NoDup; [intros a b E; lia| apply seq_NoDup].
  - apply in_map_iff. exists (Z.to_nat c). split; [lia| apply in_seq; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma csum_epi_exh : ltac2:(CDefT.buildp (gd_tbl_APopEmb ()) "Ph,$1;.Pc,$10.P,(18.(19.+1.R1.)(19.R1.+1?.))P,(13.$1<.(1=.R3.R2.)$1>.)P,(13.$1<.(1?.(?.R4.)R3.)$20.)(13.$10.(1:.(21.(22.R5.R4.=$1>.)))(15.(1:.(21.R5.))+1.))")
(* [comment removed for export] *).
Proof.
  intros h c Hc FZ EX. apply (csum_step (epi h) (epi (null_h h c 0 true)) c Hc).
  - intros j NE. apply epi_frame; cbn [h_reg h_acct null_h acct_set_exh a_exh]; unfold null_reg; destruct (Z.eqb_spec j c) as [E|_]; [exfalso; exact (NE E)| reflexivity| exfalso; exact (NE E)| reflexivity].
  - unfold epi, frozen in *. cbn [h_reg h_acct null_h acct_set_exh a_exh]. unfold null_reg, rN. rewrite Z.eqb_refl. cbn [r_mapped_user r_alloc_user].
    rewrite Z.add_0_r. rewrite FZ, EX. destruct (class_size c <=? _); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem awf'_emb : ltac2:(CDefT.buildp (gd_tbl_APopEmb ()) "Ph,$1;.Pd,$10.Psz,$10.P,(23.VhAR,R3.)P,(24.R3.$25.)P,(26.=R4.)P,(19.(15.R5.$25.)(27.VhAR,))P,(13.$10.(28.R6.+1000.)=)P,(29.(19.(15.R7.$25.)(2:.(1.R8.)))(19.(15.(2:.(1.R8.))+2000011000.)R7.))P,(29.(19.(15.R8.$25.)(2;.(1.R9.)))(19.(15.(2;.(1.R9.))+800000.)R8.))P,(18.(19.=R8.)(19.R8.(2<.$2=.(1:.(21.R:.)))))(23.VhAR,(2>.R;.R:.R9.))")
(* [comment removed for export] *).
Proof.
  (intros h d sz dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG); intros G1 G2 G3 G4 G5 G6 SZ).
  split; [exact WL|]. split; [exact WC|]. split; [exact WR|]. split; [exact WK|]. split; [exact WQ|]. split; [exact WS|]. split; [exact WD|]. split; [exact WB|]. split; [exact WBIG|].
  split; [| exact WG].
  ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
  split.
  - right. cbn [h_acct h_L emb_h a_emb a_esz acct_set_emb]. exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (proj1 SZ))))))).
  - (* [comment removed for export] *)
    split; [cbn [h_acct emb_h a_esz acct_set_emb]; exact (proj2 SZ)| split; [exact X8| exact X9]].
Qed.

End ARUN_1.
