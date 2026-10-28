(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Ltac2 gd_tbl_AVstT () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.AFreeSlot.zsum"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vperm"; "Stdlib.Lists.List.fold_right"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_eager"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_lazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.sec_tr"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.uunit_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.funit_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.ri_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaSlice"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.pa_tr"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.fixed_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.emb_tr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lit"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.hulls_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.space_end"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPrimHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.breg"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.kPaHullLen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserLimit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "R_ugrow"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_add_sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "R_fgrow"; "R_pa"; "R_secadd"; "R_secrm"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_remove"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.dgrow"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.cb_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vranges_ok"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.bwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "Stdlib.Lists.List.filter"; "Corelib.Init.Datatypes.negb"; "Stdlib.ZArith.BinInt.Z.eqb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.lkind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_kind"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_len"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.munmap_model"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "ARUN_2.TRANS.shpb"; "ARUN_2.TRANS.shpe"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_next"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.v_eb"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CN"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.VLIMIT"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CSB"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma Permutation_filter : forall {A} (f : A -> bool) (l l' : list A), Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip; exact IH| exact IH].
  - destruct (f y), (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L59308586510.700000<S1n1s1k1E2Hk". (* [comment removed for export] *)
#[using="Type"] Lemma NoDup_map_ofnat_seq : forall s n, List.NoDup (map Z.of_nat (seq s n)).
Proof.
  intros s n. revert s. induction n as [|n IH]; intros s; cbn; [constructor|]. constructor; [| apply IH].
  intros H. apply in_map_iff in H. ddestruct H as (k & E & Hk). apply in_seq in Hk. apply Nat2Z.inj in E. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma flat_map_agree : forall {A B} (F F' : A -> list B) (l : list A), (forall a, In a l -> F' a = F a) -> flat_map F' l = flat_map F l.
Proof.
  intros A B F F' l AGR. induction l as [|a l IH]; [reflexivity|]. cbn [flat_map].
  rewrite (AGR a ltac:(left; reflexivity)), (IH ltac:(intros b Hb; apply AGR; right; exact Hb)). reflexivity.
Qed.

#[using="Type"] Lemma flat_map_perm_insert : forall {B} (F F' : Z -> list B) (x : B) (c : Z) (l : list Z),
  List.NoDup l -> In c l -> (forall a, In a l -> a <> c -> F' a = F a) -> Permutation (F' c) (x :: F c) ->
  Permutation (flat_map F' l) (x :: flat_map F l).
Proof.
  intros B F F' x c l ND IN AGR PC. induction l as [|a l IH]; [destruct IN|]. cbn [flat_map].
  inversion ND as [|a' l' NI ND']; subst.
  destruct (Z.eq_dec a c) as [->|NE].
  - assert (E : flat_map F' l = flat_map F l).
    { apply flat_map_agree. intros b Hb. apply AGR; [right; exact Hb| intros ->; exact (NI Hb)]. }
    rewrite E. change (x :: F c ++ flat_map F l) with ((x :: F c) ++ flat_map F l). apply Permutation_app_tail. exact PC.
  - destruct IN as [->|IN]; [exfalso; apply NE; reflexivity|].
    rewrite (AGR a ltac:(left; reflexivity) NE).
    specialize (IH ND' IN ltac:(intros b Hb NEb; apply AGR; [right; exact Hb| exact NEb])).
    eapply Permutation_trans; [apply Permutation_app_head; exact IH|]. apply Permutation_sym. apply Permutation_middle.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L25185359512.14L39031216456.1500000900BS1f1c1d1lS1f1d1a1l". (* [comment removed for export] *)
#[using="Type"] Lemma zsum_update : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Pf,P,$0.$0.Pf',P,$0.$0.Pc,$0.Pd,$0.Pl,(1.$0.)P,(2.$0.R1.)P,(3.$0.R4.R2.)P,Pa,$0.P,(3.$0.R1.R4.)P,(4.(5.$0.R2.R7.))(5.$0.A1.R9.R3.A1.R:.R3.)P,(5.$0.A1.R7.R6.(6.A1.R8.R6.R5.))(5.$0.(7.$0.R8.R5.)(6.(7.$0.R9.R5.)R6.))")
(* [comment removed for export] *).
Proof.
  intros f f' c d l ND IN AGR E. induction l as [|a l IH]; [destruct IN|]. cbn [zsum]. inversion ND as [|a' l' NI ND']; subst.
  destruct (Z.eq_dec a c) as [->|NE].
  - assert (E2 : zsum f' l = zsum f l).
    { apply zsum_ext. intros b Hb. apply AGR; [right; exact Hb| intros ->; exact (NI Hb)]. }
    rewrite E2, E. lia.
  - destruct IN as [->|IN]; [exfalso; apply NE; reflexivity|]. rewrite (AGR a ltac:(left; reflexivity) NE).
    rewrite (IH ND' IN ltac:(intros b Hb NEb; apply AGR; [right; exact Hb| exact NEb])). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020=L2424960062.3L6755912672.3000006007S1n2HnS". (* [comment removed for export] *)
#[using="Type"] Lemma zseq_succ : forall n, 0 <= n -> zseq (n + 1) = zseq n ++ [n].
Proof.
  intros n Hn. unfold zseq. rewrite Z2Nat.inj_add, Nat.add_1_r, seq_S, map_app by lia. cbn [map]. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma classes_NoDup : List.NoDup classes.
Proof. unfold classes. apply NoDup_map_ofnat_seq. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L20674443272.3L25492742081.300000600<S1c2HcS1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma classes_in : forall c, 1 <= c <= 31 -> In c classes.
Proof.
  intros c Hc. unfold classes, kNumClasses. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma vperm_refl : forall v, vperm v v.
Proof. intros v. unfold vperm. repeat split; apply Permutation_refl. Qed.
#[using="Type"] Lemma vperm_trans : forall v1 v2 v3, vperm v1 v2 -> vperm v2 v3 -> vperm v1 v3.
Proof.
  (intros v1 v2 v3 dd_H; ddestruct dd_H as (P1 & P2 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8); intros dd_H; ddestruct dd_H as (Q1 & Q2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8)). unfold vperm.
  repeat split; first [eapply Permutation_trans; eassumption | etransitivity; eassumption].
Qed.
#[using="Type"] Lemma vperm_add_sub : forall v v' lo n cs, vperm v v' -> vperm (v_add_sub v lo n cs) (v_add_sub v' lo n cs).
Proof.
  (intros v v' lo n cs dd_H; ddestruct dd_H as (P1 & P2 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8)). unfold vperm, v_add_sub. cbn.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8. repeat split; try reflexivity; [apply perm_skip; exact P1| exact P2].
Qed.
#[using="Type"] Lemma vperm_add_eager : forall v v' lo n cs, vperm v v' -> vperm (v_add_eager v lo n cs) (v_add_eager v' lo n cs).
Proof.
  (intros v v' lo n cs dd_H; ddestruct dd_H as (P1 & P2 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8)). unfold vperm, v_add_eager. cbn.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8. repeat split; try reflexivity; apply perm_skip; assumption.
Qed.
#[using="Type"] Lemma vperm_add_lazy : forall v v' lo n, vperm v v' -> vperm (v_add_lazy v lo n) (v_add_lazy v' lo n).
Proof.
  (intros v v' lo n dd_H; ddestruct dd_H as (P1 & P2 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8)). unfold vperm, v_add_lazy. cbn.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8. repeat split; try reflexivity; apply perm_skip; assumption.
Qed.
#[using="Type"] Lemma vperm_fold_eager : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Pl,(1.$0.)Pv,$8.Pv',$8.P,(9.R2.R1.)(9.(:.$8.$0.La,$0.Lv,$8.(;.R1.R2.(<.+2.+14.)$=.)R3.R4.)(:.$8.$0.La,$0.Lv,$8.(;.R1.R2.(<.+2.+14.)$=.)R2.R4.))")
(* [comment removed for export] *).
Proof. intros l v v' P. induction l as [|a l IH]; cbn [fold_right]; [exact P| apply vperm_add_eager; exact IH]. Qed.
#[using="Type"] Lemma vperm_fold_lazy : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Pl,(1.$0.)Pv,$8.Pv',$8.P,(9.R2.R1.)(9.(:.$8.$0.Lb,$0.Lv,$8.(>.R1.R2.(<.+2.+17.))R3.R4.)(:.$8.$0.Lb,$0.Lv,$8.(>.R1.R2.(<.+2.+17.))R2.R4.))")
(* [comment removed for export] *).
Proof. intros l v v' P. induction l as [|a l IH]; cbn [fold_right]; [exact P| apply vperm_add_lazy; exact IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma tr_of_inv : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pt,$10.P,(3.$10.R1.(11.R2.))(12.(13.$0.Lb,$0.(14.(3.$0.R1.(15.(16.R4.)))(5.$10.R3.(17.R1.))))(12.(13.$0.Lb,$0.(14.(3.$0.R1.(18.(16.R4.)))(5.$10.R3.(19.R1.))))(12.(13.$1:.Lsh,$1:.(14.(3.$1:.R1.(1;.(1<.R4.)))(5.$10.R3.(1=.R1.))))(12.(13.$0.Lc,$0.(13.$0.Lj,$0.(14.(14.(1>.+1.R2.)(1>.R2.+1?.))(14.(14.(1>.=R1.)(1?.R1.(20.(21.(22.R5.R2.))$23.)))(5.$10.R4.(24.(25.R5.)R2.R1.))))))(12.(13.$0.Lc,$0.(13.$0.Lj,$0.(14.(14.(1>.+1.R2.)(1>.R2.+1?.))(14.(14.(1>.=R1.)(1?.R1.(20.(26.(22.R5.R2.))$23.)))(5.$10.R4.(27.(25.R5.)R2.R1.))))))(12.(5.$10.R2.(28.(25.R3.)))(12.(13.$0.Lj,$0.(14.(14.(1>.=R1.)(1?.R1.(20.(29.R4.)$2:.)))(5.$10.R3.(2;.(25.R4.)R1.))))(3.$10.R2.(2<.$10.(2=.(25.R3.))(2>.R3.))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
Proof.
  intros h t Ht. unfold tr_of in Ht. rewrite !in_app_iff in Ht.
  destruct Ht as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]].
  - left. apply in_map_iff in Ht. ddestruct Ht as (b & <- & Hb). exists b. auto.
  - right; left. apply in_map_iff in Ht. ddestruct Ht as (b & <- & Hb). exists b. auto.
  - do 2 right; left. apply in_map_iff in Ht. ddestruct Ht as (b & <- & Hb). exists b. auto.
  - unfold units_of in Ht. apply in_flat_map in Ht. ddestruct Ht as (c & Hc & Ht). pose proof (classes_spec c Hc) as CC.
    apply in_app_iff in Ht. destruct Ht as [Ht|Ht]; apply in_map_iff in Ht; ddestruct Ht as (j & <- & Hj); apply in_zseq in Hj.
    + do 3 right; left. dexists c, j. auto.
    + do 4 right; left. dexists c, j. auto.
  - do 5 right; left. destruct Ht as [<-|[]]. reflexivity.
  - do 6 right; left. apply in_map_iff in Ht. ddestruct Ht as (j & <- & Hj). apply in_zseq in Hj. exists j. auto.
  - do 7 right. apply in_app_iff. left. exact Ht.
  - do 7 right. apply in_app_iff. right. exact Ht.
Qed.

#[using="Type"] Lemma fixed_of_lit : forall L t, In t (fixed_of L) -> t_lit t = true.
Proof.
  intros L t Ht. unfold fixed_of in Ht. rewrite !in_app_iff in Ht. destruct Ht as [Ht|[Ht|Ht]].
  - destruct Ht as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
  - apply in_map_iff in Ht. ddestruct Ht as (r & <- & _). reflexivity.
  - destruct Ht as [<-|[<-|[<-|[]]]]; reflexivity.
Qed.

#[using="Type"] Lemma fixed_emb_lit : forall h t, In t (fixed_of (h_L h) ++ emb_tr h) -> t_lit t = true.
Proof.
  intros h t Ht. apply in_app_iff in Ht. destruct Ht as [Ht|Ht]; [exact (fixed_of_lit _ _ Ht)|].
  unfold emb_tr in Ht. destruct (a_emb (h_acct h) =? 0); [destruct Ht| destruct Ht as [<-|[]]; reflexivity].
Qed.

(* [comment removed for export] *)
Section GEO.
  Variable AL : asan_layout.

  #[using="Type"] Lemma lit_apart_hull : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pt,$10.PH,(30.$0.$0.)P,(31.VhAR,VAL,R4.R3.)P,(3.$10.R3.(11.R5.))P,(5.$32.(33.R4.)$=.)P,(3.(30.$0.$0.)R4.(34.(25.R7.)))(12.(1>.(35.R6.)(36.$0.$0.R5.))(1>.(6.(36.$0.$0.R5.)(37.$0.$0.R5.))(38.R6.)))")
(* [comment removed for export] *).
  Proof.
    intros h mo t H K Ht TL HH. destruct (hulls_apart_tr AL h mo t H K Ht HH) as [(_ & _ & F & _)|X]; [rewrite TL in F; discriminate F| exact X].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10313436014.4700000:S3hAR1L2H1". (* [comment removed for export] *)
  #[using="Type"] Lemma wfL_facts : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "PL,$39.P,(3:.VhAR,R1.)(14.(1>.(3;.R2.)(3<.R2.))(14.(1>.(3<.R2.)(6.(3;.R2.)(<.+2.+10.)))(14.(5.$0.(3=.(3<.R2.)(<.+2.+10.))=)(14.(1>.(6.(3>.R2.)+1000.)(6.(3;.R2.)$3?.))(14.(1>.$40.(3;.R2.))(14.(41.(42.R2.)+800000.)(5.$0.(3=.(42.R2.)+1000.)=)))))))")
(* [comment removed for export] *).
  Proof. intros L WL. unfold wf_L in WL. unfold kPrimHullLen. unfold lowhigh in *. decompose [and] WL. repeat split; try assumption; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Ltac geo := unfold node_tr, store_tr, sec_tr, uunit_tr, funit_tr, pa_tr, ri_tr, ri_base, fa_beg, region_beg, kRegionSize, kUserMapSize, kUserLimit,
                     kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, space_end, kSpaceSize, kPrimHullLen, kPaHullLen, kPaSlice, kHighMemBeg, lowhigh, t_hi in *;
              cbn [t_lo t_len t_lit fst snd] in *.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00E0?L13318706061.10L15730926390.30L15733024566.31L16370771165.27L18926753607.27L18928663569.28L22934763951.12L22937035026.14L24533011678.13L40279369813.27L41079622018.12L41081655615.14L41370042806.20L43153469325.27L48349871560.5 L51324363965.28L56995914634.14L57721344538.27L58319307633.10L6755429322.27 L9409744447.13 00000C00O00`01901B01K01Z01o02F02Z02h03I03Q03i04604F04[04n05B05U05oS1h1c1t2Hc2F13MU01XS1h1c2c'3MU0S1h1c2c'3MU04MU0'S1h1c2Hc4ROOM2sh2F43MU01XS1h1c3MU0S1h1c3MU0S1h1c4ROOM1j2HjS1h1c4ROOM2c'1j2Hj2GTS1h1c2Hc4ROOM1j2F22Hj1XS1h1c2Hc2sh2F13MU01XS1h1c1j3MU02J1S1h1c2c'1j3MU06MULIM'2J12LT5MFAB'S1h1c2HcS1h1c2Hc4ROOM1b2F43MU01XS1h1c2Hc4ROOMS1h1c2c'3MU03Hc'S1h1c4ROOM2c'1j2Hj2GTS1h1c2Hc1b2F13MU01XS1h1c1t2Hc4ROOM2F21XS1h1c2Hc1b2F13MU01XS1h1c3PAB2Hc1j2F13MU01X2J1". (* [comment removed for export] *)
  #[using="Type"] Lemma uunit_new_apart : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pc,$0.Pt,$10.P,(31.VhAR,VAL,R4.R3.)P,(3:.VhAR,(25.R5.))P,(43.R6.)P,(14.(1>.=(29.R7.))(1>.(29.R7.)$44.))P,(14.(1>.+1.R6.)(1>.R6.+1?.))P,(1>.(6.(21.(22.R9.R7.))$23.)$45.)P,(3.$10.R7.(11.R:.))(12.(1>.(6.(6.(46.(25.R;.)R9.)(21.(22.R;.R9.)))$23.)(38.R8.))(1>.(35.R8.)(6.(46.(25.R;.)R9.)(21.(22.R;.R9.)))))")
(* [comment removed for export] *).
  Proof.
    intros h mo c t K WL BR PAB Hc ROOM Ht.
    pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c' & j & Hc' & Hj & ->)|[(c' & j & Hc' & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]].
    - destruct (lit_apart_hull h mo (node_tr b) _ K Ht eq_refl ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - destruct (lit_apart_hull h mo (store_tr b) _ K Ht eq_refl ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - destruct (lit_apart_hull h mo (sec_tr sh) _ K Ht eq_refl ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - dpose (BR c' ltac:(unfold kNumClasses; lia)) as (MU0' & MUAL' & MULIM' & _). geo.
      pose proof (Z.div_mod (r_mapped_user (h_reg h c')) (2^18) ltac:(lia)) as DM. rewrite MUAL' in DM.
      assert (J1 : j * 2^18 + 2^18 <= r_mapped_user (h_reg h c')) by (clear - Hj DM; nia).
      destruct (Z.lt_total c' c) as [LT|[->|GT]]; [right; clear - J1 LT MULIM' MULIM ROOM Hj MU0 MFAB Hc Hc'; lia| right; clear - J1 MULIM' MULIM ROOM Hj MU0 MFAB Hc Hc'; lia| left; clear - J1 GT MULIM' MULIM ROOM Hj MU0 MFAB Hc Hc'; lia].
    - dpose (BR c' ltac:(unfold kNumClasses; lia)) as (_ & _ & _ & MFAL' & MFAB'). geo.
      pose proof (Z.div_mod (r_mapped_fa (h_reg h c')) (2^18) ltac:(lia)) as DM. rewrite MFAL' in DM.
      assert (J1 : j * 2^18 + 2^18 <= r_mapped_fa (h_reg h c')) by (clear - Hj DM; nia).
      destruct (Z.lt_total c' c) as [LT|[->|GT]]; [right; clear - J1 LT MFAB' MULIM ROOM Hj MU0 MFAB Hc Hc'; lia| left; clear - J1 MFAB' MULIM ROOM Hj MU0 MFAB Hc Hc'; lia| left; clear - J1 GT MFAB' MULIM ROOM Hj MU0 MFAB Hc Hc'; lia].
    - left. geo. clear - Hc ROOM MULIM; lia.
    - pose proof (hulls_apart AL h mo K) as HA. geo.
      pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (h_pa_committed h) 131072 ltac:(lia)) as MB.
      assert (J1 : j * 131072 + 131072 <= h_pa_committed h) by (clear - Hj DM MB; nia).
      destruct HA as [X|X]; [left| right]; clear - X J1 Hj PAB F1 F2 Hc ROOM MULIM MU0; lia.
    - destruct (lit_apart_hull h mo t _ K Ht (fixed_emb_lit _ _ HF) ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; clear - X F1 F2 Hc ROOM MULIM MU0; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L15730926390.30L15733024566.31L16370771165.27L17688675655.13L17690713594.11L18926753607.27L18928663569.28L22937035026.13L24533011678.12L25934068372.27L29047360941.9 L3348915901.12 L41370042806.20L43153469325.27L48347773509.5 L48633981860.27L51324363965.28L56995914634.13L58319307633.9 L68542176933.2700000<00M00f01H01b01k02402I02`03803L03g03o04G04T04l05<05Q05e06>S1h1c2c'3MU0S1h1c2c'3MU04MU0'S1h1c2Hc4ROOM2sh2F43MU01XS1h1c2c'1j4MFAB6MULIM'2J12LT5MFAB'S1h1c1j3MU04MFAB2J16MULIM'S1h1c3MU0S1h1c3MU0S1h1c4ROOM2c'1j2Hj2GTS1h1c2Hc4ROOM1j2F22Hj1XS1h1c2Hc1b2F13MU04MFAB1XS1h1c1t2Hc2F14MFAB1XS1h1c3PAB2Hc1j2F14MFAB1X2J1S1h1c2HcS1h1c2Hc4ROOM1b2F43MU01XS1h1c2Hc4ROOMS1h1c2Hc1b2F13MU04MFAB1XS1h1c2c'3MU03Hc'S1h1c4ROOM2c'1j2Hj2GTS1h1c1t2Hc4ROOM2F21XS1h1c2Hc2sh2F13MU04MFAB1X". (* [comment removed for export] *)
  #[using="Type"] Lemma funit_new_apart : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pc,$0.Pt,$10.P,(31.VhAR,VAL,R4.R3.)P,(3:.VhAR,(25.R5.))P,(43.R6.)P,(14.(1>.=(29.R7.))(1>.(29.R7.)$44.))P,(14.(1>.+1.R6.)(1>.R6.+1?.))P,(1>.(6.(26.(22.R9.R7.))$47.)$48.)P,(3.$10.R7.(11.R:.))(12.(1>.(6.(6.(49.(25.R;.)R9.)(26.(22.R;.R9.)))$23.)(38.R8.))(1>.(35.R8.)(6.(49.(25.R;.)R9.)(26.(22.R;.R9.)))))")
(* [comment removed for export] *).
  Proof.
    intros h mo c t K WL BR PAB Hc ROOM Ht.
    pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c' & j & Hc' & Hj & ->)|[(c' & j & Hc' & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]].
    - destruct (lit_apart_hull h mo (node_tr b) _ K Ht eq_refl ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - destruct (lit_apart_hull h mo (store_tr b) _ K Ht eq_refl ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - destruct (lit_apart_hull h mo (sec_tr sh) _ K Ht eq_refl ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - dpose (BR c' ltac:(unfold kNumClasses; lia)) as (MU0' & MUAL' & MULIM' & _). geo.
      pose proof (Z.div_mod (r_mapped_user (h_reg h c')) (2^18) ltac:(lia)) as DM. rewrite MUAL' in DM.
      assert (J1 : j * 2^18 + 2^18 <= r_mapped_user (h_reg h c')) by (clear - Hj DM; nia).
      destruct (Z.lt_total c' c) as [LT|[->|GT]]; [right; clear - J1 LT MULIM' MFAB ROOM Hj MU0 MFAB Hc Hc'; lia| right; clear - J1 MULIM' MFAB ROOM Hj MU0 MFAB Hc Hc'; lia| left; clear - J1 GT MULIM' MFAB ROOM Hj MU0 MFAB Hc Hc'; lia].
    - dpose (BR c' ltac:(unfold kNumClasses; lia)) as (_ & _ & _ & MFAL' & MFAB'). geo.
      pose proof (Z.div_mod (r_mapped_fa (h_reg h c')) (2^18) ltac:(lia)) as DM. rewrite MFAL' in DM.
      assert (J1 : j * 2^18 + 2^18 <= r_mapped_fa (h_reg h c')) by (clear - Hj DM; nia).
      destruct (Z.lt_total c' c) as [LT|[->|GT]]; [right; clear - J1 LT MFAB' MFAB ROOM Hj MU0 MFAB Hc Hc'; lia| right; clear - J1 MFAB' MFAB ROOM Hj MU0 MFAB Hc Hc'; lia| left; clear - J1 GT MFAB' MFAB ROOM Hj MU0 MFAB Hc Hc'; lia].
    - left. geo. clear - Hc ROOM MFAB; lia.
    - pose proof (hulls_apart AL h mo K) as HA. geo.
      pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (h_pa_committed h) 131072 ltac:(lia)) as MB.
      assert (J1 : j * 131072 + 131072 <= h_pa_committed h) by (clear - Hj DM MB; nia).
      destruct HA as [X|X]; [left| right]; clear - X J1 Hj PAB F1 F2 Hc ROOM MFAB; lia.
    - destruct (lit_apart_hull h mo t _ K Ht (fixed_emb_lit _ _ HF) ltac:(left; reflexivity)) as [X|X]; geo; [right| left]; clear - X F1 F2 Hc ROOM MFAB; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L15730926390.25L15733024566.26L17622751511.12L18926748590.21L21274425667.22L21844597148.22L29335970630.5 L30839067309.7 L30840874758.3 L42888309838.22L51096982803.22L51324363965.23L56647535754.22L5687275638.12 L591601440.5   L6398670236.7  L68325248868.1200000:00I00n01501@01Q01\01h02002<02G02U02e03>03J03W040S1h3PA02c'S1h3PA02c'4MU0'S1h3PA02c'1j2F21X3Hc'6MULIM'2J15MFAB'S1h3PA0S1h3PA01b1XS1h3PA04ROOM2sh1XS1h1t3PA01XS1h3PA02F41XS1h1j2J1S1h3PA02sh1XS1h3PA01b1XS1h3PA02c'3Hc'S1h3PA04ROOM1b1XS1h4ROOM2c'1j2F11X3Hc'2HjS1h1t4ROOM1XS1h4ROOM2F11XS1h4ROOM2c'1j2F11X3Hc'2Hj". (* [comment removed for export] *)
  #[using="Type"] Lemma pa_new_apart : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pt,$10.P,(31.VhAR,VAL,R3.R2.)P,(3:.VhAR,(25.R4.))P,(43.R5.)P,(1>.=(29.R6.))P,(1>.(6.(29.R7.)$2:.)$44.)P,(5.$0.(3=.(29.R8.)$2:.)=)P,(3.$10.R7.(11.R9.))(12.(1>.(6.(6.(42.(25.R:.))(29.R:.))$2:.)(38.R8.))(1>.(35.R8.)(6.(42.(25.R:.))(29.R:.))))")
(* [comment removed for export] *).
  Proof.
    intros h mo t K WL BR PA0 ROOM PAL Ht.
    pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). pose proof (hulls_apart AL h mo K) as HA.
    destruct (tr_of_inv h t Ht) as [(b & Hb & ->)|[(b & Hb & ->)|[(sh & Hsh & ->)|[(c' & j & Hc' & Hj & ->)|[(c' & j & Hc' & Hj & ->)|[->|[(j & Hj & ->)|HF]]]]]]].
    - destruct (lit_apart_hull h mo (node_tr b) _ K Ht eq_refl ltac:(right; left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - destruct (lit_apart_hull h mo (store_tr b) _ K Ht eq_refl ltac:(right; left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - destruct (lit_apart_hull h mo (sec_tr sh) _ K Ht eq_refl ltac:(right; left; reflexivity)) as [X|X]; geo; [right| left]; lia.
    - dpose (BR c' ltac:(unfold kNumClasses; lia)) as (MU0' & MUAL' & MULIM' & _). geo.
      pose proof (Z.div_mod (r_mapped_user (h_reg h c')) (2^18) ltac:(lia)) as DM. rewrite MUAL' in DM.
      assert (J1 : j * 2^18 + 2^18 <= r_mapped_user (h_reg h c')) by (clear - Hj DM; nia).
      destruct HA as [X|X]; [right| left]; clear - X J1 Hj Hc' MULIM' F1 F2 PA0 ROOM; lia.
    - dpose (BR c' ltac:(unfold kNumClasses; lia)) as (_ & _ & _ & MFAL' & MFAB'). geo.
      pose proof (Z.div_mod (r_mapped_fa (h_reg h c')) (2^18) ltac:(lia)) as DM. rewrite MFAL' in DM.
      assert (J1 : j * 2^18 + 2^18 <= r_mapped_fa (h_reg h c')) by (clear - Hj DM; nia).
      destruct HA as [X|X]; [right| left]; clear - X J1 Hj Hc' MFAB' F1 F2 PA0 ROOM; lia.
    - geo. destruct HA as [X|X]; [right| left]; clear - X F1 F2 F4 PA0 ROOM; lia.
    - geo.
      pose proof (Z.div_mod (h_pa_committed h) 131072 ltac:(lia)) as DM. rewrite PAL in DM.
      assert (J1 : j * 131072 + 131072 <= h_pa_committed h) by (clear - Hj DM; nia). right. clear - J1; lia.
    - destruct (lit_apart_hull h mo t _ K Ht (fixed_emb_lit _ _ HF) ltac:(right; left; reflexivity)) as [X|X]; geo; [right| left]; clear - X PA0 ROOM; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308513745.1300000AS2t12t21E1X2L12L2". (* [comment removed for export] *)
  #[using="Type"] Lemma tr_lo_inj : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pt1,$10.Pt2,$10.P,(31.VhAR,VAL,R4.R3.)P,(3.$10.R3.(11.R5.))P,(3.$10.R3.(11.R6.))P,(5.$0.(38.R5.)(38.R4.))(5.$10.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros h mo t1 t2 K H1 H2 E. destruct (tr_apart AL h mo t1 t2 K H1 H2) as [X|X]; [exact X|].
    dpose (tr_wf AL h mo t1 K H1) as (_ & L1 & _). dpose (tr_wf AL h mo t2 K H2) as (_ & L2 & _). unfold t_hi in X. exfalso. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End GEO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition R_ugrow (h : ahst) (c : Z) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "(14.(5.$39.(25.O1.)(25.O3.))(14.Pc',$0.P,(4.(5.$0.R1.O2.))(5.$0.(21.(22.O1.R2.))(21.(22.O3.R2.)))(14.(5.$0.(21.(22.O1.O2.))(6.(21.(22.O3.O2.))$23.))(14.Pc',$0.(5.$0.(26.(22.O1.R1.))(26.(22.O3.R1.)))(14.(5.(1.$0.)(15.(16.O1.))(15.(16.O3.)))(14.(5.(1.$0.)(18.(16.O1.))(18.(16.O3.)))(14.(5.(1.$1:.)(1;.(1<.O1.))(1;.(1<.O3.)))(14.(5.(1.(30.$0.$0.))(4:.(4;.O1.))(4:.(4;.O3.)))(14.(5.$0.(29.O1.)(29.O3.))(5.$0.(4<.(4;.O1.))(4<.(4;.O3.))))))))))))")
(* [comment removed for export] *).
Definition R_fgrow (h : ahst) (c : Z) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "(14.(5.$39.(25.O1.)(25.O3.))(14.Pc',$0.(5.$0.(21.(22.O1.R1.))(21.(22.O3.R1.)))(14.Pc',$0.P,(4.(5.$0.R1.O2.))(5.$0.(26.(22.O1.R2.))(26.(22.O3.R2.)))(14.(5.$0.(26.(22.O1.O2.))(6.(26.(22.O3.O2.))$47.))(14.(5.(1.$0.)(15.(16.O1.))(15.(16.O3.)))(14.(5.(1.$0.)(18.(16.O1.))(18.(16.O3.)))(14.(5.(1.$1:.)(1;.(1<.O1.))(1;.(1<.O3.)))(14.(5.(1.(30.$0.$0.))(4:.(4;.O1.))(4:.(4;.O3.)))(14.(5.$0.(29.O1.)(29.O3.))(5.$0.(4<.(4;.O1.))(4<.(4;.O3.))))))))))))")
(* [comment removed for export] *).
Definition R_pa (h : ahst) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "(14.(5.$39.(25.O1.)(25.O2.))(14.Pc',$0.(5.$0.(21.(22.O1.R1.))(21.(22.O2.R1.)))(14.Pc',$0.(5.$0.(26.(22.O1.R1.))(26.(22.O2.R1.)))(14.(5.(1.$0.)(15.(16.O1.))(15.(16.O2.)))(14.(5.(1.$0.)(18.(16.O1.))(18.(16.O2.)))(14.(5.(1.$1:.)(1;.(1<.O1.))(1;.(1<.O2.)))(14.(5.(1.(30.$0.$0.))(4:.(4;.O1.))(4:.(4;.O2.)))(14.(5.$0.(29.O1.)(6.(29.O2.)$2:.))(5.$0.(4<.(4;.O1.))(4<.(4;.O2.)))))))))))")
(* [comment removed for export] *).
Definition R_secadd (h : ahst) (sh : shdr) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "(14.(5.$39.(25.O1.)(25.O3.))(14.Pc',$0.(5.$0.(21.(22.O1.R1.))(21.(22.O3.R1.)))(14.Pc',$0.(5.$0.(26.(22.O1.R1.))(26.(22.O3.R1.)))(14.(5.(1.$0.)(15.(16.O1.))(15.(16.O3.)))(14.(5.(1.$0.)(18.(16.O1.))(18.(16.O3.)))(14.(4=.$1:.(1;.(1<.O1.))(4>.$1:.O2.(1;.(1<.O3.))))(14.(5.(1.(30.$0.$0.))(4:.(4;.O1.))(4:.(4;.O3.)))(14.(5.$0.(29.O1.)(29.O3.))(5.$0.(4<.(4;.O1.))(4<.(4;.O3.)))))))))))")
(* [comment removed for export] *).
Definition R_secrm (h : ahst) (sh : shdr) (h' : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "(14.(5.$39.(25.O1.)(25.O3.))(14.Pc',$0.(5.$0.(21.(22.O1.R1.))(21.(22.O3.R1.)))(14.Pc',$0.(5.$0.(26.(22.O1.R1.))(26.(22.O3.R1.)))(14.(5.(1.$0.)(15.(16.O1.))(15.(16.O3.)))(14.(5.(1.$0.)(18.(16.O1.))(18.(16.O3.)))(14.(4=.$1:.(4>.$1:.O2.(1;.(1<.O1.)))(1;.(1<.O3.)))(14.(5.(1.(30.$0.$0.))(4:.(4;.O1.))(4>.(30.$0.$0.)(4?.$0.$0.(50.O2.)(51.O2.))(4:.(4;.O3.))))(14.(5.$0.(29.O1.)(29.O3.))(5.$0.(4<.(4;.O1.))(4<.(4;.O3.)))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
End ARUN_1.
Ltac perm_push := first [ apply Permutation_middle | apply perm_skip; apply Permutation_refl
                        | eapply Permutation_trans; [apply Permutation_middle|]; apply Permutation_app_head; perm_push
                        | eapply Permutation_trans; [apply perm_swap|]; apply perm_skip; perm_push ].

Section ARUN_2. Context {hAR : arun}.
Section PERM.
  (* [comment removed for export] *)
  #[using="Type"] Lemma perm_mid4 : forall {X} (x : X) (A B C D E : list X) D', Permutation D' (x :: D) ->
    Permutation (x :: A ++ B ++ C ++ D ++ E) (A ++ B ++ C ++ D' ++ E).
  Proof.
    intros X x A B C D E D' P.
    transitivity ((A ++ B ++ C) ++ x :: (D ++ E)).
    { replace (x :: A ++ B ++ C ++ D ++ E) with (x :: (A ++ B ++ C) ++ (D ++ E)) by (rewrite <- !app_assoc; reflexivity). apply Permutation_middle. }
    rewrite <- !app_assoc. do 3 apply Permutation_app_head. change (x :: D ++ E) with ((x :: D) ++ E). apply Permutation_app_tail. apply Permutation_sym. exact P.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11721887029.21L15724765464.20L15726601483.19L2884439661.19 L32693320459.21L45769042961.19L512922078.19  L63537583328.2100000<00H00T00`00l01801D01RS1h1c2mu3MU0S1h1c2mu3MU0S1h1c2mu3MU0S1h1c2mu3MU0S1h1c2mu3MU0S1h1c2mu3MU0S1h1c2mu3MU0S1h1c2mu3MU01H". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_of_ugrow : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pc,$0.Ph',$?.P,(14.(1>.+1.R2.)(1>.R2.+1?.))P,(1>.=(21.(22.R4.R3.)))P,(5.$0.(3=.(21.(22.R5.R4.))$23.)=)P,(52.R6.R5.R4.)(9.(53.(54.R7.)(6.(46.(25.R7.)R6.)(21.(22.R7.R6.)))$23.$=.)(54.R5.))")
(* [comment removed for export] *).
  Proof.
    (intros h c h' Hc MU0 MUAL dd_H; ddestruct dd_H as (EL & EU & EUc & EF & ENB & EBL & ESC & EGH & EPA & EEM)). pose proof (emb_tr_ext h h' EEM) as EMT.
    set (mu := r_mapped_user (h_reg h c)) in *.
    assert (UE : Permutation (units_of h') (uunit_tr (h_L h) c (mu / kUserMapSize) :: units_of h)).
    { unfold units_of. rewrite EL. apply (flat_map_perm_insert _ _ _ c); [apply classes_NoDup| apply classes_in; exact Hc| |].
      - intros a _ NE. rewrite (EU a NE), EF. reflexivity.
      - rewrite EUc, EF. fold mu. unfold kUserMapSize in *. replace (mu + 2^18) with (mu + 1 * 2^18) by lia. rewrite Z.div_add by lia.
        rewrite zseq_succ by (apply Z.div_pos; lia). rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
    assert (TE : uunit_tr (h_L h) c (mu / kUserMapSize) = TR (region_beg (h_L h) c + mu) kUserMapSize KEager false true).
    { unfold uunit_tr. f_equal. pose proof (Z.div_mod mu kUserMapSize ltac:(unfold kUserMapSize; lia)). rewrite MUAL in H. lia. }
    rewrite TE in UE.
    unfold vperm, vst_of, v_add_sub. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb v_cover v_cb20 v_cb23 v_unit].
    rewrite EL, EGH. split; [| split; [| repeat split; try reflexivity]].
    - unfold tr_of. rewrite ?EMT. rewrite ENB, EBL, ESC, EPA, EL. apply perm_mid4. exact UE.
    - unfold cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. apply Permutation_refl.
    - unfold eb_of. rewrite ?EMT. rewrite ENB, ESC, EGH, EPA. fold classes.
      rewrite (zsum_update (fun c0 => r_mapped_user (h_reg h c0) + r_mapped_fa (h_reg h c0)) (fun c0 => r_mapped_user (h_reg h' c0) + r_mapped_fa (h_reg h' c0)) c kUserMapSize classes classes_NoDup (classes_in c Hc)).
      + lia.
      + intros a _ NE. rewrite (EU a NE), EF. reflexivity.
      + rewrite EUc, EF. fold mu. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. reflexivity.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L15224824573.19L15724765464.20L15726601483.19L2884439661.19 L32693320459.21L39605341150.19L51714356358.21L52173518576.2100000=00J00W00d01101>01K01ZS1h1c3mfa3MF0S1h1c3mfa3MF0S1h1c3mfa3MF0S1h1c3mfa3MF0S1h1c3mfa3MF0S1h1c3mfa3MF0S1h1c3mfa3MF0S1h1c3mfa3MF01H". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_of_fgrow : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pc,$0.Ph',$?.P,(14.(1>.+1.R2.)(1>.R2.+1?.))P,(1>.=(26.(22.R4.R3.)))P,(5.$0.(3=.(26.(22.R5.R4.))$47.)=)P,(55.R6.R5.R4.)(9.(53.(54.R7.)(6.(49.(25.R7.)R6.)(26.(22.R7.R6.)))$23.$=.)(54.R5.))")
(* [comment removed for export] *).
  Proof.
    (intros h c h' Hc MF0 MFAL dd_H; ddestruct dd_H as (EL & EU & EF & EFc & ENB & EBL & ESC & EGH & EPA & EEM)). pose proof (emb_tr_ext h h' EEM) as EMT.
    set (mfa := r_mapped_fa (h_reg h c)) in *.
    assert (UE : Permutation (units_of h') (funit_tr (h_L h) c (mfa / kUserMapSize) :: units_of h)).
    { unfold units_of. rewrite EL. apply (flat_map_perm_insert _ _ _ c); [apply classes_NoDup| apply classes_in; exact Hc| |].
      - intros a _ NE. rewrite (EF a NE), EU. reflexivity.
      - rewrite EFc, EU. fold mfa. unfold kUserMapSize, kFreeArrayMapSize in *. replace (mfa + 2^18) with (mfa + 1 * 2^18) by lia. rewrite Z.div_add by lia.
        rewrite zseq_succ by (apply Z.div_pos; lia). rewrite map_app. cbn [map]. apply Permutation_sym. rewrite app_assoc. apply Permutation_cons_append. }
    assert (TE : funit_tr (h_L h) c (mfa / kUserMapSize) = TR (fa_beg (h_L h) c + mfa) kUserMapSize KEager false true).
    { unfold funit_tr. f_equal. pose proof (Z.div_mod mfa kUserMapSize ltac:(unfold kUserMapSize; lia)). unfold kUserMapSize, kFreeArrayMapSize in *. rewrite MFAL in H. lia. }
    rewrite TE in UE.
    unfold vperm, vst_of, v_add_sub. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb v_cover v_cb20 v_cb23 v_unit].
    rewrite EL, EGH. split; [| split; [| repeat split; try reflexivity]].
    - unfold tr_of. rewrite ?EMT. rewrite ENB, EBL, ESC, EPA, EL. apply perm_mid4. exact UE.
    - unfold cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. apply Permutation_refl.
    - unfold eb_of. rewrite ?EMT. rewrite ENB, ESC, EGH, EPA. fold classes.
      rewrite (zsum_update (fun c0 => r_mapped_user (h_reg h c0) + r_mapped_fa (h_reg h c0)) (fun c0 => r_mapped_user (h_reg h' c0) + r_mapped_fa (h_reg h' c0)) c kUserMapSize classes classes_NoDup (classes_in c Hc)).
      + lia.
      + intros a _ NE. rewrite (EF a NE), EU. reflexivity.
      + rewrite EFc, EU. fold mfa. unfold kUserMapSize, kFreeArrayMapSize. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. reflexivity.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18926277955.16L18926294339.17L18928400409.17L27611873399.17L29409748404.17L32693027262.18L43579301705.1700000700>00E00N00U00\00cS1h3PA0S1h3PA0S1h3PA0S1h3PA01HS1h3PA0S1h3PA0S1h3PA0". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_of_pa : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Ph',$?.P,(1>.=(29.R2.))P,(5.$0.(3=.(29.R3.)$2:.)=)P,(56.R4.R3.)(9.(53.(54.R5.)(6.(42.(25.R5.))(29.R5.))$2:.$=.)(54.R4.))")
(* [comment removed for export] *).
  Proof.
    (intros h h' PA0 PAL dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & ESC & EGH & EPA & EEM)). pose proof (emb_tr_ext h h' EEM) as EMT.
    assert (UE : units_of h' = units_of h) by (apply units_of_ext; assumption).
    assert (TE : pa_tr (h_L h) (h_pa_committed h / kPaSlice) = TR (l_pa (h_L h) + h_pa_committed h) kPaSlice KEager false true).
    { unfold pa_tr. f_equal. pose proof (Z.div_mod (h_pa_committed h) kPaSlice ltac:(unfold kPaSlice; lia)). rewrite PAL in H. lia. }
    unfold vperm, vst_of, v_add_sub. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb v_cover v_cb20 v_cb23 v_unit].
    rewrite EL, EGH. split; [| split; [| repeat split; try reflexivity]].
    - unfold tr_of. rewrite ?EMT. rewrite ENB, EBL, ESC, EPA, EL, UE. unfold kPaSlice in *. replace (h_pa_committed h + 131072) with (h_pa_committed h + 1 * 131072) by lia. rewrite Z.div_add by lia.
      rewrite zseq_succ by (apply Z.div_pos; lia). rewrite map_app. cbn [map]. unfold kPaSlice in TE. rewrite TE.
      rewrite <- !app_assoc. cbn [app]. perm_push.
    - unfold cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. apply Permutation_refl.
    - unfold eb_of. rewrite ?EMT. rewrite ENB, ESC, EGH, EPA. rewrite (eb_of_ext h h') || idtac.
      assert (E2 : forall l, zsum (fun c => r_mapped_user (h_reg h' c) + r_mapped_fa (h_reg h' c)) l = zsum (fun c => r_mapped_user (h_reg h c) + r_mapped_fa (h_reg h c)) l).
      { induction l as [|a l IH]; [reflexivity|]. cbn [zsum]. rewrite EU, EF, IH. reflexivity. }
      rewrite E2. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. reflexivity.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L3574664093.17 L53236977953.1700000600<S1h2shS1h2sh". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_of_secadd : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Psh,$1:.Ph',$?.P,(57.R3.R2.R1.)(9.(;.(54.R4.)(50.R3.)(51.R3.)$=.)(54.R2.))")
(* [comment removed for export] *).
  Proof.
    (intros h sh h' dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & PSC & EGH & EPA & EEM)). pose proof (emb_tr_ext h h' EEM) as EMT.
    assert (UE : units_of h' = units_of h) by (apply units_of_ext; assumption).
    assert (E2 : forall l, zsum (fun c => r_mapped_user (h_reg h' c) + r_mapped_fa (h_reg h' c)) l = zsum (fun c => r_mapped_user (h_reg h c) + r_mapped_fa (h_reg h c)) l).
    { induction l as [|a l IH]; [reflexivity|]. cbn [zsum]. rewrite EU, EF, IH. reflexivity. }
    assert (PC : Permutation (map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h'))) ((s_map_beg sh, s_map_size sh) :: map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h)))).
    { change ((s_map_beg sh, s_map_size sh) :: map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h))) with (map (fun s => (s_map_beg s, s_map_size s)) (sh :: s_chunks (h_sec h))). apply Permutation_map. exact PSC. }
    unfold vperm, vst_of, v_add_eager. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb v_cover v_cb20 v_cb23 v_unit].
    rewrite EL, EGH. split; [| split; [| repeat split; try reflexivity]].
    - unfold tr_of. rewrite ?EMT. rewrite ENB, EBL, EPA, EL, UE.
      transitivity (sec_tr sh :: map node_tr (d_nb (h_dep h)) ++ map store_tr (d_bl (h_dep h)) ++ map sec_tr (s_chunks (h_sec h)) ++ units_of h ++ [ri_tr (h_L h)] ++ map (pa_tr (h_L h)) (zseq (h_pa_committed h / kPaSlice)) ++ fixed_of (h_L h) ++ emb_tr h);
        [apply perm_skip; apply Permutation_refl|].
      transitivity (map node_tr (d_nb (h_dep h)) ++ map store_tr (d_bl (h_dep h)) ++ sec_tr sh :: map sec_tr (s_chunks (h_sec h)) ++ units_of h ++ [ri_tr (h_L h)] ++ map (pa_tr (h_L h)) (zseq (h_pa_committed h / kPaSlice)) ++ fixed_of (h_L h) ++ emb_tr h);
        [perm_push|].
      do 2 apply Permutation_app_head. change (sec_tr sh :: map sec_tr (s_chunks (h_sec h)) ++ ?r) with (map sec_tr (sh :: s_chunks (h_sec h)) ++ r).
      apply Permutation_app_tail. apply Permutation_map. apply Permutation_sym. exact PSC.
    - unfold cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, EGH.
      transitivity (hulls_of (h_L h) ++ map (fun t => (t_lo t, t_len t)) (fixed_of (h_L h)) ++ map (fun b => (b, 2^20)) (d_nb (h_dep h)) ++ map (fun b => (b, 2^23)) (d_bl (h_dep h))
                      ++ (s_map_beg sh, s_map_size sh) :: map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h)) ++ a_sech (h_acct h) ++ map (fun t => (t_lo t, t_len t)) (emb_tr h));
        [perm_push|].
      do 4 apply Permutation_app_head. change ((s_map_beg sh, s_map_size sh) :: ?m ++ ?r) with (((s_map_beg sh, s_map_size sh) :: m) ++ r).
      apply Permutation_app_tail. apply Permutation_sym. exact PC.
    - unfold eb_of. rewrite ?EMT. rewrite ENB, EGH, EPA, E2. rewrite (zsum_perm _ _ _ PSC). cbn [zsum]. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, EGH. rewrite !zsum_app. rewrite (zsum_perm _ _ _ PC). cbn [zsum snd]. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, EGH. rewrite !zsum_app. rewrite (zsum_perm _ _ _ PC). cbn [zsum snd]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L24534246005.22L66322999343.2200000900BS1h2sh2h'S1h2sh2h'". (* [comment removed for export] *)
  #[using="Type"] Lemma vst_of_secrm : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Psh,$1:.Ph',$?.P,(58.R3.R2.R1.)P,(2.$10.(11.R4.))P,Pt,$10.P,(3.$10.R1.(11.R6.))P,(5.$0.(38.R2.)(50.R6.))(5.$10.R3.(1=.R7.))(9.(59.(54.R6.)(50.R5.)(4>.(30.$0.$0.)(4?.$0.$0.(50.R5.)(51.R5.))(5:.(30.$0.$0.))))(54.R4.))")
(* [comment removed for export] *).
  Proof.
    (intros h sh h' dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & PSC & EGH & EPA & EEM); intros ND UNIQ). pose proof (emb_tr_ext h h' EEM) as EMT.
    assert (UE : units_of h' = units_of h) by (apply units_of_ext; assumption).
    assert (E2 : forall l, zsum (fun c => r_mapped_user (h_reg h' c) + r_mapped_fa (h_reg h' c)) l = zsum (fun c => r_mapped_user (h_reg h c) + r_mapped_fa (h_reg h c)) l).
    { induction l as [|a l IH]; [reflexivity|]. cbn [zsum]. rewrite EU, EF, IH. reflexivity. }
    assert (PC : Permutation ((s_map_beg sh, s_map_size sh) :: map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h'))) (map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h)))).
    { change ((s_map_beg sh, s_map_size sh) :: map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h'))) with (map (fun s => (s_map_beg s, s_map_size s)) (sh :: s_chunks (h_sec h'))). apply Permutation_map. exact PSC. }
    (* [comment removed for export] *)
    assert (PT : Permutation (tr_of h) (sec_tr sh :: tr_of h')).
    { unfold tr_of. rewrite ?EMT. rewrite ENB, EBL, EPA, EL, UE. apply Permutation_sym.
      transitivity (map node_tr (d_nb (h_dep h)) ++ map store_tr (d_bl (h_dep h)) ++ sec_tr sh :: map sec_tr (s_chunks (h_sec h')) ++ units_of h ++ [ri_tr (h_L h)] ++ map (pa_tr (h_L h)) (zseq (h_pa_committed h / kPaSlice)) ++ fixed_of (h_L h) ++ emb_tr h);
        [perm_push|].
      do 2 apply Permutation_app_head. change (sec_tr sh :: map sec_tr (s_chunks (h_sec h')) ++ ?r) with (map sec_tr (sh :: s_chunks (h_sec h')) ++ r).
      apply Permutation_app_tail. apply Permutation_map. exact PSC. }
    assert (NI : ~ In (sec_tr sh) (tr_of h')).
    { intros Hin. pose proof (Permutation_NoDup PT ND) as ND'. inversion ND' as [|? ? X _]; subst. exact (X Hin). }
    assert (FE : List.filter (fun t => negb (t_lo t =? s_map_beg sh)) (tr_of h') = tr_of h').
    { apply forallb_filter_id. apply forallb_forall. intros t Ht. destruct (Z.eqb_spec (t_lo t) (s_map_beg sh)) as [E|NE]; [| reflexivity].
      exfalso. apply NI. rewrite <- (UNIQ t ltac:(eapply Permutation_in; [apply Permutation_sym; exact PT| right; exact Ht]) E). exact Ht. }
    unfold vperm, vst_of, v_remove. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb v_cover v_cb20 v_cb23 v_unit].
    rewrite EL, EGH. split; [| split; [| repeat split; try reflexivity]].
    - transitivity (List.filter (fun t => negb (t_lo t =? s_map_beg sh)) (sec_tr sh :: tr_of h')); [apply Permutation_filter; exact PT|].
      cbn [List.filter]. unfold sec_tr at 1. cbn [t_lo]. rewrite Z.eqb_refl. cbn [negb]. rewrite FE. apply Permutation_refl.
    - unfold cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, EGH. rewrite !app_assoc. apply Permutation_app_head with (l := ((((hulls_of (h_L h) ++ _) ++ _) ++ _))) || idtac.
      rewrite <- !app_assoc. do 4 apply Permutation_app_head.
      transitivity (((s_map_beg sh, s_map_size sh) :: map (fun s => (s_map_beg s, s_map_size s)) (s_chunks (h_sec h'))) ++ a_sech (h_acct h) ++ map (fun t => (t_lo t, t_len t)) (emb_tr h)); [apply Permutation_app_tail; apply Permutation_sym; exact PC|].
      cbn [app]. apply Permutation_middle.
    - unfold eb_of. rewrite ?EMT. rewrite ENB, EGH, EPA, E2. rewrite <- (zsum_perm _ _ _ PSC). cbn [zsum snd]. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, EGH. rewrite !zsum_app. rewrite <- (zsum_perm _ _ _ PC). cbn [zsum snd]. lia.
    - unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, EGH. rewrite !zsum_app. rewrite <- (zsum_perm _ _ _ PC). cbn [zsum snd]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L16714085305.1600000;S1S1h2sn2sb". (* [comment removed for export] *)
  #[using="Type"] Lemma cb_of_grow : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "PS,$0.Ph,$?.Psn,(1.$0.)Psb,(1.$0.)Ph',$?.P,(5;.R4.R3.R2.R1.)(5.$0.(5<.R6.R2.)(6.(6.(5<.R6.R5.)(7.$0.L,$0.(6.(20.(<.+2.+14.)R7.)+2.)R4.))(7.$0.L,$0.(6.(20.(<.+2.+17.)R7.)+2.)R3.)))")
(* [comment removed for export] *).
  Proof.
    (intros S h sn sb h' dd_H; ddestruct dd_H as (EL & EU & EF & ENB & EBL & ESC & EGH & EPA & EEM)). pose proof (emb_tr_ext h h' EEM) as EMT. unfold cb_of, cover_of. rewrite ?EMT. rewrite EL, ENB, EBL, ESC, EGH.
    rewrite !map_app, !zsum_app, !zsum_map. cbn [snd]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End PERM.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TRANS.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.

    #[using="Type"] Lemma HK_perm : forall h v mo, vperm v (vst_of h) -> HKv AL v mo -> vranges_ok AL v -> HK AL h mo.
  Proof. intros h v mo P K R. split; [exact (HKv_perm AL _ _ mo P K)| exact (vranges_ok_perm AL _ _ P R)]. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L18928457539.11L55122173139.12L63977956896.1100000700D00OS1h3NR0S1h3NRM3NR01HS1h3NR03NR8". (* [comment removed for export] *)
  #[using="Type"] Lemma bwf_pa : forall h, bwf h -> 0 <= h_pa_committed h <= kPaHullLen /\ h_pa_committed h mod kPaSlice = 0.
  Proof.
    (intros h dd_H; ddestruct dd_H as (_ & _ & WS & _)). ddestruct WS as (_ & NRM & NR0 & NR8 & PAE & _). unfold kPaHullLen, kPaSlice, kPtrArrayChunks in *. rewrite PAE.
    split; [lia|]. rewrite Zmult_mod_distr_l || idtac. replace (8 * s_nres (h_sec h)) with (s_nres (h_sec h) / 16384 * 131072); [apply Z_mod_mult|].
    pose proof (Z.div_mod (s_nres (h_sec h)) 16384 ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma bwf_L : forall h, bwf h -> wf_L (h_L h). Proof. (intros h dd_H; ddestruct dd_H as ((WL & _) & _)). exact WL. Qed.
  #[using="Type"] Lemma bwf_breg : forall h, bwf h -> breg h. Proof. (intros h dd_H; ddestruct dd_H as (_ & B & _)). exact B. Qed.

  #[using="Type"] Lemma vranges_ok_rm : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Pv,$8.Plo,$0.Pgh,(1.(30.$0.$0.))P,(5=.VAL,R3.)P,(5>.(30.$0.$0.)Lr,(30.$0.$0.)(14.(1>.=(36.$0.$0.R1.))(1>.=(37.$0.$0.R1.)))R2.)(5=.VAL,(59.R5.R4.R3.))")
(* [comment removed for export] *).
  Proof.
    (intros v lo gh dd_H; ddestruct dd_H as (A & B & C); intros G). split; [exact A|]. unfold csranges, lazyranges in *. unfold v_remove. cbn [v_stk v_img v_tr v_ghost]. split.
    - inversion B as [|? ? B1 B2]; subst. inversion B2 as [|? ? B3 B4]; subst. apply Forall_app in B4. destruct B4 as [B5 B6].
      constructor; [exact B1|]. constructor; [exact B3|]. apply Forall_app. split; [| apply Forall_app; split; [exact G| exact B6]].
      apply Forall_forall. intros r Hr. apply in_map_iff in Hr. ddestruct Hr as (t & <- & Ht). apply filter_In in Ht. destruct Ht as [Ht TC]. apply filter_In in Ht. destruct Ht as [Ht _].
      apply (proj1 (Forall_forall _ _) B5). apply in_map_iff. exists t. split; [reflexivity|]. apply filter_In. auto.
    - apply Forall_forall. intros r Hr. apply in_map_iff in Hr. ddestruct Hr as (t & <- & Ht). apply filter_In in Ht. destruct Ht as [Ht TC]. apply filter_In in Ht. destruct Ht as [Ht _].
      apply (proj1 (Forall_forall _ _) C). apply in_map_iff. exists t. split; [reflexivity|]. apply filter_In. auto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L14305291612.1800000<S2lo1n2H02H1". (* [comment removed for export] *)
  #[using="Type"] Lemma vranges_ok_sub : forall v lo n, vranges_ok AL v -> 0 <= lo -> 0 <= n -> vranges_ok AL (v_add_sub v lo n true).
  Proof.
    (intros v lo n dd_H; ddestruct dd_H as (A & B & C); intros H0 H1). split; [exact A|]. unfold csranges, lazyranges in *. unfold v_add_sub. cbn [v_stk v_img v_tr v_ghost List.filter is_lazy_cs t_kind t_cs map app]. split.
    - inversion B as [|? ? B1 B2]; subst. inversion B2 as [|? ? B3 B4]; subst. constructor; [exact B1|]. constructor; [exact B3|]. constructor; [cbn; lia| exact B4].
    - exact C.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L14305291612.1800000<S2lo1n2H02H1". (* [comment removed for export] *)
  #[using="Type"] Lemma vranges_ok_eager : forall v lo n cs, vranges_ok AL v -> 0 <= lo -> 0 <= n -> vranges_ok AL (v_add_eager v lo n cs).
  Proof.
    (intros v lo n cs dd_H; ddestruct dd_H as (A & B & C); intros H0 H1). split; [exact A|]. unfold csranges, lazyranges in *. unfold v_add_eager. cbn [v_stk v_img v_tr v_ghost List.filter]. split.
    - inversion B as [|? ? B1 B2]; subst. inversion B2 as [|? ? B3 B4]; subst. constructor; [exact B1|]. constructor; [exact B3|].
      destruct cs; cbn [map app]; [constructor; [cbn; lia| exact B4]| exact B4].
    - cbn [is_lazy_cs t_kind]. exact C.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L14305291612.18L2424953571.14 00000<00BS2lo1n2H02H1S1n2H1". (* [comment removed for export] *)
  #[using="Type"] Lemma vranges_ok_lazy : forall v lo n, vranges_ok AL v -> 0 <= lo -> 0 <= n -> vranges_ok AL (v_add_lazy v lo n).
  Proof.
    (intros v lo n dd_H; ddestruct dd_H as (A & B & C); intros H0 H1). split; [exact A|]. unfold csranges, lazyranges in *. unfold v_add_lazy. cbn [v_stk v_img v_tr v_ghost List.filter is_lazy_cs t_kind t_cs map app]. split.
    - inversion B as [|? ? B1 B2]; subst. inversion B2 as [|? ? B3 B4]; subst. constructor; [exact B1|]. constructor; [exact B3|]. constructor; [cbn; lia| exact B4].
    - constructor; [cbn; lia| exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L20170001314.2000005S1v1n". (* [comment removed for export] *)
  #[using="Type"] Lemma vnb_add_sub : forall v lo n, vnb (v_add_sub v lo n true) = vnb v + (n / 32768 + 3).
  Proof. intros v lo n. unfold vnb, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_sub List.filter is_lazy_cs t_kind t_cs map app zsum]. cbn [t_lo t_len]. unfold npages_shadow at 3. cbn [snd]. clear; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L1408774912.4  L15724829484.36L19664136986.3 L25160960115.35L2882047989.36 L2882371819.40 L31423185352.5 L38210979716.5 L41370042806.30L51852849206.36L52566661889.2 L55010289068.35L58254917350.6 L66010957007.2 00000;00D00N00W00c00o01>01N01Y01e01k02702I02OS1h1c2Q12Q2S1h1c3MU0S1h1c4ROOMS1h1c3MU0S1h1c2UA3MU0S1h1c2UA3MU0S1h1c2Hc2F13MU0S1h1c2Hc4ROOM2F2S1h1c2Hc2UAS1h1c2UA3MU0S1h2SLS1h1c2UA3MU0S1h1c2Hc2F12F53MU0S1h2F5". (* [comment removed for export] *)
  #[using="ASB IMH"] Theorem HK_ugrow : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pc,$0.Ph',$?.P,(31.VhAR,VAL,R4.R3.)P,(5?.VhAR,R5.)P,(1>.(60.R6.)$61.)P,(14.(1>.+1.R5.)(1>.R5.+1?.))P,(1>.(6.(21.(22.R8.R6.))$23.)$45.)P,(52.R9.R7.R6.)ZUA,$0.(6.(46.(25.R:.)R8.)(21.(22.R:.R8.)))(14.(31.VhAR,VAL,R8.(62.+32.R1.$23.R:.))(14.(5.$32.(63.(64.(65.R:.))(66.&40.R1.)(66.&40.$23.))$=.)(14.(5.$32.(67.(68.(65.R:.))(66.&40.R1.)(66.&40.$23.))$=.)(69.+32.R1.$23.R:.))))")
(* [comment removed for export] *).
  Proof.
    intros h mo c h' K B HV Hc ROOM R UA.
    pose proof K as [Kv VR]. pose proof (bwf_L h B) as WL. pose proof (bwf_breg h B) as BR. pose proof (bwf_pa h B) as [PAB PAL].
    pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    assert (SL : v_eb (vst_of h) + 4096 * vnb (vst_of h) + CU <= VLIMIT) by (apply vst_slack; [exact B| exact HV| unfold CU, npg_shadow, kUserMapSize; cbn; lia]).
    ddestruct (HKv_commit_sub AL (vst_of h) mo (l_b6 (h_L h), kPrimHullLen) UA kUserMapSize true VR Kv ASB ltac:(rewrite IMH; lia)
                ltac:(left; reflexivity)) as (K' & MC & RF & GR).
    - cbn [fst]. subst UA. unfold region_beg, kRegionSize. clear - F1 Hc MU0. lia.
    - cbn [fst snd]. subst UA. unfold region_beg, kRegionSize, kPrimHullLen, kUserMapSize, kUserLimit in *. clear - F2 Hc ROOM. lia.
    - subst UA. unfold region_beg, kRegionSize, kUserMapSize in *.
      pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)) as Q1. rewrite F3 in Q1. pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)) as Q2. rewrite MUAL in Q2.
      replace (l_sb (h_L h) + c * 2^32 + r_mapped_user (h_reg h c)) with ((16 * (l_sb (h_L h) / 2^16) + c * 2^20 + 64 * (r_mapped_user (h_reg h c) / 2^18)) * 4096) by (clear - Q1 Q2; lia).
      apply Z_mod_mult.
    - reflexivity.
    - unfold kUserMapSize; lia.
    - cbn [fst]. clear - F5; unfold kHighMemBeg in F5; lia.
    - (* [comment removed for export] *)
      cbn [vst_of v_unit]. subst UA. apply (uunit_unit (h_L h) c _ WL Hc MU0 MUAL). unfold kUserMapSize, kUserLimit, kRegionSize in *. clear - ROOM. lia.
    - intros t Ht. exact (uunit_new_apart AL h mo c t K WL BR PAB Hc ROOM Ht).
    - rewrite vnb_add_sub. unfold CU, npg_shadow, kUserMapSize in SL |- *. clear - SL. lia.
    - split; [| split; [exact MC| split; [exact RF| exact GR]]].
      apply (HK_perm h' (v_add_sub (vst_of h) UA kUserMapSize true)); [apply vst_of_ugrow; try assumption| exact K'| apply vranges_ok_sub; [exact VR| | unfold kUserMapSize; lia]].
      subst UA. unfold region_beg, kRegionSize. clear - F1 F5 Hc MU0; unfold kHighMemBeg in F5; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L15724829484.36L19300062698.6 L25160960115.35L2882047989.36 L2882371819.40 L31961702792.3 L38210979716.5 L41370042806.30L43192437904.5 L49887477806.4 L51852849206.36L52566661889.2 L55010289068.35L66010957007.2 00000900L00U00b00o01901I01U01e02002=02C02P02VS1h1c3MU0S1h1c2Hc2F12F54MFABS1h1c3MU0S1h1c3FAA3MU0S1h1c3FAA3MU0S1h1c4MFABS1h1c2Hc4ROOM2F2S1h1c2Hc3FAAS1h1c2Hc2F14MFABS1h1c2Q12Q2S1h1c3FAA3MU0S1h2SLS1h1c3FAA3MU0S1h2F5". (* [comment removed for export] *)
  #[using="ASB IMH"] Theorem HK_fgrow : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pc,$0.Ph',$?.P,(31.VhAR,VAL,R4.R3.)P,(5?.VhAR,R5.)P,(1>.(60.R6.)$61.)P,(14.(1>.+1.R5.)(1>.R5.+1?.))P,(1>.(6.(26.(22.R8.R6.))$47.)$48.)P,(55.R9.R7.R6.)ZFAA,$0.(6.(49.(25.R:.)R8.)(26.(22.R:.R8.)))(14.(31.VhAR,VAL,R8.(62.+32.R1.$47.R:.))(14.(5.$32.(63.(64.(65.R:.))(66.&40.R1.)(66.&40.$47.))$=.)(14.(5.$32.(67.(68.(65.R:.))(66.&40.R1.)(66.&40.$47.))$=.)(69.+32.R1.$47.R:.))))")
(* [comment removed for export] *).
  Proof.
    intros h mo c h' K B HV Hc ROOM R FAA.
    pose proof K as [Kv VR]. pose proof (bwf_L h B) as WL. pose proof (bwf_breg h B) as BR. pose proof (bwf_pa h B) as [PAB PAL].
    pose proof (wfL_facts _ WL) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). dpose (BR c ltac:(unfold kNumClasses; lia)) as (MU0 & MUAL & MULIM & MFAL & MFAB).
    assert (SL : v_eb (vst_of h) + 4096 * vnb (vst_of h) + CU <= VLIMIT) by (apply vst_slack; [exact B| exact HV| unfold CU, npg_shadow, kUserMapSize; cbn; lia]).
    change kFreeArrayMapSize with kUserMapSize.
    ddestruct (HKv_commit_sub AL (vst_of h) mo (l_b6 (h_L h), kPrimHullLen) FAA kUserMapSize true VR Kv ASB ltac:(rewrite IMH; lia)
                ltac:(left; reflexivity)) as (K' & MC & RF & GR).
    - cbn [fst]. subst FAA. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. clear - F1 Hc MFAB. lia.
    - cbn [fst snd]. subst FAA. unfold fa_beg, region_beg, kRegionSize, kPrimHullLen, kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *. clear - F2 Hc ROOM. lia.
    - subst FAA. unfold fa_beg, region_beg, kRegionSize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *.
      pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)) as Q1. rewrite F3 in Q1. pose proof (Z.div_mod (r_mapped_fa (h_reg h c)) (2^18) ltac:(lia)) as Q2. rewrite MFAL in Q2.
      replace (l_sb (h_L h) + c * 2^32 + 3758096384 + r_mapped_fa (h_reg h c)) with ((16 * (l_sb (h_L h) / 2^16) + c * 2^20 + 917504 + 64 * (r_mapped_fa (h_reg h c) / 2^18)) * 4096) by (clear - Q1 Q2; lia).
      apply Z_mod_mult.
    - reflexivity.
    - unfold kUserMapSize; lia.
    - cbn [fst]. clear - F5; unfold kHighMemBeg in F5; lia.
    - (* [comment removed for export] *)
      cbn [vst_of v_unit]. subst FAA. apply (funit_unit (h_L h) c _ WL Hc); [clear - MFAB; lia| exact MFAL| exact ROOM].
    - intros t Ht. exact (funit_new_apart AL h mo c t K WL BR PAB Hc ROOM Ht).
    - rewrite vnb_add_sub. unfold CU, npg_shadow, kUserMapSize in SL |- *. clear - SL. lia.
    - split; [| split; [exact MC| split; [exact RF| exact GR]]].
      apply (HK_perm h' (v_add_sub (vst_of h) FAA kUserMapSize true)); [apply vst_of_fgrow; try assumption; clear - MFAB; lia| exact K'| apply vranges_ok_sub; [exact VR| | unfold kUserMapSize; lia]].
      subst FAA. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. clear - F1 F5 Hc MFAB; unfold kHighMemBeg in F5; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L20170001314.2000005S1v1n". (* [comment removed for export] *)
  #[using="Type"] Lemma vnb_add_eager : forall v lo n, vnb (v_add_eager v lo n true) = vnb v + (n / 32768 + 3).
  Proof. intros v lo n. unfold vnb, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_eager List.filter is_lazy_cs t_kind t_cs map app zsum]. cbn [t_lo t_len]. unfold npages_shadow at 3. cbn [snd]. clear; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  
  (* [comment removed for export] *)
  #[using="Type"] Lemma filter_remove_perm : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Pl,(1.$10.)Pt,$10.P,(2.$10.R2.)P,(3.$10.R2.R3.)P,Pt',$10.P,(3.$10.R1.R5.)P,(5.$0.(38.R2.)(38.R5.))(5.$10.R3.R6.)(4=.$10.R5.(4>.$10.R4.(6:.$10.Lt',$10.(6;.(6<.(38.R1.)(38.R5.)))R5.)))")
(* [comment removed for export] *).
  Proof.
    intros l t ND Hin UNIQ. induction l as [|u l IH]; [destruct Hin|]. cbn [List.filter].
    inversion ND as [|? ? NI ND']; subst. destruct Hin as [->|Hin].
    - rewrite Z.eqb_refl. cbn [negb]. rewrite forallb_filter_id; [apply Permutation_refl|]. apply forallb_forall. intros u Hu.
      destruct (Z.eqb_spec (t_lo u) (t_lo t)) as [E|NE]; [| reflexivity]. exfalso. apply NI. rewrite <- (UNIQ u ltac:(right; exact Hu) E). exact Hu.
    - destruct (Z.eqb_spec (t_lo u) (t_lo t)) as [E|NE].
      + exfalso. apply NI. rewrite (UNIQ u ltac:(left; reflexivity) E). exact Hin.
      + cbn [negb]. transitivity (u :: t :: List.filter (fun t' => negb (t_lo t' =? t_lo t)) l); [| apply perm_swap].
        apply perm_skip. apply IH; [exact ND'| exact Hin| intros t' Ht' E'; apply UNIQ; [right; exact Ht'| exact E']].
  Qed.

  #[using="Type"] Lemma vnb_remove_eager : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Pv,$8.Pt,$10.P,(2.$10.(6=.R2.))P,(3.$10.R2.(6=.R3.))P,(5.$32.(6>.R3.)$=.)P,(5.$6?.(70.R4.)$71.)P,Pt',$10.P,(3.$10.R1.(6=.R7.))P,(5.$0.(38.R2.)(38.R7.))(5.$10.R3.R8.)(5.$0.(72.(59.R7.(38.R6.)(4>.(30.$0.$0.)(4?.$0.$0.(38.R6.)(73.R6.))(5:.(30.$0.$0.)))))(72.R7.))")
(* [comment removed for export] *).
  Proof.
    intros v t ND Hin TC TK UNIQ. pose proof (filter_remove_perm (v_tr v) t ND Hin UNIQ) as PT. unfold vnb. f_equal.
    - apply zsum_perm. unfold csranges, v_remove. cbn [v_stk v_img v_tr v_ghost]. apply perm_skip. apply perm_skip. apply Permutation_sym.
      transitivity (map (fun t0 => (t_lo t0, t_len t0)) (List.filter t_cs (t :: List.filter (fun t' => negb (t_lo t' =? t_lo t)) (v_tr v))) ++ v_ghost v);
        [apply Permutation_app_tail; apply Permutation_map; apply Permutation_filter; exact PT|].
      cbn [List.filter]. rewrite TC. cbn [map app]. apply Permutation_middle.
    - apply zsum_perm. unfold lazyranges, v_remove. cbn [v_tr]. apply Permutation_map. apply Permutation_sym.
      transitivity (List.filter is_lazy_cs (t :: List.filter (fun t' => negb (t_lo t' =? t_lo t)) (v_tr v))); [apply Permutation_filter; exact PT|].
      cbn [List.filter]. unfold is_lazy_cs at 1. rewrite TK. apply Permutation_refl.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L26881819752.3L33808108716.200000:00AS2sh2W02W1S2sh2W0". (* [comment removed for export] *)
  #[using="ASB"] Theorem HK_secrm : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Psh,$1:.Ph',$?.P,(31.VhAR,VAL,R4.R3.)P,(3.$1:.R3.(1;.(1<.R5.)))P,(58.R6.R4.R3.)(14.(31.VhAR,VAL,R4.(74.(50.R5.)(51.R5.)R6.))(5.$32.(75.(64.(65.R6.))(66.&40.(50.R5.))(66.&40.(51.R5.)))$=.))")
(* [comment removed for export] *).
  Proof.
    intros h mo sh h' K Hsh R. pose proof K as [Kv VR].
    pose proof (tr_of_sec h sh Hsh) as HT.
    assert (UNIQ : forall t, In t (tr_of h) -> t_lo t = s_map_beg sh -> t = sec_tr sh).
    { intros t Ht E. apply (tr_lo_inj AL h mo t (sec_tr sh) K Ht HT). exact E. }
    pose proof (tr_of_NoDup AL h mo K) as ND.
    pose proof (vst_of_secrm h sh h' R ND UNIQ) as P.
    dpose (tr_wf AL h mo (sec_tr sh) K HT) as (W0 & W1 & W2 & W3 & W4 & W6 & W7).
    destruct (HKv_munmap AL (vst_of h) mo (sec_tr sh) Kv ASB HT eq_refl eq_refl ltac:(clear - W0; lia) eq_refl ltac:(intros t' Ht' E; exact (UNIQ t' Ht' E))) as [K' MH].
    - rewrite (vnb_remove_eager (vst_of h) (sec_tr sh) ND HT eq_refl eq_refl ltac:(intros t' Ht' E; exact (UNIQ t' Ht' E))).
      ddestruct Kv as (_ & _ & _ & _ & _ & _ & BUD & _). exact BUD.
    - split; [| exact MH]. apply (HK_perm h' _ _ P K'). apply vranges_ok_rm; [exact VR|]. constructor; [cbn; clear - W0 W1; unfold sec_tr in *; cbn in *; lia| constructor].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition shpb (beg : Z) : Z := (0x7fff8000 + beg / 8 + 4095) / 4096 * 4096.
  Definition shpe (beg size : Z) : Z := (0x7fff8000 + beg / 8 + size / 8) / 4096 * 4096.

  
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L12810505031.29L16289020385.29L18926329814.19L18928457686.21L18930958230.20L18930958230.22L20691378622.7 L20691378745.7 L20889782577.23L27699465504.4 L27699466149.4 L33939722775.28L53785284619.31L54224644169.21L59976651606.3 L61028779636.29L61028845172.27L63368119852.29L63368119981.28L63368231057.26L63368316460.31L63368316589.30L63374621462.2800000G00]00i01;01J01\02302J02a03003?03T03n04B04O04a05305E05W05i06;06M06_S3beg4size2B04HIGH2PB1nS3beg4size2B03LOW2PB1nS3beg4size1nS3beg4size2B02PB1nS3beg4size2B01nS3beg4size2B02PB1nS3beg4size2PB3PER2D12D3S3beg4size2PB3PER2D12D2S3beg4size2B02PB1n1H2H0S3beg2PB3PBR2D0S3beg2PB3PBR2D3S3beg4size2B02BE2PB1nS3beg4size2B02PB1n1H2H12H2S3beg4size2B01n1H2H0S3beg4size2NES3beg4size2B02PB1nS3beg4size2B02PB1nS3beg4size2B02PB1nS3beg4size2B02PB1nS3beg4size2B02PB1nS3beg4size2B02PB1nS3beg4size2B02PB1nS3beg4size2B02PB1n". (* [comment removed for export] *)
  #[using="Type"] Theorem HK_madvise : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pbeg,$0.Psize,$0.P,(31.VhAR,VAL,R4.R3.)P,(1>.=R3.)P,(1?.=R3.)P,(1>.(6.R5.R4.)(<.+2.+2?.))P,(12.(1>.(6.R6.R5.)+7???8000.)(1>.$40.R6.))P,(1?.(76.R7.)(77.R7.R6.))ZPB,$0.(76.R8.)Zn,$0.(78.(77.R9.R8.)R1.)(14.(5.$32.(79.(65.R;.)(66.&40.R2.)(66.&40.R1.))$=.)(31.VhAR,VAL,R<.(7:.R;.(66.&40.R2.)(66.&40.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros h mo beg size K B0 S0 BE BAND NE PB n. pose proof K as [Kv VR].
    assert (PBR : 0x7fff8000 + beg / 8 <= PB < 0x7fff8000 + beg / 8 + 4096 /\ PB mod 4096 = 0).
    { subst PB. unfold shpb. pose proof (Z.div_mod (0x7fff8000 + beg / 8 + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + beg / 8 + 4095) 4096 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    assert (PER : 0x7fff8000 + beg / 8 + size / 8 - 4096 < shpe beg size <= 0x7fff8000 + beg / 8 + size / 8 /\ shpe beg size mod 4096 = 0).
    { unfold shpe. pose proof (Z.div_mod (0x7fff8000 + beg / 8 + size / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + beg / 8 + size / 8) 4096 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    destruct PBR as [PBR PBM]. destruct PER as [PER PEM].
    assert (NPOS : 0 < n) by (subst n PB; clear - NE; lia).
    assert (NM : n mod 4096 = 0) by (subst n; rewrite Zminus_mod, PEM, PBM; reflexivity).
    pose proof (Z.div_pos beg 8 B0 ltac:(lia)) as D0. assert (D1 : beg / 8 + size / 8 <= (beg + size) / 8).
    { pose proof (Z.div_mod beg 8 ltac:(lia)). pose proof (Z.mod_pos_bound beg 8 ltac:(lia)). pose proof (Z.div_mod size 8 ltac:(lia)). pose proof (Z.mod_pos_bound size 8 ltac:(lia)). apply Z.div_le_lower_bound; lia. }
    assert (D2 : (beg + size) / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47 / 8) with 17592186044416 in D2.
    destruct BAND as [LOW|HIGH].
    - (* [comment removed for export] *)
      assert (D3 : (beg + size) / 8 <= 0x7fff8000 / 8) by (apply Z.div_le_mono; lia). change (0x7fff8000 / 8) with 268431360 in D3.
      destruct (HKv_madvise AL (vst_of h) mo (TR 0x7fff7000 0x10000000 KLazy true false) PB n Kv) as (OKG & K').
      + unfold vst_of. cbn [v_tr]. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. right. right. left. reflexivity.
      + reflexivity. + reflexivity.
      + cbn [t_lo]. clear - PBR D0. lia.
      + unfold t_hi. cbn [t_lo t_len]. subst n. clear - PER D1 D3 PBR. lia.
      + exact PBM. + exact NM. + exact NPOS.
      + split; [exact OKG| split; [exact K'| exact VR]].
    - (* [comment removed for export] *)
      assert (D3 : kHighMemBeg / 8 <= beg / 8) by (apply Z.div_le_mono; lia). unfold kHighMemBeg in D3. change (17594333495296 / 8) with 2199291686912 in D3.
      destruct (HKv_madvise AL (vst_of h) mo (TR 0x2008fff7000 0xdfff0001000 KLazy true false) PB n Kv) as (OKG & K').
      + unfold vst_of. cbn [v_tr]. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. right. right. right. right. left. reflexivity.
      + reflexivity. + reflexivity.
      + cbn [t_lo]. clear - PBR D3. lia.
      + unfold t_hi. cbn [t_lo t_len]. subst n. clear - PER D1 D2 PBR. lia.
      + exact PBM. + exact NM. + exact NPOS.
      + split; [exact OKG| split; [exact K'| exact VR]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L7457442676.2000005S1v1n". (* [comment removed for export] *)
  #[using="Type"] Lemma vnb_add_lazy : forall v lo n, vnb (v_add_lazy v lo n) = vnb v + (n / 32768 + 3) + (n / 4096 + 1).
  Proof. intros v lo n. unfold vnb, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_lazy List.filter is_lazy_cs t_kind t_cs map app zsum]. cbn [t_lo t_len]. unfold npages_shadow at 3. unfold npages_inside at 1. cbn [snd]. clear; lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L18926664858.23L34909867513.25L45250163605.21L50566837732.21L52566661889.2 L59375271233.23L63767303484.20L67788690458.22L67788838045.23L67792739209.2500000:00G00Q00b00h01201<01F01P01ZS3hAR1a2uaS3hAR1a2ua2A0S3hAR1a2uaS3hAR2AL3IML1a2uaS1h2SLS3hAR1a2uaS3hAR1a2uaS3hAR1a2uaS3hAR1a2uaS3hAR1a2ua". (* [comment removed for export] *)
  #[using="ASB IML IMH"] Theorem HK_node : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pa,(7;.&40.)Ph',$?.P,(31.VhAR,VAL,R4.R3.)Zua,$0.(7<.&40.R3.)P,(5.$0.(3=.R1.+1000.)=)P,(1?.=R2.)P,(1>.(6.R3.(<.+2.+14.))(7=.VhAR,))P,(5.$32.(67.(2<.(30.(7;.&40.)(7;.&40.))(68.(65.R8.))(64.(65.R8.)))R7.(66.&40.(<.+2.+14.)))$=.)P,(1>.(6.(6.(7>.(54.R:.))(7?.+1000.(72.(54.R:.))))$80.)$81.)P,(5;.R;.(4>.$0.R6.(5:.$0.))(5:.$0.)R8.)(14.(31.VhAR,VAL,R9.(82.+22.R:.(<.+2.+14.)R;.))(14.(83.(84.VAL,(54.R9.))R7.(<.+2.+14.))(14.(1>.+65?000.R7.)(12.(1>.(6.R7.(<.+2.+14.))+7???7000.)(1>.+10007???8000.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros h mo a h' K ua AAL A0 ACE RF SL DG. pose proof K as [Kv VR].
    assert (N20 : bv_unsigned (Z_to_bv 64 (2^20)) = 2^20) by (apply u64_lit; lia).
    pose proof (HKv_fresh_above_img AL (vst_of h) mo a (Z_to_bv 64 (2^20)) Kv RF A0 IML ltac:(rewrite IMH; lia) ltac:(rewrite N20; lia) ltac:(rewrite N20; exact ACE)) as IMA. rewrite IMH in IMA. fold ua in IMA.
    pose proof (HKv_fresh_band AL (vst_of h) mo a (Z_to_bv 64 (2^20)) Kv RF ltac:(rewrite N20; lia)) as BND. rewrite N20 in BND. fold ua in BND.
    pose proof (HKv_grant_eager AL (vst_of h) mo a (2^20) true Kv ltac:(rewrite ASB; lia) ltac:(rewrite ASB; lia) AAL A0 ACE ltac:(lia) eq_refl ltac:(rewrite IMH; exact IMA) RF) as K'.
    cbn zeta in K'. fold ua in K'. specialize (K' ltac:(rewrite vnb_add_eager; unfold CN, npg_shadow, kDepotBlockBytes in SL; cbn [v_eb v_add_eager]; clear - SL; lia)).
    pose proof (vst_of_grow h h' [ua] [] DG) as P. cbn [fold_right] in P.
    split; [| split; [| exact (conj IMA BND)]].
    - apply (HK_perm h' _ _ P K'). apply vranges_ok_eager; [exact VR| lia| lia].
    - intros x Hx. apply (proj1 (vcs_perm AL _ _ x P)). unfold vcs, v_add_eager. cbn [v_tr v_stk v_img]. right. right.
      eexists. split; [left; reflexivity|]. unfold t_hi. cbn. exact (conj eq_refl Hx).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L18926664858.23L27571207402.2 L27607433216.21L34909867513.25L50158733945.25L50163156333.23L50163336682.22L50566837729.21L51035119644.20L59375271233.2300000:00@00J00W00a00k01501F01P01ZS3hAR1a2uaS1h2SLS3hAR1a2uaS3hAR1a2ua2A0S3hAR1a2uaS3hAR1a2uaS3hAR1a2uaS3hAR2AL3IML1a2uaS3hAR1a2uaS3hAR1a2ua". (* [comment removed for export] *)
  #[using="ASB IML IMH"] Theorem HK_store : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pa,(7;.&40.)Ph',$?.P,(31.VhAR,VAL,R4.R3.)Zua,$0.(7<.&40.R3.)P,(5.$0.(3=.R1.+1000.)=)P,(1?.=R2.)P,(1>.(6.R3.(<.+2.+17.))(7=.VhAR,))P,(5.$32.(67.(2<.(30.(7;.&40.)(7;.&40.))(68.(65.R8.))(64.(65.R8.)))R7.(66.&40.(<.+2.+17.)))$=.)P,(1>.(6.(6.(7>.(54.R:.))(7?.+1000.(72.(54.R:.))))$85.)$81.)P,(5;.R;.(5:.$0.)(4>.$0.R6.(5:.$0.))R8.)(14.(31.VhAR,VAL,R9.(82.+4022.R:.(<.+2.+17.)R;.))(14.(83.(84.VAL,(54.R9.))R7.(<.+2.+17.))(14.(1>.+65?000.R7.)(12.(1>.(6.R7.(<.+2.+17.))+7???7000.)(1>.+10007???8000.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros h mo a h' K ua AAL A0 ACE RF SL DG. pose proof K as [Kv VR].
    assert (N23 : bv_unsigned (Z_to_bv 64 (2^23)) = 2^23) by (apply u64_lit; lia).
    pose proof (HKv_fresh_above_img AL (vst_of h) mo a (Z_to_bv 64 (2^23)) Kv RF A0 IML ltac:(rewrite IMH; lia) ltac:(rewrite N23; lia) ltac:(rewrite N23; exact ACE)) as IMA. rewrite IMH in IMA. fold ua in IMA.
    pose proof (HKv_fresh_band AL (vst_of h) mo a (Z_to_bv 64 (2^23)) Kv RF ltac:(rewrite N23; lia)) as BND. rewrite N23 in BND. fold ua in BND.
    pose proof (HKv_grant_lazy AL (vst_of h) mo a (2^23) Kv ltac:(rewrite ASB; lia) ltac:(rewrite ASB; lia) AAL A0 ACE ltac:(lia) eq_refl ltac:(rewrite IMH; exact IMA) RF) as K'.
    cbn zeta in K'. fold ua in K'. specialize (K' ltac:(rewrite vnb_add_lazy; unfold CSB, npg_shadow, kStoreBlockBytes in SL; cbn [v_eb v_add_lazy]; clear - SL; lia)).
    pose proof (vst_of_grow h h' [] [ua] DG) as P. cbn [fold_right] in P.
    split; [| split; [| exact (conj IMA BND)]].
    - apply (HK_perm h' _ _ P K'). apply vranges_ok_lazy; [exact VR| lia| lia].
    - intros x Hx. apply (proj1 (vcs_perm AL _ _ x P)). unfold vcs, v_add_lazy. cbn [v_tr v_stk v_img]. right. right.
      eexists. split; [left; reflexivity|]. unfold t_hi. cbn. exact (conj eq_refl Hx).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L37135269212.400000;S2h01h2CB1X". (* [comment removed for export] *)
  #[using="Type"] Theorem HK_room20 : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph0,$?.Ph,$?.Pmo,$2?.P,(5?.VhAR,R3.)P,(1>.(60.R4.)$61.)P,(31.VhAR,VAL,R4.R3.)P,(1>.(5<.(<.+2.+14.)R5.)(6.(5<.(<.+2.+14.)R6.)+8.))P,(1>.(6.(6.(7>.(54.R6.))(7?.+1000.(72.(54.R6.))))(<.+2.+14.))$81.)(13.(7;.&40.)La,(7;.&40.)(86.VhAR,+22.(<.+2.+14.)R7.R1.))")
(* [comment removed for export] *).
  Proof.
    intros h0 h mo B HV [Kv VR] CB SL. apply (HKv_room20 AL (vst_of h) mo 0x22 VR Kv); [| intros _; exact SL].
    pose proof (vst_cb20' h0 B HV) as X. unfold vst_of in X |- *. cbn [v_cb20] in X |- *. clear - X CB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L10775262156.400000;S2h01h2CB1X". (* [comment removed for export] *)
  #[using="Type"] Theorem HK_room23 : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph0,$?.Ph,$?.Pmo,$2?.P,(5?.VhAR,R3.)P,(1>.(60.R4.)$61.)P,(31.VhAR,VAL,R4.R3.)P,(1>.(5<.(<.+2.+17.)R5.)(6.(5<.(<.+2.+17.)R6.)+8.))(13.(7;.&40.)La,(7;.&40.)(86.VhAR,+4022.(<.+2.+17.)R6.R1.))")
(* [comment removed for export] *).
  Proof.
    intros h0 h mo B HV [Kv VR] CB. apply (HKv_room23 AL (vst_of h) mo 0x4022 VR Kv); [| intros E; discriminate E].
    pose proof (vst_cb23' h0 B HV) as X. unfold vst_of in X |- *. cbn [v_cb23] in X |- *. clear - X CB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Theorem HK_apart : ltac2:(CDefT.buildp (gd_tbl_AVstT ()) "Ph,$?.Pmo,$2?.Pa,(7;.&40.)Pn,(7;.&40.)P,(31.VhAR,VAL,R4.R3.)P,(5.$32.(67.(2<.(30.(7;.&40.)(7;.&40.))(68.(65.R4.))(64.(65.R4.)))R3.R2.)$=.)P,(1>.+10000.(7<.&40.R3.))P,(1>.(6.(7<.&40.R5.)(7<.&40.R4.))(7=.VhAR,))Px,$0.P,(12.(84.VAL,(54.R9.)R1.)(14.(1>.(87.VAL,)R1.)(1?.R1.(88.VAL,))))(4.(14.(1>.(7<.&40.R8.)R2.)(1?.R2.(6.(7<.&40.R8.)(7<.&40.R7.)))))")
(* [comment removed for export] *).
  Proof. intros h mo a n [Kv _] RF N16 CE x Hx. exact (HKv_apart AL (vst_of h) mo a n Kv RF N16 CE x Hx). Qed.
End TRANS.

End ARUN_2.
