(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AModelXE AModelC24 APop AW_FreeP AW_FreeK AW_FreeG.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_FreeR () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "Stdlib.Lists.List.In"; "Stdlib.Lists.List.NoDup"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.rm_ab"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.find"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_cls"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Nat.sub"; "Corelib.Lists.ListDef.firstn"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.swap_remove"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma NoDup_map_inj : forall {A B} (f : A -> B) (l : list A) x y, NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l x y ND Hx Hy E. induction l as [|a l IH]; [destruct Hx|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hx as [->|Hx], Hy as [->|Hy]; [reflexivity| | | exact (IH ND' Hx Hy)].
  - exfalso. apply NI. rewrite E. apply in_map. exact Hy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
Qed.

#[using="Type"] Lemma In_firstn_In : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_app_iff. left. exact H. Qed.
#[using="Type"] Lemma In_skipn_In : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_app_iff. right. exact H. Qed.

#[using="Type"] Lemma rm_ab_In : forall ab ks x, In x (rm_ab ab ks) <-> In x ks /\ ck_ab x <> ab.
Proof.
  intros ab ks x. unfold rm_ab. rewrite filter_In. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma rm_ab_notin : forall ab ks, ~ In ab (map ck_ab ks) -> rm_ab ab ks = ks.
Proof.
  intros ab ks NI. induction ks as [|y ks IH]; [reflexivity|]. cbn. cbn in NI.
  destruct (Z.eqb_spec (ck_ab y) ab) as [E|NE]; [exfalso; apply NI; left; exact E|]. cbn. f_equal. apply IH. intros H; apply NI; right; exact H.
Qed.
#[using="Type"] Lemma rm_ab_cons : forall ab x ks, rm_ab ab (x :: ks) = if ck_ab x =? ab then rm_ab ab ks else x :: rm_ab ab ks.
Proof. intros ab x ks. cbn. destruct (ck_ab x =? ab); reflexivity. Qed.
#[using="Type"] Lemma rm_ab_split : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "Pks,(0.$1.)Pk,$1.P,(2.$1.R1.R2.)P,(3.$4.(5.$1.$4.$6.R3.))(7.(0.$1.)Ll1,(0.$1.)(7.(0.$1.)Ll2,(0.$1.)(8.(9.(0.$1.)R6.(:.$1.R2.(;.$1.R5.R1.)))(9.(0.$1.)(<.(6.R5.)R6.)(:.$1.R2.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros ks k Hk ND. induction ks as [|x ks IH]; [destruct Hk|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  rewrite rm_ab_cons. destruct Hk as [->|Hk].
  - dexists [], ks. rewrite Z.eqb_refl. split; [reflexivity|]. cbn. apply rm_ab_notin. exact NI.
  - ddestruct (IH Hk ND') as (l1 & l2 & E1 & E2). dexists (x :: l1), l2. split; [rewrite E1; reflexivity|].
    destruct (Z.eqb_spec (ck_ab x) (ck_ab k)) as [E|NE].
    + exfalso. apply NI. rewrite E. apply in_map. exact Hk.
    + rewrite E2. reflexivity.
Qed.

#[using="Type"] Lemma NoDup_map_app_mid : forall {A B} (f : A -> B) l1 (x : A) l2, NoDup (map f (l1 ++ x :: l2)) -> NoDup (map f (l1 ++ l2)).
Proof. intros A B f l1 x l2 ND. rewrite map_app in *. cbn in ND. exact (NoDup_remove_1 _ _ _ ND). Qed.

#[using="Type"] Lemma find_app_skip : forall {A} (p : A -> bool) l1 x l2, p x = false -> find p (l1 ++ x :: l2) = find p (l1 ++ l2).
Proof. intros A p l1 x l2 Px. induction l1 as [|y l1 IH]; cbn; [rewrite Px; reflexivity|]. destruct (p y); [reflexivity| exact IH]. Qed.

#[using="Type"] Lemma find_rm_other : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "Pp,P,$1.$=.Pks,(0.$1.)Pk,$1.P,(2.$1.R1.R2.)P,(3.$4.(5.$1.$4.$6.R3.))P,(9.$=.A1.R5.R3.$>.)(9.(?.$1.)(10.$1.R6.(<.(6.R4.)R5.))(10.$1.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros p ks k Hk ND Pk. ddestruct (rm_ab_split ks k Hk ND) as (l1 & l2 & E1 & E2). rewrite E2, E1. symmetry. apply find_app_skip. exact Pk.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma NoDup_codes_le : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "Pl,(0.$4.)Pn,$4.Ps,$4.P,(11.=R1.)P,(12.=R3.)P,(3.$4.R5.)P,(13.$4.Lq,$4.(7.$4.Lk,$4.(8.(8.(12.=R1.)(11.R1.R7.))(9.$4.R2.(14.R1.R6.))))R6.)(12.(15.(16.$4.R7.))R6.)")
(* [comment removed for export] *).
Proof.
  intros l n s S0 N0 ND F.
  assert (INCL : incl l (map (fun k => Z.of_nat k * s) (seq 0 (Z.to_nat n)))).
  { intros q Hq. pose proof (proj1 (Forall_forall _ _) F q Hq) as (k & Hk & ->). apply in_map_iff. exists (Z.to_nat k).
    split; [rewrite Z2Nat.id by lia; reflexivity| apply in_seq; lia]. }
  pose proof (NoDup_incl_length ND INCL) as LE. rewrite length_map, length_seq in LE. lia.
Qed.

#[using="Type"] Lemma WFK_of_WFR : forall h, WFR h -> h_havol h <= AVOL_MAX -> WFK h.
Proof.
  (intros h dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG); intros HV).
  split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB (conj WBIG (conj WG HV)))))].
  intros c Hc. pose proof (WR c Hc) as R. cbn zeta in R. ddestruct R as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _).
  cbn zeta. split; [exact R0|]. split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [exact R6|]. split; [exact R7| exact R8].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma batch_slot : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "Ph,$17.Pb,$18.P,(19.VhAR,R2.)P,(2.$18.R2.(:.$18.(1:.(1;.R3.))(1:.(1<.R3.))))(7.$4.Li,$4.(8.(8.(12.=R1.)(11.R1.(1=.R5.$1>.)))(9.$4.(1?.R4.)(20.(21.R5.)$1>.R1.))))")
(* [comment removed for export] *).
Proof.
  (intros h b dd_H; ddestruct dd_H as (_ & _ & _ & _ & WQ & _); intros Hb). ddestruct WQ as (TQ & (GQ & _) & _).
  apply in_app_iff in Hb as [Hb|Hb].
  - destruct (q_batches (h_tq h)) as [|b0 tb]; [destruct Hb|]. destruct TQ as [(_ & _ & B4) TB].
    destruct Hb as [<-|Hb]; [exact B4|]. destruct (proj1 (Forall_forall _ _) TB b Hb) as (_ & _ & B4'). exact B4'.
  - destruct (proj1 (Forall_forall _ _) GQ b Hb) as (_ & _ & _ & B4'). exact B4'.
Qed.

#[using="Type"] Lemma owned_chunk_not_batch : forall h c q, NoDup (owned h c) -> In q (chunk_set h c) -> In q (batch_set h c) -> False.
Proof.
  intros h c q ND HC HB. unfold owned in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND.
  exact (NoDup_app_l_r _ _ q ND HC HB).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma batch_vs_chunk : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "Ph,$17.Pk,$1.Pb,$18.P,(19.VhAR,R3.)P,(2.$1.R3.(22.R4.))P,(9.$=.(23.R4.)$24.)P,(2.$18.R4.(:.$18.(1:.(1;.R6.))(1:.(1<.R6.))))(25.(12.(26.(1?.R5.)+2000.)(6.R6.))(12.(26.(6.R6.)(27.(28.R6.)))(1?.R5.)))")
(* [comment removed for export] *).
Proof.
  intros h k b WF Hk P Hb. dpose WF as (WL' & _ & WR & (WKF & _ & _) & _). pose proof WL' as (WL & _).
  ddestruct (batch_slot h b WF Hb) as (i & Hi & EB).
  pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (_ & _ & _ & WX). rewrite P in WX. ddestruct WX as (_ & C30 & j & Hj & EK).
  unfold kBatchClass in *.
  destruct (Z.eq_dec (ck_cls k) 24) as [E24|N24].
  - rewrite E24 in *. assert (NIJ : i <> j).
    { intros ->. pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDO & _).
      apply (owned_chunk_not_batch h 24 (compact (h_L h) 24 (ck_ab k)) NDO).
      + unfold chunk_set. apply in_map_iff. exists k. split; [reflexivity|]. apply filter_In. split; [exact Hk|]. rewrite P, E24. reflexivity.
      + unfold batch_set, kBatchClass. rewrite Z.eqb_refl. apply in_map_iff. exists b. split; [rewrite EB, EK; reflexivity| exact Hb]. }
    rewrite EB, EK. unfold chunk_at. change (class_size 24) with 8192.
    assert (i + 1 <= j \/ j + 1 <= i) as [LE|GT] by lia; [left| right]; lia.
  - destruct (slot_le h 24 i WR ltac:(lia) Hi) as [A1 A2]. destruct (slot_le h (ck_cls k) j WR ltac:(lia) Hj) as [B1 B2].
    pose proof (user_vs_user h (ck_cls k) 24 WR ltac:(lia) ltac:(lia) N24) as UU.
    pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU1 & _).
    pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU2 & _).
    rewrite EB, EK. change (class_size 24) with 8192 in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition funit (f : option bool) : Z := match f with Some true => kFreeArrayMapSize | _ => 0 end.
(* [comment removed for export] *)
Definition fsel (h : ahst) (c : Z) (f : option bool) : ahst := match f with Some _ => h_fagrow h c | None => h end.

Section RecP.
  Variables (h : ahst) (k : chunk) (dr : bool) (cnt : nat) (f : option bool) (b0 : batch) (tb : list batch) (rest : list Z).
  Let L := h_L h.
  Let c := ck_cls k.
  Let p := h_cache h c.
  Let r := h_reg h c.
  Let q := compact L c (ck_ab k).
  Let h' := h_recp h k dr cnt f.

  Hypothesis WF : WFR h.
  Hypothesis CI : h_cinit h = true.
  Hypothesis Hk : In k (h_chunks h).
  Hypothesis STQ : ck_st k = CHUNK_QUARANTINE.
  Hypothesis PRIM : ck_prim k = true.
  Hypothesis HB : q_batches (h_tq h) = b0 :: tb.
  Hypothesis HE : b_elems b0 = ck_hdr k :: rest.
  Hypothesis DR : if dr then pc_count p = max_count c /\ cnt = Z.to_nat (max_count c / 2) else pc_count p < max_count c.
  Hypothesis FOK : f = None \/ f = Some true.
  Hypothesis NF4 : dr = true -> 4 * (r_nfreed r + Z.of_nat cnt) <= r_mapped_fa r + funit f.
  Hypothesis FX : f = Some true -> dr = true /\ r_mapped_fa r < 4 * (r_nfreed r + Z.of_nat cnt).
  (* [comment removed for export] *)
  Hypothesis HGU : forall k', In k' (h_chunks h) -> k' <> k -> ck_hdr k' = ck_hdr k -> False.

  (* [comment removed for export] *)
  Local Ltac clr := clear WF CI Hk STQ PRIM HB HE DR FOK NF4 FX HGU.
  #[using="Type"] Lemma recp_L : h_L h' = h_L h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_chunks : h_chunks h' = rm_ab (ck_ab k) (h_chunks h). Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="HB"] Lemma recp_tq : q_batches (h_tq h') = b_pop b0 :: tb.
  Proof. clear WF CI Hk STQ PRIM HE DR FOK NF4 FX HGU. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; cbn; rewrite HB; reflexivity. Qed.
  #[using="Type"] Lemma recp_gq : h_gq h' = h_gq h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_sec : h_sec h' = h_sec h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_dep : h_dep h' = h_dep h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_acct : h_acct h' = h_acct h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_havol : h_havol h' = h_havol h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_cinit : h_cinit h' = h_cinit h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_pa : h_pa_committed h' = h_pa_committed h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_ia : h_ia h' = h_ia h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  #[using="Type"] Lemma recp_fake : h_fake h' = h_fake h. Proof. clr. subst h'. unfold h_recp, h_lcd. destruct dr; [destruct f as [[|]|]|]; reflexivity. Qed.
  
  #[using="Type"] Lemma recp_reg : forall c', h_reg h' c' =
    if (c' =? c) && dr then RG (r_mapped_user r) (r_alloc_user r) (r_mapped_fa r + funit f) (r_fa r ++ pc_lastn p cnt) else h_reg h c'.
  Proof.
    intros c'. clr. subst h' r p c L. unfold h_recp, h_lcd, h_popq, h_push, h_drain, fgrow, h_fagrow. destruct dr; [destruct f as [[|]|]|]; cbn;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; unfold fupd; destruct (Z.eqb_spec c' (ck_cls k)) as [->|NE]; cbn;
      rewrite ?Z.eqb_refl, ?fupd_same, ?Z.add_0_r; try reflexivity.
    all: try (rewrite (proj2 (Z.eqb_neq _ _) NE); reflexivity).
  Qed.

  #[using="Type"] Lemma recp_cache : forall c', h_cache h' c' = if c' =? c then pc_push (if dr then pc_dropn p cnt else p) q else h_cache h c'.
  Proof.
    intros c'. clr. subst h' r p c q L. unfold h_recp, h_lcd, h_popq, h_push, h_drain, fgrow, h_fagrow. destruct dr; [destruct f as [[|]|]|]; cbn;
      unfold fupd; destruct (Z.eqb_spec c' (ck_cls k)) as [->|NE]; cbn; rewrite ?Z.eqb_refl; try reflexivity.
  Qed.

  #[using="c p r"] Lemma recp_carved : forall c', carved h' c' = carved h c'.
  Proof. intros c'. unfold carved. rewrite recp_reg. destruct ((c' =? c) && dr) eqn:E; [| reflexivity]. apply andb_prop in E as [E _]. apply Z.eqb_eq in E. subst c'. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="hAR cnt WF Hk PRIM"] Lemma recp_kfacts : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "(8.(8.(12.+1.Vc,)(12.Vc,+1>.))(7.$4.Lj,$4.(8.(8.(12.=R1.)(11.R1.(1=.Vh,Vc,)))(8.(9.$4.(6.Vk,)(20.VL,Vc,R1.))(8.(9.$4.Vq,(14.R1.(29.(27.Vc,)+10.)))(9.$4.(14.+10.Vq,)(14.R1.(27.Vc,))))))))")
(* [comment removed for export] *).
  Proof.
    dpose WF as (WL & WC & WR & (WKF & _ & _) & _).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX). rewrite PRIM in WX. ddestruct WX as (ECLS & C30 & j & Hj & EAB).
    subst c. split; [exact C30|]. exists j. split; [exact Hj|]. split; [exact EAB|].
    pose proof (class_size_mod16 (ck_cls k) ltac:(lia)) as M16. pose proof (Z.div_mod (class_size (ck_cls k)) 16 ltac:(lia)) as D16.
    subst q L. rewrite EAB, compact_chunk_at by exact M16. split; [reflexivity| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="hAR WF Hk PRIM"] Lemma chunk_set_split : exists A1 A2, chunk_set h c = A1 ++ q :: A2 /\ chunk_set h' c = A1 ++ A2.
  Proof.
    dpose WF as (_ & _ & _ & (_ & ND & _) & _).
    ddestruct (rm_ab_split (h_chunks h) k Hk ND) as (l1 & l2 & E1 & E2).
    unfold chunk_set. rewrite recp_chunks, recp_L, E2. rewrite E1.
    rewrite !filter_app. cbn [filter]. rewrite PRIM. fold c. rewrite Z.eqb_refl. cbn [andb map]. rewrite !map_app. cbn [map].
    dexists (map (fun k0 => compact (h_L h) c (ck_ab k0)) (filter (fun k0 => ck_prim k0 && (ck_cls k0 =? c)) l1)),
           (map (fun k0 => compact (h_L h) c (ck_ab k0)) (filter (fun k0 => ck_prim k0 && (ck_cls k0 =? c)) l2)).
    split; reflexivity.
  Qed.

  #[using="hAR WF Hk PRIM"] Lemma chunk_set_other : forall c', c' <> c -> chunk_set h' c' = chunk_set h c'.
  Proof.
    intros c' NE. dpose WF as (_ & _ & _ & (_ & ND & _) & _).
    ddestruct (rm_ab_split (h_chunks h) k Hk ND) as (l1 & l2 & E1 & E2).
    unfold chunk_set. rewrite recp_chunks, recp_L, E2. rewrite E1.
    rewrite !filter_app. cbn [filter]. rewrite PRIM. cbn [andb]. destruct (Z.eqb_spec (ck_cls k) c') as [E|_]; [exfalso; apply NE; rewrite <- E; reflexivity|].
    reflexivity.
  Qed.

  #[using="b0 tb HB"] Lemma batch_set_same : forall c', batch_set h' c' = batch_set h c'.
  Proof.
    intros c'. unfold batch_set. rewrite recp_tq, recp_gq, recp_L, HB. cbn [map app b_addr b_pop]. reflexivity.
  Qed.

  #[using="hAR b0 tb L c p r q WF Hk PRIM HB DR NF4 FX"] Lemma owned_perm : forall c', 0 <= c' < kNumClasses -> Permutation (owned h' c') (owned h c').
  Proof.
    intros c' Hc'. unfold owned, fa_set, cache_set. rewrite recp_reg, recp_cache, batch_set_same.
    destruct (Z.eqb_spec c' c) as [->|NE].
    - ddestruct chunk_set_split as (A1 & A2 & -> & ->). cbn [andb].
      destruct dr.
      + cbn [r_fa pc_chunks pc_push pc_dropn]. unfold pc_lastn. fold p. fold r.
        set (n0 := (length (pc_chunks p) - cnt)%nat). rewrite <- (firstn_skipn n0 (pc_chunks p)) at 3.
        rewrite <- !app_assoc. apply Permutation_app_head.
        (* [comment removed for export] *)
        eapply Permutation_trans. { apply Permutation_app_swap_app. }
        rewrite <- ?app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply (Permutation_middle A1 (A2 ++ batch_set h c) q).
      + cbn [pc_chunks pc_push]. fold p. rewrite <- ?app_assoc. apply Permutation_app_head. apply Permutation_app_head. cbn [app]. apply (Permutation_middle A1 (A2 ++ batch_set h c) q).
    - cbn [andb]. rewrite (chunk_set_other c' NE). apply Permutation_refl.
  Qed.

  
  (* [comment removed for export] *)
  Let okq (c' : Z) : Z -> Prop := fun x => 0 <= x /\ exists kk, 0 <= kk < carved h c' /\ 16 * x = kk * class_size c'.

  #[using="hAR cnt WF Hk PRIM"] Lemma q_ok : okq c q.
  Proof.
    ddestruct recp_kfacts as (C30 & j & Hj & EAB & Hq & H16). split; [| exists j; split; [exact Hj| exact H16]].
    rewrite Hq. pose proof (class_size_range c ltac:(lia)). apply Z.mul_nonneg_nonneg; [lia|]. apply Z.div_pos; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR b0 WF HB HE"] Lemma elems_nodup : NoDup ((ck_hdr k :: rest) ++ flat_map b_elems (tb ++ q_batches (h_gq h))).
  Proof.
    dpose WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & WX2 & _) & _) || dpose WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [_ WX2] & _).
    revert WX2. rewrite HB. cbn [flat_map app]. rewrite HE, flat_map_app. intros X. exact X.
  Qed.

  #[using="hAR WF Hk"] Lemma other_chunk_kept : forall k', In k' (h_chunks h) -> k' <> k -> In k' (h_chunks h').
  Proof.
    intros k' Hk' NE. rewrite recp_chunks. apply rm_ab_In. split; [exact Hk'|]. intros EA. apply NE.
    dpose WF as (_ & _ & _ & (_ & ND & _) & _). exact (NoDup_map_inj ck_ab _ _ _ ND Hk' Hk EA).
  Qed.

  #[using="hAR WF Hk"] Lemma elem_chunk_kept : forall e k', In k' (h_chunks h) -> ck_hdr k' = e -> e <> ck_hdr k -> In k' (h_chunks h').
  Proof. intros e k' Hk' He NE. apply other_chunk_kept; [exact Hk'|]. intros ->. exact (NE (eq_sym He)). Qed.

  #[using="hAR c p r WF Hk"] Lemma wf_batch_kept : forall b, wf_batch h b -> (forall e, In e (b_elems b) -> e <> ck_hdr k) -> wf_batch h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4); intros NE). dpose WF as (_ & _ & _ & (_ & ND & _) & _).
    split; [exact B1|]. split; [| split].
    - rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. rewrite recp_chunks.
      rewrite (find_rm_other (fun k0 => ck_hdr k0 =? e) (h_chunks h) k Hk ND); [reflexivity|]. apply Z.eqb_neq. intros E. exact (NE e He (eq_sym E)).
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k' & Hk' & S' & H').
      exists k'. split; [exact (elem_chunk_kept e k' Hk' H' (NE e He))| split; [exact S'| exact H']].
    - rewrite recp_carved, recp_L. exact B4.
  Qed.

  #[using="hAR c p r WF Hk"] Lemma wf_batch_r_kept : forall b, wf_batch_r h b -> (forall e, In e (b_elems b) -> e <> ck_hdr k) -> wf_batch_r h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B3 & B4); intros NE). split; [exact B1|]. split.
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k' & Hk' & S' & H').
      exists k'. split; [exact (elem_chunk_kept e k' Hk' H' (NE e He))| split; [exact S'| exact H']].
    - rewrite recp_carved, recp_L. exact B4.
  Qed.

  #[using="b0 tb rest L c p r q WF CI Hk PRIM HB HE DR FOK NF4 FX HGU okq"] Theorem WFR_recp : WFR h'.
  Proof.
    dpose WF as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    dpose WK as (WKF & ND & WKSEC). ddestruct recp_kfacts as (C30 & j & Hj & EAB & Hq & H16).
    pose proof (class_size_range c ltac:(lia)) as CSR. pose proof (max_count_range c ltac:(lia)) as MCR.
    assert (HMAX : pc_max p = max_count c /\ pc_csize p = class_size c).
    { pose proof (WC c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. rewrite CI in X. destruct X as (X & _). apply X. lia. }
    destruct HMAX as [HMAX HCSZ].
    pose proof elems_nodup as END.
    split; [rewrite recp_L; exact WL|].
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. rewrite recp_cinit, CI, recp_cache, recp_carved.
      pose proof (WC c' Hc') as X. cbn zeta in X. rewrite CI in X. ddestruct X as (X1 & X2 & X3 & X4 & X5).
      destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (conj X1 (conj X2 (conj X3 (conj X4 X5))))].
      fold p in X1, X2, X3, X4, X5 |- *. unfold pc_count in *.
      assert (LEN : forall dr' : bool, length (pc_chunks (pc_push (if dr' then pc_dropn p cnt else p) q)) = (length (pc_chunks (if dr' then pc_dropn p cnt else p)) + 1)%nat).
      { intros dr'. cbn [pc_chunks pc_push]. rewrite length_app. reflexivity. }
      split; [intros _; cbn [pc_max pc_csize pc_push]; destruct dr; cbn [pc_max pc_csize pc_dropn]; exact (X1 ltac:(lia))|].
      split; [intros E0; exfalso; lia|].
      assert (CNT' : Z.of_nat (length (pc_chunks (pc_push (if dr then pc_dropn p cnt else p) q))) <= max_count c
                     /\ Z.of_nat (length (pc_chunks (pc_push (if dr then pc_dropn p cnt else p) q))) <= 16).
      { rewrite LEN. destruct dr; cbn [pc_chunks pc_dropn].
        - destruct DR as [D1 D2]. rewrite firstn_length_le by lia. assert (1 <= max_count c / 2) by (apply Z.div_le_lower_bound; lia). lia.
        - lia. }
      split; [destruct dr; cbn [pc_max pc_push pc_dropn]; rewrite HMAX; lia|]. split; [lia|].
      cbn [pc_chunks pc_push]. apply Forall_app. split.
      - destruct dr; cbn [pc_chunks pc_dropn]; [| exact X5]. apply Forall_forall. intros x Hx.
        exact (proj1 (Forall_forall _ _) X5 x (In_firstn_In _ _ _ Hx)).
      - constructor; [| constructor]. exact q_ok. }
    split. { (* [comment removed for export] *)
      intros c' Hc'. cbn zeta. rewrite recp_reg, recp_carved.
      pose proof (WR c' Hc') as X. cbn zeta in X. ddestruct X as (X0 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
      assert (NDP : NoDup (owned h' c') /\ (forall kk, 0 <= kk < carved h c' <-> In (kk * class_size c' / 16) (owned h' c'))).
      { split; [exact (Permutation_NoDup (Permutation_sym (owned_perm c' Hc')) X10)|].
        intros kk. rewrite (X11 kk). split; intros H; [eapply Permutation_in; [apply Permutation_sym, owned_perm; exact Hc'| exact H]
                                                    | eapply Permutation_in; [apply owned_perm; exact Hc'| exact H]]. }
      destruct NDP as [NDo PARTo].
      destruct ((c' =? c) && dr) eqn:E.
      - apply andb_prop in E as [E ->]. apply Z.eqb_eq in E. subst c'. fold r in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9 |- *.
        cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. destruct DR as [D1 D2].
        unfold r_nfreed in *. cbn [r_fa]. rewrite length_app. unfold pc_lastn. rewrite length_skipn.
        assert (FU : 0 <= funit f <= kFreeArrayMapSize /\ funit f mod kFreeArrayMapSize = 0) by (destruct f as [[|]|]; cbn; unfold kFreeArrayMapSize; (split; [lia| reflexivity])).
        assert (CNTL : (cnt <= length (pc_chunks p))%nat) by (unfold pc_count in D1; subst cnt; assert (max_count c / 2 <= max_count c) by (apply Z.div_le_upper_bound; lia); lia).
        split; [intros E0; exfalso; lia|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
        split. { unfold kFreeArrayMapSize in *. destruct FU as [[F0 F1] F2].
                 rewrite Z.add_mod, X6, F2 by lia. reflexivity. }
        split. { (* [comment removed for export] *)
          split; [lia|]. destruct f as [[|]|]; cbn [funit]; [| lia| lia].
          destruct (FX eq_refl) as [_ LT]. unfold r_nfreed in LT. subst cnt.
          (* [comment removed for export] *)
          pose proof WX as (WX1 & _). pose proof (WX1 c ltac:(unfold kNumClasses; lia)) as B. fold r in B.
          unfold kFreeArraySize, kFreeArrayMapSize, kUserLimit in *. unfold carved in *. fold r in B |- *.
          assert (CB : r_alloc_user r / class_size c <= 3758096384 / 32)
            by (apply Z.le_trans with (m := 3758096384 / class_size c); [apply Z.div_le_mono; lia| apply Z.div_le_compat_l; lia]).
          change (3758096384 / 32) with 117440512 in CB. lia. }
        split. { specialize (NF4 eq_refl). unfold r_nfreed in NF4. clear - NF4 CNTL. lia. }
        split. { apply Forall_app. split; [exact X9|]. pose proof (WC c ltac:(unfold kNumClasses; lia)) as Y. cbn zeta in Y. ddestruct Y as (_ & _ & _ & _ & Y5).
                 fold p in Y5. apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) Y5 x (In_skipn_In _ _ _ Hx)). }
        split; [exact NDo| exact PARTo].
      - split; [exact X0|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
        split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact NDo| exact PARTo]. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - apply Forall_forall. intros k' Hk'. rewrite recp_chunks in Hk'. apply rm_ab_In in Hk' as [Hk' _].
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as X. unfold wf_chunk' in *. rewrite recp_carved, recp_L, recp_sec. exact X.
      - rewrite recp_chunks. ddestruct (rm_ab_split (h_chunks h) k Hk ND) as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in ND. exact (NoDup_map_app_mid _ _ _ _ ND).
      - rewrite recp_sec. intros i sh Hi. ddestruct (WKSEC i sh Hi) as (k' & Hk' & P' & R'). exists k'. split; [| exact (conj P' R')].
        apply other_chunk_kept; [exact Hk'|]. intros ->. rewrite PRIM in P'. discriminate P'. }
    split. { (* [comment removed for export] *)
      ddestruct WQ as (WT & WGQ & NDA & UQ). rewrite HB in WT. destruct WT as [WB0 WTB].
      assert (NE0 : forall e, In e rest -> e <> ck_hdr k).
      { intros e He ->. cbn in END. inversion END as [|? ? NI _]; subst. apply NI. apply in_app_iff. left. exact He. }
      assert (NEG : forall b e, In b (tb ++ q_batches (h_gq h)) -> In e (b_elems b) -> e <> ck_hdr k).
      { intros b e Hb He ->. cbn in END. inversion END as [|? ? NI _]; subst. apply NI. apply in_app_iff. right. apply in_flat_map. exists b. split; assumption. }
      split; [| split; [| split]].
      - rewrite recp_tq. split.
        + ddestruct WB0 as (B1 & B2 & B3). split; [unfold b_count in *; cbn [b_elems b_pop]; rewrite HE in B1 |- *; cbn [tl]; cbn [length] in B1; lia|].
          split.
          * cbn [b_elems b_pop]. rewrite HE. cbn [tl]. apply Forall_forall. intros e He.
            rewrite HE in B2. inversion B2 as [|? ? _ B2']; subst. destruct (proj1 (Forall_forall _ _) B2' e He) as (k' & Hk' & S' & H').
            exists k'. split; [exact (elem_chunk_kept e k' Hk' H' (NE0 e He))| split; [exact S'| exact H']].
          * rewrite recp_carved, recp_L. cbn [b_addr b_pop]. exact B3.
        + apply Forall_forall. intros b Hb. apply wf_batch_r_kept; [exact (proj1 (Forall_forall _ _) WTB b Hb)|].
          intros e He. apply (NEG b e); [apply in_app_iff; left; exact Hb| exact He].
      - rewrite recp_gq. ddestruct WGQ as (G1 & G2 & G3). split; [| exact (conj G2 G3)].
        apply Forall_forall. intros b Hb. apply wf_batch_kept; [exact (proj1 (Forall_forall _ _) G1 b Hb)|].
        intros e He. apply (NEG b e); [apply in_app_iff; right; exact Hb| exact He].
      - rewrite recp_tq, recp_gq. rewrite HB in NDA. cbn [map app b_addr b_pop] in *. exact NDA.
      - intros k' Hk' S'. rewrite recp_tq, recp_gq. rewrite recp_chunks in Hk'. apply rm_ab_In in Hk' as [Hk' NA].
        assert (NK : k' <> k) by (intros ->; exact (NA eq_refl)).
        assert (NH : ck_hdr k' <> ck_hdr k) by (intros E; exact (HGU k' Hk' NK E)).
        ddestruct (UQ k' Hk' S') as (b & [Hb Hin] & U). rewrite HB in Hb.
        destruct Hb as [<-|Hb].
        + exists (b_pop b0). split.
          * split; [left; reflexivity|]. cbn [b_elems b_pop]. rewrite HE in Hin |- *. cbn [tl]. destruct Hin as [E|Hin]; [exfalso; exact (NH (eq_sym E))| exact Hin].
          * intros b' [Hb' Hin']. destruct Hb' as [<-|Hb']; [reflexivity|]. exfalso.
            assert (b0 = b') by (apply U; rewrite HB; cbn [app]; split; [right; exact Hb'| exact Hin']). subst b'.
            rewrite HB in NDA. cbn in NDA. inversion NDA as [|? ? NI _]; subst. apply NI. rewrite <- ?map_app. apply in_map. exact Hb'.
        + exists b. split.
          * split; [right; exact Hb| exact Hin].
          * intros b' [Hb' Hin']. destruct Hb' as [<-|Hb']; [| apply U; rewrite HB; cbn [app]; split; [right; exact Hb'| exact Hin']].
            exfalso. cbn [b_elems b_pop] in Hin'. rewrite HE in Hin'. cbn [tl] in Hin'.
            assert (b = b0) by (apply U; rewrite HB; cbn [app]; split; [left; reflexivity| rewrite HE; right; exact Hin']). subst b.
            rewrite HB in NDA. cbn in NDA. inversion NDA as [|? ? NI _]; subst. apply NI. rewrite <- ?map_app. apply in_map. exact Hb. }
    split; [unfold wf_sec; rewrite recp_sec, recp_pa; exact WS|].
    split; [unfold wf_depot'; rewrite recp_dep; exact WD|].
    split; [unfold wf_budget, SECC; rewrite recp_acct, recp_havol, recp_sec; exact WB|].
    split; [unfold wf_big; rewrite recp_sec, recp_acct, recp_L; exact WBIG|].
    split. { (* [comment removed for export] *)
      ddestruct WX as (WX1 & WX2 & WX3 & WX4 & WX5 & WX67).
      assert (X67' : wf_x67 h').   (* [comment removed for export] *)
      { apply (wf_x67_frame_acct h h' recp_L recp_acct); [| | exact WX67].
        - intros c' Hc'. rewrite recp_reg.
          destruct ((c' =? c) && dr) eqn:E; [| split; reflexivity]. apply andb_prop in E as [E _]. apply Z.eqb_eq in E. subst c'. split; reflexivity.
        - (* [comment removed for export] *) rewrite !blocks_blk_of, recp_chunks. unfold rm_ab. apply cnt24_blk_filter. }
      split; [| split; [| split; [| rewrite recp_sec, recp_havol; split; [exact WX4| split; [exact WX5| exact X67']]]]].
      - intros c' Hc'. rewrite recp_reg, recp_carved. destruct ((c' =? c) && dr) eqn:E; [| exact (WX1 c' Hc')].
        apply andb_prop in E as [E ->]. apply Z.eqb_eq in E. subst c'. cbn [r_mapped_fa]. fold r.
        destruct f as [[|]|]; cbn [funit]; [| rewrite Z.add_0_r; exact (WX1 c Hc')| rewrite Z.add_0_r; exact (WX1 c Hc')].
        destruct (FX eq_refl) as [_ LT].
        (* [comment removed for export] *)
        assert (LE : r_nfreed r + Z.of_nat cnt <= carved h c); [| unfold kFreeArrayMapSize; lia].
        pose proof (WR c ltac:(unfold kNumClasses; lia)) as X. cbn zeta in X. ddestruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X9 & X10 & _).
        pose proof (WC c ltac:(unfold kNumClasses; lia)) as Y. cbn zeta in Y. ddestruct Y as (_ & _ & _ & _ & Y5). fold p in Y5. fold r in X9.
        unfold owned, fa_set, cache_set in X10. fold r in X10. fold p in X10.
        assert (ND2 : NoDup (r_fa r ++ pc_chunks p)).
        { replace (r_fa r ++ pc_chunks p ++ chunk_set h c ++ batch_set h c) with ((r_fa r ++ pc_chunks p) ++ (chunk_set h c ++ batch_set h c)) in X10
            by (rewrite <- ?app_assoc; reflexivity). exact (NoDup_app_remove_r _ _ X10). }
        pose proof (NoDup_codes_le (r_fa r ++ pc_chunks p) (carved h c) (class_size c / 16)
                      ltac:(apply Z.div_str_pos; pose proof (class_size_mod16 c ltac:(lia)); lia)
                      ltac:(unfold carved; apply Z.div_pos; [pose proof (WR c ltac:(unfold kNumClasses; lia)) as Z0; cbn zeta in Z0; lia| lia]) ND2) as CNT'.
        rewrite length_app, Nat2Z.inj_add in CNT'. unfold r_nfreed. destruct DR as [D1 D2]. unfold pc_count in D1.
        assert (Z.of_nat cnt <= Z.of_nat (length (pc_chunks p))) by (subst cnt; assert (max_count c / 2 <= max_count c) by (apply Z.div_le_upper_bound; lia); lia).
        enough (OK : Forall (fun q0 => exists kk, 0 <= kk < carved h c /\ q0 = kk * (class_size c / 16)) (r_fa r ++ pc_chunks p)) by (specialize (CNT' OK); lia).
        apply Forall_app. pose proof (class_size_mod16 c ltac:(lia)) as M16. pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D16.
        split; apply Forall_forall; intros x Hx.
        + destruct (proj1 (Forall_forall _ _) X9 x Hx) as (_ & kk & Hkk & E16). exists kk. split; [exact Hkk| lia].
        + destruct (proj1 (Forall_forall _ _) Y5 x Hx) as (_ & kk & Hkk & E16). exists kk. split; [exact Hkk| lia].
      - rewrite recp_tq, recp_gq. cbn [flat_map app b_elems b_pop]. rewrite HE. cbn [tl]. cbn in END. inversion END; subst. rewrite flat_map_app in *. assumption.
      - rewrite recp_cinit, CI. intros X; discriminate X. }
    unfold wf_ghost. rewrite recp_acct, recp_L. exact WG.
  Qed.

  (* [comment removed for export] *)
  #[using="p r FOK FX"] Lemma kview_recp : kview_eq (fsel h c f) h'.
  Proof.
    clear WF CI Hk STQ PRIM HB HE DR NF4 HGU. unfold kview_eq. rewrite recp_L, recp_dep, recp_sec, recp_pa, recp_acct. split; [destruct f; reflexivity|].
    split; [| destruct f; cbn; repeat split; reflexivity].
    intros c'. rewrite recp_reg. unfold fsel. destruct f as [b|].
    - cbn [h_reg h_fagrow set_reg]. unfold fupd. destruct (Z.eqb_spec c' c) as [->|NE]; cbn [andb].
      + destruct dr; cbn; [| destruct (FX ltac:(destruct FOK as [E|E]; [discriminate E| exact E])) as [D _]; discriminate D].
        destruct b; cbn; split; reflexivity || (destruct FOK as [E|E]; discriminate E).
      + split; reflexivity.
    - destruct (Z.eqb_spec c' c) as [->|NE]; cbn [andb]; [| split; reflexivity].
      destruct dr; cbn [r_mapped_user r_mapped_fa funit]; split; try reflexivity. rewrite Z.add_0_r. reflexivity.
  Qed.
End RecP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma swap_remove_mid : forall {A} (l1 : list A) x l2 lst, swap_remove (length l1) (l1 ++ x :: l2 ++ [lst]) = l1 ++ lst :: l2.
Proof.
  intros A l1 x l2 lst. unfold swap_remove.
  assert (E : l1 ++ x :: l2 ++ [lst] = (l1 ++ x :: l2) ++ [lst]) by (rewrite <- app_assoc; reflexivity).
  rewrite E, length_app. cbn [length]. rewrite Nat.add_sub, nth_error_app2, Nat.sub_diag by lia. cbn [nth_error].
  rewrite removelast_last. rewrite length_app. cbn [length].
  replace (length l1 <? length l1 + S (length l2))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  rewrite skipn_app. replace (length l1 + 1 - length l1)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity.
Qed.

#[using="Type"] Lemma swap_remove_last : forall {A} (l1 : list A) x, swap_remove (length l1) (l1 ++ [x]) = l1.
Proof.
  intros A l1 x. unfold swap_remove. rewrite length_app. cbn [length]. rewrite Nat.add_sub, nth_error_app2, Nat.sub_diag by lia. cbn [nth_error].
  rewrite removelast_last, Nat.ltb_irrefl, firstn_all, app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma nth_error_split_last : forall {A} (l : list A) i x, nth_error l i = Some x ->
  (exists l1 l2 lst, l = l1 ++ x :: l2 ++ [lst] /\ length l1 = i) \/ (exists l1, l = l1 ++ [x] /\ length l1 = i).
Proof.
  intros A l i x H. ddestruct (List.nth_error_split l i H) as (l1 & l2 & E & L).
  destruct l2 as [|y l2'] using rev_ind.
  - right. exists l1. split; [exact E| exact L].
  - left. dexists l1, l2', y. split; [exact E| exact L].
Qed.

#[using="Type"] Lemma swap_remove_perm : forall {A} (l : list A) i x, nth_error l i = Some x -> Permutation (x :: swap_remove i l) l.
Proof.
  intros A l i x H. destruct (nth_error_split_last l i x H) as [(l1 & l2 & lst & -> & <-)|(l1 & -> & <-)].
  - rewrite swap_remove_mid. eapply Permutation_trans; [| apply Permutation_middle].
    apply perm_skip. apply Permutation_app_head.
    change (lst :: l2) with ([lst] ++ l2). apply Permutation_app_comm.
  - rewrite swap_remove_last. eapply Permutation_trans; [| apply Permutation_app_comm]. apply Permutation_refl.
Qed.

#[using="Type"] Lemma swap_remove_length : forall {A} (l : list A) i x, nth_error l i = Some x -> length (swap_remove i l) = (length l - 1)%nat.
Proof.
  intros A l i x H. pose proof (Permutation_length (swap_remove_perm l i x H)) as E. cbn in E. lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma swap_remove_from : forall {A} (l : list A) i x j y, nth_error l i = Some x -> nth_error (swap_remove i l) j = Some y ->
  exists j0, j0 <> i /\ nth_error l j0 = Some y.
Proof.
  intros A l i x j y H Hj. destruct (nth_error_split_last l i x H) as [(l1 & l2 & lst & -> & <-)|(l1 & -> & <-)].
  - rewrite swap_remove_mid in Hj. destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
    + exists j. split; [lia|]. rewrite nth_error_app1 in Hj |- * by lia. exact Hj.
    + rewrite nth_error_app2 in Hj by lia. destruct (j - length l1)%nat as [|d] eqn:D; cbn [nth_error] in Hj.
      * exists (length l1 + 1 + length l2)%nat. split; [lia|]. rewrite nth_error_app2 by lia. replace (length l1 + 1 + length l2 - length l1)%nat with (S (length l2)) by lia. cbn [nth_error].
        rewrite nth_error_app2, Nat.sub_diag by lia. cbn. exact Hj.
      * exists (length l1 + 1 + d)%nat. split; [lia|]. rewrite nth_error_app2 by lia. replace (length l1 + 1 + d - length l1)%nat with (S d) by lia. cbn [nth_error].
        rewrite nth_error_app1; [exact Hj|]. apply nth_error_Some_length in Hj. exact Hj.
  - rewrite swap_remove_last in Hj. exists j. pose proof (nth_error_Some_length _ _ _ Hj) as LT. split; [lia|]. rewrite nth_error_app1 by lia. exact Hj.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma swap_remove_to : forall {A} (l : list A) i x j y, nth_error l i = Some x -> nth_error l j = Some y -> j <> i ->
  exists j', nth_error (swap_remove i l) j' = Some y.
Proof.
  intros A l i x j y H Hj NE. destruct (nth_error_split_last l i x H) as [(l1 & l2 & lst & -> & <-)|(l1 & -> & <-)].
  - rewrite swap_remove_mid. destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
    + exists j. rewrite nth_error_app1 in Hj |- * by lia. exact Hj.
    + rewrite nth_error_app2 in Hj by lia. destruct (j - length l1)%nat as [|d] eqn:D; [exfalso; lia|]. cbn [nth_error] in Hj.
      destruct (Nat.lt_ge_cases d (length l2)) as [LT2|GE2].
      * exists (length l1 + S d)%nat. rewrite nth_error_app2 by lia. replace (length l1 + S d - length l1)%nat with (S d) by lia. cbn [nth_error].
        rewrite nth_error_app1 in Hj by lia. exact Hj.
      * rewrite nth_error_app2 in Hj by lia. destruct (d - length l2)%nat as [|d'] eqn:D'; cbn [nth_error] in Hj; [| destruct d'; discriminate Hj].
        exists (length l1). rewrite nth_error_app2, Nat.sub_diag by lia. cbn. exact Hj.
  - rewrite swap_remove_last. pose proof (nth_error_Some_length _ _ _ Hj) as LT. rewrite length_app in LT. cbn in LT.
    exists j. rewrite nth_error_app1 in Hj by lia. exact Hj.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma upd_app_l : forall {X} (l r : list X) i x, (i < length l)%nat -> upd (l ++ r) i x = upd l i x ++ r.
Proof.
  intros X l. induction l as [|y l IH]; intros r [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma swap_remove_upd : ltac2:(CDefT.buildp (gd_tbl_AW_FreeR ()) "Pl,(0.$4.)Prest,(0.$4.)Pi,$2:.Px,$4.Plst,$4.P,(9.(?.$4.)(2;.$4.R5.R3.)(2<.$4.R2.))P,(9.(?.$4.)(2;.$4.R6.(2=.(16.$4.R6.)#1.))(2<.$4.R2.))(9.(0.$4.)(2>.$4.(2=.(16.$4.R7.)#1.)(2?.$4.(:.$4.R7.R6.)R5.R3.))(30.$4.R5.R7.))")
(* [comment removed for export] *).
Proof.
  intros l rest i x lst H HL. pose proof (nth_error_Some_length _ _ _ H) as IL.
  rewrite upd_app_l by exact IL.
  replace (firstn (length l - 1) (upd l i lst ++ rest)) with (firstn (length l - 1) (upd l i lst))
    by (rewrite (firstn_app (length l - 1) (upd l i lst) rest), upd_length; replace (length l - 1 - length l)%nat with 0%nat by lia; cbn [firstn]; symmetry; apply app_nil_r).
  rewrite upd_firstn_skipn by exact IL.
  destruct (nth_error_split_last l i x H) as [(l1 & l2 & lst' & E & <-)|(l1 & E & <-)].
  - assert (EL : lst' = lst).
    { rewrite E in HL. replace (l1 ++ x :: l2 ++ [lst']) with ((l1 ++ x :: l2) ++ [lst']) in HL by (rewrite <- app_assoc; reflexivity).
      rewrite length_app in HL. cbn [length] in HL. rewrite Nat.add_sub, nth_error_app2, Nat.sub_diag in HL by lia. cbn in HL. congruence. }
    subst lst'.
    replace (firstn (length l1) l) with l1 by (rewrite E, firstn_app, Nat.sub_diag, firstn_all; cbn; symmetry; apply app_nil_r).
    replace (skipn (S (length l1)) l) with (l2 ++ [lst]) by (rewrite E, skipn_app, skipn_all2 by lia; replace (S (length l1) - length l1)%nat with 1%nat by lia; reflexivity).
    replace (length l - 1)%nat with (length l1 + S (length l2))%nat by (rewrite E, length_app; cbn [length]; rewrite length_app; cbn [length]; lia).
    rewrite E, swap_remove_mid. rewrite firstn_app, firstn_all2 by lia. f_equal.
    replace (length l1 + S (length l2) - length l1)%nat with (S (length l2)) by lia. cbn [firstn]. f_equal.
    rewrite firstn_app, Nat.sub_diag, firstn_all. cbn. apply app_nil_r.
  - replace (firstn (length l1) l) with l1 by (rewrite E, firstn_app, Nat.sub_diag, firstn_all; cbn; symmetry; apply app_nil_r).
    replace (skipn (S (length l1)) l) with (@nil Z) by (rewrite E, skipn_app, skipn_all2 by lia; replace (S (length l1) - length l1)%nat with 1%nat by lia; reflexivity).
    replace (length l - 1)%nat with (length l1) by (rewrite E, length_app; cbn [length]; lia).
    rewrite E, swap_remove_last. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn. apply app_nil_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RecS.
  Variables (h : ahst) (k : chunk) (i : nat) (b0 : batch) (tb : list batch) (rest : list Z).
  Let L := h_L h.
  Let h1 := h_rec_sec h k i.
  Let h' := h_recs h k i.

  Hypothesis WF : WFR h.
  Hypothesis GEO : hgeom h.
  Hypothesis Hk : In k (h_chunks h).
  Hypothesis STQ : ck_st k = CHUNK_QUARANTINE.
  Hypothesis SEC : ck_prim k = false.
  Hypothesis NTHS : nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k))).
  Hypothesis HB : q_batches (h_tq h) = b0 :: tb.
  Hypothesis HE : b_elems b0 = ck_hdr k :: rest.
  Hypothesis HGU : forall k', In k' (h_chunks h) -> k' <> k -> ck_hdr k' = ck_hdr k -> False.

  Local Ltac clr := clear WF GEO Hk STQ SEC NTHS HB HE HGU.
  #[using="Type"] Lemma recs_L : h_L h' = h_L h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_chunks : h_chunks h' = rm_ab (ck_ab k) (h_chunks h). Proof. clr. reflexivity. Qed.
  #[using="HB"] Lemma recs_tq : q_batches (h_tq h') = b_pop b0 :: tb. Proof. clear WF GEO Hk STQ SEC NTHS HE HGU. subst h'. unfold h_recs, h_popq. cbn. rewrite HB. reflexivity. Qed.
  #[using="Type"] Lemma recs_gq : h_gq h' = h_gq h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_dep : h_dep h' = h_dep h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_reg : forall c', h_reg h' c' = h_reg h c'. Proof. clr. intros; reflexivity. Qed.
  #[using="Type"] Lemma recs_cache : forall c', h_cache h' c' = h_cache h c'. Proof. clr. intros; reflexivity. Qed.
  #[using="Type"] Lemma recs_cinit : h_cinit h' = h_cinit h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_pa : h_pa_committed h' = h_pa_committed h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_ia : h_ia h' = h_ia h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_fake : h_fake h' = h_fake h. Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_havol : h_havol h' = h_havol h. Proof. clr. reflexivity. Qed.
    #[using="Type"] Lemma recs_secl : s_chunks (h_sec h') = swap_remove i (s_chunks (h_sec h)). Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_nres : s_nres (h_sec h') = s_nres (h_sec h). Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_acct : a_sech (h_acct h') = (ck_map_beg k, ck_map_size k) :: a_sech (h_acct h). Proof. clr. reflexivity. Qed.
  #[using="Type"] Lemma recs_carved : forall c', carved h' c' = carved h c'. Proof. clr. intros; reflexivity. Qed.
  
  #[using="hAR WF Hk SEC"] Lemma chunk_set_sameS : forall c', chunk_set h' c' = chunk_set h c'.
  Proof.
    intros c'. unfold chunk_set. rewrite recs_chunks, recs_L. f_equal.
    dpose WF as (_ & _ & _ & (_ & ND & _) & _). pose proof Hk as HK0. pose proof SEC as P0. clear - ND HK0 P0. revert ND HK0.
    induction (h_chunks h) as [|x l IH]; intros ND HK0; [reflexivity|]. rewrite rm_ab_cons. cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
    destruct HK0 as [->|HK1].
    - rewrite Z.eqb_refl. cbn [filter]. rewrite P0. cbn [andb]. rewrite rm_ab_notin; [reflexivity| exact NI].
    - destruct (Z.eqb_spec (ck_ab x) (ck_ab k)) as [E|NE].
      + exfalso. apply NI. rewrite E. apply in_map. exact HK1.
      + cbn [filter]. rewrite (IH ND' HK1). reflexivity.
  Qed.

  #[using="b0 tb HB"] Lemma batch_set_sameS : forall c', batch_set h' c' = batch_set h c'.
  Proof. intros c'. unfold batch_set. rewrite recs_tq, recs_gq, recs_L, HB. cbn [map app b_addr b_pop]. reflexivity. Qed.

  #[using="hAR b0 tb WF Hk SEC HB"] Lemma owned_sameS : forall c', owned h' c' = owned h c'.
  Proof. intros c'. unfold owned, fa_set, cache_set. rewrite recs_reg, recs_cache, chunk_set_sameS, batch_set_sameS. reflexivity. Qed.

  #[using="Type"] Lemma kview_recs : kview_eq h1 h'.
  Proof. clr. unfold kview_eq. repeat split; reflexivity. Qed.

  #[using="hAR WF Hk"] Lemma other_chunk_keptS : forall k', In k' (h_chunks h) -> k' <> k -> In k' (h_chunks h').
  Proof.
    intros k' Hk' NE. rewrite recs_chunks. apply rm_ab_In. split; [exact Hk'|]. intros EA. apply NE.
    dpose WF as (_ & _ & _ & (_ & ND & _) & _). exact (NoDup_map_inj ck_ab _ _ _ ND Hk' Hk EA).
  Qed.
  #[using="hAR WF Hk"] Lemma elem_chunk_keptS : forall e k', In k' (h_chunks h) -> ck_hdr k' = e -> e <> ck_hdr k -> In k' (h_chunks h').
  Proof. intros e k' Hk' He NE. apply other_chunk_keptS; [exact Hk'|]. intros ->. exact (NE (eq_sym He)). Qed.

  #[using="hAR WF Hk"] Lemma wf_batch_keptS : forall b, wf_batch h b -> (forall e, In e (b_elems b) -> e <> ck_hdr k) -> wf_batch h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4); intros NE). dpose WF as (_ & _ & _ & (_ & ND & _) & _).
    split; [exact B1|]. split; [| split].
    - rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. rewrite recs_chunks.
      rewrite (find_rm_other (fun k0 => ck_hdr k0 =? e) (h_chunks h) k Hk ND); [reflexivity|]. apply Z.eqb_neq. intros E. exact (NE e He (eq_sym E)).
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k' & Hk' & S' & H').
      exists k'. split; [exact (elem_chunk_keptS e k' Hk' H' (NE e He))| split; [exact S'| exact H']].
    - rewrite recs_carved, recs_L. exact B4.
  Qed.

  #[using="hAR WF Hk"] Lemma wf_batch_r_keptS : forall b, wf_batch_r h b -> (forall e, In e (b_elems b) -> e <> ck_hdr k) -> wf_batch_r h' b.
  Proof.
    (intros b dd_H; ddestruct dd_H as (B1 & B3 & B4); intros NE). split; [exact B1|]. split.
    - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k' & Hk' & S' & H').
      exists k'. split; [exact (elem_chunk_keptS e k' Hk' H' (NE e He))| split; [exact S'| exact H']].
    - rewrite recs_carved, recs_L. exact B4.
  Qed.

  #[using="hAR b0 WF HB HE"] Lemma elems_nodupS : NoDup ((ck_hdr k :: rest) ++ flat_map b_elems (tb ++ q_batches (h_gq h))).
  Proof.
    dpose WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & WX2 & _) & _) || dpose WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [_ WX2] & _).
    revert WX2. rewrite HB. cbn [flat_map app]. rewrite HE, flat_map_app. intros X. exact X.
  Qed.

  #[using="b0 tb rest WF GEO Hk SEC NTHS HB HE HGU"] Theorem WFR_recs : WFR h'.
  Proof.
    dpose WF as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    dpose WK as (WKF & ND & WKSEC). dpose WS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (KN & KST & KP & KX). rewrite SEC in KX. ddestruct KX as (i0 & N0 & MB4 & MB0 & MBH & MBL).
    pose proof (proj1 (Forall_forall _ _) S8 _ (nth_error_In _ _ NTHS)) as (SZ4 & SZB & SS0). cbn [s_map_size s_size] in SZ4, SZB, SS0.
    pose proof elems_nodupS as END.
    pose proof (swap_remove_perm (s_chunks (h_sec h)) i _ NTHS) as PERM.
    split; [rewrite recs_L; exact WL|].
    split. { (* [comment removed for export] *) intros c' Hc'. cbn zeta. rewrite recs_cinit, recs_cache, recs_carved. exact (WC c' Hc'). }
    split. { (* [comment removed for export] *) intros c' Hc'. cbn zeta. rewrite recs_reg, recs_carved, owned_sameS. exact (WR c' Hc'). }
    split. { (* [comment removed for export] *)
      split; [| split].
      - apply Forall_forall. intros k' Hk'. rewrite recs_chunks in Hk'. apply rm_ab_In in Hk' as [Hk' NA].
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (X1 & X2 & X3 & X4). unfold wf_chunk'. rewrite recs_carved, recs_L, recs_secl.
        split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. destruct (ck_prim k'); [exact X4|].
        ddestruct X4 as (j & Nj & R4). destruct (Nat.eq_dec j i) as [->|NE].
        { exfalso. rewrite NTHS in Nj. apply NA. unfold ck_map_beg in Nj. injection Nj as E1 E2 E3. lia. }
        destruct (swap_remove_to _ i _ j _ NTHS Nj NE) as [j' Nj']. exists j'. split; [exact Nj'| exact R4].
      - rewrite recs_chunks. ddestruct (rm_ab_split (h_chunks h) k Hk ND) as (l1 & l2 & E1 & E2). rewrite E2. rewrite E1 in ND. exact (NoDup_map_app_mid _ _ _ _ ND).
      - rewrite recs_secl. intros j sh Hj. destruct (swap_remove_from _ i _ j sh NTHS Hj) as (j0 & NE & Hj0).
        ddestruct (WKSEC j0 sh Hj0) as (k' & Hk' & P' & R' & Q'). exists k'. split; [| exact (conj P' (conj R' Q'))].
        apply other_chunk_keptS; [exact Hk'|]. intros ->.
        (* [comment removed for export] *)
        apply NE. apply (proj1 (NoDup_nth_error (map s_map_beg (s_chunks (h_sec h)))) S7 j0 i).
        + rewrite length_map. exact (nth_error_Some_length _ _ _ Hj0).
        + rewrite !nth_error_map, Hj0, NTHS. cbn. rewrite R'. reflexivity. }
    split. { (* [comment removed for export] *)
      ddestruct WQ as (WT & WGQ & NDA & UQ). rewrite HB in WT. destruct WT as [WB0 WTB].
      assert (NE0 : forall e, In e rest -> e <> ck_hdr k).
      { intros e He ->. cbn in END. inversion END as [|? ? NI _]; subst. apply NI. apply in_app_iff. left. exact He. }
      assert (NEG : forall b e, In b (tb ++ q_batches (h_gq h)) -> In e (b_elems b) -> e <> ck_hdr k).
      { intros b e Hb He ->. cbn in END. inversion END as [|? ? NI _]; subst. apply NI. apply in_app_iff. right. apply in_flat_map. exists b. split; assumption. }
      split; [| split; [| split]].
      - rewrite recs_tq. split.
        + ddestruct WB0 as (B1 & B2 & B3). split; [unfold b_count in *; cbn [b_elems b_pop]; rewrite HE in B1 |- *; cbn [tl]; cbn [length] in B1; lia|].
          split.
          * cbn [b_elems b_pop]. rewrite HE. cbn [tl]. apply Forall_forall. intros e He.
            rewrite HE in B2. inversion B2 as [|? ? _ B2']; subst. destruct (proj1 (Forall_forall _ _) B2' e He) as (k' & Hk' & S' & H').
            exists k'. split; [exact (elem_chunk_keptS e k' Hk' H' (NE0 e He))| split; [exact S'| exact H']].
          * rewrite recs_carved, recs_L. cbn [b_addr b_pop]. exact B3.
        + apply Forall_forall. intros b Hb. apply wf_batch_r_keptS; [exact (proj1 (Forall_forall _ _) WTB b Hb)|].
          intros e He. apply (NEG b e); [apply in_app_iff; left; exact Hb| exact He].
      - rewrite recs_gq. ddestruct WGQ as (G1 & G2 & G3). split; [| exact (conj G2 G3)].
        apply Forall_forall. intros b Hb. apply wf_batch_keptS; [exact (proj1 (Forall_forall _ _) G1 b Hb)|].
        intros e He. apply (NEG b e); [apply in_app_iff; right; exact Hb| exact He].
      - rewrite recs_tq, recs_gq. rewrite HB in NDA. cbn [map app b_addr b_pop] in *. exact NDA.
      - intros k' Hk' S'. rewrite recs_tq, recs_gq. rewrite recs_chunks in Hk'. apply rm_ab_In in Hk' as [Hk' NA].
        assert (NK : k' <> k) by (intros ->; exact (NA eq_refl)).
        assert (NH : ck_hdr k' <> ck_hdr k) by (intros E; exact (HGU k' Hk' NK E)).
        ddestruct (UQ k' Hk' S') as (b & [Hb Hin] & U). rewrite HB in Hb.
        destruct Hb as [<-|Hb].
        + exists (b_pop b0). split.
          * split; [left; reflexivity|]. cbn [b_elems b_pop]. rewrite HE in Hin |- *. cbn [tl]. destruct Hin as [E|Hin]; [exfalso; exact (NH (eq_sym E))| exact Hin].
          * intros b' [Hb' Hin']. destruct Hb' as [<-|Hb']; [reflexivity|]. exfalso.
            assert (b0 = b') by (apply U; rewrite HB; cbn [app]; split; [right; exact Hb'| exact Hin']). subst b'.
            rewrite HB in NDA. cbn in NDA. inversion NDA as [|? ? NI _]; subst. apply NI. rewrite <- ?map_app. apply in_map. exact Hb'.
        + exists b. split.
          * split; [right; exact Hb| exact Hin].
          * intros b' [Hb' Hin']. destruct Hb' as [<-|Hb']; [| apply U; rewrite HB; cbn [app]; split; [right; exact Hb'| exact Hin']].
            exfalso. cbn [b_elems b_pop] in Hin'. rewrite HE in Hin'. cbn [tl] in Hin'.
            assert (b = b0) by (apply U; rewrite HB; cbn [app]; split; [left; reflexivity| rewrite HE; right; exact Hin']). subst b.
            rewrite HB in NDA. cbn in NDA. inversion NDA as [|? ? NI _]; subst. apply NI. rewrite <- ?map_app. apply in_map. exact Hb. }
    split. { (* [comment removed for export] *)
      unfold wf_sec. rewrite recs_secl, recs_nres, recs_pa. rewrite (swap_remove_length _ i _ NTHS).
      pose proof (nth_error_Some_length _ _ _ NTHS) as IL.
      split; [lia|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|]. split; [exact S5|]. split; [lia|]. split.
      - apply (Permutation_map s_map_beg) in PERM. cbn [map] in PERM. pose proof (Permutation_NoDup (Permutation_sym PERM) S7) as X. inversion X; assumption.
      - apply Forall_forall. intros sh Hsh. apply (proj1 (Forall_forall _ _) S8). eapply Permutation_in; [exact PERM| right; exact Hsh]. }
    split; [unfold wf_depot'; rewrite recs_dep; exact WD|].
    split. { (* [comment removed for export] *)
      unfold wf_budget, SECC. rewrite recs_acct, recs_havol, recs_secl. ddestruct WB as (GWF & HV0 & SECB). split; [| split; [exact HV0|]].
      - constructor; [cbn [fst snd]; lia| exact GWF].
      - unfold SECC in SECB. pose proof (Permutation_map sec_cost_live PERM) as P2. cbn [map] in P2.
        assert (SUM : forall l l' : list Z, Permutation l l' -> sum l = sum l').
        { clear. intros l l' P. induction P; unfold sum in *; cbn [fold_right] in *; lia. }
        rewrite <- (SUM _ _ P2) in SECB. cbn [sum fold_right map] in SECB |- *. unfold sec_cost_live at 1 in SECB. unfold sec_cost_ghost at 1. cbn [s_map_size fst snd] in SECB |- *.
        unfold sum in *. lia. }
    split. { (* [comment removed for export] *)
      unfold wf_big. rewrite recs_secl, recs_acct, recs_L. ddestruct WBIG as (BG1 & BG2 & BG3 & BG4). split; [| split; [| exact (conj BG3 BG4)]].
      - apply Forall_forall. intros sh Hsh. apply (proj1 (Forall_forall _ _) BG1). eapply Permutation_in; [exact PERM| right; exact Hsh].
      - constructor; [| exact BG2]. cbn [snd]. pose proof (proj1 (Forall_forall _ _) BG1 _ (nth_error_In _ _ NTHS)) as X. cbn in X. exact X. }
    split. { (* [comment removed for export] *)
      ddestruct WX as (WX1 & WX2 & WX3 & WX4 & WX5 & WX6 & WX7 & WX8 & WX9).
      split; [| split; [| split; [| rewrite recs_secl, recs_nres, recs_havol, (swap_remove_length _ i _ NTHS); split; [clear - WX4; lia| split; [exact WX5| split; [exact WX6| split; [exact WX7| split; [exact WX8|]]]]]]]].
      4:{ (* [comment removed for export] *) rewrite !blocks_blk_of, recs_chunks. unfold rm_ab. eapply Z.le_trans; [apply cnt24_blk_filter| exact WX9]. }
      - intros c' Hc'. rewrite recs_reg, recs_carved. exact (WX1 c' Hc').
      - rewrite recs_tq, recs_gq. cbn [flat_map app b_elems b_pop]. rewrite HE. cbn [tl]. cbn in END. inversion END; subst. rewrite flat_map_app in *. assumption.
      - rewrite recs_cinit. intros X c' Hc'. rewrite recs_reg. exact (WX3 X c' Hc'). }
    (* [comment removed for export] *)
    unfold wf_ghost. rewrite recs_acct, recs_L. constructor; [| exact WG]. cbn [fst snd].
    pose proof (z_sec_hull h GEO i _ NTHS) as Y1. pose proof (z_sec_pa h GEO i _ NTHS) as Y2. unfold zapart in Y1, Y2. cbn [fst snd s_map_beg s_map_size] in Y1, Y2.
    unfold lowhigh in *.   (* [comment removed for export] *)
    repeat split; try assumption; try lia.
  Qed.
End RecS.

End ARUN_1.
