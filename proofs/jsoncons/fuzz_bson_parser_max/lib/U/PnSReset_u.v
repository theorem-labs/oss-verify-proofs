(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMSRS.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

(* [comment removed for export] *)
Lemma elem_of_In (x : Z) (l : list Z) : In x l -> x ∈ l.
Proof. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_app (l1 l2 : list (Z * Z)) B1 m1 B2 m2 :
  NoDup (map fst (l1 ++ l2)) -> In (B1, m1) l1 -> In (B2, m2) l2 -> B1 <> B2.
Proof.
  induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
  destruct H1 as [->|H1].
  - cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
  - apply IH; assumption.
Qed.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma own_nodup (s : PM.pst) LBX : NoDup (map fst (PM.parser_own s ++ LBX)) ->
  PM.sr_qc (PM.p_src s) <> PM.p_b s /\ (forall c n p, PM.p_tb s = PM.VLong c n p -> PM.sr_qc (PM.p_src s) <> p /\ PM.p_b s <> p).
Proof.
  intros ND. unfold PM.parser_own, PM.src_own, PM.vec_own in ND. cbn [app map fst] in ND.
  inversion ND as [|x l NI ND1]. subst x l. inversion ND1 as [|x l NI1 ND2]. subst x l.
  split.
  - intros E. apply NI. rewrite E. apply elem_of_In. left. reflexivity.
  - intros c n p TB. rewrite TB in NI, NI1. cbn [PM.vs_own app map fst] in NI, NI1. split.
    + intros E. apply NI. rewrite E. apply elem_of_In. right. left. reflexivity.
    + intros E. apply NI1. rewrite E. apply elem_of_In. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma reset_post segs A M M1 op ois (s : PM.pst) (P : Z -> Prop) :
  PM.parser_at segs A PMSP.T3 PMSP.T4 M op ois s -> (1 <= length (PM.p_stk s))%nat ->
  0 <= op -> op + 384 <= 2 ^ 64 -> 0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mem_grows M M1 ->
  (forall i, (op <= i < op + 8 \/ op + 16 <= i < op + 336 \/ op + 360 <= i < op + 368 \/ op + 376 <= i < op + 384
              \/ PM.sr_qc (PM.p_src s) <= i < PM.sr_qc (PM.p_src s) + PM.CHUNK) -> ~ P i) ->
  L5.u8_at segs M1 (op + 8) 1 -> L5.u8_at segs M1 (op + 8 + 1) 0 -> L5.u32_at segs M1 (op + 12) 0 ->
  L5.u64_at segs M1 (op + 368) (PM.p_b s + 32) ->
  L5.u32_at segs M1 (PM.p_b s) 0 -> L5.u64_at segs M1 (PM.p_b s + 8) 0 -> L5.u8_at segs M1 (PM.p_b s + 16) 0 -> L5.u64_at segs M1 (PM.p_b s + 24) 0 ->
  PM.vstr_at segs PMSP.T3 M1 (op + 336) (PM.p_tb (PMSP.pst_reset s)) ->
  PM.parser_at segs A PMSP.T3 PMSP.T4 M1 op ois (PMSP.pst_reset s).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) LEN Ho Ho' Hq Hq' FRZ MG AV
         C8 C9 C12 C368 E0 E8 E16 E24 TB1.
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
  assert (DG : forall a n, L5.defined M a n -> L5.defined M1 a n) by (intros a n Dn i Hi; apply MG; apply Dn; exact Hi).
  unfold PM.parser_at. cbn [PMSP.pst_reset PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H0]|].
  split; [apply DG; exact D|]. split; [exact I|]. split; [exact C8|]. split; [replace (op + 9) with (op + 8 + 1) by lia; exact C9|].
  split; [exact C12|].
  split; [apply (L5C.u8_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H20]|].
  split; [apply (PMF.nullis_at_agree segs A M M1); [lia|lia| apply AG; [lia|lia| intros i Hi; apply AV; lia]| exact NI]|].
  split; [apply (PMF.src_fields_at_agree segs M M1 (op + 24) ois (ois + 16) (PM.p_src s)); [lia|lia|exact Hq|exact Hq'| apply AG; [lia|lia| intros i Hi; apply AV; lia]
                                                    | apply AG; [lia|lia| intros i Hi; apply AV; lia]| exact SRC]|].
  split; [apply (PMF.u32_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H328]|].
  split; [exact I|]. split; [exact TB1|].
  split; [| split; [right; reflexivity|]; split; [left; reflexivity|]; unfold PM.MAX_DEPTH; lia].
  destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
  pose proof (PM.pow2_pos (PM.p_k s) ltac:(lia)) as P2k.
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact V0]|].
  split; [cbn [length]; replace (PM.p_b s + 32 * Z.of_nat 1) with (PM.p_b s + 32) by lia; replace (op + 360 + 8) with (op + 368) by lia; exact C368|].
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact V16]|].
  split; [exact Hk|]. split; [cbn [length]; lia|]. split; [exact Hal|].
  split; [apply DG; exact DB|]. split; [exact I|]. split; [exact I|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth Z.of_nat].
  unfold PM.pstate_at, PM.ps_root. cbn [PM.ps_mode PM.ps_len PM.ps_type PM.ps_idx]. rewrite Z.add_0_r.
  split; [exact E0|]. split; [exact E8|]. split; [exact E16| exact E24].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Lemma blocks_apart_heap LB cr M VM B1 m1 B2 m2 :
  hi_heap HI LB cr M VM -> In (B1, m1) LB -> In (B2, m2) LB -> B1 <> B2 -> B1 + m1 <= B2 \/ B2 + m2 <= B1.
Proof.
  intros HH H1 H2 NE. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B1, m1) H1) as (_ & _ & AP). cbn [fst snd] in AP.
  apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma heap_nodup LB cr M VM : hi_heap HI LB cr M VM -> NoDup (map fst LB).
Proof. intros HH. exact (proj1 (proj2 (hio_wf L SCFG HI HIok LB cr M VM HH))). Qed.
(* [comment removed for export] *)
Lemma own_not_in LB1 LB2 cr M VM B m a : hi_heap HI (LB1 ++ LB2) cr M VM -> In (B, m) LB1 -> B <= a < B + m -> ~ in_block LB2 a.
Proof.
  intros HH Hin Ha ((B2 & m2) & HX & Hr). cbn [fst snd] in Hr.
  assert (NE : B <> B2) by (apply (fst_neq_app LB1 LB2 B m B2 m2 (heap_nodup _ _ _ _ HH) Hin HX)).
  destruct (blocks_apart_heap _ _ _ _ B m B2 m2 HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror HX)) NE); lia.
Qed.
(* [comment removed for export] *)
Lemma own_not_client LB1 LB2 cr M VM B m a sp scr :
  hi_heap HI (LB1 ++ LB2) cr M VM -> In (B, m) LB1 -> B <= a < B + m -> ~ client_addr L LB2 sp scr a.
Proof.
  intros HH Hin Ha [IB|[[S1 _]|[IM _]]].
  - exact (own_not_in LB1 LB2 cr M VM B m a HH Hin Ha IB).
  - destruct (PMFR.brange_of_heap L HI HIok _ LB1 cr M VM HH (fun x H => in_or_app _ _ _ (or_introl H)) B m Hin) as (_ & _ & Q4). lia.
  - destruct (PMFR.brange_of_heap L HI HIok _ LB1 cr M VM HH (fun x H => in_or_app _ _ _ (or_introl H)) B m Hin) as (_ & Q1 & _). lia.
Qed.

(* [comment removed for export] *)

End WithHeap.
End PMSRS.
