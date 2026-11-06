(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Agenxn8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asancq9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Back4sr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.NoRey4t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan Asanqlm.

Module Asann85.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanz3l AsanPlan Asanqlm.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
(* [comment removed for export] *)
End Iface.
End Asann85.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang2p.Asann85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Asanrb8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanwqd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module Asanku0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require StoreOk ShapeAlg SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require MmapSim AsanAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Agenxn8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asanbbl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Asancq9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.Back4sr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanwqd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanwqd.Asanrb8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AxSyqqh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanz3l AsanPlan Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec.AsanCeil.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lit_diff_sound : forall E e f d,
  lit_diff e f = Some d ->
  0 <= d < two64 /\ (bv_unsigned (edenot E e) - bv_unsigned (edenot E f)) mod two64 = d.
Proof.
  intros E e f d H. unfold lit_diff in H.
  pose proof (mkAlu_denot E ALU_SUB e f) as D. unfold esub in H.
  destruct (mkAlu ALU_SUB e f) eqn:Hm; try discriminate. injection H as <-.
  cbn [edenot] in D. apply (f_equal bv_unsigned) in D. rewrite u_sub64 in D. rewrite u_lit64 in D.
  split; [apply Z.mod_pos_bound; unfold two64; lia|]. unfold two64 in *. rewrite <- D. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma page_aligned_sound : forall SEGS E M k e,
  know_ok SEGS E M k -> page_aligned k e = true -> bv_unsigned (edenot E e) mod 4096 = 0.
Proof.
  intros SEGS E M k e HK H. unfold page_aligned in H.
  assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
  { intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr Hdiv]. apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [|exact Hdiv]. change 4096 with (2 ^ 12). apply pow2_divide_le. lia. }
  destruct e; try (apply GEN; apply Z.leb_le; exact H).
  apply Z.eqb_eq in H. cbn [edenot]. rewrite u_lit64. unfold two64.
  rewrite Z.mod_mod_divide; [exact H|]. exists (2 ^ 52). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_false_of_overlap : forall L (lo n a sz : word),
  In (a, sz) L -> iv_overlap lo n a sz = true -> region_free L lo n = false.
Proof.
  intros L lo n a sz Hin Hov. induction L as [|[a' sz'] L IH]; [destruct Hin|].
  cbn [region_free]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite Hov. reflexivity.
  - rewrite (IH Hin). apply andb_false_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_refuted : forall m d (a sz : word),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d + page_size < 2 ^ 64)%Z ->  (* [comment removed for export] *)
  In (a, sz) (vm_reserved h ++ vm_maps h) ->
  (bv_unsigned b < bv_unsigned a + bv_unsigned sz)%Z -> (bv_unsigned a < bv_unsigned b + d)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = false.
Proof.
  intros m d a sz h b Hbal Hdal Hd Hb0 Hnw Hin Hov1 Hov2.
  unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia.
  rewrite (region_free_false_of_overlap _ b (Z_to_bv 64 (d + page_size)) a sz Hin).
  - rewrite andb_false_r. reflexivity.
  - unfold iv_overlap. rewrite (u64_lit (d + page_size)) by (unfold page_size in *; lia).
    assert (Hov2' : (bv_unsigned a < bv_unsigned b + (d + page_size))%Z) by (unfold page_size in *; lia).
    rewrite (proj2 (Z.ltb_lt _ _) Hov1), (proj2 (Z.ltb_lt _ _) Hov2'). reflexivity.
Qed.

Lemma sum_sizes_app : forall l1 l2, sum_sizes (l1 ++ l2) = sum_sizes l1 + sum_sizes l2.
Proof. intros l1 l2. induction l1 as [|iv l1 IH]; cbn [sum_sizes app]; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma Some_pair_inj : forall {T U : Type} (a c : T) (b d : U), Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof. intros T U a c b d H. split; congruence. Qed.

Lemma zfill_in : forall (b l : word) m (x : word),
  bv_unsigned b <= bv_unsigned x < bv_unsigned b + bv_unsigned l ->
  zfill b l m x = Some (Z_to_bv 8 0).
Proof.
  intros b l m x Hx. unfold zfill, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_cons : forall z (a n : word) l,
  in_ivs z ((a, n) :: l) = (((bv_unsigned a <=? z) && (z <? bv_unsigned a + bv_unsigned n)) || in_ivs z l)%bool.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (iv_disjoint p) l /\ seps l.
Proof. intros p l H. inversion H; subst; auto. Qed.

Lemma seps_In_disjoint : forall l p q,
  seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) -> In p l -> In q l -> p <> q -> iv_disjoint p q.
Proof.
  induction l as [|h t IH]; intros p q Hs Hpos Hp Hq Hne; [destruct Hp|].
  apply seps_cons_inv in Hs as [Hf Ht].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - exfalso. exact (Hne eq_refl).
  - exact (proj1 (Forall_forall _ _) Hf q Hq).
  - pose proof (proj1 (Forall_forall _ _) Hf p Hp) as D. unfold iv_disjoint in *. lia.
  - apply IH; auto. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

Lemma seps_NoDup : forall l, seps l -> (forall iv, In iv l -> 0 < bv_unsigned (snd iv)) -> List.NoDup l.
Proof.
  induction l as [|h t IH]; intros Hs Hpos; [constructor|].
  apply seps_cons_inv in Hs as [Hf Ht]. constructor.
  - intros Hin. pose proof (proj1 (Forall_forall _ _) Hf h Hin) as D. pose proof (Hpos h (or_introl eq_refl)). unfold iv_disjoint in D. lia.
  - apply IH; [exact Ht|]. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.

Section SoundB.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis RES_cover : APS.res_cover_ok SEGS A.
Hypothesis SHADOW_val : APS.shadow_val_ok A.
Hypothesis NX0_ok : APS.nx0_ok nx0.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
Hypothesis RES_len : APS.res_len_ok SEGS A.   (* [comment removed for export] *)

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Let free_apart_hull' := Asanwqd.free_apart_hull SEGS A RES_len HULL_ok RES_cover.
Let grant_cs1_ok' := Asanwqd.grant_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_frame SHADOW_val argH_top.
Let kdisj_new_ok' := Asanwqd.kdisj_new_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok RES_cover SHADOW_val.
Let regs_ok_regupd_same' := Asanwqd.regs_ok_regupd_same SEGS A RES_len.
Let grant_new_facts' := Asanwqd.grant_new_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok argH_top.

(* [comment removed for export] *)
Theorem node_exit_sound : exit_stmt SEGS A LIMIT SINV argH FS0.
Proof.
  intros cs code E R FULL model HC Hec Hn.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_1; dand5 dR_1 as Hpc0 Hpc4 w HF HE | destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE) ]).
  unfold node_exit in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 10) as [c0|] eqn:H10.
  2:{ destruct a7; try discriminate; repeat (destruct p; try discriminate). }
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 c0 HC ltac:(lia) H10) as [G10 Hc0].
  assert (H94 : (a7 = 94 \/ a7 = 93) /\ code = Z.land c0 255).
  { destruct a7 as [|p|p]; try discriminate;
      repeat (destruct p as [p|p|]; try discriminate); injection Hn as <-; auto. }
  destruct H94 as [Ha7 ->].
  assert (G17 : getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94 \/ getr R (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 93).
  { destruct Ha7 as [-> | ->].
    - left. exact (proj1 (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 94 HC ltac:(lia) H17)).
    - right. exact (proj1 (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 93 HC ltac:(lia) H17)). }
  unfold cfg_of. rewrite <- (bv_and_255 c0 Hc0).
  eapply srz_exit_at_lazy; [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact G10].
Qed.


(* [comment removed for export] *)
#[using="NX0_ok SINV_agree argH_agree"] Theorem node_sys_sound_YSetTid : sys_stmt SEGS A nx0 LIMIT SINV argH FS0 YSetTid.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_2; dand5 dR_2 as Hpc0 Hpc4 w HF HE | destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE) ]).
  cbn [node_sys] in Hn. unfold node_settid in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (negb (a_tidset cs) && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hts Hfresh]. apply negb_true_iff in Hts.
  apply Some_inj in Hn. rename Hn into Ecs'.
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 96 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_tid _ _ _ _ _ _ _ _ _ _ _ HC Hts) as Htid.
  (first [ pose proof ((fresh_ok_parts nx0 cs Hfresh)) as dR_3; dand7 dR_3 as Fsr Fkn Fmaps Fallow Fbrk Ffd Fle | destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle) ]).
  unfold cfg_of.
  eapply (srz_set_tid_lazy SEGS); [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact G17 | exact Htid |].
  intros tid Htidr.
  set (v := nxt cs) in *.
  set (E' := ext1 E v tid).
  assert (Hag : env_agree v E E') by apply (ext1_agree).
  pose proof (cs_ok_agree SEGS A nx0 LIMIT NX0_ok SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
  rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
  replace (pc cs + 4) with (pc cs') by (rewrite <- Ecs'; reflexivity).
  apply (Hk E' (regupd R 10 tid) FULL (with_tid tid model)).
  - split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
  - (* [comment removed for export] *)
    assert (Hv : edenot E' (EVar v) = tid) by (cbn [edenot]; unfold E'; apply ext1_at).
    assert (HMr : Mr A argH E' cs' (with_tid tid model) FULL = Mr A argH E' cs model FULL).
    { unfold Mr. f_equal. apply functional_extensionality. intros a. rewrite <- Ecs'.
      unfold hid, vis, in_allow, in_vis, in_sh. reflexivity. }
    assert (HA : allowA A E' cs' = allowA A E' cs) by (rewrite <- Ecs'; reflexivity).
    subst cs'.
    destruct HC'; constructor; rewrite ?HMr, ?HA;
      cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next];
      try assumption; try reflexivity; try discriminate.
    + (* [comment removed for export] *) apply (regs_ok_set_n); [exact co_regs0 | lia | exact Hv].
    + (* [comment removed for export] *) constructor; [|exact co_know0].
      cbn [kentry_ok]. rewrite Hv. unfold PID_MAX. unfold PID_MAX_ENVELOPE in Htidr. lia.
    + (* [comment removed for export] *) destruct co_minv0; constructor; assumption.
  - reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="SINV_frame"] Lemma brk_keep_ok : forall E cs R FULL model,
  cs_ok E cs R FULL model ->
  cs_ok E (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) (regupd R 10 (vm_brk (m_vmmaps model))) FULL model.
Proof.
  intros E cs R FULL model HC.
  change (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4))
    with (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs (a_ss cs)) 10 (a_brk cs)) (kn cs) (nxt cs))).
  eapply (cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0);
    [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC)
    | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
  cbn [mk_ss s_regs]. apply (regs_ok_set_n);
    [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | symmetry; exact (co_brk _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.

(* [comment removed for export] *)
Lemma brk_req_sound : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_req cs = Some d ->
  0 < d /\ d mod 4096 = 0 /\ d <= 2 ^ 40 /\
  (bv_unsigned (edenot E (reg cs 10)) - bv_unsigned (vm_brk (m_vmmaps model))) mod two64 = d.
Proof.
  intros E cs R FULL model d HC H. unfold brk_req in H.
  destruct (lit_diff (reg cs 10) (a_brk cs)) as [d0|] eqn:Hld; [|discriminate].
  destruct (Z.ltb 0 d0 && Z.eqb (d0 mod 4096) 0 && Z.leb d0 (2 ^ 40))%bool eqn:Hc; [|discriminate].
  injection H as <-.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3.
  destruct (lit_diff_sound E _ _ _ Hld) as [_ Hm].
  rewrite (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). auto.
Qed.

(* [comment removed for export] *)
Lemma brk_base_ok_sound : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_base_ok A cs d = true ->
  let b := vm_brk (m_vmmaps model) in
  bv_unsigned b mod 4096 = 0 /\ 0 < bv_unsigned b /\ img_hi A <= bv_unsigned b /\ bv_unsigned b + d <= KHI.
Proof.
  intros E cs R FULL model d HC H b. unfold brk_base_ok in H.
  apply andb_prop in H as [Hal H].
  destruct (xlo (kn cs) (a_brk cs)) as [lo|] eqn:Hlo; [|discriminate].
  destruct (xhi (kn cs) (a_brk cs)) as [hi|] eqn:Hhi; [|discriminate].
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H0 Hi].
  apply Z.ltb_lt in H0. apply Z.leb_le in Hi. apply Z.leb_le in Hk.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hlo) as L.
  pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hhi) as Hh.
  pose proof (page_aligned_sound SEGS E _ (kn cs) _ HK Hal) as P.
  rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) in L, Hh, P. unfold b. lia.
Qed.

(* [comment removed for export] *)
Lemma brk_req_val : forall E cs R FULL model d,
  cs_ok E cs R FULL model -> brk_req cs = Some d -> brk_base_ok A cs d = true ->
  getr R (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (vm_brk (m_vmmaps model)) + d).
Proof.
  intros E cs R FULL model d HC Hr Hb.
  (first [ pose proof ((brk_req_sound E cs R FULL model d HC Hr)) as dR_4; dand4 dR_4 as D1 D2 D3 Dm | destruct (brk_req_sound E cs R FULL model d HC Hr) as (D1 & D2 & D3 & Dm) ]).
  (first [ pose proof ((brk_base_ok_sound E cs R FULL model d HC Hb)) as dR_5; dand4 dR_5 as B1 B2 B3 B4 | destruct (brk_base_ok_sound E cs R FULL model d HC Hb) as (B1 & B2 & B3 & B4) ]).
  rewrite (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)).
  pose proof (u64_range (edenot E (reg cs 10))) as Hr10. pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
  apply bv_eq. rewrite u64_lit by (unfold KHI in *; lia). unfold two64, KHI in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="SINV_frame"] Theorem node_sys_sound_YBrk : sys_stmt SEGS A nx0 LIMIT SINV argH FS0 YBrk.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn Hk.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_6; dand5 dR_6 as Hpc0 Hpc4 w HF HE | destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE) ]).
  cbn [node_sys] in Hn. unfold node_brk1 in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  (* [comment removed for export] *)
  assert (POST : forall ok : bool, (if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None) = Some cs' ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 (vm_brk (m_vmmaps model))) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T).
  { intros ok Hok. destruct ok; [|discriminate]. apply Some_inj in Hok.
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc cs') by (rewrite <- Hok; reflexivity).
    apply (Hk E (regupd R 10 (vm_brk (m_vmmaps model))) FULL model);
      [split; apply env_agree_refl | rewrite <- Hok; apply brk_keep_ok; exact HC | reflexivity]. }
  unfold cfg_of.
  destruct (reg_lit cs 10) as [[|p|p]|] eqn:H10.
  1: { (* [comment removed for export] *)
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 0 HC ltac:(lia) H10) as [G10 _].
    eapply (srz_brk_query_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10 |].
    exact (POST true Hn). }
  (* [comment removed for export] *)
    all: destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
    all: destruct (brk_grow_blocked A cs d) eqn:Hblk; [|discriminate].
    all: specialize (POST true Hn).
    all: unfold brk_grow_blocked in Hblk; apply andb_prop in Hblk as [Hbase Hex].
    all: (first [ pose proof ((brk_req_sound E cs R FULL model d HC Hreq)) as dR_7; dand4 dR_7 as D1 D2 D3 Dm | destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm) ]).
    all: (first [ pose proof ((brk_base_ok_sound E cs R FULL model d HC Hbase)) as dR_8; dand4 dR_8 as B1 B2 B3 B4 | destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4) ]).
    all: pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
    all: apply existsb_exists in Hex as [m [Hmin Hm]]; apply andb_prop in Hm as [Hm Hm2]; apply andb_prop in Hm as [Hnf Hm1]; apply negb_true_iff in Hnf.
    all: pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hm1) as L1;
         pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hm2) as L2;
         cbn [xt_den] in L1, L2; rewrite <- (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) in L1, L2.
    all: pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
    all: eapply (srz_brk_grow_blocked_lazy SEGS); [exact HF | exact HE | exact Hh | exact G17 | exact G10
         | rewrite u64_lit by (unfold KHI in *; lia); lia
         | rewrite u64_lit by (unfold KHI in *; lia); pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC); lia
         | rewrite u64_lit by (unfold KHI in *; lia); lia
         | | exact POST].
    all: apply (brk_grow_ok_aligned_refuted model d (edenot E (am_base m)) (edenot E (am_len m)));
         [exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI, page_size in *; lia | | lia | lia].  (* [comment removed for export] *)
    all: apply in_or_app; right; exact (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hmin Hnf).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_grow_ok_aligned_elim : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d + page_size < 2 ^ 64)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (bv_unsigned b + d <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true
  /\ (vm_backing_used m + d <= vm_limit h)%Z.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hnw H.
  unfold page_size in Hnw. pose proof (u64_range b) as Hbr.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H. rewrite Hureq in H.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in H by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in H
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in H by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z in H by lia.
  apply andb_prop in H as [H Hlive]. apply andb_prop in H as [Htop Hrf].
  apply Z.leb_le in Htop. apply Z.leb_le in Hlive.
  rewrite bv_sub_unsigned in Hlive. rewrite Hureq in Hlive.
  rewrite bv_wrap_small in Hlive by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Htop | exact Hrf | lia].
Qed.

(* [comment removed for export] *)
Lemma srz_brk_grow_opt : forall regs (pc : word) mem rom model w (d : Z) (TA TB : TSet),
  fetch_word SEGS pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  srealizes SEGS (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) TA ->
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes SEGS (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) rom)
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) TB) ->
  (forall tr, TB tr <-> TA tr) ->
  srealizes SEGS (mkCfg (mkst regs pc mem rom) model) TA.
Proof.
  intros regs pc mem rom model w d TA TB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hsb H10 HA HB Hsub.
  pose proof (u64_range b) as Hbr.
  destruct (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d))) eqn:Hadm.
  - eapply srz_conseq.
    + eapply (srz_brk_grow_lazy SEGS regs pc mem rom model w d TA TB HF HE Hh H17 Hbal Hdal Hd Hb0 Hnw ltac:(fold h b; lia) H10 Hadm HA (HB eq_refl) (fun tr Ht => proj2 (Hsub tr) Ht)).
    + intros tr. unfold t_alt2. split; [intros [Ht|Ht]; [exact Ht | exact (proj1 (Hsub tr) Ht)] | intros Ht; left; exact Ht].
  - eapply (srz_brk_grow_blocked_lazy SEGS regs pc mem rom model w (Z_to_bv 64 (bv_unsigned b + d)) TA HF HE Hh H17 H10);
      fold h b; rewrite ?u64_lit by lia; try lia; try exact Hadm; exact HA.
Qed.

(* [comment removed for export] *)
Lemma cs_ok_rebrk : forall E cs R FULL model e (r : word),
  cs_ok E cs R FULL model -> edenot E e = r ->
  bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned r ->
  let h := m_vmmaps model in
  cs_ok E (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) e (a_fd cs) (a_tidset cs))
        R FULL (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) r
                                          (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model).
Proof.
  intros E cs R FULL model e r HC He Hsb h.
  destruct HC; constructor;
    cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn nxt pc
         m_vmmaps with_vmmaps vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp
         m_halted m_fds m_fs m_tid m_vm_lazy m_vm_materialized] in *;
    try assumption; try (symmetry; assumption).
  (* [comment removed for export] *)
  eapply MInv_transport; [exact co_minv0 | reflexivity | reflexivity | destruct co_minv0 as [_ _ _ _ B]; exact B].
Qed.

(* [comment removed for export] *)
Lemma kmem_ok_s : forall E M s ne (lo n : Z),
  estart E s = lo -> elenZ E ne = n -> 0 <= lo < 2 ^ 64 -> 0 <= n -> lo + n <= 2 ^ 64 ->
  (forall x : word, lo <= bv_unsigned x < lo + n -> M x = Some (Z_to_bv 8 0)) ->
  know_ok SEGS E M [KWr s ne; KZero s ne].
Proof.
  intros E M s ne lo n Hs Hn Hlo Hn0 Hhi BYTE.
  assert (Hfl : flat E s (elenZ E ne)) by (unfold flat; rewrite Hs, Hn; lia).
  constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; rewrite ?Hs, ?Hn.
  - intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. unfold wview. rewrite (BYTE x) by lia. discriminate.
  - intros i Hi. apply BYTE. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="argH_top SHADOW_val argH_high SHADOW_ok HULL_ok SEGS_in_hull"] Lemma grant_vis_add_split : forall E cs1 cs2 base bb bk ne R FULL model (a n : word) nZ,
  cs_ok E cs1 R FULL model ->
  vis_add A LIMIT cs1 base ne (KWr (SA bb bk) ne :: KZero (SA bb bk) ne :: kn cs1) = Some cs2 ->
  kimg_in_hull A (kn cs1) ->
  edenot E base = a -> estart E (SA bb bk) = bv_unsigned a -> edenot E ne = n -> bv_unsigned n = nZ -> 0 <= nZ ->
  bv_unsigned a + nZ <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ ->
     in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true
     /\ in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
     /\ argH E x = false) ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + nZ -> FULL x = Some (Z_to_bv 8 0)) ->
  cs_ok E cs2 R FULL model.
Proof.
  intros E cs1 cs2 base bb bk ne R FULL model a n nZ HC1 Hva Hkh Hbase Hest Hne Un HnZ Hhi NEW ZERO.
  pose proof (u64_range a) as Ra.
  eapply (APS.vis_add_sound SEGS A LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) HULL_ok SHADOW_ok SHADOW_val SINV argH argH_top FS0 0%nat);
    [exact Hva | exact HC1 |].
  (first [ pose proof ((Asanwqd.vis_add_inv A LIMIT cs1 base ne _ cs2 Hva)) as dR_9; dex1 dR_9 as nhi; destruct dR_9 as [Hnhi Ecs2] | pose proof ((Asanwqd.vis_add_inv A LIMIT cs1 base ne _ cs2 Hva)) as dR_9; dand3 dR_9 as nhi Hnhi Ecs2 | destruct (Asanwqd.vis_add_inv A LIMIT cs1 base ne _ cs2 Hva) as (nhi & Hnhi & Ecs2) ]).
  change (KWr (SA bb bk) ne :: KZero (SA bb bk) ne :: kn cs1) with ([KWr (SA bb bk) ne; KZero (SA bb bk) ne] ++ kn cs1).
  apply Forall_app. split.
  - (* [comment removed for export] *)
    eapply (kmem_ok_s E _ (SA bb bk) ne (bv_unsigned a) nZ); [exact Hest | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
    intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_10; dand3 dR_10 as N1 N2 N3 | destruct (NEW x Hx) as (N1 & N2 & N3) ]).
    unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
    unfold vis. rewrite N1, N2. cbn [negb andb].
    assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
    { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
  - (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
    eapply (APS.know_ok_unhide SEGS A); [apply (APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high) | exact Hkh | | | exact HK1].
    + intros y Hy. rewrite Ecs2 in Hy. eapply APS.hid_cons_sub. exact Hy.
    + intros y Hy. apply (APS.hid_hull A HULL_ok argH argH_high). exact Hy.
Qed.

(* [comment removed for export] *)
Lemma vis_add_shape : forall cs b n k cs2,
  vis_add A LIMIT cs b n k = Some cs2 ->
  flat_x (kn cs) (fst (split_lit b)) (snd (split_lit b)) n = true
  /\ pc cs2 = pc cs /\ s_regs (a_ss cs2) = s_regs (a_ss cs) /\ a_vis cs2 = (b, n) :: a_vis cs
  /\ a_maps cs2 = a_maps cs /\ a_ghost cs2 = a_ghost cs.
Proof.
  intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. (* [comment removed for export] *) unfold vis_add_ref in Hv.
  destruct (split_lit b) as [bb bk] eqn:Hsplit.
  destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
  destruct (xhi (kn cs) n) as [nhi|] eqn:Hnhi; [|discriminate].
  match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hv as <-. cbn [fst snd pc a_ss s_pc s_regs a_vis a_maps a_ghost mk_ss].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _].
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc Hflat].
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. exact Hflat.
Qed.

(* [comment removed for export] *)
#[using="grant_new_facts' regs_ok_regupd_same' kdisj_new_ok' grant_cs1_ok' free_apart_hull' RES_len argH_top SHADOW_val RES_cover SINV_frame argH_high SHADOW_ok HULL_ok SEGS_in_hull"] Theorem node_brk2_sound : brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Proof.
  intros cs csa csb E R FULL model TA TB HC Hec Hn HkA HkB Hsub.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_11; dand5 dR_11 as Hpc0 Hpc4 w HF HE | destruct (is_ecall_at_sound SEGS cs Hec) as (Hpc0 & Hpc4 & w & HF & HE) ]).
  pose proof HULL_ok as HU; unfold hull_ok in HU; (first [ dand4 HU as U0 U1 U2 U3 | destruct HU as (U0 & U1 & U2 & U3) ]).
  unfold node_brk2 in Hn.
  destruct (reg_lit cs 17) as [a7|] eqn:H17; [|discriminate].
  destruct a7 as [|p|p]; try discriminate; repeat (destruct p as [p|p|]; try discriminate).
  destruct (brk_req cs) as [d|] eqn:Hreq; [|discriminate].
  destruct (brk_grow_possible A LIMIT cs d && AP.expr_vars_lt (nxt cs) (reg cs 10))%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hposs _].
  destruct (split_lit (a_brk cs)) as [bb bk] eqn:Hsplit.
  set (csB := ACS _ _ _ _ _ _ _ _ _ _ _) in Hn.
  destruct (vis_add A LIMIT csB (a_brk cs) (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB)) as [csB'|] eqn:Hva; [|discriminate].
  apply Some_pair_inj in Hn as [EcsA EcsB]. subst csB'.
  (* [comment removed for export] *)
  destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 214 HC ltac:(lia) H17) as [G17 _].
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hh.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  unfold brk_grow_possible in Hposs.
  apply andb_prop in Hposs as [Hposs Hbudget]. apply andb_prop in Hposs as [Hposs Hnoh]. apply andb_prop in Hposs as [Hbase Hnf].
  unfold budget_ok in Hbudget. apply Z.leb_le in Hbudget.
  (first [ pose proof ((brk_req_sound E cs R FULL model d HC Hreq)) as dR_13; dand4 dR_13 as D1 D2 D3 Dm | destruct (brk_req_sound E cs R FULL model d HC Hreq) as (D1 & D2 & D3 & Dm) ]).
  (first [ pose proof ((brk_base_ok_sound E cs R FULL model d HC Hbase)) as dR_14; dand4 dR_14 as B1 B2 B3 B4 | destruct (brk_base_ok_sound E cs R FULL model d HC Hbase) as (B1 & B2 & B3 & B4) ]).
  pose proof (brk_req_val E cs R FULL model d HC Hreq Hbase) as G10.
  pose proof (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as Hres.
  pose proof (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC) as Hsbrk.
  pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) as Hbrk.
  set (h := m_vmmaps model) in *. set (b := vm_brk h) in *.
  pose proof (u64_range b) as Hbr.
  assert (Eb : edenot E (a_brk cs) = b) by (symmetry; exact Hbrk).
  unfold cfg_of.
  eapply (srz_brk_grow_opt R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w d TA TB HF HE Hh G17);
    fold h b; [exact B1 | exact D2 | exact D1 | exact B2 | unfold KHI in *; lia | exact Hsbrk | exact G10 | | | exact Hsub].
  - (* [comment removed for export] *)
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csa) by (rewrite <- EcsA; reflexivity).
    apply (HkA E (regupd R 10 b) FULL model);
      [split; apply env_agree_refl | rewrite <- EcsA; apply (brk_keep_ok); exact HC | reflexivity].
  - (* [comment removed for export] *)
    intros Hadm.
    (first [ pose proof ((brk_grow_ok_aligned_elim model d B1 D2 D1 B2 ltac:(fold h b; unfold KHI, page_size in *; lia) Hadm)) as dR_15; dand3 dR_15 as Htop Hrfg Hlive | destruct (brk_grow_ok_aligned_elim model d B1 D2 D1 B2 ltac:(fold h b; unfold KHI, page_size in *; lia) Hadm) as (Htop & Hrfg & Hlive) ]).
    fold h b in Htop, Hrfg, Hlive.
    set (dw := Z_to_bv 64 d). assert (Udw : bv_unsigned dw = d) by (unfold dw; apply u64_lit; unfold KHI in *; lia).
    assert (Hrf : region_free (vm_reserved h ++ vm_maps h) b dw = true).
    { apply (region_free_prefix _ b dw (Z_to_bv 64 (d + page_size))); [|exact Hrfg].
      rewrite Udw, u64_lit by (unfold KHI, page_size in *; lia). unfold page_size. lia. }
    pose proof (free_apart_hull' model b dw d Hres Hrf Udw D1) as HULLb. fold h b in HULLb.
    set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
    assert (Ureq : bv_unsigned req = bv_unsigned b + d) by (unfold req; apply u64_lit; unfold KHI in *; lia).
    (* [comment removed for export] *)
    set (h'' := mkVmMapsFull (vm_reserved h) ((b, dw) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) b (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    set (model'' := with_vmmaps h'' model). set (FULL' := zfill b dw FULL). set (R' := regupd R 10 req).
    assert (GPo : Asanwqd.grant_post KRW b dw model model'') by (constructor; reflexivity).
    assert (GM : Asanwqd.grant_mem KRW b dw FULL FULL').
    { split; intros x Hx; unfold FULL'; cbn [kind_none]; [apply zfill_out; exact Hx | apply zfill_in; exact Hx]. }
    (first [ pose proof ((Asanwqd.vis_add_inv A LIMIT csB (a_brk cs) (ELit d) _ csb Hva)) as dR_16; dex1 dR_16 as nhi; destruct dR_16 as [Hnhi Ecsb] | pose proof ((Asanwqd.vis_add_inv A LIMIT csB (a_brk cs) (ELit d) _ csb Hva)) as dR_16; dand3 dR_16 as nhi Hnhi Ecsb | destruct (Asanwqd.vis_add_inv A LIMIT csB (a_brk cs) (ELit d) _ csb Hva) as (nhi & Hnhi & Ecsb) ]).
    rewrite (v_addi_pc (pc cs) Hpc0 Hpc4).
    replace (pc cs + 4) with (pc csb) by (rewrite Ecsb; reflexivity).
    apply (HkB E R' FULL' _); [split; apply env_agree_refl | | reflexivity].
    (* [comment removed for export] *)
    (first [ pose proof ((grant_cs1_ok' E cs R FULL model KRW b dw d model'' FULL'
                (s_regs (a_ss cs)) R'
                (kdisj_new A (kn_grant_filter A (kn cs) (a_maps cs)) (a_maps cs) (a_brk cs) (ELit d))
                (a_brk cs) (ELit d) d true (a_ylo cs) (nxt cs)
                HC Udw D1 D2 B1 HULLb Htop Hrf GPo GM)) as dR_17; dand3 dR_17 as HC1 MROUT MRSAME | destruct (grant_cs1_ok' E cs R FULL model KRW b dw d model'' FULL'
                (s_regs (a_ss cs)) R'
                (kdisj_new A (kn_grant_filter A (kn cs) (a_maps cs)) (a_maps cs) (a_brk cs) (ELit d))
                (a_brk cs) (ELit d) d true (a_ylo cs) (nxt cs)
                HC Udw D1 D2 B1 HULLb Htop Hrf GPo GM) as (HC1 & MROUT & MRSAME) ]).
    + (* [comment removed for export] *) unfold R'. rewrite Asanwqd.bv5_10. apply regs_ok_regupd_same'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia |].
      rewrite G10. reflexivity.
    + exact Eb.
    + cbn [edenot]. reflexivity.
    + (* [comment removed for export] *)
      eapply kdisj_new_ok';
        [exact HC | | exact Eb | cbn [edenot]; reflexivity | exact Udw | exact D1 | exact Hrf | exact Htop | exact B1 | exact D2].   (* [comment removed for export] *)
      (* [comment removed for export] *)
      apply Forall_forall. intros K0 HK0. apply (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K0).
      unfold kn_grant_filter in HK0. apply APS.kimg_clip_incl in HK0. apply filter_In in HK0 as [HK0 _]. exact HK0.
    + reflexivity.
    + reflexivity.
    + lia.
    + intros _. exact Hbudget.
    + lia.
    + intros m Hm Hk. exfalso. unfold no_holes in Hnoh. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. cbv beta in X. rewrite Hk in X. discriminate.
    + (* [comment removed for export] *)
      pose proof (cs_ok_rebrk E _ R' FULL' model'' (reg cs 10) req HC1
                    ltac:(rewrite <- (APS.reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)); exact G10)
                    ltac:(replace (vm_start_brk (m_vmmaps model'')) with (vm_start_brk h) by reflexivity; rewrite Ureq; lia)) as HC2.
      cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset add_entry m_vmmaps with_vmmaps
           vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp] in HC2.
      eapply (grant_vis_add_split E csB csb (a_brk cs) bb bk (ELit d) R' FULL' _ b dw d);
        [exact HC2 | exact Hva | | exact Eb | | cbn [edenot]; reflexivity | exact Udw | lia | unfold KHI in *; lia | |].
      * (* [comment removed for export] *)
        unfold csB, kn. cbn [a_ss mk_ss s_know]. apply (APS.kimg_in_hull_app A); [|unfold kn_grant_filter; apply (APS.kimg_clip_in_hull A)].
        apply (Asanwqd.kimg_in_hull_pure A). apply Asanwqd.kdisj_new_pure.
      * (* [comment removed for export] *)
        destruct (vis_add_shape csB (a_brk cs) (ELit d) _ _ Hva) as (Hflat & _). rewrite Hsplit in Hflat. cbn [fst snd] in Hflat.
        (first [ pose proof ((flat_x_sound SEGS E _ (kn csB) bb bk (ELit d) (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) Hflat)) as dR_18; dand3 dR_18 as Fb1 Fb2 Fb3 | destruct (flat_x_sound SEGS E _ (kn csB) bb bk (ELit d) (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) Hflat) as (Fb1 & Fb2 & Fb3) ]).
        rewrite <- Eb. symmetry. apply (u_of_split E (a_brk cs) bb bk Hsplit). cbn [edenot] in Fb2. fold dw in Fb2. rewrite ?Udw, ?u64_lit in Fb2 by (unfold KHI in *; lia). lia.
      * (* [comment removed for export] *)
        intros x Hx.
        match goal with |- context [vm_maps (m_vmmaps ?M)] =>
          replace (vm_maps (m_vmmaps M)) with ((b, dw) :: vm_maps h) by reflexivity;
          replace (vm_noaccess (m_vmmaps M)) with (vm_noaccess h) by reflexivity end.
        rewrite in_ivs_cons. cbn [fst snd]. rewrite Udw.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb orb].
        (first [ pose proof ((grant_new_facts' E cs R FULL model b dw d HC Hrf Udw D1 HULLb Htop x Hx)) as dR_19; dand4 dR_19 as _ N2 N3 _ | destruct (grant_new_facts' E cs R FULL model b dw d HC Hrf Udw D1 HULLb Htop x Hx) as (_ & N2 & N3 & _) ]).
        split; [reflexivity|]. split; [exact N2 | exact N3].
      * (* [comment removed for export] *)
        intros x Hx. unfold FULL'. apply zfill_in. rewrite Udw. exact Hx.
Qed.

End SoundB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundMunmap.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : length (segments_reserved SEGS) = n_res A.
Hypothesis HULL_ok : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis SHADOW_ok : 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_hullH : RES_hull_def SEGS A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis RES_cover : APS.res_cover_ok SEGS A.
Hypothesis SHADOW_val : APS.shadow_val_ok A.
Hypothesis NX0_ok : APS.nx0_ok nx0.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
Variable FS0 : Fs.Fs.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT NX0_ok SINV argH argH_agree SINV_agree FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB HULL_ok SHADOW_ok SHADOW_val SINV argH argH_top FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.

#[using="reg_lit_sound' reg_sound' HULL_ok RES_len"] Lemma mmap_len_sound : forall E cs R FULL model ne nlo nhi,
  CSOK E cs R FULL model -> mmap_len cs = Some (ne, nlo, nhi) ->
  let len := bv_unsigned (edenot E (reg cs 11)) in
  getr R (Z_to_bv 5 11) = Z_to_bv 64 len
  /\ 0 < len < 2 ^ 64
  /\ edenot E ne = Z_to_bv 64 (page_round_up_Z len)
  /\ 0 < nlo /\ nlo <= page_round_up_Z len <= nhi
  /\ page_round_up_Z len mod 4096 = 0
  /\ (forall E', edenot E' (reg cs 11) = edenot E (reg cs 11) -> edenot E' ne = edenot E ne).
Proof.
  intros E cs R FULL model ne nlo nhi HC HML len.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
  pose proof (u64_range (edenot E (reg cs 11))) as Hr.
  rewrite mmap_len_eq in HML. (* [comment removed for export] *) unfold mmap_len_ref in HML.
  destruct (reg_lit cs 11) as [lz|] eqn:H11.
  - destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
    destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
    assert (Hlen : len = lz).
    { unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
    rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
    rewrite page_up_eq.
    split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
  - destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
    match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection HML as <- <- <-.
    apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
    apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
    pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
    destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
    assert (Hmod : len mod 4096 = 0).
    { unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
      replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
        by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    assert (Hpr : page_round_up_Z len = len).
    { unfold page_round_up_Z, page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    rewrite Hpr.
    split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
    split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
    intros E' HE'. exact HE'.
Qed.

(* [comment removed for export] *)
Lemma bv5_10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bv5_17 : (17%bv : bv 5) = Z_to_bv 5 (Z.of_nat 17). Proof. apply bv_eq. reflexivity. Qed.

Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as H1. exact H1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="HULL_ok RES_len A"] Lemma split_flat_estart : forall E M k e b off n,
  know_ok SEGS E M k -> split_lit e = (b, off) -> flat_x k b off n = true ->
  estart E (SA b off) = bv_unsigned (edenot E e)
  /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof.
  intros E M k e b off n HK Hsp Hfl.
  (first [ pose proof ((APS.flat_x_sound SEGS E M k b off n HK Hfl)) as dR_20; dand3 dR_20 as F1 F2 F3 | destruct (APS.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3) ]).
  pose proof (APS.u_of_split E e b off Hsp ltac:(lia)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

(* [comment removed for export] *)

Lemma covered_maps_subtract : forall l lo hi x,
  ivs_wf l -> lo <= hi ->
  covered (maps_subtract l lo hi) x = (covered l x && negb (in_rng lo hi x))%bool.
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.

(* [comment removed for export] *)
#[using="RES_len A"] Lemma len_eqb_sound : forall E M k n m,
  know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as B1.
    cbn [xt_den] in A1, B1. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
#[using="HULL_ok RES_len A"] Lemma kzero_x_sound : forall E M allkn k b off n,
  know_ok SEGS E M allkn -> know_ok SEGS E M k -> kzero_x allkn k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64
  /\ forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> M x = Some (Z_to_bv 8 0).
Proof.
  intros E M allkn k b off n HA HK. induction k as [|K k IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK HK]. cbn [kzero_x] in H.
  assert (CONT : forall zb zk zn,
            kentry_ok SEGS E M (KZero (SA zb zk) zn) ->
            estart E (SA zb zk) <= estart E (SA b off) -> estart E (SA b off) + elenZ E n <= estart E (SA zb zk) + elenZ E zn ->
            0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64
            /\ forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> M x = Some (Z_to_bv 8 0)).
  { intros zb zk zn [Hfl Hz] I1 I2. (first [ dand4 Hfl as F1 F2 F3 F4 | destruct Hfl as (F1 & F2 & F3 & F4) ]). split; [lia|]. split; [lia|].
    intros x Hx. replace x with (Z_to_bv 64 (estart E (SA zb zk) + (bv_unsigned x - estart E (SA zb zk)))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
    apply Hz. lia. }
  destruct K as [|[zb zk] zn| | | | | | | |]; try (apply IH; assumption).
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc end.
  - destruct (expr_eqb b zb && (zk <=? off))%bool eqn:Hb; [|discriminate].
    apply andb_prop in Hb as [Hb Hzk]. apply expr_eqb_eq in Hb. subst zb. apply Z.leb_le in Hzk.
    destruct (xhi allkn n) as [nh|] eqn:Hnh; [|discriminate]. destruct (xlo allkn zn) as [zl|] eqn:Hzl; [|discriminate].
    apply Z.leb_le in Hc. pose proof (xhi_sound SEGS E M allkn n nh HA Hnh). pose proof (xlo_sound SEGS E M allkn zn zl HA Hzl).
    apply (CONT b zk zn HKK); unfold estart, elenZ; cbn [a_base a_off]; lia.
  - destruct (xinside allkn b off n zb zk zn) eqn:Hins; [|apply IH; assumption].
    pose proof (xinside_sound SEGS E M allkn b off n zb zk zn HA Hins) as [I1 I2]. apply (CONT zb zk zn HKK I1 I2).
Qed.

(* [comment removed for export] *)
#[using="HULL_ok RES_len A"] Lemma kentry_keep_foot : forall E M M' K,
  kentry_ok SEGS E M K ->
  (forall x : word, match kfoot E K with
                    | Some (s, l) => s <= bv_unsigned x < s + l
                    | None => False end -> M' x = M x) ->
  (forall x : word, M x = None -> M' x = None) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K HK Hin Hnone.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok kfoot] in *;
    try exact HK.
  - (* [comment removed for export] *) (first [ dand3 HK as Hw Hfl Hrd | destruct HK as (Hw & Hfl & Hrd) ]). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. apply rdn_ext; [rewrite (flat_u E _ _ Hfl); destruct Hfl; lia|].
    intros x Hx. apply Hin. rewrite (flat_u E _ _ Hfl) in Hx. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. (first [ dand4 Hfl as F1 F2 F3 F4 | destruct Hfl as (F1 & F2 & F3 & F4) ]).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) (first [ dand3 HK as Hfl Hlen Hz | destruct HK as (Hfl & Hlen & Hz) ]). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. (first [ dand4 Hfl as F1 F2 F3 F4 | destruct Hfl as (F1 & F2 & F3 & F4) ]).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) (first [ dand3 HK as HA HB HC | destruct HK as (HA & HB & HC) ]). split; [exact HA|]. split; [exact HB|]. intros i Hi. apply Hnone. apply HC. exact Hi.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. (first [ dand4 Hfl as F1 F2 F3 F4 | destruct Hfl as (F1 & F2 & F3 & F4) ]).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hin by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. (first [ dand4 Hfl as F1 F2 F3 F4 | destruct Hfl as (F1 & F2 & F3 & F4) ]).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. (first [ dand4 Hfl as F1 F2 F3 F4 | destruct Hfl as (F1 & F2 & F3 & F4) ]).
    rewrite Hin; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition sh_iv (E : env) (k : list kentry) (p : expr * expr) : Z * Z :=
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in (estart E (SA sb sk), elenZ E sn).

(* [comment removed for export] *)
#[using="kentry_apart_b_sem'"] Lemma fold_unfill_inv : forall E M k gone acc K,
  know_ok SEGS E M k ->
  (forall K', In K' acc -> In K' k) ->
  In K (fold_left (fun kk p => let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in kn_unfill kk sb sk sn) gone acc) ->
  In K acc /\ (kimg_b K = true \/ forall p, In p gone -> kfoot_apart E K (fst (sh_iv E k p)) (snd (sh_iv E k p))).
Proof.
  intros E M k gone. induction gone as [|p gone IH]; intros acc K HK Hacc Hin.
  - cbn in Hin. split; [exact Hin|]. right. intros q [].
  - cbn [fold_left] in Hin.
    destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
    assert (Hacc' : forall K', In K' (kn_unfill acc sb sk sn) -> In K' k).
    { intros K' HK'. unfold kn_unfill in HK'. apply filter_In in HK' as [HK' _]. apply Hacc. exact HK'. }
    destruct (IH _ K HK Hacc' Hin) as [Hin1 Hrest].
    unfold kn_unfill in Hin1. apply filter_In in Hin1 as [Hin0 Hkeep]. split; [exact Hin0|].
    apply orb_prop in Hkeep as [Himg|Hap]; [left; exact Himg|].
    destruct Hrest as [Himg|Hrest]; [left; exact Himg|]. right.
    intros q [<-|Hq]; [|apply Hrest; exact Hq].
    unfold sh_iv. rewrite Hsh. cbn [fst snd].
    rewrite APS.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [|exact Hap].
    unfold know_ok. apply Forall_forall. intros K' HK'. exact (proj1 (Forall_forall _ _) HK K' (Hacc K' HK')).
Qed.

Lemma existsb_filter_split : forall {T} (g h : T -> bool) l,
  existsb h l = (existsb h (List.filter g l) || existsb h (List.filter (fun x => negb (g x)) l))%bool.
Proof.
  intros T g h l. induction l as [|x l IH]; cbn; [reflexivity|].
  destruct (g x); cbn; rewrite IH; destruct (h x); cbn; rewrite ?orb_true_r; reflexivity.
Qed.

#[using="regs_ok_set_n' kentry_apart_b_sem' reg_lit_sound' reg_sound' argH_top SINV_frame SHADOW_ok HULL_ok RES_len"] Lemma node_munmap_sound : forall cs cs' E R FULL model T,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_munmap A cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T HC Hec Hn HK.
  (first [ pose proof ((Asanwqd.is_ecall_at_sound SEGS cs Hec)) as dR_30; dex1 dR_30 as w; dand4 dR_30 as Hf He Hp0 Hp4 | pose proof ((Asanwqd.is_ecall_at_sound SEGS cs Hec)) as dR_30; dand5 dR_30 as w Hf He Hp0 Hp4 | destruct (Asanwqd.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4) ]).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
  rewrite node_munmap_eq in Hn. (* [comment removed for export] *) unfold node_munmap_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 215).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  subst z17.
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsp.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hgone]. apply andb_prop in Hcond as [Hcond Hhi64]. apply andb_prop in Hcond as [Hcond HFLAT]. apply andb_prop in Hcond as [Hhas Hpal].
  set (k := kn cs) in *.
  set (g := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) in *.
  set (ng := fun p : expr * expr => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) in *.
  assert (NG : forall l, List.filter ng l = List.filter (fun p => negb (g p)) l).
  { intros l. induction l as [|p l IH]; cbn; [reflexivity|]. rewrite IH. subst g ng. cbv beta. destruct (split_lit (fst p)); reflexivity. }
  rewrite !NG in Hn, Hgone. clear NG ng.
  set (gone := List.filter (fun p => negb (g p)) (a_vis cs)) in *.
  set (kept := List.filter g (a_vis cs)) in *.
  apply some_inj in Hn. subst cs'.
  (* [comment removed for export] *)
  apply existsb_exists in Hhas as (m & Hm & Hmatch). unfold amap_match in Hmatch. apply andb_prop in Hmatch as [Hb Hlen_eq].
  pose proof (len_eqb_sound E _ k ne (am_len m) HKN Hlen_eq) as Hne_eq.
  (first [ pose proof ((mmap_len_sound E cs R FULL model ne nlo nhi HC HML)) as dR_31; dand7 dR_31 as R11 Hlen Hne Hnlo HnZ _ _ | destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & _ & _) ]).
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (addr := edenot E (reg cs 10)). set (n := edenot E (am_len m)).
  assert (Haddr : True) by exact I.
  apply andb_prop in Hb as [Hnf Hb]. apply negb_true_iff in Hnf. apply expr_eqb_eq in Hb.
  assert (Haddr' : edenot E (am_base m) = addr) by (subst addr; rewrite Hb; reflexivity). clear Haddr. rename Haddr' into Haddr.
  pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
  pose proof (maps_match_In E _ _ m MM Hm Hnf) as HIN.
  pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
  assert (BPOS : forall iv, In iv (vm_maps (m_vmmaps model)) -> 0 < bv_unsigned (snd iv)).
  { intros iv Hiv. exact (proj1 (proj1 (Forall_forall _ _) HB iv Hiv)). }
  (first [ pose proof ((proj1 (Forall_forall _ _) HB (amap_den E m) HIN)) as dR_32; dand5 dR_32 as B1 B2 B3 B4 B5 | pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5) ]).
  unfold amap_den in B1, B2, B3, B4, B5. cbn [fst snd] in B1, B2, B3, B4, B5. rewrite Haddr in B2, B4, B5. fold n in B1, B3, B4, B5.
  pose proof (u64_range addr) as Ra. pose proof (u64_range n) as Rn.
  destruct (xhi k (reg cs 10)) as [ahi|] eqn:Hahi; [|discriminate]. apply Z.ltb_lt in Hhi64.
  pose proof (xhi_sound SEGS E _ k (reg cs 10) ahi HKN Hahi) as Hahi'. fold addr in Hahi'. unfold two64 in Hhi64.
  assert (Un : bv_unsigned n = nZ).
  { unfold n. rewrite <- Hne_eq, Hne. apply u64_lit. lia. }
  assert (HnZw : Z_to_bv 64 nZ = n) by (rewrite <- Un; apply Z_to_bv_bv_unsigned).
  (first [ pose proof ((split_flat_estart E _ k (reg cs 10) bb bk ne HKN Hsp HFLAT)) as dR_33; dand3 dR_33 as Hest _ _ | destruct (split_flat_estart E _ k (reg cs 10) bb bk ne HKN Hsp HFLAT) as (Hest & _ & _) ]). fold addr in Hest.
  assert (HelenZ : elenZ E ne = nZ) by (unfold elenZ; rewrite Hne; apply u64_lit; lia).
  set (lo := bv_unsigned addr) in *. set (hi := lo + nZ).
  (* [comment removed for export] *)
  assert (Hlohi : (hi <= img_lo A \/ img_hi A <= lo) /\ hi <= alloc_top (m_vmmaps model) /\ lo < hi /\ lo mod 4096 = 0 /\ hi mod 4096 = 0).
  { subst hi. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. rewrite Z.add_mod, B2 by lia. rewrite <- Un, B3. reflexivity. }
  pose proof (co_tophi _ _ _ _ _ _ _ _ _ _ _ HC) as HTOPHI. unfold TOPMAX in HTOPHI.
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP.
  pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 215 HC ltac:(lia) H17) as [R17 _]. rewrite <- bv5_17 in R17.
  pose proof (reg_sound' E cs R FULL model 10 HC ltac:(lia)) as R10. fold addr in R10. rewrite <- bv5_10 in R10.
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  (* [comment removed for export] *)
  pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS.
  assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
            bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m'))).
  { intros m' Hm' Hnf' Hne'. pose proof (maps_match_disjoint SEGS A RES_len E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
  (* [comment removed for export] *)
  assert (DISJl : forall iv, In iv (vm_maps (m_vmmaps model)) -> iv <> amap_den E m ->
            bv_unsigned (fst iv) + bv_unsigned (snd iv) <= lo \/ hi <= bv_unsigned (fst iv)).
  { intros iv Hiv Hne'. pose proof (seps_In_disjoint _ iv (amap_den E m) SEPS BPOS Hiv HIN Hne') as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. rewrite Haddr in D. fold n lo in D. subst hi. lia. }
  assert (UNIQ : forall iv, In iv (vm_maps (m_vmmaps model)) -> fst iv = addr -> iv = amap_den E m).
  { intros [ib isz] Hiv Hb0. cbn [fst] in Hb0. subst ib.
    destruct (bv_eqb isz n) eqn:Hs.
    - apply bv_eqb_eq in Hs. subst isz. unfold amap_den. rewrite Haddr. reflexivity.
    - exfalso. assert (Hne' : (addr, isz) <> amap_den E m).
      { unfold amap_den. rewrite Haddr. fold n. intros Heq. injection Heq as Heq. rewrite Heq, bv_eqb_refl in Hs. discriminate. }
      pose proof (DISJl _ Hiv Hne') as D. cbn [fst snd] in D. pose proof (BPOS _ Hiv) as P. cbn [snd] in P. subst lo hi. lia. }
  assert (MATCH : forall m', In m' (a_maps cs) -> negb (amap_match k (reg cs 10) ne m') = negb (amap_eqb m' m)).
  { intros m' Hm'. f_equal. unfold amap_match.
    destruct (amap_eqb m' m) eqn:Hmm.
    - apply APS.amap_eqb_eq in Hmm. subst m'. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq. reflexivity.
    - assert (Hne' : m <> m') by (intros <-; rewrite amap_eqb_refl in Hmm; discriminate).
      destruct (is_fog m') eqn:Hnf'; [reflexivity|]. cbn [negb andb].
      destruct (expr_eqb (reg cs 10) (am_base m')) eqn:Heq; [|reflexivity]. exfalso.
      apply expr_eqb_eq in Heq.
      pose proof (DISJ' m' Hm' Hnf' Hne') as D. rewrite <- Heq in D. fold addr lo in D.
      pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' MM Hm' Hnf')) as (C1 & _). unfold amap_den in C1. cbn [snd] in C1. lia. }
  assert (MAPS' : maps_match E (List.filter (fun m' => negb (amap_match k (reg cs 10) ne m')) (a_maps cs)) (map_remove (vm_maps (m_vmmaps model)) addr)).
  { rewrite (filter_ext_in _ (fun m' => negb (amap_eqb m' m))) by (intros m' Hm'; exact (MATCH m' Hm')).
    rewrite <- Haddr. apply maps_match_remove; [exact MM | exact Hm | exact Hnf | exact (seps_NoDup _ SEPS BPOS) |].
    intros iv Hiv Hfst. apply UNIQ; [exact Hiv | rewrite Hfst; exact Haddr]. }
  assert (INMAPS' : forall z, in_ivs z (map_remove (vm_maps (m_vmmaps model)) addr) = (in_ivs z (vm_maps (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
  { intros z. unfold map_remove.
    destruct (in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model)))) eqn:Hl; symmetry.
    - apply in_ivs_true' in Hl as (iv & Hiv & Hziv). apply filter_In in Hiv as [Hiv Hkeep]. apply negb_true_iff in Hkeep.
      assert (Hne' : iv <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
      pose proof (DISJl iv Hiv Hne') as D.
      apply andb_true_intro. split; [apply (proj2 (in_ivs_true' _ _)); exists iv; auto|].
      apply negb_true_iff. unfold in_rng. apply andb_false_iff. destruct D; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
    - apply andb_false_iff.
      destruct (in_ivs z (vm_maps (m_vmmaps model))) eqn:Hin; [right|left; reflexivity].
      apply in_ivs_true' in Hin as (iv & Hiv & Hziv). apply negb_false_iff.
      destruct (bv_eqb (fst iv) addr) eqn:Hfa.
      + apply bv_eqb_eq in Hfa. pose proof (UNIQ iv Hiv Hfa) as ->. unfold amap_den in Hziv. cbn [fst snd] in Hziv. rewrite Haddr in Hziv. fold n lo in Hziv.
        unfold in_rng. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; subst hi; lia.
      + exfalso. assert (X : in_ivs z (List.filter (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) = true); [|congruence].
        apply (proj2 (in_ivs_true' _ _)). exists iv. split; [|exact Hziv]. apply filter_In. rewrite Hfa. auto. }
  (* [comment removed for export] *)
  assert (GONE : forall p, In p gone ->
            (forall z, (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)) = true -> lo <= z < hi)%bool
            /\ (0 <= fst (sh_iv E k p))
            /\ (forall x : word, fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p) -> MR E cs model FULL x = Some (Z_to_bv 8 0))
            /\ (forall z, (sh_lo A E p <=? z) && (z <? sh_hi A E p) = true -> fst (sh_iv E k p) <= z < fst (sh_iv E k p) + snd (sh_iv E k p))%bool).
  { intros p Hp.
    pose proof (proj1 (forallb_forall _ _) Hgone p Hp) as G. cbv beta in G.
    assert (Hpv : In p (a_vis cs)) by (unfold gone in Hp; apply filter_In in Hp as [Hp _]; exact Hp).
    destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
    destruct (shadow_of A k (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
    apply andb_prop in G as [G Gz]. apply andb_prop in G as [G Gin]. apply andb_prop in G as [Gab Gan].
    apply Z.leb_le in Gab. apply Z.leb_le in Gan.
    assert (AL8 : forall e, 3 <= ealign k e -> uE E e mod 8 = 0).
    { intros e Hee. destruct (ealign_sound SEGS E _ k e HKN) as [_ [q Hq]]. unfold uE. rewrite Hq.
      replace (2 ^ ealign k e) with (2 ^ (ealign k e - 3) * 8) by (rewrite <- (Z.pow_add_r 2 _ 3) by lia; f_equal; lia).
      rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
    pose proof (AL8 _ Gab) as A8b. pose proof (AL8 _ Gan) as A8n.
    pose proof (xinside_sound SEGS E _ k pb pk (snd p) bb bk ne HKN Gin) as [I1 I2]. rewrite Hest, ?HelenZ in I1, I2. rewrite HelenZ in I2.
    unfold elenZ in I2.
    pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(pose proof (u64_range (edenot E (snd p))); unfold CEIL in *; subst hi; lia)) as Up.
    (first [ pose proof ((kzero_x_sound E _ k k sb sk sn HKN HKN Gz)) as dR_34; dand3 dR_34 as Z1 Z2 Z3 | destruct (kzero_x_sound E _ k k sb sk sn HKN HKN Gz) as (Z1 & Z2 & Z3) ]).
    unfold sh_iv. rewrite Hsh. cbn [fst snd].
    split; [|split; [exact Z1 | split; [exact Z3|]]].
    - intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold uE in *. rewrite Up in Hz1, Hz2. subst hi. lia.
    - (* [comment removed for export] *)
      unfold shadow_of in Hsh.
      destruct (split_lit (eadd (mkSrl k (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
      assert (Usn : elenZ E (mkSrl k (snd p) 3) = bv_unsigned (edenot E (snd p)) / 8).
      { unfold elenZ. rewrite (mkSrl_denot SEGS E _ k (snd p) 3 (Z_to_bv 64 3) HKN) by (rewrite u64_lit by lia; reflexivity).
        rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
      rewrite Usn in *.
      pose proof (APS.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
      apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
      rewrite (mkSrl_denot SEGS E _ k (fst p) 3 (Z_to_bv 64 3) HKN) in D by (rewrite u64_lit by lia; reflexivity).
      rewrite u_srl64 in D. pose proof SHADOW_ok as SO. pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn'.
      change (2 ^ (3 mod 64)) with 8 in D.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite !u64_lit in D by (clear - SO; lia).   (* [comment removed for export] *)
      rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (clear - SO Rb Rn'; lia).   (* [comment removed for export] *)
      intros z Hz. apply andb_prop in Hz as [Hz1 Hz2]. apply Z.leb_le in Hz1. apply Z.ltb_lt in Hz2. unfold sh_lo, sh_hi, uE in Hz1, Hz2.
      unfold estart. cbn [a_base a_off]. unfold estart in Z1, Z2. cbn [a_base a_off] in Z1, Z2.
      (* [comment removed for export] *)
      rewrite Z_to_bv_unsigned, bv_wrap64_mod in D. unfold uE in A8b, A8n. clear - A8b Z1 Z2 D Rb Hz1 Hz2; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  (* [comment removed for export] *)
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. (first [ pose proof (Hwf) as dR_35; dand4 dR_35 as W1 W2 W3 Wsp | pose proof Hwf as (W1 & W2 & W3 & Wsp) ]).
  unfold cfg_of.
  eapply (srz_munmap_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len T Hf He Hhalt R17 R10 B2 R11 ltac:(lia)).
  { unfold TASK_SIZE. fold nZ. unfold CEIL in *. lia. }  (* [comment removed for export] *)
  { fold nZ. rewrite HnZw. apply map_has_intro. rewrite <- Haddr. exact HIN. }
  fold nZ. rewrite HnZw. rewrite (v_addi_pc (pc cs) Hp0 Hp4).
  set (model' := munmap_model addr n model). set (FULL' := unfill addr n FULL).
  match goal with |- srealizes _ (mkCfg _ ?mo) _ => change mo with model' end.
  set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _) in HK.
  specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
  unfold cfg_of in HK. replace (pc cs') with (pc cs + 4) in HK by reflexivity. rewrite bv5_10. apply HK; [|reflexivity]. clear HK.
  (* [comment removed for export] *)
  assert (PM : vm_maps (m_vmmaps model') = map_remove (vm_maps (m_vmmaps model)) addr) by reflexivity.
  assert (PN : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PL : m_vm_lazy model' = maps_subtract (m_vm_lazy model) lo (lo + bv_unsigned n)) by reflexivity.
  assert (PISP : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model)) by reflexivity.  (* [comment removed for export] *)
  assert (ATOP' : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model)) by reflexivity.  (* [comment removed for export] *)
  assert (PT : m_vm_materialized model' = List.filter (page_outside_range lo (lo + bv_unsigned n)) (m_vm_materialized model)) by reflexivity.
  rewrite Un in PN, PL, PT. fold hi in PN, PL, PT.
  (* [comment removed for export] *)
  assert (NOACC : forall z, in_ivs z (vm_noaccess (m_vmmaps model')) = (in_ivs z (vm_noaccess (m_vmmaps model)) && negb (in_rng lo hi z))%bool).
  { intros z. rewrite PN, !in_ivs_covered. apply covered_maps_subtract; [exact W2 | lia]. }
  assert (LAZYOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x ->
            page_in_ranges (page_base x) (m_vm_lazy model') = page_in_ranges (page_base x) (m_vm_lazy model)).
  { intros x Hx. rewrite PL. (first [ dand5 Hlohi as L1 L2 L3 L4 L5 | destruct Hlohi as (L1 & L2 & L3 & L4 & L5) ]).
    pose proof (page_of_byte_out_aligned x lo hi L4 L5 Hx). apply page_in_ranges_subtract_out; [exact W3 | lia | unfold page_size; lia]. }
  assert (ALW : forall z, in_allow A E cs z = (in_allow A E cs' z || existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool gone
                                                 || existsb (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool gone)%bool).
  { intros z. unfold in_allow, in_vis, in_sh, cs'. cbn [a_vis]. subst kept gone.
    rewrite (existsb_filter_split g (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs)).
    rewrite (existsb_filter_split g (fun p => (sh_lo A E p <=? z) && (z <? sh_hi A E p))%bool (a_vis cs)).
    destruct (existsb _ _), (existsb _ _), (existsb _ _), (existsb _ _); reflexivity. }
  assert (VISLE : forall x : word, VIS E cs' model' x = true -> VIS E cs model x = true /\ (lo <= bv_unsigned x < hi -> False)).
  { intros x Hv. unfold vis in Hv |- *. rewrite ATOP', PM, INMAPS', NOACC in Hv. (first [ dand5 Hlohi as L1 L2 L3 L4 L5 | destruct Hlohi as (L1 & L2 & L3 & L4 & L5) ]).
    destruct (in_rng lo hi (bv_unsigned x)) eqn:Hr.
    - unfold in_rng in Hr. apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.ltb_lt in Hr2.
      replace (in_hull A (bv_unsigned x)) with false in Hv by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1 as [L1|L1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      replace (alloc_top (m_vmmaps model) <=? bv_unsigned x) with false in Hv by (symmetry; apply Z.leb_gt; lia).   (* [comment removed for export] *)
      rewrite andb_false_r in Hv. cbn in Hv. discriminate.
    - assert (Hx : bv_unsigned x < lo \/ hi <= bv_unsigned x).
      { unfold in_rng in Hr. apply andb_false_iff in Hr as [Hr|Hr]; [apply Z.leb_gt in Hr | apply Z.ltb_ge in Hr]; lia. }
      split; [|lia]. rewrite (LAZYOUT x Hx) in Hv. rewrite !andb_true_r in Hv.
      apply orb_prop in Hv as [Hv|Hv]; [rewrite Hv; reflexivity|]. apply orb_true_iff. right.
      apply andb_prop in Hv as [Hv1 Hv2]. apply andb_prop in Hv1 as [Hv0 Hv1]. rewrite Hv0, Hv1. cbn [andb negb].
      apply orb_prop in Hv2 as [Hv2|Hv2]; [rewrite Hv2; reflexivity|]. rewrite (ALW (bv_unsigned x)), Hv2. cbn [orb]. apply orb_true_r. }
  assert (VISEQ : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
            (forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
            VIS E cs' model' x = VIS E cs model x).
  { intros x Hx Hnsh. unfold vis. rewrite ATOP', PM, INMAPS', NOACC, (LAZYOUT x Hx), (ALW (bv_unsigned x)).
    replace (in_rng lo hi (bv_unsigned x)) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb]. rewrite !andb_true_r.
    replace (existsb (fun p => (uE E (fst p) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p) + uE E (snd p)))%bool gone) with false.
    2: { symmetry. apply APS.existsb_false_forall. intros p Hp. destruct (GONE p Hp) as (G1 & _).
         match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
    replace (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) with false.
    2: { symmetry. apply APS.existsb_false_forall. intros p Hp. (first [ pose proof ((GONE p Hp)) as dR_38; dand4 dR_38 as _ _ _ G4 | destruct (GONE p Hp) as (_ & _ & _ & G4) ]).
         match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. exact (Hnsh p Hp (G4 _ Ht)). }
    rewrite !orb_false_r. reflexivity. }
  (* [comment removed for export] *)
  assert (MRNONE : forall x : word, MR E cs model FULL x = None -> MR E cs' model' FULL' x = None).
  { intros x Hx. unfold Mr, mrestrict, hid in Hx |- *.
    destruct (argH E x); [reflexivity|]. cbn [orb] in *.
    destruct (VIS E cs' model' x) eqn:Hv'; [|reflexivity]. cbn [negb].
    destruct (VISLE x Hv') as [Hv Hnin]. rewrite Hv in Hx. cbn [negb] in Hx.
    unfold FULL'. rewrite unfill_out by (rewrite Un; lia). exact Hx. }
  assert (MRKEEP : forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
            (forall p, In p gone -> ~ (fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p))) ->
            MR E cs' model' FULL' x = MR E cs model FULL x).
  { intros x Hx Hnsh. unfold Mr, mrestrict, hid. rewrite (VISEQ x Hx Hnsh). unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hx). reflexivity. }
  (* [comment removed for export] *)
  assert (HALLOW_in : forall iv, In iv (ALLOW E cs') <-> In iv (ALLOW E cs)).
  { intros iv. unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply in_flat_map_split. }
  assert (HALLOW_bytes : A_bytes (ALLOW E cs') = A_bytes (ALLOW E cs)).
  { unfold allowA, cs'. cbn [a_vis a_ghost]. subst kept gone. rewrite <- ?app_assoc. apply A_bytes_flat_map_split. }
  assert (DISJF : forall m', In m' (List.filter (fun m0 => negb (amap_match k (reg cs 10) ne m0)) (a_maps cs)) ->
            In m' (a_maps cs) /\ m <> m'
            /\ (is_fog m' = false -> bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo \/ hi <= bv_unsigned (edenot E (am_base m')))).
  { intros m' Hm'. apply filter_In in Hm' as [Hm' Hnm].
    assert (Hne' : m <> m').
    { intros <-. unfold amap_match in Hnm. rewrite Hnf, <- Hb, expr_eqb_refl, Hlen_eq in Hnm. discriminate. }
    split; [exact Hm'|]. split; [exact Hne'|]. intros Hnf'. exact (DISJ' m' Hm' Hnf' Hne'). }
  assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
  { intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
  destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xsplit Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xtop Xptop Xlzsub Xtophi Xnapos].
  (first [ dand5 Hlohi as L1 L2 L3 L4 L5 | destruct Hlohi as (L1 & L2 & L3 & L4 & L5) ]).
  assert (HAeq : ALLOW E cs' = flat_map (allow1 A E) (kept ++ gone ++ a_ghost cs)) by reflexivity.
  constructor; rewrite ?HAeq; subst cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn s_regs s_log s_know s_next mk_ss];
    try set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _) in *.
  - (* [comment removed for export] *) apply regs_ok_set_n'; [exact Xregs | lia | reflexivity].
  - reflexivity.
  - (* [comment removed for export] *) unfold know_ok. apply Forall_forall. intros K HinK.
    destruct (fold_unfill_inv E _ k gone (kn_unfill k bb bk ne) K Xknow
                ltac:(intros K' HK'; unfold kn_unfill in HK'; apply filter_In in HK' as [HK' _]; exact HK') HinK) as [Hin0 Hsh].
    unfold kn_unfill in Hin0. apply filter_In in Hin0 as [Hin0 Hkeep0].
    pose proof (proj1 (Forall_forall _ _) Xknow K Hin0) as HKK.
    destruct (kimg_b K) eqn:HnotImg.
    { destruct K; try discriminate. cbn [kentry_ok] in HKK |- *. (first [ dand3 HKK as HA' HB' HCC | destruct HKK as (HA' & HB' & HCC) ]).
      split; [exact HA'|]. split; [exact HB'|]. intros i Hi. apply MRNONE. apply HCC. exact Hi. }
    apply kentry_keep_foot with (M := MR E cs model FULL); [exact HKK | | exact MRNONE].
    intros x Hfx.
    cbn [orb] in Hkeep0. rewrite APS.kentry_apart_bp_eq in Hkeep0.
    pose proof (kentry_apart_b_sem' E _ k K bb bk ne Xknow Hkeep0) as Hap0. rewrite Hest, HelenZ in Hap0.
    destruct Hsh as [Himg|Hsh]; [rewrite Himg in HnotImg; discriminate|].
    unfold kfoot_apart in Hap0, Hsh.
    destruct (kfoot E K) as [[fs fl]|] eqn:Hkf; [|destruct Hfx].
    apply MRKEEP; [subst hi; lia|]. intros p Hp Hin. pose proof (Hsh p Hp) as HH. rewrite ?Hkf in HH. cbn [fst snd] in Hin. lia.
  - unfold model'. rewrite munmap_model_halted. exact Xhalt.
  - unfold fds_ok in *. exact Xfds.
  - exact Xfs.
  - exact Xtid.
  - exact Xres.
  - exact Xlimit.
  - rewrite PM. exact MAPS'.
  - (* [comment removed for export] *)
    rewrite PM. apply Forall_forall. intros m' Hm' Hk'. (first [ pose proof ((DISJF m' Hm')) as dR_41; dand3 dR_41 as Hm0 _ _ | destruct (DISJF m' Hm') as (Hm0 & _ & _) ]).
    destruct (proj1 (Forall_forall _ _) Xholes m' Hm0 Hk') as [HF1 HF2]. split; [|exact HF2].
    intros iv Hiv. apply HF1. apply in_app_iff in Hiv as [Hiv|Hiv]; apply in_app_iff; [left; exact Hiv | right].
    unfold map_remove in Hiv. apply filter_In in Hiv as [Hiv _]. exact Hiv.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. apply seps_filter. exact Xseps.
  - (* [comment removed for export] *) unfold model_ivs_wf. rewrite PM, PN, PL. split; [|split; [|split; [|unfold init_sp_ok in *; rewrite PISP; exact Wsp]]].
    + unfold map_remove. apply ivs_wf_filter. exact W1.
    + apply maps_subtract_wf; [exact W2 | lia].
    + apply maps_subtract_wf; [exact W3 | lia].
  - (* [comment removed for export] *) rewrite ATOP', PM. unfold map_remove. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. exact (proj1 (Forall_forall _ _) Xbounds iv Hiv).
  - (* [comment removed for export] *) rewrite ATOP', PL. apply Forall_forall. intros q Hq. (first [ pose proof ((maps_subtract_pieces _ _ _ q W3 Hq)) as dR_42; dex1 dR_42 as r; dand4 dR_42 as Hr R1 R2 _ | pose proof ((maps_subtract_pieces _ _ _ q W3 Hq)) as dR_42; dand5 dR_42 as r Hr R1 R2 _ | destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _) ]).
    pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia.
  - (* [comment removed for export] *) intros z Hz. rewrite PM, INMAPS'. rewrite NOACC in Hz. apply andb_prop in Hz as [Hz1 Hz2]. rewrite (Xnasub z Hz1), Hz2. reflexivity.
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk'. (first [ pose proof ((DISJF m' Hm')) as dR_43; dand3 dR_43 as Hm0 Hne' D | destruct (DISJF m' Hm') as (Hm0 & Hne' & D) ]).
    assert (Hnf' : is_fog m' = false) by (apply KNF; tauto). specialize (D Hnf').
    rewrite PN. pose proof (proj1 (Forall_forall _ _) Xnone m' Hm0 Hk') as X.
    pose proof (proj1 (Forall_forall _ _) HB (amap_den E m') (maps_match_In E _ _ m' Xmaps Hm0 Hnf')) as (C1 & _).
    unfold amap_den in *. apply maps_subtract_keeps; [lia | exact C1 | exact X | cbn [fst snd]; subst hi; lia].
  - (* [comment removed for export] *) apply Forall_forall. intros m' Hm' Hk' x Hx. (first [ pose proof ((DISJF m' Hm')) as dR_44; dand3 dR_44 as Hm0 Hne' D | destruct (DISJF m' Hm') as (Hm0 & Hne' & D) ]).
    specialize (D ltac:(apply KNF; tauto)).
    destruct (proj1 (Forall_forall _ _) Xkinds m' Hm0 Hk' x Hx) as [K1 K2].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x) by lia.
    rewrite NOACC, K1, (LAZYOUT x Hxo), K2. split; reflexivity.
  - (* [comment removed for export] *) rewrite PM. unfold map_remove. rewrite sum_sizes_app. rewrite sum_sizes_app in Xtotsz.
    pose proof (sum_sizes_filter_le (fun p => negb (bv_eqb (fst p) addr)) (vm_maps (m_vmmaps model))) as SF.
    change (vm_reserved (m_vmmaps model')) with (vm_reserved (m_vmmaps model)). lia.
  - (* [comment removed for export] *) exact I.
  - exact Xbrk.
  - exact Xsbrk.
  - (* [comment removed for export] *) rewrite (eager_used_sem model'), (eager_used_sem model Xwf) in *.
    2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
    rewrite PM. unfold map_remove.
    eapply Z.le_trans; [|exact Xeager]. apply sum_count_filter_le.
    intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
    (* [comment removed for export] *)
    assert (Hxo : x < lo \/ hi <= x).
    { assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
      pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
    f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
    replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
    cbn [negb]. rewrite !andb_true_r. reflexivity.
  - (* [comment removed for export] *) rewrite <- HAeq, HALLOW_bytes. exact Xabytes.
  - (* [comment removed for export] *) rewrite <- HAeq. destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?PT.
    + apply NoDup_filter. exact N1.
    + intros q Hq. apply filter_In in Hq as [Hq _]. exact (N2 q Hq).
    + intros q Hq. apply filter_In in Hq as [Hq _]. pose proof (N3 q Hq) as P3.
      unfold page_allowedb in *. apply existsb_exists in P3 as (iv & Hiv & Hbb). apply existsb_exists. exists iv. split; [apply HALLOW_in; exact Hiv | exact Hbb].
    + intros q Hq. apply filter_In in Hq as [Hq Ho]. pose proof (N4 q Hq) as P4.
      unfold page_outside_range in Ho. apply negb_true_iff in Ho.
      pose proof (N2 q Hq) as Qa. unfold page_size in Qa.
      rewrite PL. rewrite page_in_ranges_subtract_out; [exact P4 | exact W3 | lia | ].
      unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; (clear - B2 Ho Qa; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    + rewrite HALLOW_bytes.
      assert (EG : eager_used model' <= eager_used model); [|change (vm_limit (m_vmmaps model')) with (vm_limit (m_vmmaps model)); lia].
      rewrite (eager_used_sem model'), (eager_used_sem model Xwf).
      2: { unfold model_ivs_wf. rewrite PM, PN, PL. split; [unfold map_remove; apply ivs_wf_filter; exact W1|]. split; [apply maps_subtract_wf; try assumption; lia|]. split; [apply maps_subtract_wf; try assumption; lia | unfold init_sp_ok in *; rewrite PISP; exact Wsp]. }
      rewrite PM. unfold map_remove. apply sum_count_filter_le.
      intros q Hq Hkeep x Hx. apply negb_true_iff in Hkeep.
      assert (Hxo : x < lo \/ hi <= x).
      { assert (Hne' : q <> amap_den E m) by (intros ->; unfold amap_den in Hkeep; cbn [fst] in Hkeep; rewrite Haddr, bv_eqb_refl in Hkeep; discriminate).
        pose proof (DISJl q Hq Hne'). unfold B, S in Hx. lia. }
      f_equal. rewrite !covered_app, PN, PL. rewrite !covered_maps_subtract by (first [exact W2 | exact W3 | lia]).
      replace (in_rng lo hi x) with false by (symmetry; unfold in_rng; apply andb_false_iff; destruct Hxo; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
      cbn [negb]. rewrite !andb_true_r. reflexivity.
  - (* [comment removed for export] *) intros x Hh Hmx Hna Hlz Hgh.
    assert (Hgh0 : in_ghost E cs (bv_unsigned x) = false).
    { unfold in_ghost in Hgh |- *. subst cs'. cbn [a_ghost] in Hgh. rewrite existsb_app in Hgh. apply orb_false_iff in Hgh as [_ Hgh]. exact Hgh. }
    rewrite PM, INMAPS' in Hmx. apply andb_prop in Hmx as [Hmx Hxo'].
    assert (Hxo : bv_unsigned x < lo \/ hi <= bv_unsigned x).
    { apply negb_true_iff in Hxo'. unfold in_rng in Hxo'. apply andb_false_iff in Hxo' as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia. }
    unfold FULL'. rewrite unfill_out by (rewrite Un; exact Hxo).
    rewrite NOACC in Hna. apply andb_false_iff in Hna as [Hna|Hna]; [| rewrite Hxo' in Hna; discriminate].
    rewrite (LAZYOUT x Hxo) in Hlz.
    (* [comment removed for export] *)
    destruct (HID E cs model x) eqn:Hold; [exact (Xzero x Hold Hmx Hna Hlz Hgh0)|].
    unfold hid in Hh, Hold. destruct (argH E x); [discriminate|]. cbn [orb] in Hh, Hold.
    apply negb_true_iff in Hh. apply negb_false_iff in Hold.
    (* [comment removed for export] *)
    assert (SHX : exists p, In p gone /\ fst (sh_iv E k p) <= bv_unsigned x < fst (sh_iv E k p) + snd (sh_iv E k p)).
    { destruct (existsb (fun p => (sh_lo A E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi A E p))%bool gone) eqn:Hex.
      - apply existsb_exists in Hex as (p & Hp & Hpx). exists p. split; [exact Hp|]. (first [ pose proof ((GONE p Hp)) as dR_45; dand4 dR_45 as _ _ _ G4 | destruct (GONE p Hp) as (_ & _ & _ & G4) ]). exact (G4 _ Hpx).
      - exfalso. unfold vis in Hh, Hold. rewrite ATOP', PM, INMAPS', NOACC, (LAZYOUT x Hxo) in Hh. rewrite (ALW (bv_unsigned x)), Hex in Hold.
        replace (existsb (fun p0 => (uE E (fst p0) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p0) + uE E (snd p0)))%bool gone) with false in Hold.
        2: { symmetry. apply APS.existsb_false_forall. intros p0 Hq0. destruct (GONE p0 Hq0) as (G1 & _).
             match goal with |- ?t = false => destruct t eqn:Ht; [|reflexivity] end. exfalso. pose proof (G1 _ Ht). lia. }
        rewrite Hxo' in Hh. cbn [negb] in Hh. rewrite !andb_true_r in Hh. rewrite !orb_false_r in Hold. rewrite Hh in Hold. discriminate. }
    (first [ dex1 SHX as p; destruct SHX as [Hp Hpx] | dand3 SHX as p Hp Hpx | destruct SHX as (p & Hp & Hpx) ]). (first [ pose proof ((GONE p Hp)) as dR_47; dand4 dR_47 as _ _ G3 _ | destruct (GONE p Hp) as (_ & _ & G3 & _) ]).
    pose proof (G3 x Hpx) as Z0. unfold Mr, mrestrict, hid in Z0. rewrite Hold in Z0.
    destruct (argH E x); [discriminate|]. cbn in Z0. exact Z0.
  - (* [comment removed for export] *) eapply SINV_frame; [|exact Xsinv]. intros x Hx. unfold FULL'. apply unfill_out. pose proof (argH_top _ _ _ Xsinv Hx). rewrite Un. subst hi. unfold uE in *. lia.
  - (* [comment removed for export] *) rewrite ATOP'. exact Xtop.
  - (* [comment removed for export] *) rewrite ATOP'. exact Xptop.
  - (* [comment removed for export] *) intros z Hz. rewrite PM, INMAPS'. rewrite PL in Hz. rewrite in_ivs_covered in Hz. rewrite covered_maps_subtract in Hz by (first [exact W3 | lia]).
    apply andb_prop in Hz as [Hz1 Hz2]. rewrite <- in_ivs_covered in Hz1. rewrite (Xlzsub z Hz1). rewrite Hz2. reflexivity.
  - (* [comment removed for export] *) rewrite ATOP'. exact Xtophi.
  - (* [comment removed for export] *) rewrite PN. apply maps_subtract_pos. exact Xnapos.
Qed.


#[using="regs_ok_set_n' kentry_apart_b_sem' reg_lit_sound' reg_sound' argH_top SINV_frame SHADOW_ok HULL_ok RES_len"] Theorem node_sys_sound_YMunmap : sys_stmt SEGS A nx0 LIMIT SINV argH FS0 YMunmap.
Proof. intros cs cs' E R FULL model T HC Hpre Hn HK. eapply node_munmap_sound; eauto. Qed.

End SoundMunmap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SoundSys.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis RES_cover : APS.res_cover_ok SEGS A.
Hypothesis SHADOW_val : APS.shadow_val_ok A.
Hypothesis NX0_ok : APS.nx0_ok nx0.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.

#[using="argH_top NX0_ok SINV_agree SINV_frame argH_agree SHADOW_ok HULL_ok RES_len"] Theorem node_sys_sound : forall y, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Proof.
  intros [| |].
  - exact (node_sys_sound_YMunmap SEGS A nx0 LIMIT SINV argH RES_len HULL_ok SHADOW_ok SINV_frame argH_top FS0).
  - exact (node_sys_sound_YBrk SEGS A nx0 LIMIT SINV argH FS0 SINV_frame).
  - exact (node_sys_sound_YSetTid SEGS A nx0 LIMIT SINV argH FS0 argH_agree SINV_agree NX0_ok).
Qed.
End SoundSys.
End Asanku0.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Hypothesis RES_cover : APS.res_cover_ok SEGS A.
Hypothesis SHADOW_val : APS.shadow_val_ok A.
Hypothesis NX0_ok : APS.nx0_ok nx0.
Hypothesis argH_top : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT NX0_ok SINV argH argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB HULL_ok SHADOW_ok SHADOW_val SINV argH argH_top FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
Let cs_argH_top := Asanwqd.cs_argH_top SEGS A LIMIT SINV argH FS0 argH_top.
Let budget_slack := Asanwqd.budget_slack SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let escale_4096_denot := Asanwqd.escale_4096_denot SEGS A RES_len HULL_ok.
Let find_containing_sound := Asanwqd.find_containing_sound SEGS A RES_len.
Let fixed_args_sound := Asanwqd.fixed_args_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let fixed_cs1 := Asanwqd.fixed_cs1 A.
Let gap_ok_sound := Asanwqd.gap_ok_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let gap_weight_eq := Asanwqd.gap_weight_eq SEGS A RES_len.
Let grant_cs1_ok := Asanwqd.grant_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_frame SHADOW_val argH_top.
Let grant_eager_le := Asanwqd.grant_eager_le SEGS A RES_len HULL_ok.
Let grant_keep_apart := Asanwqd.grant_keep_apart SEGS A RES_len HULL_ok SHADOW_val.
Let grant_new_facts := Asanwqd.grant_new_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok argH_top.
Let grant_vis_add := Asanwqd.grant_vis_add SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high SHADOW_val argH_top.
Let grant_wf := Asanwqd.grant_wf SEGS A RES_len.
Let in_allow_ext := Asanwqd.in_allow_ext A.
Let inside_maps_apart := Asanwqd.inside_maps_apart SEGS A RES_len HULL_ok.
Let kimg_in_hull_cons2 := Asanwqd.kimg_in_hull_cons2 A HULL_ok SHADOW_ok.
Let kimg_in_hull_pure := Asanwqd.kimg_in_hull_pure A.
Let kmem_ok := Asanwqd.kmem_ok SEGS A RES_len HULL_ok.
Let kn_grant_filter_ok := Asanwqd.kn_grant_filter_ok SEGS A RES_len HULL_ok SHADOW_val.
Let kn_rezero_clip_ok := Asanwqd.kn_rezero_clip_ok SEGS A RES_len HULL_ok.
Let kn_rezero_hull_ok := Asanwqd.kn_rezero_hull_ok SEGS A RES_len HULL_ok.
Let kn_rezero_ok_gen := Asanwqd.kn_rezero_ok_gen SEGS A RES_len HULL_ok.
Let kn_unfill_clip_ok := Asanwqd.kn_unfill_clip_ok SEGS A RES_len HULL_ok.
Let maps_match_disjoint := Asanwqd.maps_match_disjoint SEGS A RES_len.
Let mmap_fixed_grant_cs1 := Asanwqd.mmap_fixed_grant_cs1 SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame SHADOW_val argH_top.   (* [comment removed for export] *)
Let mmap_fixed_old_facts := Asanwqd.mmap_fixed_old_facts SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let mmap_fixed_hole_facts := Asanwqd.mmap_fixed_hole_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let fixed_pre := Asanwqd.fixed_pre SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_len_sound := Asanwqd.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_null_cs1 := Asanwqd.mmap_null_cs1 SEGS A nx0 LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok argH_agree SINV_frame SINV_agree RES_cover SHADOW_val NX0_ok argH_top.
Let null_cs1 := Asanwqd.null_cs1 A.
Let overlap_sum_contained := Asanwqd.overlap_sum_contained SEGS A RES_len HULL_ok.
Let page_aligned_sound := Asanwqd.page_aligned_sound SEGS A RES_len.
Let refuse_cont := Asanwqd.refuse_cont SEGS A nx0 LIMIT SINV argH FS0 RES_len SINV_frame.
Let refuse_ok := Asanwqd.refuse_ok SEGS A LIMIT SINV argH FS0 RES_len SINV_frame.
Let region_free_of_apart := Asanwqd.region_free_of_apart SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let regs_ok_regupd_same := Asanwqd.regs_ok_regupd_same SEGS A RES_len.
Let reserved_free_above := Asanwqd.reserved_free_above SEGS A RES_len RES_hull HULL_ok.
Let safe_range_apart := Asanwqd.safe_range_apart SEGS A RES_len HULL_ok SHADOW_val.
Let seps_map_disjoint := Asanwqd.seps_map_disjoint SEGS A RES_len.
Let shadow_facts_new_ok := Asanwqd.shadow_facts_new_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let slice_args := Asanwqd.slice_args SEGS A LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let slice_hyps := Asanwqd.slice_hyps SEGS A LIMIT SINV argH FS0.
Let split_flat_estart := Asanwqd.split_flat_estart SEGS A RES_len HULL_ok.
Let vis_add_inv := Asanwqd.vis_add_inv A LIMIT.
Let vis_add_slice_ok := Asanwqd.vis_add_slice_ok SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high SHADOW_val argH_top.
Let vis_grant_out := Asanwqd.vis_grant_out SEGS A RES_len.
Let page_base_aligned := Asanwqd.page_base_aligned SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_MR_out := Asanwqd.sl_MR_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_bounds := Asanwqd.sl_bounds SEGS A LIMIT SINV argH FS0.
Let sl_eager := Asanwqd.sl_eager SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_in_maps := Asanwqd.sl_in_maps SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_in := Asanwqd.sl_lazy_in SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_out := Asanwqd.sl_lazy_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lohi := Asanwqd.sl_lohi SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_noacc_in := Asanwqd.sl_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_noacc_out := Asanwqd.sl_noacc_out SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_vis_in_E := Asanwqd.sl_vis_in_E SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_in_F := Asanwqd.sl_vis_in_F SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_in_G := Asanwqd.sl_vis_in_G SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_out := Asanwqd.sl_vis_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_wf' := Asanwqd.sl_wf' SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let slice_cs1_ok := Asanwqd.slice_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_top.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_null_sound2 : forall cs kd (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 -> reg_lit cs 10 = Some 0 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some (if kind_lazy kd then 16418 else 34) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = negb (kind_none kd) ->
  mmap_null A nx0 LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd eager visible cs' E R FULL model TB HC Hec H17 H10 H12 H13 H14 H15 Hkind Hkfog Hvisible Hn HK.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_1; dex1 dR_1 as w; dand4 dR_1 as Hf He Hp0 Hp4 | pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_1; dand5 dR_1 as w Hf He Hp0 Hp4 | destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4) ]).
  pose proof Hn as Hn0.
  unfold mmap_null in Hn.
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hnoh].     (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
  apply andb_prop in Hcond as [Hfresh Hnev].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_10 in R10. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  (first [ pose proof ((mmap_len_sound E cs R FULL model ne nlo nhi HC HML)) as dR_2; dand7 dR_2 as R11 Hlen Hne Hnlo HnZ HnZal HneE | destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE) ]).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ).
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.  (* [comment removed for export] *)
  destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as [a0 Ha0g].
  pose proof (grant_ok_na_pin_of_gate _ _ _ _ Hisp Ha0g) as Ha0.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CONT : forall (a : word) model' FULL',
            grant_ok_na_pin model a nZ = true ->
            grant_post kd a n model model' -> grant_mem kd a n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros a model' FULL' Hg GPo GM Hfs.
    (first [ pose proof ((mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev
                ltac:(intros ->; cbn in Hbud; unfold budget_ok in Hbud; apply Z.leb_le in Hbud; exact Hbud)
                Hkind Hkfog Hnoh Hg GPo GM)) as dR_3; dand6 dR_3 as HC1 Hbase HneE' Un Hag0 NEW | destruct (mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev
                ltac:(intros ->; cbn in Hbud; unfold budget_ok in Hbud; apply Z.leb_le in Hbud; exact Hbud)
                Hkind Hkfog Hnoh Hg GPo GM) as (HC1 & Hbase & HneE' & Un & Hag0 & NEW) ]).
    fold len nZ n in HC1, HneE', Un, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      (first [ pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_4; dex1 dR_4 as nhi2; destruct dR_4 as [_ ->] | pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_4; dand3 dR_4 as nhi2 _ -> | destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->) ]). reflexivity. }
    specialize (HK E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    - (* [comment removed for export] *)
      assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hvisible |- *; congruence).
      pose proof (u64_range a) as Ra.
      unfold grant_ok_na_pin in Hg. apply andb_prop in Hg as [Hg _].
      apply andb_prop in Hg as [Hg Hceil]. apply Z.leb_le in Hceil. pose proof (alloc_top_lt (m_vmmaps model)) as HTlt. unfold two_pow_64 in HTlt.
      eapply (grant_vis_add E' (null_cs1 cs kd eager ne nlo nhi) cs' _ ne _ FULL' model' a n nZ HC1 Hn).
      + unfold null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
        apply kimg_in_hull_pure. apply Forall_cons; [exact I | apply (proj2 (Forall_app _ _ _)); split; [apply null_kend_pure | apply kdisj_new_pure]].
      + exact Hbase.
      + exact HneE'.
      + exact Un.
      + lia.
      + lia.
      + intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_5; dand4 dR_5 as N1 N2 N3 _ | destruct (NEW x Hx) as (N1 & N2 & N3 & _) ]). rewrite (gp_noacc _ _ _ _ _ GPo), Hrw. auto.
      + intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity.
    - injection Hn as <-. exact HC1. }
  (* [comment removed for export] *)
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  - (* [comment removed for export] *)
    destruct eager; [|discriminate].
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. split; [exact Ha0|]. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
      apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + intros a Hg _. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. split; [exact Ha0|]. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4022. reflexivity.
    + intros a Hg _. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * pose proof Hg as Hg'. unfold grant_ok_na_pin in Hg'. apply andb_prop in Hg' as [Hg' _].
        apply andb_prop in Hg' as [Hg' Hceil]. apply andb_prop in Hg' as [Hal Hpos].
        apply Z.eqb_eq in Hal. apply Z.leb_le in Hceil. pose proof (alloc_top_lt (m_vmmaps model)) as HTlt. unfold two_pow_64 in HTlt. unfold page_size in Hal.
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt Hisp R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * pose proof Hg as Hg'. unfold grant_ok_na_pin in Hg'. apply andb_prop in Hg' as [Hg' _].
        apply andb_prop in Hg' as [Hg' Hceil]. apply andb_prop in Hg' as [Hal Hpos].
        apply Z.eqb_eq in Hal. apply Z.leb_le in Hceil. pose proof (alloc_top_lt (m_vmmaps model)) as HTlt. unfold two_pow_64 in HTlt. unfold page_size in Hal.
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_fixed_grant_sound2 : forall (nore : bool) cs ms0 top b off ne nlo nhi kd (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some (if nore then 1064994 else if kind_lazy kd then 16434 else 50) ->
  (nore = true -> kind_lazy kd = true) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  (negb eager || budget_ok LIMIT cs nhi)%bool = true ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
     \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
  (bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= KHI
   \/ a_ylo cs <= bv_unsigned (edenot E (reg cs 10))) ->
  mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros nore cs ms0 top b off ne nlo nhi kd eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hnore H14 H15 Hkind Hkfog Hvisible HFA Htop Hbud HC0 Hrf Hholes Hside Hn HK.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_6; dex1 dR_6 as w; dand4 dR_6 as Hf He Hp0 Hp4 | pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_6; dand5 dR_6 as w Hf He Hp0 Hp4 | destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4) ]).
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
  unfold mmap_fixed_grant in Hn.
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  (first [ pose proof ((fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA)) as dR_7; dand3 dR_7 as Hsp HML _ | destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & _) ]).
  (first [ pose proof ((mmap_len_sound E cs R FULL model ne nlo nhi HC HML)) as dR_8; dand3 dR_8 as R11 Hlen _ | destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _) ]).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (first [ pose proof ((fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop)) as dR_9; dand10 dR_9 as HneE Un Hest Hal Hpos Himg HtopA R10 HnZal HnZ | destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop)
    as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ) ]).
  fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaK : bv_unsigned addr + nZ <= CEIL) by lia.   (* [comment removed for export] *)
  rewrite <- bv5_10 in R10.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_ceiling) by (rewrite CEIL_eq; fold nZ; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CONT : forall model' FULL',
            grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' GPo GM Hfs.
    destruct (mmap_fixed_grant_cs1 cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 Hrf Hholes Hside Hbudget Hkind Hkfog GPo GM) as (HC1 & NEW).
    fold len nZ n addr in HC1, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      (first [ pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_10; dex1 dR_10 as nhi2; destruct dR_10 as [_ ->] | pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_10; dand3 dR_10 as nhi2 _ -> | destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->) ]). reflexivity. }
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    - (* [comment removed for export] *)
      subst eager. assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hkind |- *; congruence).
      pose proof (u64_range addr) as Ra.
      eapply (vis_add_sound'); [exact Hn | exact HC1 |].
      (first [ pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_11; dex1 dR_11 as nhi2; destruct dR_11 as [_ Ecs2] | pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_11; dand3 dR_11 as nhi2 _ Ecs2 | destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs2) ]).
      apply Forall_app. split.
      + (* [comment removed for export] *)
        assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat, elenZ; rewrite Hest, HneE, Un; unfold CEIL in HaK; lia).
        assert (BYTE : forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
                  MR E cs' model' FULL' x = Some (Z_to_bv 8 0)).
        { intros x Hx. (first [ pose proof ((NEW x Hx)) as dR_12; dand3 dR_12 as N1 N2 N3 | destruct (NEW x Hx) as (N1 & N2 & N3) ]).
          unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1. rewrite (gp_noacc _ _ _ _ _ GPo), Hrw, N2. cbn [negb andb].
          assert (Hallow : in_allow A E cs' (bv_unsigned x) = true).
          { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd with_maps0]. unfold uE. fold addr. rewrite HneE, Un.
            rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
          rewrite Hallow, !orb_true_r. cbn [negb]. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity. }
        constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; unfold elenZ; rewrite Hest, HneE, Un.
        * intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
          apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in HaK; lia); unfold CEIL in HaK; lia|].
          intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in HaK; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
        * intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in HaK; lia). lia.
      + (* [comment removed for export] *)
        pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
        eapply know_ok_unhide'; [apply H_off_segments_cs' | | | | exact HK1].
        * unfold fixed_cs1, add_entry. cbn [kn a_ss mk_ss s_know with_maps0]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
          destruct kd; cbn [mkind_eqb]; try (apply kimg_in_hull_pure; apply Forall_nil).
          apply kimg_in_hull_pure. apply Forall_flat_map. apply Forall_forall. intros p _. unfold shadow_facts.
          destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn].
          destruct (find_containing _ _ _ _ _ _); [| destruct (split_lit (fst p)) as [bb bk]; destruct (band_split _ _ _ _ _ _ _ _ _); [|apply Forall_nil]];
            (apply Forall_cons; [exact I|]; apply Forall_cons; [exact I|]; apply Forall_nil).
        * intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
        * intros y Hy. apply hid_hull'. exact Hy.
    - injection Hn as <-. exact HC1. }
  (* [comment removed for export] *)
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  - (* [comment removed for export] *)
    destruct eager; [|discriminate]. destruct nore; [discriminate (Hnore eq_refl)|].
    eapply (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 (or_introl mmap_flags_core_32) R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_32. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    assert (HCORE : mmap_flags_core (Z_to_bv 64 (if nore then 1064994 else 16434)) = 50 \/ mmap_flags_core (Z_to_bv 64 (if nore then 1064994 else 16434)) = 1048610)
      by (destruct nore; [right; exact mmap_flags_core_104022 | left; exact mmap_flags_core_4032]).
    assert (HNR : mmap_noreserve_b (Z_to_bv 64 (if nore then 1064994 else 16434)) = true)
      by (destruct nore; [exact mmap_noreserve_b_104022 | exact mmap_noreserve_b_4032]).
    eapply (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 (if nore then 1064994 else 16434)) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 HCORE R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite HNR. reflexivity.
    + rewrite with_mmap_backing_lazy by apply HNR.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. destruct nore; [discriminate (Hnore eq_refl)|].
    eapply (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 (or_introl mmap_flags_core_32) R14 R15 Hrf).
    + rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    assert (HCORE : mmap_flags_core (Z_to_bv 64 (if nore then 1064994 else 16434)) = 50 \/ mmap_flags_core (Z_to_bv 64 (if nore then 1064994 else 16434)) = 1048610)
      by (destruct nore; [right; exact mmap_flags_core_104022 | left; exact mmap_flags_core_4032]).
    assert (HNR : mmap_noreserve_b (Z_to_bv 64 (if nore then 1064994 else 16434)) = true)
      by (destruct nore; [exact mmap_noreserve_b_104022 | exact mmap_noreserve_b_4032]).
    eapply (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 (if nore then 1064994 else 16434)) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 HCORE R14 R15 Hrf).
    + rewrite with_mmap_backing_lazy by apply HNR.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Lemma mmap_fixed_free_sound2 : forall (nore : bool) cs kd (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some (if nore then 1064994 else if kind_lazy kd then 16434 else 50) ->
  (nore = true -> kind_lazy kd = true) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros nore cs kd eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hnore H14 H15 Hkind Hkfog Hvisible Hn HK.
  unfold mmap_fixed_free in Hn.
  destruct (fixed_args A cs KHI) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
  - (* [comment removed for export] *)
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall].
    (first [ pose proof ((mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall)) as dR_13; dand4 dR_13 as HC0 Hrf Hholes Hside | destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes & Hside) ]).
    eapply (mmap_fixed_grant_sound2 nore cs (a_maps cs) KHI b off ne nlo nhi kd eager visible cs' E R FULL model TB
              HC Hec H17 H12 H13 Hnore H14 H15 Hkind Hkfog Hvisible HFA ltac:(unfold KHI, CEIL; lia) Hbud
              HC0 Hrf Hholes Hside Hn HK).
  - (* [comment removed for export] *)
    destruct (fixed_args A cs CEIL) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA2; [|discriminate].
    destruct (find_hole (kn cs) (a_maps cs) (reg cs 10) ne) as [h|] eqn:Hfh; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hap Hbud].
    (first [ pose proof ((mmap_fixed_hole_facts cs b off ne nlo nhi h E R FULL model HC HFA2 Hfh Hap)) as dR_14; dand4 dR_14 as HC0 Hrf Hholes Hside | destruct (mmap_fixed_hole_facts cs b off ne nlo nhi h E R FULL model HC HFA2 Hfh Hap) as (HC0 & Hrf & Hholes & Hside) ]).
    eapply (mmap_fixed_grant_sound2 nore cs (unhole (a_maps cs) h) CEIL b off ne nlo nhi kd eager visible cs' E R FULL model TB
              HC Hec H17 H12 H13 Hnore H14 H15 Hkind Hkfog Hvisible HFA2 ltac:(lia) Hbud
              HC0 Hrf Hholes Hside Hn HK).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_mprotect_sound2 : forall cs cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_mprotect A LIMIT cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs cs' E R FULL model TB HC Hec Hn HK.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_15; dex1 dR_15 as w; dand4 dR_15 as Hf He Hp0 Hp4 | pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_15; dand5 dR_15 as w Hf He Hp0 Hp4 | destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4) ]).
  rewrite node_mprotect_eq in Hn. (* [comment removed for export] *) unfold node_mprotect_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [z12|] eqn:H12.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (fixed_args_in cs) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.   (* [comment removed for export] *)
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 226 /\ z12 = 3).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->].
  destruct (find_containing (kn cs) (a_maps cs) [KNONE; KNONELAZY] b off ne) as [m|] eqn:Hfind; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hbud _].
  unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
  destruct (reg_lit_sound' E cs R FULL model 17 226 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 3 HC ltac:(lia) H12) as [R12 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12.
  (first [ pose proof ((slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)) as dR_16; dand20 dR_16 as Hm [Hkind Hnf] R10 R11 Hlen Hne Un HnZpos HnZ HnZal Hal Hpos Himg Hest Hin1 Hin2 HmC Hmc Hrfres Hov | destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov) ]).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.  (* [comment removed for export] *)
  pose proof (u64_range addr) as Ra.
  assert (Hkind' : am_kind m = KNONE \/ am_kind m = KNONELAZY) by (cbn in Hkind; destruct Hkind as [<-|[<-|[]]]; auto).
  (* [comment removed for export] *)
  assert (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true).
  { pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hkind') as X.
    eapply map_contains_intro; [exact X | exact Hin1 | rewrite Un; exact Hin2]. }
  unfold cfg_of.
  eapply (srz_mprotect1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len TB Hf He Hhalt R17 R10 Hal R11 ltac:(lia)).
  - unfold two_pow_64. fold nZ. unfold TOPMAX in HmC. lia.
  - exact R12.
  - exact Hna.
  - exact Hmc.
  - apply mprotect_budget_ok_intro_gen; [exact Hwf|]. pose proof (budget_slack E cs R FULL model nhi HC ltac:(unfold budget_ok; apply Z.leb_le; exact Hbud)). fold nZ n. lia.
  - fold nZ. fold n.
    set (model' := mprotect_model addr n model). set (FULL' := zfill addr n FULL).
    assert (SPo : slice_post SlM addr n model model') by (constructor; reflexivity).
    assert (SM : slice_mem SlM addr n FULL FULL').
    { split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
    assert (SH : slice_hyps E cs R FULL model SlM m addr n nZ model' FULL').
    { constructor; try assumption; intros HH; [discriminate HH|]. intros Hk. rewrite Hk in Hkind'. destruct Hkind'; discriminate. }
    rewrite (v_addi_pc (pc cs) Hp0 Hp4).
    (first [ pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_17; dex1 dR_17 as nhi2; destruct dR_17 as [_ Ecs'] | pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_17; dand3 dR_17 as nhi2 _ Ecs' | destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs') ]).
    assert (Hpc : pc cs' = pc cs + 4) by (rewrite Ecs'; reflexivity).
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc, <- bv5_10 in HK. apply HK; [|reflexivity]. clear HK.
    assert (Hregs' : regs_ok E (sr_upd (s_regs (a_ss cs)) 10 (ELit 0)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0))).
    { apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | reflexivity]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model SlM m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
    { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
    pose proof (slice_cs1_ok E cs R FULL model SlM m addr n nZ model' FULL' SH _ _ _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
    cbn [sl_charge] in HC1.
    eapply (vis_add_slice_ok E _ cs' (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
    + exact Hn.
    + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
    + reflexivity.
    + exact Hest.
    + unfold elenZ. rewrite Hne. exact Un.
    + lia.
    + lia.
    + lia.
    + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
      split; [exact (sl_in_maps E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [exact (sl_noacc_in E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [destruct (argH E x) eqn:Ea; [pose proof (cs_argH_top E cs R FULL model x HC Ea);
              (first [ pose proof ((sl_bounds E cs R FULL model SlM m addr n nZ model' FULL' SH)) as dR_18; dand5 dR_18 as _ _ _ _ B5A | pose proof (sl_bounds E cs R FULL model SlM m addr n nZ model' FULL' SH) as (_ & _ & _ & _ & B5A) ]); lia | reflexivity]|].
      rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gate_sound : forall cs prot flags isnull,
  mmap_gate cs = Some (prot, flags, isnull) ->
  reg_lit cs 17 = Some 222 /\ reg_lit cs 12 = Some prot /\ reg_lit cs 13 = Some flags
  /\ reg_lit cs 14 = Some (two64 - 1) /\ reg_lit cs 15 = Some 0
  /\ (isnull = true -> reg_lit cs 10 = Some 0).
Proof.
  intros cs prot flags isnull Hg. unfold mmap_gate in Hg.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [p|] eqn:H12.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 13) as [f|] eqn:H13.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 14) as [m1|] eqn:H14.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 15) as [z15|] eqn:H15.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 222 /\ z15 = 0).
  { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->]. cbn iota in Hg.
  match type of Hg with (if negb ?c then None else _) = _ => destruct c eqn:Hm1; [|discriminate] end. cbn [negb] in Hg.
  apply Z.eqb_eq in Hm1. subst m1. injection Hg as <- <- <-.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity.
  destruct (reg_lit cs 10) as [[|p10|p10]|]; intros H; try discriminate H. reflexivity.
Qed.

Theorem node_mmap2_sound : mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Proof.
  intros cs csa csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmap2 in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  (first [ pose proof ((mmap_gate_sound cs prot flags isnull Hg)) as dR_19; dand6 dR_19 as H17 H12 H13 H14 H15 H10 | destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10) ]).
  match type of Hn with (match ?g with Some csG => _ | None => None end) = _ => destruct g as [csG|] eqn:HG; [|discriminate] end.
  injection Hn as <- <-.
  destruct isnull.
  - specialize (H10 eq_refl).
    assert (ARMS : (prot = 3 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KRW true true = Some csG)
                   \/ (prot = 3 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KRWLAZY false true = Some csG)
                   \/ (prot = 0 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KNONE false false = Some csG)
                   \/ (prot = 0 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KNONELAZY false false = Some csG)).
    { repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]].
    + eapply (mmap_null_sound2 cs KRW true true); eauto; reflexivity.
    + eapply (mmap_null_sound2 cs KRWLAZY false true); eauto; reflexivity.
    + eapply (mmap_null_sound2 cs KNONE false false); eauto; reflexivity.
    + eapply (mmap_null_sound2 cs KNONELAZY false false); eauto; reflexivity.
  - assert (ARMS : (prot = 3 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
                   \/ (prot = 3 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KRW true true = Some csG)
                   \/ (prot = 0 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)
                   \/ (prot = 0 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KNONE false false = Some csG)
                   \/ (prot = 3 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)     (* [comment removed for export] *)
                   \/ (prot = 0 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)). (* [comment removed for export] *)
    { repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]]]].
    + eapply (mmap_fixed_free_sound2 false cs KRWLAZY false false); eauto; try reflexivity; discriminate.
    + eapply (mmap_fixed_free_sound2 false cs KRW true true); eauto; try reflexivity; discriminate.
    + eapply (mmap_fixed_free_sound2 false cs KNONELAZY false false); eauto; try reflexivity; discriminate.
    + eapply (mmap_fixed_free_sound2 false cs KNONE false false); eauto; try reflexivity; discriminate.
    + eapply (mmap_fixed_free_sound2 true cs KRWLAZY false false); eauto; reflexivity.
    + eapply (mmap_fixed_free_sound2 true cs KNONELAZY false false); eauto; reflexivity.
Qed.

Theorem node_mprotect2_sound : mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Proof.
  intros cs csa csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mprotect2 in Hn.
  destruct (node_mprotect A LIMIT cs) as [csG|] eqn:HG; [|discriminate]. injection Hn as <- <-.
  eapply node_mprotect_sound2; eauto.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slarm_of (arm : fixed_in_arm) : slarm := match arm with ArmE => SlE | ArmF => SlF | ArmG => SlG end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_fixed_in_sound3 : forall (hole : bool) cs arm b off ne nlo nhi m csO E R FULL model (TB : TSet),
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
  reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  fixed_in_args cs arm = Some (b, off, ne, nlo, nhi, m) ->
  mmap_fixed_in A LIMIT cs arm = Some csO ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csO R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc csO) FULL' model') TB) ->
  (* [comment removed for export] *)
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros hole cs arm b off ne nlo nhi m csO E R FULL model TB HC Hec H17 H12 H13 H14 H15 HFI Hn HKB.
  (first [ pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_20; dex1 dR_20 as w; dand4 dR_20 as Hf He Hp0 Hp4 | pose proof ((is_ecall_at_sound SEGS cs Hec)) as dR_20; dand5 dR_20 as w Hf He Hp0 Hp4 | destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4) ]).
  (* [comment removed for export] *)
  rewrite fixed_in_args_eq in HFI. (* [comment removed for export] *) unfold fixed_in_args_ref in HFI.
  destruct (fixed_args_in cs) as [[[[[b0 off0] ne0] nlo0] nhi0]|] eqn:HFA; [|discriminate].   (* [comment removed for export] *)
  destruct (find_containing (kn cs) (a_maps cs) _ b0 off0 ne0) as [m0|] eqn:Hfind; [|discriminate].
  match type of HFI with (if ?c then _ else _) = _ => destruct c eqn:Hvars; [|discriminate] end.
  injection HFI as -> -> -> -> -> ->.
  rewrite mmap_fixed_in_eq in Hn. (* [comment removed for export] *) unfold mmap_fixed_in_ref in Hn. rewrite fixed_in_args_eq in Hn. unfold fixed_in_args_ref in Hn. rewrite HFA, Hfind, Hvars in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hbud; [|discriminate] end.
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  (first [ pose proof ((slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)) as dR_21; dand20 dR_21 as Hm [Hkind Hnf] R10 R11 Hlen Hne Un HnZpos HnZ HnZal Hal Hpos Himg Hest Hin1 Hin2 HmC Hmc Hrfres Hov | destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov) ]).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.  (* [comment removed for export] *)
  pose proof (u64_range addr) as Ra.
  (* [comment removed for export] *)
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)).
  { fold nZ. (first [ pose proof ((proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m)
                 (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf))) as dR_22; dand5 dR_22 as _ _ _ _ B5A | pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m)
                 (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)) as (_ & _ & _ & _ & B5A) ]). cbn [amap_den fst snd] in B5A. lia. }
  assert (HF : slarm_of arm = SlF -> am_kind m = KRWLAZY).
  { intros Hs. destruct arm; try discriminate. cbn in Hkind. destruct Hkind as [<-|[]]. reflexivity. }
  assert (HnF : slarm_of arm <> SlF -> am_kind m <> KRWLAZY).
  { intros Hs Hk. destruct arm; [|exact (Hs eq_refl)|]; cbn in Hkind; rewrite Hk in Hkind; destruct Hkind as [|[|[|[]]]]; discriminate. }
  set (prot := match arm with ArmG => 0 | _ => 3 end) in *.
  set (flg := match arm with ArmF => 16434 | _ => 50 end) in *.
  assert (Hprot : prot = 0 \/ prot = 3) by (destruct arm; cbn; lia).
  assert (Hcore : mmap_flags_core (Z_to_bv 64 flg) = 50) by (destruct arm; [apply mmap_flags_core_32 | apply mmap_flags_core_4032 | apply mmap_flags_core_32]).
  (* [comment removed for export] *)
  assert (CONTB : forall model' FULL',
            slice_post (slarm_of arm) addr n model model' -> slice_mem (slarm_of arm) addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' SPo SM Hfs.
    assert (SH : slice_hyps E cs R FULL model (slarm_of arm) m addr n nZ model' FULL') by (constructor; assumption).
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc csO = pc cs + 4).
    { destruct arm; try (injection Hn as <-; reflexivity). (first [ pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_23; dex1 dR_23 as nhi2; destruct dR_23 as [_ ->] | pose proof ((vis_add_inv _ _ _ _ _ Hn)) as dR_23; dand3 dR_23 as nhi2 _ -> | destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->) ]). reflexivity. }
    specialize (HKB E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HKB. rewrite Hpc in HKB. apply HKB; [|exact Hfs]. clear HKB.
    assert (Hregs' : regs_ok E (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)).
    { apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | rewrite <- bv5_10; exact R10]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    pose proof (slice_cs1_ok E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)) as CS1.
    destruct arm; cbn [slarm_of sl_charge] in *.
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
      { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
      unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
      pose proof (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
      eapply (vis_add_slice_ok E _ csO (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
      + exact Hn.
      + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
      + reflexivity.
      + exact Hest.
      + unfold elenZ. rewrite Hne. exact Un.
      + lia.
      + lia.
      + lia.
      + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
        split; [exact (sl_in_maps E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [exact (sl_noacc_in E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [destruct (argH E x) eqn:Ea; [pose proof (cs_argH_top E cs R FULL model x HC Ea);
                (first [ pose proof ((sl_bounds E cs R FULL model SlE m addr n nZ model' FULL' SH)) as dR_24; dand5 dR_24 as _ _ _ _ B5A | pose proof (sl_bounds E cs R FULL model SlE m addr n nZ model' FULL' SH) as (_ & _ & _ & _ & B5A) ]); lia | reflexivity]|].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_rezero (kn cs) b off ne))).
      { eapply kn_rezero_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT' |].
        intros x Hx Hdef. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx.
        unfold Mr, mrestrict, hid in Hdef |- *.
        rewrite (sl_vis_in_F E cs R FULL model SlF m addr n nZ model' FULL' SH eq_refl cs x eq_refl Hx).
        destruct (argH E x); [exfalso; apply Hdef; reflexivity|]. cbn [orb] in *.
        destruct (VIS E cs model x); [|exfalso; apply Hdef; reflexivity]. cbn [negb].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)).
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_cutout (kn cs) b off ne))).
      { apply know_ok_filter. eapply (APS.know_ok_cutout SEGS); [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact MROUT']. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)). }
  (* [comment removed for export] *)
  unfold cfg_of.
  assert (R12' : getr R 12 = Z_to_bv 64 prot) by (destruct arm; exact R12).
  assert (R13' : getr R 13 = Z_to_bv 64 flg) by (destruct arm; exact R13).
  eapply (srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w prot (Z_to_bv 64 flg) addr len TB
            Hf He Hhalt R17 Hprot Hcore R10 Hal Hpos R11 ltac:(lia) Hce R12' R13' R14 R15 Hrfres Hmc).
  - (* [comment removed for export] *) intros Hp3. fold nZ n. destruct arm; cbn in Hp3; try discriminate Hp3; subst flg.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
      unfold budget_ok in Hbud. pose proof (budget_slack E cs R FULL model nhi HC Hbud). lia.
    + apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact Hwf | exact Hal | unfold page_size; rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, TOPMAX in *; lia |].
      eapply vm_backing_used_limit; [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | apply A_wf_allowA'].
  - fold nZ. fold n. destruct arm; subst prot flg; cbn [Z.eqb slarm_of] in CONTB |- *.
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
      apply CONTB; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_vm_forget_range.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, TOPMAX in *; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Theorem node_mmapin_sound : forall hole : bool, mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).
Proof.
  intros hole cs csa csb cscs E R FULL model TB HC Hec Hn HKB.
  unfold node_mmapin in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  (first [ pose proof ((mmap_gate_sound cs prot flags isnull Hg)) as dR_25; dand6 dR_25 as H17 H12 H13 H14 H15 _ | destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & _) ]).
  destruct isnull; [discriminate|]. cbv zeta in Hn.
  assert (CASES : forall arm,
     reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
     reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
     match fixed_in_args cs arm, mmap_fixed_in A LIMIT cs arm with
     | Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed A hole cs b off ne m)
     | _, _ => None
     end = Some (csa, csb, cscs) ->
     srealizes SEGS (cfg R (pc cs) FULL model) TB).
  { intros arm H12' H13' Hn'.
    destruct (fixed_in_args cs arm) as [[[[[[b off] ne] nlo] nhi] m]|] eqn:HFI; [|discriminate].
    destruct (mmap_fixed_in A LIMIT cs arm) as [csO|] eqn:HO; [|discriminate]. injection Hn' as <- <- <-.
    eapply (mmap_fixed_in_sound3 hole cs arm b off ne nlo nhi m csO); eauto. }
  destruct prot as [|p|p]; try discriminate Hn; try (repeat (destruct p as [p|p|]; try discriminate Hn));
  destruct flags as [|q|q]; try discriminate Hn; try (repeat (destruct q as [q|q|]; try discriminate Hn));
  refine (CASES _ _ _ Hn); first [exact H12 | exact H13].
Qed.

End Nodes.

(* [comment removed for export] *)
Theorem node_mmap2_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A ->
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  (* [comment removed for export] *)
  APS.res_cover_ok SEGS A -> APS.shadow_val_ok A -> APS.nx0_ok nx0 ->
  (forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a) ->
  OBL_mmap2 SEGS A nx0 LIMIT SINV argH FS0.
Proof. intros. unfold OBL_mmap2. eapply node_mmap2_sound; eauto. Qed.

Theorem node_mprotect2_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A ->
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  (* [comment removed for export] *)
  APS.res_cover_ok SEGS A -> APS.shadow_val_ok A -> APS.nx0_ok nx0 ->
  (forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a) ->
  OBL_mprotect2 SEGS A nx0 LIMIT SINV argH FS0.
Proof. intros. unfold OBL_mprotect2. eapply node_mprotect2_sound; eauto. Qed.

Theorem node_mmapin_sound_OBL : forall SEGS A nx0 LIMIT SINV argH FS0,
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A ->
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  (* [comment removed for export] *)
  APS.res_cover_ok SEGS A -> APS.shadow_val_ok A -> APS.nx0_ok nx0 ->
  (forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a) ->
  OBL_mmapin SEGS A nx0 LIMIT SINV argH FS0.
Proof. intros. unfold OBL_mmapin. eapply node_mmapin_sound; eauto. Qed.
