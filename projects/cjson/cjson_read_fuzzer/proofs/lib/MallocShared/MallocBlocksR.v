(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_malloc_enframe.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_mm_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocBlocks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_free_C.
Module F_free.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_malloc_enframe OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_mm_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_free_C.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
                /\ r_base r <= a < r_base r + round_up_pg (r_len r).

(* [comment removed for export] *)
Definition lbrm (LB : list block) (blk : block) : list block :=
  filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oracle_ok_refl m st : oracle_ok m m st.
Proof. intros rid r q h _ _ _ _ _. reflexivity. Qed.

Lemma oracle_ok_hdr_st o m st pf : ticks_ok st -> oracle_ok o m st -> oracle_ok o m (hdr_st st pf).
Proof.
  intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
  rewrite hdr_st_cell_read in Hc by exact TK.
  destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
  - apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - reflexivity.
Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof.
  pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
  set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cover_intervals tac :=
  let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros lo0 hi0 HW y Hy; cbn [In] in HW;
  repeat (destruct HW as [HW|HW]); try contradiction;
  injection HW; intros; subst lo0 hi0; tac y Hy.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
  List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
  (forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
  induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
  rewrite IH by (intros x Hx; apply HE; right; exact Hx).
  destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
    pose proof (HE a (or_introl eq_refl)); tauto.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac cover_intervals tac :=
  let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros lo0 hi0 HW y Hy; cbn [In] in HW;
  repeat (destruct HW as [HW|HW]); try contradiction;
  injection HW; intros; subst lo0 hi0; tac y Hy.
End F_free.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Malloc_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_inv3.
Module F_free_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocBlocks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_A.MallocHINV OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.Malloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prog.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_free_K F_free.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Lemma lb_remove_lbrm LB (p : bptr) A n : List.NoDup (map blk_slot LB) -> In (p, A, n) LB ->
  lb_remove p LB = lbrm LB (p, A, n).
Proof.
  intros ND Hin. unfold lb_remove, lbrm. apply filter_ext_in. intros x Hx.
  unfold bptr_eqb, blk_id, blk_slot. cbn [fst snd].
  destruct (aptr_eqb_spec' (fst (fst (fst x))) (fst p)) as [E|NE]; cbn [andb negb].
  - pose proof (NoDup_map_inj_in blk_slot LB ND x (p, A, n) Hx Hin E) as ->. cbn. rewrite Z.eqb_refl. cbn. tauto.
  - tauto.
Qed.

Lemma NoDup_map_perm {A B} (f : A -> B) (l l' : list A) : Permutation l l' -> List.NoDup (map f l) -> List.NoDup (map f l').
Proof. intros P ND. eapply Permutation_NoDup; [apply Permutation_map; exact P| exact ND]. Qed.

Lemma lbrm_perm LB LB' blk : Permutation LB LB' -> Permutation (lbrm LB blk) (lbrm LB' blk).
Proof. intros P. unfold lbrm. apply filter_Permutation. exact P. Qed.

Lemma In_lbrm_perm LB LB' blk b : Permutation LB LB' -> In b (lbrm LB blk) -> In b (lbrm LB' blk).
Proof. intros P H. eapply Permutation_in; [apply lbrm_perm; exact P| exact H]. Qed.

End CeilWrap.
End F_free_spec.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext MI_Contracts Realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocRep MallocTree MallocBlocks Malloc_iface.
Import F_free.
Import F_free_spec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocFacts_inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WRemap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WRemap.MI_WRealloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WRemap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KB_ReallocR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KB_ReallocR.MI_WRemap2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma conc_cs_remap cs rid g d nn q : s_regions cs !! rid <> None ->
  conc (cs_remap cs rid g d nn) q = if (fst q =? rid)%N then d + snd q else conc cs q.
Proof.
  intros Hr. unfold cs_remap, conc, get_region, upd_meta, upd_region, get_region. cbn.
  destruct (s_regions cs !! rid) as [r|] eqn:E; [| exfalso; exact (Hr eq_refl)]. cbn.
  destruct (N.eqb_spec (fst q) rid) as [->|NE]; [rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma conc_rr_remap_full st c up n d nn g idx q : s_slots st !! c = Some (g, idx) -> s_regions st !! (fst c) <> None ->
  conc (rr_remap_full st c up n d nn) q = if (fst q =? fst c)%N then d + snd q else conc st q.
Proof.
  intros Hs Hr. rewrite <- conc_strip, strip_rr_remap_full, Hs. rewrite conc_cs_remap by exact Hr. rewrite conc_strip. reflexivity.
Qed.

Lemma s_secret_rr_remap_full st c up n d nn : s_secret (rr_remap_full st c up n d nn) = s_secret st.
Proof.
  assert (SS : forall p e n0 i s, s_secret (set_size_i p e n0 i s) = s_secret s).
  { intros. unfold set_size_i. destruct (5 <=? _); destruct (negb _); reflexivity. }
  assert (SH : forall p n0 s, s_secret (havoc p n0 s) = s_secret s) by (intros; unfold havoc; destruct (n0 <=? 0); reflexivity).
  unfold rr_remap_full. destruct (s_slots st !! c) as [[g idx]|]; [| reflexivity].
  rewrite SH, SS. unfold upd_region, get_region. cbn. destruct (s_regions st !! fst c); reflexivity.
Qed.

Lemma s_secret_rr_inplace_full st c up n : s_secret (rr_inplace_full st c up n) = s_secret st.
Proof.
  assert (SS : forall p e n0 i s, s_secret (set_size_i p e n0 i s) = s_secret s).
  { intros. unfold set_size_i. destruct (5 <=? _); destruct (negb _); reflexivity. }
  assert (SH : forall p n0 s, s_secret (havoc p n0 s) = s_secret s) by (intros; unfold havoc; destruct (n0 <=? 0); reflexivity).
  unfold rr_inplace_full. destruct (s_slots st !! c) as [[g idx]|]; [| reflexivity]. rewrite SH, SS. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma corr_replace st st' LB BL (p : bptr) A k A' n off :
  CORR st LB BL -> NoDup (map bslot BL) -> In (p, A, k) LB ->
  A' = conc st' (fst p) + UNIT * off ->
  (forall k', In k' (bl_remove (fst p) BL) -> conc st' (bslot k') = conc st (bslot k')) ->
  CORR st' ((p, A', n) :: lbrm LB (p, A, k)) (((fst p, off), n) :: bl_remove (fst p) BL).
Proof.
  intros CR ND Hin EA CC. constructor.
  - split; [reflexivity|]. split; [reflexivity|]. exact EA.
  - rewrite (bl_remove_filter (fst p) BL ND). unfold lbrm. unfold blk_slot at 2. cbn [fst snd].
    pose proof (Forall2_filter (corr1 st) (fun b' : block => negb (aptr_eqb (blk_slot b') (fst p))) (fun k0 : blk => negb (aptr_eqb (bslot k0) (fst p))) LB BL CR
                  ltac:(intros b' k' (D1 & _ & _); rewrite D1; reflexivity)) as CRF.
    eapply Forall2_impl_in; [exact CRF|]. intros b' k' Hb' Hk' (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. rewrite D3.
    rewrite CC; [reflexivity|]. rewrite (bl_remove_filter (fst p) BL ND). exact Hk'.
Qed.

(* [comment removed for export] *)
Theorem aext_inplace : forall resv st LB (p : bptr) A k n off,
  In (p, A, k) LB -> 0 <= off -> A = conc st (fst p) + UNIT * off -> 0 <= n ->
  (forall g i, s_slots st !! (fst p) = Some (g, i) -> UNIT * off + n <= get_stride (MR st g) - IB /\ get_stride (MR st g) - IB - UNIT * off - n < 2^32) ->
  AEXT resv st LB (rr_inplace_full st (fst p) (aadd (fst p) (UNIT * off)) n) ((p, A, n) :: lbrm LB (p, A, k)).
Proof.
  intros resv st LB p A k n off Hin Ho EA Hn HF (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hin) as (kb & Hkb & (C1 & C2 & C3)).
  destruct kb as [[c off'] k']. unfold blk_slot, blk_size, blk_addr, bslot, bsize, boff in C1, C2, C3. cbn [fst snd] in C1, C2, C3. subst k' c.
  assert (off' = off) by (unfold UNIT in *; lia). subst off'.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (rr_inplace_INVL st L BL LS (fst p) off k n INV Hkb Hn
              ltac:(intros m i Hs; exact (proj1 (HF m i Hs))) ltac:(intros m i Hs; exact (proj2 (HF m i Hs)))) as [INV' CE].
  exists (set_live (map bslot (((fst p, off), n) :: bl_remove (fst p) BL)) L), LS, (((fst p, off), n) :: bl_remove (fst p) BL).
  split; [exact INV'|]. split; [reflexivity|]. split; [exact RESV|]. split; [rewrite s_secret_rr_inplace_full; exact SEC|].
  eapply corr_replace; [exact CR| exact (is_nodup _ _ _ IS)| exact Hin| |].
  - unfold conc, get_region. rewrite (ce_regions _ _ CE). exact EA.
  - intros k' _. unfold conc, get_region. rewrite (ce_regions _ _ CE). reflexivity.
Qed.

(* [comment removed for export] *)
Theorem aext_remap : forall resv st LB (p : bptr) A k n off d nn g idx,
  In (p, A, k) LB -> 0 <= off -> A = conc st (fst p) + UNIT * off -> 0 <= n ->
  s_slots st !! (fst p) = Some (g, idx) -> 48 <= m_sizeclass (MR st g) ->
  0 < d -> d mod PGSZ = 0 -> 2 * PGSZ <= nn -> nn mod PGSZ = 0 -> nn < LEN_MAX -> d + nn <= alloc_ceiling ->
  (forall q rq, s_regions st !! q = Some rq -> q <> fst (fst p) ->
     d + nn <= fst (region_live_range rq) \/ fst (region_live_range rq) + snd (region_live_range rq) <= d) ->
  UNIT * off + n <= nn - UNIT - IB -> nn - UNIT - IB - UNIT * off - n < 2^32 ->
  AEXT resv st LB (rr_remap_full st (fst p) (aadd (fst p) (UNIT * off)) n d nn) ((p, d + UNIT + UNIT * off, n) :: lbrm LB (p, A, k)).
Proof.
  intros resv st LB p A k n off d nn g idx Hin Ho EA Hn Hs Hsc Hd Hda Hnn2 Hnna HnnM Hce Hfree Hfit RS (L & LS & BL & INV & LIVE & RESV & SEC & CR).
  destruct (Forall2_In_l _ _ _ _ CR Hin) as (kb & Hkb & (C1 & C2 & C3)).
  destruct kb as [[c off'] k']. unfold blk_slot, blk_size, blk_addr, bslot, bsize, boff in C1, C2, C3. cbn [fst snd] in C1, C2, C3. subst k' c.
  assert (off' = off) by (unfold UNIT in *; lia). subst off'.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (rr_remap_INVL st L BL LS (fst p) off k n g idx d nn INV Hkb Hn Hs Hsc Hd Hda Hnn2 Hnna HnnM Hce Hfree Hfit RS)
    as (r & Hr & Kr & Hconc & Hmem & Eidx & INV').
  set (BL' := ((fst p, off), n) :: bl_remove (fst p) BL) in *.
  exists (set_live (map bslot BL') (L_remapR L (r_base r) d nn)), LS, BL'.
  split; [apply INVL_set_live; exact INV'|]. split; [reflexivity|]. split; [exact RESV|]. split; [rewrite s_secret_rr_remap_full; exact SEC|].
  (* [comment removed for export] *)
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  destruct (g63 x0 st L BL LS INV g b Hb Hsc) as (E63 & L0 & ML & NL).
  assert (Hrne : s_regions st !! fst (fst p) <> None) by (rewrite Hr; discriminate).
  subst BL'. eapply corr_replace; [exact CR| exact (is_nodup _ _ _ IS)| exact Hin| |].
  - rewrite (conc_rr_remap_full st _ _ n d nn g idx _ Hs Hrne). rewrite N.eqb_refl.
    rewrite Es, (slot_start'_eq _ _ _ IM _ _ _ Hb). cbn [snd]. unfold sstart. rewrite (hosts_gbase _ _ _ IM _ _ Hb), Eidx.
    destruct (hosts_ok _ _ _ IG _ _ Hb) as (ai & Hgb & GO). destruct (g_top _ _ _ _ _ _ GO ML) as [Hsnd _]. rewrite Hsnd. lia.
  - intros k' Hk'. rewrite (conc_rr_remap_full st _ _ n d nn g idx _ Hs Hrne).
    destruct (N.eqb_spec (fst (bslot k')) (fst (fst p))) as [E|NE]; [| reflexivity]. exfalso.
    assert (HkB : In k' BL /\ bslot k' <> fst p).
    { pose proof (is_nodup _ _ _ IS) as ND. clear -Hk' ND. induction BL as [|b0 BL IH]; cbn in *; [tauto|].
      apply NoDup_cons in ND as [N0 ND].
      destruct (aptr_eqb_spec (bslot b0) (fst p)) as [E|NE].
      - split; [right; exact Hk'|]. intros E2. apply N0. rewrite E, <- E2. apply list_elem_of_In. apply in_map. exact Hk'.
      - destruct Hk' as [<-|H]; [split; [left; reflexivity| exact NE]|]. destruct (IH H ND) as [H1 H2]. split; [right; exact H1| exact H2]. }
    destruct HkB as [Hk'' NEQ].
    destruct (is_blocks _ _ _ IS _ Hk'') as (m' & i' & Hs' & _).
    destruct (is_valid _ _ _ IS _ _ _ Hs') as ([b' Hb'] & Hi' & Es').
    rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb') in Es'.
    assert (Efb : fst b' = fst b).
    { rewrite Es' in E. cbn [fst] in E. rewrite Es, (slot_start'_eq _ _ _ IM _ _ _ Hb) in E. exact E. }
    destruct (alone x0 st L BL LS INV g b Hb Hsc b' m' Hb' Efb) as [-> ->].
    assert (i' = idx) by lia. subst i'. apply NEQ.
    rewrite Es', <- (slot_start'_eq _ _ _ IM _ _ _ Hb), <- Es. reflexivity.
Qed.


End CeilWrap.
