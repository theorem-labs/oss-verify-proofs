(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsanNodesMmLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound.AxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan.AsanPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_ivs_covered : forall z l, in_ivs z l = covered l z.
Proof.
  intros z l. unfold in_ivs, covered, in_iv, in_rng, B, S. reflexivity.
Qed.



Lemma in_ivs_true' : forall z l, in_ivs z l = true <-> exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros z l. unfold in_ivs. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
  - intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.





Lemma region_free_app : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = (region_free l1 lo n && region_free l2 lo n)%bool.
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_contains_intro : forall l (lo n : word) b s,
  In (b, s) l -> bv_unsigned b <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= bv_unsigned b + bv_unsigned s ->
  map_contains l lo n = true.
Proof.
  intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
  cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma map_has_intro : forall l (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eager_used_sem : forall m,
  model_ivs_wf m ->
  eager_used m = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)).
Proof.
  intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.

Lemma mat_pages_le_A_bytes : forall A m,
  MInv A m -> A_wf A -> Z.of_nat (length (m_vm_materialized m)) * page_size <= A_bytes A.
Proof.
  intros A m [N1 N2 N3 N4 N5] Hwf. apply allowed_pages_bound; assumption.
Qed.

Lemma vm_backing_used_le : forall A m,
  MInv A m -> A_wf A -> vm_backing_used m <= eager_used m + A_bytes A.
Proof.
  intros A m HM Hwf. rewrite vm_backing_used_split. pose proof (mat_pages_le_A_bytes A m HM Hwf). lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_subtract_pieces : forall a sz lo hi q,
  iv_wf (a, sz) -> In q (iv_subtract a sz lo hi) ->
  bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz
  /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma maps_subtract_pieces : forall l lo hi q,
  ivs_wf l -> In q (maps_subtract l lo hi) ->
  exists r, In r l /\ bv_unsigned (fst r) <= bv_unsigned (fst q)
            /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst r) + bv_unsigned (snd r)
            /\ (bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
  - destruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr | exact H].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) lo hi,
  lo < hi -> 0 < bv_unsigned sz -> (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.


(* [comment removed for export] *)

Lemma page_in_ranges_cons : forall p iv l,
  page_in_ranges p (iv :: l)
  = (((bv_unsigned (fst iv) <=? bv_unsigned p) && (bv_unsigned p + page_size <=? bv_unsigned (fst iv) + bv_unsigned (snd iv)))
     || page_in_ranges p l)%bool.
Proof. reflexivity. Qed.

Lemma page_in_ranges_app : forall p l1 l2,
  page_in_ranges p (l1 ++ l2) = (page_in_ranges p l1 || page_in_ranges p l2)%bool.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

Lemma page_in_ranges_true : forall p l,
  page_in_ranges p l = true <->
  exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.


(* [comment removed for export] *)
Lemma page_in_ranges_covers : forall p l z,
  page_in_ranges p l = true -> bv_unsigned p <= z < bv_unsigned p + page_size -> in_ivs z l = true.
Proof.
  intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
  apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_out : forall (p : word) l lo hi,
  ivs_wf l -> lo <= hi ->
  (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p) ->
  page_in_ranges p (maps_subtract l lo hi) = page_in_ranges p l.
Proof.
  intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
  induction l as [|[a sz] l IH]; [reflexivity|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
  cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract. rewrite page_in_ranges_app.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
    cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout].
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
    + destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
      destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
      destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
  - (* [comment removed for export] *)
    destruct Hout as [Hout|Hout];
    destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_subtract_in : forall (p : word) l lo hi,
  ivs_wf l -> lo <= bv_unsigned p < hi ->
  page_in_ranges p (maps_subtract l lo hi) = false.
Proof.
  intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
  destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
  pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
  rewrite in_ivs_covered in C.
  destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
  apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
  apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.



(* [comment removed for export] *)
Lemma page_base_facts : forall a : word,
  bv_unsigned (page_base a) <= bv_unsigned a /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
  /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_in_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= bv_unsigned x < hi ->
  lo <= bv_unsigned (page_base x) /\ bv_unsigned (page_base x) + 4096 <= hi.
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_of_byte_out_aligned : forall (x : word) lo hi,
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> (bv_unsigned x < lo \/ hi <= bv_unsigned x) ->
  bv_unsigned (page_base x) + 4096 <= lo \/ hi <= bv_unsigned (page_base x).
Proof.
  intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.





Lemma is_ecall_at_sound : forall SEGS cs, is_ecall_at SEGS cs = true ->
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true /\ 0 <= pc cs /\ pc cs + 4 < 2 ^ 64.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  exists w. unfold two64 in H4. auto.
Qed.














Lemma A_bytes_app' : forall l1 l2, A_bytes (l1 ++ l2) = A_bytes l1 + A_bytes l2.
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.






(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma mmap_flags_core_22 : mmap_flags_core (Z_to_bv 64 34) = 34%Z.       Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : mmap_flags_core (Z_to_bv 64 50) = 50%Z.       Proof. vm_compute. reflexivity. Qed.


Lemma mmap_noreserve_b_22 : mmap_noreserve_b (Z_to_bv 64 34) = false.   Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : mmap_noreserve_b (Z_to_bv 64 50) = false.   Proof. vm_compute. reflexivity. Qed.



Lemma with_mmap_backing_plain : forall flags a n m,
  mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.


Lemma with_mmap_backing_halted : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.



(* [comment removed for export] *)
Lemma mmap_gates_core34 : forall flags,
  mmap_flags_core flags = 34%Z ->
  mmap_modeled_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true
  /\ mmap_modeled_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags Hc. unfold mmap_modeled_b, mmap_noaccess_b. rewrite Hc.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_not_contains : forall l (lo n : word),
  (0 < bv_unsigned n)%Z ->
  region_free l lo n = true -> map_contains l lo n = false.
Proof.
  intros l lo n Hn Hfree. unfold map_contains.
  apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
  cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma mmap_errnos_ENOMEM : forall e, In e mmap_errnos -> e = ENOMEM.
Proof. intros e [<-|[]]. reflexivity. Qed.


Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (two64 - 12).
Proof. apply bv_eq. reflexivity. Qed.

Section OurSpecNodes.
Variable segs : list Segment.
(* [comment removed for export] *)
Hypothesis PLACEMENT : placement_policy.

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  StoreOk.ShapeAlg.node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  apply node_ok_of_u; [CfgStep.kit_pending_on |].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.


(* [comment removed for export] *)
Lemma node_chk_ev_mat : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
     \/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None
         /\ injected_family_off CfgStep.kit_cfg (sys_input segs ms x8) = true
         /\ exists i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)) ->
  ((forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)
   \/ (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  StoreOk.ShapeAlg.node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hcls Hnu Hh' Hacc.
  apply (node_chk_cfg segs ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hcls Hnu Hh').
  intros i. rewrite (Hacc i). apply materialize_model_accesses_nil.
Qed.




(* [comment removed for export] *)

Lemma mmap_none_check : forall ms x8 model eff flags,
  bv_unsigned x8 = 222%Z ->
  ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
  ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r   (* [comment removed for export] *)
        then match us with [] => CheckOk model [] | _ => CheckReject end
        else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
        then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
  destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta. fold nZ.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end; [reflexivity|].
  unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.


End OurSpecNodes.


Section OurSpecNodes2.
Variable segs : list Segment.





(* [comment removed for export] *)


End OurSpecNodes2.







Lemma seps_app_intro : forall l1 l2,
  seps l1 -> seps l2 -> (forall p q, In p l1 -> In q l2 -> iv_disjoint p q) -> seps (l1 ++ l2).
Proof.
  induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
  inversion H1 as [|p' l' Hf Hl]; subst. cbn [app]. constructor.
  - apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
  - apply IH; [exact Hl | exact H2 |]. intros a b Ha Hb. apply H12; [right; exact Ha | exact Hb].
Qed.

Lemma seps_iv_subtract : forall (a sz : word) lo hi,
  iv_wf (a, sz) -> lo <= hi -> seps (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  assert (S1 : forall p : word * word, seps [p]) by (intros p; apply seps_cons; [apply Forall_nil | apply seps_nil]).
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
    try apply S1; try apply seps_nil.
  apply seps_cons; [|apply S1]. apply Forall_cons; [|apply Forall_nil].
  unfold iv_disjoint. cbn [fst snd]. rewrite !u64_lit by lia. left. lia.
Qed.

Lemma seps_maps_subtract : forall l lo hi,
  seps l -> ivs_wf l -> lo <= hi -> seps (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
  cbn [maps_subtract]. apply seps_app_intro; [apply seps_iv_subtract; assumption | apply IH; assumption |].
  intros p q Hp Hq.
  destruct (iv_subtract_pieces a sz lo hi p Ha Hp) as (P1 & P2 & P3).
  destruct (maps_subtract_pieces l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & Q3).
  pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_disjoint in *. cbn [fst snd] in *. lia.
Qed.









(* [comment removed for export] *)
End AsanNodesMmLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhKSys.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_mat' : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_halted' : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. intros h m. reflexivity. Qed.

Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] -> vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [fd [maps lazy mat] io fsys proc lim time]; cbn in Hl, Hm; subst; reflexivity.
Qed.



(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m))
                 (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Closed.
  Variable segs : list Segment.



End Closed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen.
  Context {fx : FPState}.
  Variable segs : list Segment.

  Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (x8 : word) : machine_state :=
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}.

  Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
  Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. reflexivity. Qed.
  Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
  Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. reflexivity. Qed.
  Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
  Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. reflexivity. Qed.
  Lemma arg_reg_3' : Z_to_bv 5 (10 + Z.of_nat 3) = (13%bv : reg). Proof. apply bv_eq. reflexivity. Qed.
  Lemma arg_reg_4' : Z_to_bv 5 (10 + Z.of_nat 4) = (14%bv : reg). Proof. apply bv_eq. reflexivity. Qed.
  Lemma arg_reg_5' : Z_to_bv 5 (10 + Z.of_nat 5) = (15%bv : reg). Proof. apply bv_eq. reflexivity. Qed.
  Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
  Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3'. reflexivity. Qed.
  Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
  Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4'. reflexivity. Qed.
  Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
  Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5'. reflexivity. Qed.

  Lemma adv_set_epend : forall regs pc mem rom x8 v,
    advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v) = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
  Proof. intros. unfold epend. apply adv_set. Qed.

  Lemma adv_ret_epend : forall regs pc mem rom x8 r,
    advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
  Proof. intros. rewrite apply_effect_no_write. apply adv_set_epend. Qed.

  Lemma adv_retU_epend : forall regs pc mem rom x8 r,
    advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
  Proof. intros. exact (adv_ret_epend regs pc mem rom x8 r). Qed.

  Lemma adv_zeros1_epend : forall regs pc mem rom x8 a n,
    advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect a [] [(a, n)]))
    = mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom.
  Proof. intros. unfold epend. apply adv_mmap_grant. Qed.

  Lemma adv_zerosr_epend : forall regs pc mem rom x8 r a n,
    advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] [(a, n)]))
    = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
  Proof.
    intros regs pc mem rom x8 r a n.
    assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
    { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
    unfold epend, apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
    rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
    cbv beta iota zeta.
    cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
    unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
  Qed.

  Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
    advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
    = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
  Proof.
    intros regs pc mem rom x8 r a n.
    assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
    { cbn [apply_writes apply_zeros]. apply FunctionalExtensionality.functional_extensionality. intro x.
      unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd]. rewrite Bool.orb_false_r. reflexivity. }
    unfold epend, apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
    rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
    cbv beta iota zeta.
    cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
    unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma node_sys : forall regs pc mem rom model w,
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    node_ok segs (mkCfg (mkst regs pc mem rom) model) unit (fun _ => [])
            (fun _ => mkCfg (epend regs pc mem rom (getr regs 17)) model).
  Proof.
    intros regs pc mem rom model w Hh Hl HF HE.
    apply node_instr; [exact Hh | exact Hl | reflexivity |].
    unfold epend. apply (step_ecall segs regs pc mem rom w HF HE).
  Qed.

  Lemma P_sys : forall (P : config -> Prop) regs pc mem rom model w,
    kclosed segs P ->
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    P (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
    P (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros P regs pc mem rom model w HP Hh Hl HF HE Hk.
    apply (HP _ unit tt _ (node_sys regs pc mem rom model w Hh Hl HF HE)). intros []. exact Hk.
  Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma P_brk : forall (P : config -> Prop) regs pc mem rom model w,
    kclosed segs P ->
    m_halted model = None -> m_vm_lazy model = [] ->
    fetch_word segs pc = Some w -> is_ecall w = true ->
    getr regs 17 = Z_to_bv 64 214 ->
    (forall r, brk_resolution_ok model (getr regs 10) r ->
       P (mkCfg (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
                    (mkEffectU r [] (brk_zeros (getr regs 10) r (vm_brk (m_vmmaps model)))
                                    (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])))
                (brk_model (getr regs 10) r model))) ->
    P (mkCfg (mkst regs pc mem rom) model).
  Proof.
    intros P regs pc mem rom model w HP Hh Hl HF HE H17 Hk.
    apply (P_sys P regs pc mem rom model w HP Hh Hl HF HE).
    assert (Hno : bv_unsigned (getr regs 17) = 214) by (rewrite H17; apply u_Z2bv; lia).
    (* [comment removed for export] *)
    assert (Hr0 : brk_resolution_ok model (getr regs 10) (vm_brk (m_vmmaps model))).
    { unfold brk_resolution_ok, Mmap.brk_r_ok.
      destruct (w_is0 (getr regs 10) || (bv_unsigned (getr regs 10) <? bv_unsigned (min_brk (m_vmmaps model))))%bool.
      - apply bv_eqb_refl.
      - destruct (bv_unsigned (getr regs 10) <? bv_unsigned (vm_brk (m_vmmaps model))).
        + rewrite bv_eqb_refl, Bool.orb_true_r. reflexivity.
        + rewrite bv_eqb_refl, Bool.orb_true_r. cbn [andb].
          unfold Mmap.brk_grow_ok. rewrite Z.ltb_irrefl, Bool.andb_false_r. reflexivity. }
    set (ms := epend regs pc mem rom (getr regs 17)).
    pose proof (node_brk_u segs ms model (getr regs 17) Hh Hl eq_refl Hno) as Nu.
    pose proof (node_ok_exact segs (mkCfg ms model) _ (fun _ => []) (brk_nx ms model) Nu
                  (CfgStep.kit_pending_off_sysno segs ms model (getr regs 17) 214 eq_refl Hno eq_refl)
                  (fun i => brk_nx_halted segs ms model (getr regs 17) i Hh Hl Hno)) as N.
    destruct (brk_exact_inh segs ms model (getr regs 17) Hh Hl eq_refl Hno) as (i0 & Hi0).
    apply (HP _ _ (exist _ i0 Hi0) _ N).
    intros [[r Hr] Hx]. cbn [proj1_sig]. clear Hx. unfold brk_nx. cbn [proj1_sig]. unfold ms in *.
    rewrite (ms_gpr_epend0 regs pc mem rom (getr regs 17)) in Hr |- *.
    apply Hk. exact Hr.
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Section MmapRw.
    Variables (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (w : bv 32) (len : Z).
    Hypotheses (Hh : m_halted model = None) (Hl : m_vm_lazy model = []).
    Hypotheses (HF : fetch_word segs pc = Some w) (HE : is_ecall w = true).
    Hypotheses (H17 : getr regs 17 = Z_to_bv 64 222)
               (H11 : getr regs 11 = Z_to_bv 64 len) (Hlen : 0 < len < 2 ^ 64)
               (H12 : getr regs 12 = Z_to_bv 64 3) (H13 : getr regs 13 = Z_to_bv 64 34)
               (H14 : getr regs 14 = Z_to_bv 64 (-1)) (H15 : getr regs 15 = Z_to_bv 64 0).

    Let nZ : Z := page_round_up_Z len.
    Let n : word := Z_to_bv 64 nZ.
    Let ms : machine_state := epend regs pc mem rom (getr regs 17).

    Lemma mmrw_no : bv_unsigned (getr regs 17) = 222.
    Proof. rewrite H17; apply u_Z2bv; lia. Qed.

    Lemma mmrw_args : mmap_args_ok ms.
    Proof.
      unfold mmap_args_ok, ms. rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
      rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
      intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u_Z2bv in Hc by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hc. lia.
    Qed.

    Lemma mmrw_len : bv_unsigned (ms_gpr ms 1) = len.
    Proof. unfold ms. rewrite ms_gpr_epend1, H11. apply u_Z2bv; lia. Qed.

    (* [comment removed for export] *)
    Definition mmrw_fail (e : Z) : config :=
      mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model.
    Definition mmrw_grant (a : word) : config :=
      mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a n mem) rom) (mmap_model a n model).

    (* [comment removed for export] *)
    Lemma mmrw_rf : mmap_grant_refusable (ms_gpr ms 3) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))
                    = mmap_grant_refusable (Z_to_bv 64 34) model nZ.
    Proof. rewrite mmrw_len. unfold ms. rewrite ms_gpr_epend3, H13. reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma node_mmap_rw_grant :
      mmap_grant_refusable (Z_to_bv 64 34) model nZ = false ->
      node_ok segs (mkCfg ms model)
        {a : word | grant_ok (getr regs 10) model a nZ = true}
        (fun _ => [])
        (fun i => match i with exist _ a _ => mmrw_grant a end).
    Proof.
      intros RF.
      pose proof (node_mmap_grant segs ms model (getr regs 17) Hh Hl eq_refl mmrw_no mmrw_args
                    (eq_trans mmrw_rf RF)) as N.
      assert (E0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; apply ms_gpr_epend0).
      assert (E1 : page_round_up_Z (bv_unsigned (ms_gpr ms 1)) = nZ) by (rewrite mmrw_len; reflexivity).
      assert (E2 : page_round_up (ms_gpr ms 1) = n) by (unfold page_round_up; rewrite mmrw_len; reflexivity).
      unshelve eapply (node_ok_reindex segs _ _ _ _ _ _ _
                (fun j => match j with exist _ a Ha => exist _ a _ end)
                (fun i => match i with exist _ a Ha => exist _ a _ end) N).
      - cbn. rewrite E0, E1. exact Ha.
      - cbn. rewrite <- E0, <- E1. exact Ha.
      - intros [a Ha]; cbn -[ms n nZ]; split; try reflexivity.
        unfold mmrw_grant; rewrite <- E2, <- (adv_zeros1_epend regs pc mem rom (getr regs 17)); reflexivity.
      - intros [a Ha]; cbn -[ms n nZ]; split; try reflexivity.
        unfold mmrw_grant; rewrite <- E2, <- (adv_zeros1_epend regs pc mem rom (getr regs 17)); reflexivity.
    Qed.



  End MmapRw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Section MmapNa.
    Variables (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (w : bv 32) (len : Z).
    Hypotheses (Hh : m_halted model = None) (Hl : m_vm_lazy model = []) (Hmat : m_vm_materialized model = []).
    Hypotheses (HF : fetch_word segs pc = Some w) (HE : is_ecall w = true).
    Hypotheses (H17 : getr regs 17 = Z_to_bv 64 222)
               (H11 : getr regs 11 = Z_to_bv 64 len) (Hlen : 0 < len < 2 ^ 64)
               (H12 : getr regs 12 = Z_to_bv 64 0) (H13 : getr regs 13 = Z_to_bv 64 34)
               (H14 : getr regs 14 = Z_to_bv 64 (-1)) (H15 : getr regs 15 = Z_to_bv 64 0).

    Let nZ : Z := page_round_up_Z len.
    Let n : word := Z_to_bv 64 nZ.
    Let ms : machine_state := epend regs pc mem rom (getr regs 17).

    Lemma mmna_no : bv_unsigned (getr regs 17) = 222.
    Proof. rewrite H17; apply u_Z2bv; lia. Qed.

    Lemma mmna_len : bv_unsigned (ms_gpr ms 1) = len /\ ms_gpr ms 1 <> Z_to_bv 64 0.
    Proof.
      unfold ms. rewrite ms_gpr_epend1, H11. split; [apply u_Z2bv; lia|].
      intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u_Z2bv in Hc by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hc. lia.
    Qed.

    Definition mmna_fail (e : Z) : config :=
      mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model.
    Definition mmna_grant (a : word) : config :=
      mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (unfill a n mem) rom) (noaccess_model a n model).

    (* [comment removed for export] *)
    Lemma mmna_check : forall eff,
      check_syscall (sys_input segs ms (getr regs 17)) eff model
      = match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in mmap_errnos r
            then match us with [] => CheckOk model [] | _ => CheckReject end
            else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)]
                 then CheckOk (with_mmap_backing (Z_to_bv 64 34) r n (noaccess_model r n model)) []
                 else CheckReject
        | _ => CheckReject
        end.
    Proof.
      intros eff. destruct mmna_len as [L1 L2].
      pose proof (mmap_none_check segs ms (getr regs 17) model eff (Z_to_bv 64 34) mmna_no L2
                    ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                    ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) mmap_flags_core_22
                    ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                    ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as X.
      cbv zeta in X. rewrite L1 in X. exact X.
    Qed.

    (* [comment removed for export] *)
    Lemma grant_na_pin_not_refusable : forall a, grant_ok_na_pin model a nZ = true -> mmap_reserve_refusable model nZ = false.
    Proof.
      intros a Ha. unfold mmap_reserve_refusable.
      rewrite (vm_find_base_complete (m_vmmaps model) nZ a Ha). reflexivity.
    Qed.


    (* [comment removed for export] *)
    Lemma node_mmap_na_when :
      node_ok segs (mkCfg ms model)
        ({e : Z | In e (mmap_errnos_when (mmap_reserve_refusable model nZ))} + {a : word | grant_ok_na_pin model a nZ = true})
        (fun _ => [])
        (fun i => match i with inl (exist _ e _) => mmna_fail e | inr (exist _ a _) => mmna_grant a end).
    Proof.
      assert (Hn0 : 0 <= nZ) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
      set (ERR := mmap_errnos_when (mmap_reserve_refusable model nZ)).
      assert (HERR : forall e, In e ERR -> In e mmap_errnos) by (intros e; apply mmap_errnos_when_sub).
      pose (I := ({e : Z | In e ERR} + {a : word | grant_ok_na_pin model a nZ = true})%type).
      pose (effs := fun i : I => match i with
                               | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
                               | inr (exist _ a _) => mkEffectU a [] [] [(a, n)] [] [] end).
      pose (ms' := fun i : I => match i with
                              | inl _ => model
                              | inr (exist _ a _) => with_mmap_backing (Z_to_bv 64 34) a n (noaccess_model a n model) end).
      assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = errno_ret_in mmap_errnos r)
        by (intros r; exact (CfgStep.refusal_b_mmap (sys_input segs ms (getr regs 17)) model r mmna_no)).
      assert (N : node_ok segs (mkCfg ms model) I (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
      { apply (node_chk_ev_mat segs ms model (getr regs 17) I effs ms' (fun _ => []) Hh eq_refl).
        - intros [[e He]|[a Ha]]; cbn [effs ms']; rewrite mmna_check.
          + rewrite (errno_ret_in_intro _ _ (HERR e He)). reflexivity.
          + rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
            rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
        - intros [r ws zs us cs ci] m' evs Hc. rewrite mmna_check in Hc.
          destruct ws; [|discriminate]. destruct zs; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (errno_ret_in mmap_errnos r) eqn:Er.
          + destruct us; [|discriminate]. injection Hc as <- <-.
            destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
            destruct (mmap_reserve_refusable model nZ) eqn:RF.
            * left. assert (He' : In e ERR) by (unfold ERR; try rewrite RF; exact He).
              exists (inl (exist _ e He')). repeat split; reflexivity.
            * right. cbn [eff_ret]. rewrite Hrb. split; [exact Er |]. split; [exact Hh |]. split.
              { rewrite (CfgStep.injected_family_off_alloc_only CfgStep.kit_cfg _ CfgStep.kit_cfg_alloc_only).
                cbn [sys_input in_sysno]. rewrite mmna_no. reflexivity. }
              unfold mmap_reserve_refusable in RF. apply negb_false_iff in RF.
              destruct (vm_gap_available_find _ _ RF) as (a & Hf).
              unfold vm_find_base in Hf. apply List.find_some in Hf as [_ Hok].
              exists (inr (exist _ a Hok)). cbn [effs eff_ret]. rewrite Hrb.
              exact (grant_na_pin_not_errno model a nZ Hn0 Hok).
          + destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
            destruct (listNN_eqb us [(r, n)]) eqn:Hlq; [|discriminate].
            apply listNN_eqb_eq in Hlq. subst us. injection Hc as <- <-.
            left. exists (inr (exist _ r Hg)). repeat split; reflexivity.
        - destruct (mmap_reserve_refusable model nZ) eqn:RF.
          + right. intros [[e He]|[a Ha]]; cbn [effs eff_ret]; rewrite Hrb.
            * apply errno_ret_in_intro. exact (HERR e He).
            * exfalso. rewrite (grant_na_pin_not_refusable a Ha) in RF. discriminate RF.
          + left. intros [[e He]|[a Ha]]; cbn [effs eff_ret]; rewrite Hrb.
            * exfalso. unfold ERR in He. try rewrite RF in He. destruct He.
            * exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
        - intros [r ws zs us cs ci] Hc. rewrite mmna_check in Hc.
          destruct ws; [|discriminate]. destruct zs; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
          destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
        - intros [[e He]|[a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold noaccess_model; rewrite with_vmmaps_halted'; exact Hh].
        - intros [[e He]|[a Ha]]; reflexivity. }
      destruct N as [N1 N2]. split.
      - intros i. pose proof (N1 i) as X. destruct i as [[e He]|[a Ha]]; cbn [effs ms'] in X; cbn.
        + unfold mmna_fail. rewrite <- (adv_retU_epend regs pc mem rom (getr regs 17)). exact X.
        + unfold mmna_grant. rewrite <- (adv_unmaps1_epend regs pc mem rom (getr regs 17)).
          rewrite <- (with_mmap_backing_plain (Z_to_bv 64 34) a n (noaccess_model a n model) mmap_noreserve_b_22). exact X.
      - intros e st Hss. destruct (N2 e st Hss) as (i & -> & ->). exists i. split; [reflexivity|].
        destruct i as [[e He]|[a Ha]]; cbn [effs ms']; cbn.
        + unfold mmna_fail. rewrite <- (adv_retU_epend regs pc mem rom (getr regs 17)). reflexivity.
        + unfold mmna_grant. rewrite <- (adv_unmaps1_epend regs pc mem rom (getr regs 17)).
          rewrite <- (with_mmap_backing_plain (Z_to_bv 64 34) a n (noaccess_model a n model) mmap_noreserve_b_22). reflexivity.
    Qed.


    (* [comment removed for export] *)
    Lemma node_mmap_na_grant :
      mmap_reserve_refusable model nZ = false ->
      node_ok segs (mkCfg ms model)
        {a : word | grant_ok_na_pin model a nZ = true}
        (fun _ => [])
        (fun i => match i with exist _ a _ => mmna_grant a end).
    Proof.
      intros RF. pose proof node_mmap_na_when as N. rewrite RF in N.
      apply (node_ok_reindex segs _ _ _ _ _ _ _
               (fun j => inr j)
               (fun i => match i with
                         | inl (exist _ e He) => match (He : In e []) with end
                         | inr j => j end) N).
      - intros [a Ha]. split; reflexivity.
      - intros [[e []]|[a Ha]]. split; reflexivity.
    Qed.


  End MmapNa.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Section Mprotect.
    Variables (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (w : bv 32) (addr : word) (len : Z).
    Hypotheses (Hh : m_halted model = None) (Hl : m_vm_lazy model = []).
    Hypotheses (HF : fetch_word segs pc = Some w) (HE : is_ecall w = true).
    Hypotheses (H17 : getr regs 17 = Z_to_bv 64 226)
               (H10 : getr regs 10 = addr) (Hal : bv_unsigned addr mod page_size = 0)
               (H11 : getr regs 11 = Z_to_bv 64 len) (Hlen : 0 < len)
               (Hnw : bv_unsigned addr + page_round_up_Z len < two_pow_64)
               (H12 : getr regs 12 = Z_to_bv 64 3).
    Let n : word := Z_to_bv 64 (page_round_up_Z len).
    Hypotheses (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true)
               (Hma : map_contains (vm_maps (m_vmmaps model)) addr n = true).
    Let ms : machine_state := epend regs pc mem rom (getr regs 17).

    Lemma mpr_no : bv_unsigned (getr regs 17) = 226.
    Proof. rewrite H17; apply u_Z2bv; lia. Qed.

    Definition mpr_fail (e : Z) : config :=
      mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model.
    Definition mpr_ok : config :=
      mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) rom) (mprotect_model addr n model).

    (* [comment removed for export] *)
    Lemma mpr_check : forall eff,
      check_syscall (sys_input segs ms (getr regs 17)) eff model
      = match eff with
        | mkEffectU r [] zs [] [] [] =>
            if errno_ret_in mprotect_errnos r
            then match zs with [] => CheckOk model [] | _ => CheckReject end
            else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
                 then CheckOk (mprotect_model addr n model) []
                 else CheckReject
        | _ => CheckReject
        end.
    Proof.
      intros eff.
      exact (mprotect_check segs ms (getr regs 17) model eff addr len mpr_no
               ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
               ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
               ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma).
    Qed.


    (* [comment removed for export] *)
    Lemma node_mprotect_when :
      node_ok segs (mkCfg ms model)
        ({e : Z | In e (mprotect_errnos_when (mprotect_refusable model addr n))} + {_ : unit | mprotect_budget_ok model addr n = true})
        (fun _ => [])
        (fun i => match i with inl (exist _ e _) => mpr_fail e | inr _ => mpr_ok end).
    Proof.
      set (ERR := mprotect_errnos_when (mprotect_refusable model addr n)).
      assert (HERR : forall e, In e ERR -> In e mprotect_errnos)
        by (intros e; unfold ERR; destruct (mprotect_refusable model addr n); [exact (fun H => H) | intros []]).
      assert (E0 : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
      assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = errno_ret_in mprotect_errnos r)
        by (intros r; exact (CfgStep.refusal_b_mprotect (sys_input segs ms (getr regs 17)) model r mpr_no)).
      pose (I := ({e : Z | In e ERR} + {_ : unit | mprotect_budget_ok model addr n = true})%type).
      pose (effs := fun i : I => match i with
                               | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
                               | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [] end).
      pose (ms' := fun i : I => match i with inl _ => model | inr _ => mprotect_model addr n model end).
      assert (N : node_ok segs (mkCfg ms model) I (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
      { apply (node_chk_ev_mat segs ms model (getr regs 17) I effs ms' (fun _ => []) Hh eq_refl).
        - intros [[e He]|[[] Hb]]; cbn [effs ms']; rewrite mpr_check.
          + rewrite (errno_ret_in_intro _ _ (HERR e He)). reflexivity.
          + rewrite E0.
            rewrite Hb. replace (w_is0 (Z_to_bv 64 0)) with true by (vm_compute; reflexivity). cbn [andb].
            rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
        - intros [r ws zs us cs ci] m' evs Hc. rewrite mpr_check in Hc.
          destruct ws; [|discriminate]. destruct us; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (errno_ret_in mprotect_errnos r) eqn:Er.
          + destruct zs; [|discriminate]. injection Hc as <- <-.
            destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->).
            destruct (mprotect_refusable model addr n) eqn:RF.
            * left. assert (He' : In e ERR) by (unfold ERR; try rewrite RF; exact He).
              exists (inl (exist _ e He')). repeat split; reflexivity.
            * right. cbn [eff_ret]. rewrite Hrb. split; [exact Er |]. split; [exact Hh |]. split.
              { rewrite (CfgStep.injected_family_off_alloc_only CfgStep.kit_cfg _ CfgStep.kit_cfg_alloc_only).
                cbn [sys_input in_sysno]. rewrite mpr_no. reflexivity. }
              unfold mprotect_refusable in RF. apply negb_false_iff in RF.
              exists (inr (exist _ tt RF)). cbn [effs eff_ret]. rewrite Hrb. exact E0.
          + destruct (Sumbool.sumbool_of_bool (mprotect_budget_ok model addr n)) as [Hb|Hb]; rewrite Hb in Hc; [|discriminate].
            destruct (w_is0 r) eqn:Hr; [|discriminate]. cbn [andb] in Hc.
            destruct (listNN_eqb zs [(addr, n)]) eqn:Hlq; [|discriminate].
            apply listNN_eqb_eq in Hlq. subst zs. injection Hc as <- <-.
            unfold w_is0 in Hr. apply bv_eqb_eq in Hr. subst r.
            left. exists (inr (exist _ tt Hb)). repeat split; reflexivity.
        - destruct (mprotect_refusable model addr n) eqn:RF.
          + right. intros [[e He]|[[] Hb]]; cbn [effs eff_ret]; rewrite Hrb.
            * apply errno_ret_in_intro. exact (HERR e He).
            * exfalso. unfold mprotect_refusable in RF. rewrite Hb in RF. discriminate RF.
          + left. intros [[e He]|[[] Hb]]; cbn [effs eff_ret]; rewrite Hrb.
            * exfalso. unfold ERR in He. try rewrite RF in He. destruct He.
            * exact E0.
        - intros [r ws zs us cs ci] Hc. rewrite mpr_check in Hc.
          destruct ws; [|discriminate]. destruct us; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
          destruct (Sumbool.sumbool_of_bool (mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)])%bool) as [E|E]; rewrite E in Hc; discriminate.
        - intros [[e He]|[[] Hb]]; cbn [ms']; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted'; exact Hh].
        - intros [[e He]|[[] Hb]]; reflexivity. }
      destruct N as [N1 N2]. split.
      - intros i. pose proof (N1 i) as X. destruct i as [[e He]|[[] Hb]]; cbn [effs ms'] in X; cbn -[ms n].
        + unfold mpr_fail. rewrite <- (adv_retU_epend regs pc mem rom (getr regs 17)). exact X.
        + unfold mpr_ok. rewrite <- (adv_zerosr_epend regs pc mem rom (getr regs 17)). exact X.
      - intros e st Hss. destruct (N2 e st Hss) as (i & -> & ->). exists i. split; [reflexivity|].
        destruct i as [[e He]|[[] Hb]]; cbn [effs ms']; cbn -[ms n].
        + unfold mpr_fail. rewrite <- (adv_retU_epend regs pc mem rom (getr regs 17)). reflexivity.
        + unfold mpr_ok. rewrite <- (adv_zerosr_epend regs pc mem rom (getr regs 17)). reflexivity.
    Qed.


    (* [comment removed for export] *)
    Lemma node_mprotect_grant :
      mprotect_budget_ok model addr n = true ->
      node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mpr_ok).
    Proof.
      intros Hb. pose proof node_mprotect_when as N.
      assert (RF : mprotect_refusable model addr n = false) by (unfold mprotect_refusable; rewrite Hb; reflexivity).
      rewrite RF in N.
      apply (node_ok_reindex segs _ _ _ _ _ _ _
               (fun _ : unit => inr (exist _ tt Hb))
               (fun _ => tt) N).
      - intros []. split; reflexivity.
      - intros [[e []]|[[] Hb']]. split; reflexivity.
    Qed.


  End Mprotect.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Section MmapFixed.
    Variables (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (w : bv 32) (addr : word) (len : Z).
    Hypotheses (Hh : m_halted model = None) (Hl : m_vm_lazy model = []) (Hmat : m_vm_materialized model = []).
    Hypotheses (HF : fetch_word segs pc = Some w) (HE : is_ecall w = true).
    Hypotheses (H17 : getr regs 17 = Z_to_bv 64 222)
               (H10 : getr regs 10 = addr) (Hal : bv_unsigned addr mod page_size = 0) (Hpos : 0 < bv_unsigned addr)
               (H11 : getr regs 11 = Z_to_bv 64 len) (Hlen : 0 < len)
               (Htop : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))
               (H12 : getr regs 12 = Z_to_bv 64 0) (H13 : getr regs 13 = Z_to_bv 64 50)
               (H14 : getr regs 14 = Z_to_bv 64 (-1)) (H15 : getr regs 15 = Z_to_bv 64 0).
    Let nZ : Z := page_round_up_Z len.
    Let n : word := Z_to_bv 64 nZ.
    Hypotheses (Hrf : region_free (vm_reserved (m_vmmaps model)) addr n = true)
               (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
    Let ms : machine_state := epend regs pc mem rom (getr regs 17).

    Lemma mmfx_no : bv_unsigned (getr regs 17) = 222.
    Proof. rewrite H17; apply u_Z2bv; lia. Qed.

    Definition mmfx_fail (e : Z) : config :=
      mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model.
    Definition mmfx_ok : config :=
      mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom) (fixed_noaccess_model addr n model).
    Definition mmfx_gone (e : Z) : config :=
      mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) (unfill addr n mem) rom) (fixed_destroyed_model addr n model).

    Lemma mmfx_len : bv_unsigned (ms_gpr ms 1) = len /\ len < 2 ^ 64 /\ 0 < nZ.
    Proof.
      pose proof (alloc_top_lt (m_vmmaps model)). pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
      unfold two_pow_64 in *.
      split; [| split; [unfold nZ; lia | unfold nZ; lia]].
      unfold ms. rewrite ms_gpr_epend1, H11. apply u_Z2bv; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma mmfx_check : forall eff,
      check_syscall (sys_input segs ms (getr regs 17)) eff model
      = match eff with
        | mkEffectU r [] [] us [] [] =>
            if errno_ret_in mmap_errnos r
            then match us with
                 | [] => CheckOk model []
                 | _ => if listNN_eqb us [(addr, n)]
                        then CheckOk (with_mmap_destroyed addr n
                               (mmap_fixed_destroyed_next (m_vmmaps model) addr n) model) []
                        else CheckReject
                 end
            else if bv_eqb r addr && listNN_eqb us [(addr, n)]
            then CheckOk (with_mmap_replacement (Z_to_bv 64 50) addr n
                   (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps model)) (vm_maps (m_vmmaps model))
                      ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                      (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model))
                      (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))) model)) []
            else CheckReject
        | _ => CheckReject
        end.
    Proof.
      intros eff. destruct mmfx_len as (L1 & L2 & L3).
      pose proof (alloc_top_lt (m_vmmaps model)) as AT. pose proof (u64_range addr) as AR.
      destruct (mmap_gates_core50 (Z_to_bv 64 50) (Z_to_bv 64 0) (mmap_flags_core_32)) as (Gm & Gn & Gfn & _ & _).
      assert (E1 : w_is0 (ms_gpr ms 1) = false).
      { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
        rewrite L1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
      rewrite (mmap_check segs ms (getr regs 17) model eff mmfx_no). unfold check_mmap.
      rewrite E1. unfold ms. rewrite ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend5, ms_gpr_epend0.
      rewrite H12, H13, H15, H10, mmap_off_aligned_b_0, (mmap_anon_b_of_core (Z_to_bv 64 50) _ mmap_flags_core_32 eq_refl), Gm, Gn, Gfn.
      cbn [negb]. cbv beta iota zeta. fold ms. rewrite L1. fold nZ.
      rewrite (proj2 (Z.leb_gt two_pow_64 (bv_unsigned addr + nZ))) by (unfold two_pow_64 in *; unfold nZ; lia).
      pose proof Htop as Htop'. fold nZ in Htop'.
      rewrite (proj2 (Z.leb_le _ _) Htop'). cbn [negb].
      rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
      rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n.
      rewrite Hrf, Hmc. cbn [andb].
      destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
      destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
      destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
      reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma node_mmap_fixed :
      node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mmfx_ok).
    Proof.
      destruct mmfx_len as (L1 & L2 & L3).
      pose (effs := fun _ : unit => mkEffectU addr [] [] [(addr, n)] [] []).
      pose (ms' := fun _ : unit => fixed_noaccess_model addr n model).
      assert (Eok : with_mmap_replacement (Z_to_bv 64 50) addr n
                      (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps model)) (vm_maps (m_vmmaps model))
                         ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                         (vm_start_brk (m_vmmaps model)) (vm_brk (m_vmmaps model)) (vm_limit (m_vmmaps model))
                         (vm_mmap_base (m_vmmaps model)) (vm_init_sp (m_vmmaps model))) model)
                    = fixed_noaccess_model addr n model).
      { unfold with_mmap_replacement. rewrite vm_forget_range_id by (first [rewrite with_vmmaps_lazy'; exact Hl | rewrite with_vmmaps_mat'; exact Hmat]).
        apply with_mmap_backing_plain. exact mmap_noreserve_b_32. }
      assert (N : node_ok segs (mkCfg ms model) unit (fun _ => [])
                    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
      assert (Ea : errno_ret_in mmap_errnos addr = false).
      { apply errno_ret_in_below; [reflexivity|]. pose proof (alloc_top_room (m_vmmaps model)).
        unfold stack_max_size, two_pow_64 in *. fold nZ in Htop. lia. }
      assert (Hrb : forall r, refusal_b (sys_input segs ms (getr regs 17)) model r = errno_ret_in mmap_errnos r)
        by (intros r; exact (CfgStep.refusal_b_mmap (sys_input segs ms (getr regs 17)) model r mmfx_no)).
      { apply (node_chk_ev_mat segs ms model (getr regs 17) unit effs ms' (fun _ => []) Hh eq_refl).
        - intros []; unfold effs, ms'; rewrite mmfx_check. rewrite Ea.
          rewrite bv_eqb_refl. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl), Eok. reflexivity.
        - intros [r ws zs us cs ci] m' evs Hc. rewrite mmfx_check in Hc.
          destruct ws; [|discriminate]. destruct zs; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (errno_ret_in mmap_errnos r) eqn:Er.
          + right. cbn [eff_ret]. rewrite Hrb. split; [exact Er |]. split.
            { destruct us as [|u us]; [injection Hc as <- <-; exact Hh |].
              destruct (listNN_eqb (u :: us) [(addr, n)]); [| discriminate]. injection Hc as <- <-.
              unfold with_mmap_destroyed. rewrite vm_forget_range_halted, with_vmmaps_halted'. exact Hh. }
            split.
            { rewrite (CfgStep.injected_family_off_alloc_only CfgStep.kit_cfg _ CfgStep.kit_cfg_alloc_only).
              cbn [sys_input in_sysno]. rewrite mmfx_no. reflexivity. }
            exists tt. cbn [effs eff_ret]. rewrite Hrb. exact Ea.
          + left. destruct (bv_eqb r addr) eqn:Hr; [|discriminate]. apply bv_eqb_eq in Hr. subst r.
            destruct (listNN_eqb us [(addr, n)]) eqn:Hlq; [|discriminate]. cbn [andb] in Hc.
            apply listNN_eqb_eq in Hlq. subst us. injection Hc as <- <-.
            exists tt. rewrite Eok. repeat split; reflexivity.
        - left. intros []. cbn [effs eff_ret]. rewrite Hrb. exact Ea.
        - intros [r ws zs us cs ci] Hc. rewrite mmfx_check in Hc.
          destruct ws; [|discriminate]. destruct zs; [|discriminate].
          destruct cs; [|discriminate]. destruct ci; [|discriminate].
          destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate | destruct (listNN_eqb _ _); discriminate] |].
          destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
        - intros []; cbn [ms']; reflexivity || exact Hh.
        - intros []; reflexivity. }
      destruct N as [N1 N2]. split.
      - intros i. pose proof (N1 i) as X. destruct i; unfold effs, ms' in X; cbn -[ms n nZ].
        unfold mmfx_ok. rewrite <- (adv_unmaps1_epend regs pc mem rom (getr regs 17)). exact X.
      - intros e st Hss. destruct (N2 e st Hss) as (i & -> & ->). exists i. split; [reflexivity|].
        destruct i; unfold effs, ms'; cbn -[ms n nZ].
        unfold mmfx_ok. rewrite <- (adv_unmaps1_epend regs pc mem rom (getr regs 17)). reflexivity.
    Qed.

  End MmapFixed.

End FPGen.
End MhKSys.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhK MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Context {fx : FPState}.          (* [comment removed for export] *)
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : forall regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
  = MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  (lazymatch goal with |- ?G => let G' := eval unfold RiscvSemantics.step_accesses in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ms_pc ms_pc_val mkst] in G in change_no_check G' end).
  rewrite Hfetch. cbv beta iota.
  (lazymatch goal with |- ?G => let G' := eval unfold RiscvSemantics.decode_exec_accesses in G in change_no_check G' end). rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : forall ms model ms',
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { (lazymatch goal with |- ?G => let G' := eval unfold mi_account_step in G in change_no_check G' end). rewrite Hstep. (lazymatch goal with |- ?G => let G' := eval cbn [accessed_ranges access_value] in G in change_no_check G' end).
    rewrite materialize_model_accesses_nil. reflexivity. }
  apply node_ok_of_u; [CfgStep.kit_pending_on |].
  split.
  - intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

#[local] Notation kclosedD := (kclosedD segs).
#[local] Notation katD := (katD segs).
#[local] Notation katwD := (katwD segs).
#[local] Notation katsD := (katsD segs).
#[local] Notation doomed := (doomed segs).
#[local] Notation kat := (kat segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma K_instr_noacc : forall (K : config -> Prop) ms model ms',
  kclosedD K ->
  m_halted model = None -> ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  K (mkCfg ms' model) -> K (mkCfg ms model).
Proof.
  intros K ms model ms' HK Hh Hsvc Hst Hk.
  apply (HK _ unit tt _ (node_instr_noacc ms model ms' Hh Hsvc Hst)); [exact Hk | intros []; left; exact Hk].
Qed.


(* [comment removed for export] *)
Lemma K_ecall : forall (K : config -> Prop) regs pc mem rom model w,
  kclosedD K ->
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  K (mkCfg (epend regs pc mem rom (getr regs 17)) model) ->
  K (mkCfg (mkst regs pc mem rom) model).
Proof.
  intros K regs pc mem rom model w HK Hh HF HE Hk.
  apply (K_instr_noacc K (mkst regs pc mem rom) model _ HK Hh eq_refl (stepacc_ecall_epend regs pc mem rom w HF HE) Hk).
Qed.

Lemma katD_ecall : forall regs pc mem rom model w Q,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  katD (mkCfg (epend regs pc mem rom (getr regs 17)) model) Q ->
  katD (mkCfg (mkst regs pc mem rom) model) Q.
Proof. intros regs pc mem rom model w Q Hh HF HE Hk K HK HQ. apply (K_ecall K regs pc mem rom model w HK Hh HF HE). exact (Hk K HK HQ). Qed.


Lemma katsD_ecall : forall regs pc mem rom model w Qok Qf,
  m_halted model = None ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  katsD (mkCfg (epend regs pc mem rom (getr regs 17)) model) Qok Qf ->
  katsD (mkCfg (mkst regs pc mem rom) model) Qok Qf.
Proof.
  intros regs pc mem rom model w Qok Qf Hh HF HE Hk F HL Hok Hf.
  apply (K_ecall (Kp F) regs pc mem rom model w (klD_p segs F HL) Hh HF HE). exact (Hk F HL Hok Hf).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MmapRw.
  Variables (ms : machine_state) (model : Model) (x8 : word).
  Hypotheses (Hh : m_halted model = None) (Hsvc : ms_svc_pending ms = Some x8)
             (Hno : bv_unsigned x8 = 222) (Hargs : mmap_args_ok ms).
  Let nZ : Z := page_round_up_Z (bv_unsigned (ms_gpr ms 1)).

  Definition mmrw_fail (e : Z) : config := mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model.
  Definition mmrw_grant (a : word) : config :=
    mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model a (page_round_up (ms_gpr ms 1)) model).


  (* [comment removed for export] *)
  Lemma node_mmap_rw_wit : forall a0, grant_ok (ms_gpr ms 0) model a0 nZ = true ->
    node_ok segs (mkCfg ms model) {a : word | grant_ok (ms_gpr ms 0) model a nZ = true} (fun _ => [])
            (fun i => match i with exist _ a _ => mmrw_grant a end).
  Proof.
    intros a0 Ha0.
    exact (node_mmap_lazy_grant segs ms model x8 Hh Hsvc Hno Hargs (grant_ok_not_refusable (ms_gpr ms 3) _ _ _ _ Ha0)).
  Qed.



  (* [comment removed for export] *)
  Lemma katsD_mmap_rw : forall Qok Qf,
    (exists a, grant_ok (ms_gpr ms 0) model a nZ = true) ->
    (forall e, In e mmap_errnos -> katD (mmrw_fail e) Qf) ->
    (forall a, grant_ok (ms_gpr ms 0) model a nZ = true -> katwD (mmrw_grant a) Qok Qf) ->
    katsD (mkCfg ms model) Qok Qf.
  Proof.
    intros Qok Qf [a0 Ha0] _ Hg.
    apply katsD_of_katwD.
    apply (katwD_node segs _ _ (exist _ a0 Ha0) _ Qok Qf (node_mmap_rw_wit a0 Ha0)).
    intros [a Ha]. exact (Hg a Ha).
  Qed.
End MmapRw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MmapNr.
  Variables (ms : machine_state) (model : Model) (x8 : word).
  Hypotheses (Hh : m_halted model = None) (Hsvc : ms_svc_pending ms = Some x8)
             (Hno : bv_unsigned x8 = 222) (Hargs : mmap_args_ok_noreserve ms).
  Let nZ : Z := page_round_up_Z (bv_unsigned (ms_gpr ms 1)).

  Definition mmnr_fail (e : Z) : config := mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model.
  Definition mmnr_grant (a : word) : config :=
    mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model).


  (* [comment removed for export] *)
  Lemma node_mmap_nr_wit : forall a0, grant_ok_nr (ms_gpr ms 0) model a0 nZ = true ->
    node_ok segs (mkCfg ms model) {a : word | grant_ok_nr (ms_gpr ms 0) model a nZ = true} (fun _ => [])
            (fun i => match i with exist _ a _ => mmnr_grant a end).
  Proof.
    intros a0 Ha0.
    assert (RF : mmap_grant_refusable (ms_gpr ms 3) model nZ = false).
    { destruct Hargs as (_ & _ & Hfl & _ & _). rewrite Hfl. exact (grant_ok_nr_not_refusable _ _ _ _ Ha0). }
    exact (node_mmap_noreserve_grant segs ms model x8 Hh Hsvc Hno Hargs RF).
  Qed.



  (* [comment removed for export] *)
  Lemma katD_mmap_nr_dm : forall Q,
    (exists a, grant_ok_nr (ms_gpr ms 0) model a nZ = true) ->
    (forall e, In e mmap_errnos -> doomed (mmnr_fail e)) ->
    (forall a, grant_ok_nr (ms_gpr ms 0) model a nZ = true -> katD (mmnr_grant a) Q) ->
    katD (mkCfg ms model) Q.
  Proof.
    intros Q [a0 Ha0] _ Hg.
    apply (katD_node segs _ _ (exist _ a0 Ha0) _ Q (node_mmap_nr_wit a0 Ha0)).
    intros [a Ha]. exact (Hg a Ha).
  Qed.
End MmapNr.

(* [comment removed for export] *)
Lemma katD_mmap_rw_dm : forall ms model x8 Q,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 222 -> mmap_args_ok ms ->
  (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
  (forall e, In e mmap_errnos -> doomed (mmrw_fail ms model e)) ->
  (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true -> katD (mmrw_grant ms model a) Q) ->
  katD (mkCfg ms model) Q.
Proof.
  intros ms model x8 Q Hh Hsvc Hno Hargs [a0 Ha0] _ Hg.
  apply (katD_node segs _ _ (exist _ a0 Ha0) _ Q (node_mmap_rw_wit ms model x8 Hh Hsvc Hno Hargs a0 Ha0)).
  intros [a Ha]. exact (Hg a Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma K_munmap : forall (K : config -> Prop) ms model x8,
  kclosedD K ->
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_args_ok ms model ->
  K (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
           (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) ->
  K (mkCfg ms model).
Proof.
  intros K ms model x8 HK Hh Hsvc Hno Hargs Hk.
  apply (HK _ unit tt _ (node_munmap_lazy segs ms model x8 Hh Hsvc Hno Hargs)); [exact Hk | intros []; left; exact Hk].
Qed.

Lemma katD_munmap : forall ms model x8 Q,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 215 ->
  munmap_args_ok ms model ->
  katD (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
              (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) Q ->
  katD (mkCfg ms model) Q.
Proof. intros ms model x8 Q Hh Hsvc Hno Hargs Hk K HK HQ. apply (K_munmap K ms model x8 HK Hh Hsvc Hno Hargs). exact (Hk K HK HQ). Qed.

End WithSegs.
End AsKSys.
Module AsanNodesLibE.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound.AxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan.AsanPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanPlanSound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
Variable segs : list Segment.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  syscall_effect_accesses eff = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hacc.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
     \/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None
         /\ injected_family_off CfgStep.kit_cfg (sys_input segs ms x8) = true
         /\ exists i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)) ->
  ((forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)
   \/ (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hcls Hnu Hh' Hacc.
  apply (node_chk_cfg segs ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hcls Hnu Hh').
  intros i. rewrite (Hacc i). apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     (exists i, eff = effs i /\ m' = ms' i /\ evs = [])
     \/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None
         /\ injected_family_off CfgStep.kit_cfg (sys_input segs ms x8) = true
         /\ exists i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)) ->
  ((forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)
   \/ (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hcls Hnu Hh' Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.






Lemma vm_add_lazy_halted : forall a n m, m_halted (vm_add_lazy a n m) = m_halted m.
Proof. reflexivity. Qed.



















(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gates_core50 : forall flags prot,
  mmap_flags_core flags = 50%Z ->
  mmap_modeled_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
  /\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
  /\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.


(* [comment removed for export] *)
Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
  if Z.eqb prot 0
  then mkVmMapsFull (vm_reserved h) (vm_maps h)
         ((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h)
    (maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

(* [comment removed for export] *)
Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
  if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.




End Noacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2 AX2S AP APS.





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).



End CsOk.
End AsanNodesLibE.
Module AsKSys2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanPlacement OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[local] Notation kclosedD := (kclosedD segs).
#[local] Notation katD := (katD segs).
#[local] Notation katwD := (katwD segs).
#[local] Notation katsD := (katsD segs).
#[local] Notation doomed := (doomed segs).

(* [comment removed for export] *)
Lemma mmap_fixedin_check_top : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
  bv_unsigned x8 = 222%Z ->
  (prot = 0 \/ prot = 3)%Z ->
  mmap_flags_core flags = 50%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
  ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  (alloc_top (m_vmmaps model) < two_pow_64)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs us [] [] =>      (* [comment removed for export] *)
        if errno_ret_in mmap_errnos r
        then match zs with
             | [] => match us with
                     | [] => CheckOk model []
                     | _ => if listNN_eqb us [(addr, n)]
                            then CheckOk (fixedin_destroyed_model addr n model) []
                            else CheckReject
                     end
             | _ => CheckReject
             end
        else
        if (Z.eqb prot 0)
        then match zs with
             | [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
                     then CheckOk (fixedin_ok_model prot flags addr n model) []
                     else CheckReject
             | _ => CheckReject
             end
        else match us with
             | [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
                     then CheckOk (fixedin_ok_model prot flags addr n model) []
                     else CheckReject
             | _ => CheckReject
             end
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop Htop64 n Hrf Hmc Hbud.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). unfold two_pow_64 in Htop64. lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). (lazymatch goal with |- ?G => let G' := eval unfold check_mmap in G in change_no_check G' end).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { (lazymatch goal with |- ?G => let G' := eval unfold w_is0 in G in change_no_check G' end). apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  rewrite E1, H2, H3, H5, H0, Hu1.
  destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
  pose proof (u64_range addr) as Har.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite G3. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64 in *; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
    rewrite (proj2 (Z.eqb_eq _ _) Hal). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end). fold n. rewrite Hrf, Hmc. (lazymatch goal with |- ?G => let G' := eval cbn [andb Z.eqb] in G in change_no_check G' end).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct zs; destruct us; reflexivity].
    destruct zs; [|destruct (errno_ret_in mmap_errnos r); reflexivity].
    reflexivity.
  - (* [comment removed for export] *)
    rewrite G4, G5. cbv beta iota zeta.
    rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64 in *; lia).
    rewrite (proj2 (Z.leb_le _ _) Htop). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
    rewrite (proj2 (Z.eqb_eq _ _) Hal). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
    rewrite (proj2 (Z.ltb_lt _ _) Hpos). (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end). fold n. rewrite Hrf, Hmc. (lazymatch goal with |- ?G => let G' := eval cbn [andb Z.eqb] in G in change_no_check G' end).
    rewrite (Hbud eq_refl).
    destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
    destruct cs; [|destruct zs; destruct us; reflexivity].
    destruct ci; [|destruct zs; destruct us; reflexivity].
    destruct (errno_ret_in mmap_errnos r); [reflexivity |].
    destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

Section Fixedin.
  Variables (ms : machine_state) (model : Model) (x8 : word) (prot : Z) (flags addr : word) (len : Z).
  Hypotheses (Hh : m_halted model = None) (Hsvc : ms_svc_pending ms = Some x8) (Hno : bv_unsigned x8 = 222%Z)
             (Hprot : (prot = 0 \/ prot = 3)%Z) (Hcore : mmap_flags_core flags = 50%Z)
             (H0 : ms_gpr ms 0 = addr) (Hal : (bv_unsigned addr mod page_size = 0)%Z) (Hpos : (0 < bv_unsigned addr)%Z)
             (H1 : ms_gpr ms 1 = Z_to_bv 64 len) (Hlen : (0 < len)%Z)
             (H2 : ms_gpr ms 2 = Z_to_bv 64 prot) (H3 : ms_gpr ms 3 = flags)
             (H4 : ms_gpr ms 4 = Z_to_bv 64 (-1)) (H5 : ms_gpr ms 5 = Z_to_bv 64 0)
             (Htop : (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z)
             (Htop64 : (alloc_top (m_vmmaps model) < two_pow_64)%Z).
  Let n : word := Z_to_bv 64 (page_round_up_Z len).
  Hypotheses (Hrf : region_free (vm_reserved (m_vmmaps model)) addr n = true)
             (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true)
             (Hbud : prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true).

  (* [comment removed for export] *)
  Definition fxin_effs (i : three) : SyscallEffect :=
    match i with
    | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
    | T2 => fixedin_ok_eff prot addr n
    | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] []
    end.
  Definition fxin_ms' (i : three) : Model :=
    match i with
    | T1 => model
    | T2 => fixedin_ok_model prot flags addr n model
    | T3 => fixedin_destroyed_model addr n model
    end.
  Definition fxin_nx (i : three) : config := mkCfg (advance_past_svc (apply_effect ms (fxin_effs i))) (fxin_ms' i).

  (* [comment removed for export] *)
  Lemma node_mmap_fixedin1 : node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => fxin_nx T2).
  Proof.
    pose proof (fun eff => mmap_fixedin_check_top ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen
                             H2 H3 H4 H5 Htop Htop64 Hrf Hmc Hbud) as Hchk.
    cbv zeta in Hchk. fold n in Hchk.
    assert (Ea : errno_ret_in mmap_errnos addr = false).
    { apply errno_ret_in_below; [reflexivity|]. pose proof (alloc_top_room (m_vmmaps model)).
      pose proof (page_round_up_Z_bounds len ltac:(lia)).
      unfold stack_max_size, two_pow_64 in *. lia. }
    assert (Hrb : forall r, refusal_b (sys_input segs ms x8) model r = errno_ret_in mmap_errnos r)
      by (intros r; exact (CfgStep.refusal_b_mmap (sys_input segs ms x8) model r Hno)).
    (lazymatch goal with |- ?G => let G' := eval unfold fxin_nx in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fxin_effs fxin_ms'] in G in change_no_check G' end).
    apply (node_chk_noacc segs ms model x8 unit (fun _ => fixedin_ok_eff prot addr n)
             (fun _ => fixedin_ok_model prot flags addr n model) Hh Hsvc).
    - intros []. cbv beta.
      (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). destruct (Z.eqb prot 0) eqn:Ep; rewrite Hchk; rewrite ?Ep; cbv beta iota;
        rewrite Ea, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    - intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Er.
      + right. cbn [eff_ret]. rewrite Hrb. split; [exact Er |]. split.
        { destruct zs; [|discriminate]. destruct us as [|u us]; [injection Hc as <- <-; exact Hh |].
          destruct (listNN_eqb (u :: us) [(addr, n)]); [|discriminate]. injection Hc as <- <-.
          unfold fixedin_destroyed_model, with_mmap_destroyed. rewrite vm_forget_range_halted, with_vmmaps_halted. exact Hh. }
        split.
        { rewrite (CfgStep.injected_family_off_alloc_only CfgStep.kit_cfg _ CfgStep.kit_cfg_alloc_only).
          cbn [sys_input in_sysno]. rewrite Hno. reflexivity. }
        exists tt. rewrite Hrb. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); exact Ea.
      + left. destruct (Z.eqb prot 0) eqn:Ep.
        * destruct zs; [|discriminate].
          destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
          destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
          apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
          exists tt. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). rewrite Ep. repeat split; reflexivity.
        * destruct us; [|discriminate].
          destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
          destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
          apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-.
          exists tt. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end). rewrite Ep. repeat split; reflexivity.
    - left. intros []. rewrite Hrb. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); exact Ea.
    - intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct (errno_ret_in mmap_errnos r).
      { destruct zs; [|discriminate]. destruct us; [discriminate|]. destruct (listNN_eqb _ _); discriminate. }
      destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
        destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
    - intros []. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_model in G in change_no_check G' end); rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
    - intros []. (lazymatch goal with |- ?G => let G' := eval unfold fixedin_ok_eff in G in change_no_check G' end); destruct (Z.eqb prot 0); reflexivity.
  Qed.




  Lemma katD_mmap_fixedin3_dm : forall Q,
    doomed (fxin_nx T1) -> katD (fxin_nx T2) Q -> doomed (fxin_nx T3) -> katD (mkCfg ms model) Q.
  Proof.
    intros Q _ HB _. apply (katD_node segs _ _ tt _ Q node_mmap_fixedin1). intros []. exact HB.
  Qed.

End Fixedin.

End WithSegs.
End AsKSys2.
Require Stdlib.Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsKSys7.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra AsanNodesMmLib AsanNodesLibE.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition OKm (addr n : word) : Model -> Model := fixedin_ok_model 3 (Z_to_bv 64 50) addr n.
Definition DSm (addr n : word) : Model -> Model := fixedin_destroyed_model addr n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OKm_eq : forall addr n m,
  OKm addr n m = vm_forget_range (u addr) (u addr + u n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps m) addr n) m).
Proof.
  intros. (lazymatch goal with |- ?G => let G' := eval unfold OKm, fixedin_ok_model, with_mmap_replacement in G in change_no_check G' end).
  rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32. reflexivity.
Qed.
Lemma DSm_eq : forall addr n m,
  DSm addr n m = vm_forget_range (u addr) (u addr + u n) (with_vmmaps (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m).
Proof. intros. reflexivity. Qed.

Lemma OKm_vmmaps : forall addr n m, m_vmmaps (OKm addr n m) = mmap_fixed_rw_next (m_vmmaps m) addr n.
Proof. intros. rewrite OKm_eq. model_proj. reflexivity. Qed.
Lemma OKm_lazy : forall addr n m, m_vm_lazy (OKm addr n m) = maps_subtract (m_vm_lazy m) (u addr) (u addr + u n).
Proof. intros. rewrite OKm_eq. model_proj. reflexivity. Qed.
Lemma OKm_mat : forall addr n m,
  m_vm_materialized (OKm addr n m) = List.filter (page_outside_range (u addr) (u addr + u n)) (m_vm_materialized m).
Proof. intros. rewrite OKm_eq. model_proj. reflexivity. Qed.
Lemma DSm_vmmaps : forall addr n m, m_vmmaps (DSm addr n m) = mmap_fixed_destroyed_next (m_vmmaps m) addr n.
Proof. intros. rewrite DSm_eq. model_proj. reflexivity. Qed.
Lemma DSm_lazy : forall addr n m, m_vm_lazy (DSm addr n m) = maps_subtract (m_vm_lazy m) (u addr) (u addr + u n).
Proof. intros. rewrite DSm_eq. model_proj. reflexivity. Qed.
Lemma DSm_mat : forall addr n m,
  m_vm_materialized (DSm addr n m) = List.filter (page_outside_range (u addr) (u addr + u n)) (m_vm_materialized m).
Proof. intros. rewrite DSm_eq. model_proj. reflexivity. Qed.

Lemma OKm_halted : forall addr n m, m_halted (OKm addr n m) = m_halted m.
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold OKm, fixedin_ok_model in G in change_no_check G' end). rewrite with_mmap_replacement_halted'. reflexivity. Qed.
Lemma DSm_halted : forall addr n m, m_halted (DSm addr n m) = m_halted m.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma eager_used_ext : forall m1 m2, m_vmmaps m1 = m_vmmaps m2 -> m_vm_lazy m1 = m_vm_lazy m2 -> eager_used m1 = eager_used m2.
Proof. intros m1 m2 H1 H2. (lazymatch goal with |- ?G => let G' := eval unfold eager_used in G in change_no_check G' end). rewrite H1, H2. reflexivity. Qed.

(* [comment removed for export] *)
Lemma OKm_frame : forall addr n m,
  OKm addr n m = mkModelOf (m_fd m) (m_vm (OKm addr n m)) (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Proof. intros addr n [fd [maps lazy mat] io fs proc lim tm]. rewrite OKm_eq. reflexivity. Qed.
Lemma DSm_frame : forall addr n m,
  DSm addr n m = mkModelOf (m_fd m) (m_vm (DSm addr n m)) (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Proof. intros addr n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_frame_vm : forall m m', same_but_materialized m m' ->
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sum_count_perm : forall P l l', Permutation l l' -> sum_count P l = sum_count P l'.
Proof. intros P l l' HP. induction HP; (lazymatch goal with |- ?G => let G' := eval cbn [sum_count] in G in change_no_check G' end); lia. Qed.
Lemma overlap_sum_perm : forall l l' lo hi, Permutation l l' -> overlap_sum l lo hi = overlap_sum l' lo hi.
Proof. intros. apply sum_count_perm. assumption. Qed.
Lemma overlap_sum_off : forall l lo hi,
  Forall (fun p : word * word => u (fst p) + u (snd p) <= lo \/ hi <= u (fst p)) l -> overlap_sum l lo hi = 0.
Proof.
  induction l as [|p l IH]; intros lo hi HF; [reflexivity|]. inversion HF as [|? ? Hp Hl]; subst.
  rewrite overlap_sum_cons, (IH _ _ Hl), iv_count_in_rng_disjoint; [lia | exact Hp].
Qed.

Lemma model_ivs_wf_OKm : forall addr n m, model_ivs_wf m -> model_ivs_wf (OKm addr n m).
Proof.
  intros addr n m Hwf. pose proof Hwf as (Wm & Wn & Wl & Wsp). pose proof (bv_unsigned_in_range 64 n).
  rewrite OKm_eq. apply model_ivs_wf_vm_forget_range; [lia|].
  apply model_ivs_wf_with_vmmaps; [exact Hwf | exact Wm | apply maps_subtract_wf; [exact Wn | lia] | reflexivity].
Qed.
Lemma model_ivs_wf_DSm : forall addr n m, model_ivs_wf m -> model_ivs_wf (DSm addr n m).
Proof.
  intros addr n m Hwf. pose proof Hwf as (Wm & Wn & Wl & Wsp). pose proof (bv_unsigned_in_range 64 n).
  rewrite DSm_eq. apply model_ivs_wf_vm_forget_range; [lia|].
  apply model_ivs_wf_with_vmmaps; [exact Hwf | apply maps_subtract_wf; [exact Wm | lia] | apply maps_subtract_wf; [exact Wn | lia] | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma eager_OKm_le : forall addr n m, model_ivs_wf m ->
  eager_used (OKm addr n m) <= eager_used m + overlap_sum (vm_maps (m_vmmaps m)) (u addr) (u addr + u n).
Proof.
  intros addr n m Hwf. pose proof Hwf as (Wm & Wn & Wl & _). pose proof (bv_unsigned_in_range 64 n) as Rn.
  rewrite (eager_used_sem _ (model_ivs_wf_OKm addr n m Hwf)), (eager_used_sem _ Hwf).
  rewrite OKm_vmmaps, OKm_lazy. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_rw_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess] in G in change_no_check G' end).
  set (lo := u addr) in *. set (hi := u addr + u n) in *.
  destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (_ & _ & Cl).
  (lazymatch goal with |- ?G => let G' := eval unfold overlap_sum in G in change_no_check G' end).
  eapply Z.le_trans; [| apply (sum_count_or_le (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (in_rng lo hi))].
  apply sum_count_mono. intros x. rewrite !covered_app, Cn, Cl.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); congruence.
Qed.

(* [comment removed for export] *)
Lemma eager_DSm_le : forall addr n m, model_ivs_wf m -> eager_used (DSm addr n m) <= eager_used m.
Proof.
  intros addr n m Hwf. pose proof Hwf as (Wm & Wn & Wl & _). pose proof (bv_unsigned_in_range 64 n) as Rn.
  rewrite (eager_used_sem _ (model_ivs_wf_DSm addr n m Hwf)), (eager_used_sem _ Hwf).
  rewrite DSm_vmmaps, DSm_lazy. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_destroyed_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess] in G in change_no_check G' end).
  set (lo := u addr) in *. set (hi := u addr + u n) in *.
  destruct (maps_subtract_sem _ lo hi Wm ltac:(lia)) as (_ & Sm & _).
  destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (_ & _ & Cl).
  rewrite Sm. apply sum_count_mono. intros x. rewrite !covered_app, Cn, Cl.
  destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_in_ranges_subtract_sub : forall (p : word) l lo hi, ivs_wf l ->
  page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  intros p l lo hi Hwf H. apply page_in_ranges_true in H. destruct H as (q & Hq & H1 & H2).
  destruct (maps_subtract_pieces l lo hi q Hwf Hq) as (r & Hr & R1 & R2 & _).
  apply page_in_ranges_true. exists r. split; [exact Hr|]. lia.
Qed.

Lemma aligned_lt_step : forall a b, a mod 4096 = 0 -> b mod 4096 = 0 -> a < b -> a + 4096 <= b.
Proof.
  intros a b Ha Hb Hlt. pose proof (Z.div_mod a 4096 ltac:(lia)) as Da. pose proof (Z.div_mod b 4096 ltac:(lia)) as Db.
  rewrite Ha in Da. rewrite Hb in Db. assert (a / 4096 < b / 4096) by lia. lia.
Qed.

Section MInvKeep.
  Variables (A : list (Z * Z)) (addr n : word) (m : Model).
  Hypothesis HM : MInv A m.
  Hypothesis Hwf : model_ivs_wf m.
  Hypothesis Hal : u addr mod page_size = 0.
  Hypothesis Hnl : (u addr + u n) mod page_size = 0.

  Lemma mat_filter_lazy : forall p,
    In p (List.filter (page_outside_range (u addr) (u addr + u n)) (m_vm_materialized m)) ->
    page_in_ranges p (maps_subtract (m_vm_lazy m) (u addr) (u addr + u n)) = true.
  Proof.
    intros p Hp. apply filter_In in Hp as [Hin Hout]. destruct HM as [N1 N2 N3 N4 N5].
    pose proof Hwf as (_ & _ & Wl & _). pose proof (bv_unsigned_in_range 64 n) as Rn.
    rewrite page_in_ranges_subtract_out; [exact (N4 p Hin) | exact Wl | lia |].
    unfold page_outside_range in Hout. apply negb_true_iff in Hout. pose proof (N2 p Hin) as Ap. unfold page_size in *.
    apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout | apply Z.ltb_ge in Hout].
    - left. apply aligned_lt_step; assumption.
    - right. exact Hout.
  Qed.

  Lemma MInv_OKm : eager_used m + overlap_sum (vm_maps (m_vmmaps m)) (u addr) (u addr + u n) + A_bytes A <= vm_limit (m_vmmaps m) ->
    MInv A (OKm addr n m).
  Proof.
    intros Hb. destruct HM as [N1 N2 N3 N4 N5]. constructor; rewrite ?OKm_mat, ?OKm_lazy.
    - apply NoDup_filter. exact N1.
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
    - exact mat_filter_lazy.
    - pose proof (eager_OKm_le addr n m Hwf). rewrite OKm_vmmaps. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_rw_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end). lia.
  Qed.

  Lemma MInv_DSm : MInv A (DSm addr n m).
  Proof.
    destruct HM as [N1 N2 N3 N4 N5]. constructor; rewrite ?DSm_mat, ?DSm_lazy.
    - apply NoDup_filter. exact N1.
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
    - exact mat_filter_lazy.
    - pose proof (eager_DSm_le addr n m Hwf). rewrite DSm_vmmaps. (lazymatch goal with |- ?G => let G' := eval unfold mmap_fixed_destroyed_next in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [vm_limit] in G in change_no_check G' end). lia.
  Qed.
End MInvKeep.

(* [comment removed for export] *)
Lemma budget_ok_commit : forall A addr n m, MInv A m -> A_wf A -> model_ivs_wf m ->
  eager_used m + A_bytes A + overlap_sum (vm_maps (m_vmmaps m)) (u addr) (u addr + u n) <= vm_limit (m_vmmaps m) ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 50) m addr n = true.
Proof.
  intros A addr n m HM HA Hwf Hb. apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
  pose proof (vm_backing_used_le A m HM HA). lia.
Qed.

(* [comment removed for export] *)
Lemma page_allowedb_app_l : forall A1 A2 p, page_allowedb A1 p = true -> page_allowedb (A1 ++ A2) p = true.
Proof. intros A1 A2 p H. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
Lemma MInv_widen : forall A lo hi m, MInv A m -> eager_used m + A_bytes A + (hi - lo) <= vm_limit (m_vmmaps m) -> MInv (A ++ [(lo, hi)]) m.
Proof.
  intros A lo hi m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
  - intros p Hp. apply page_allowedb_app_l. exact (N3 p Hp).
  - rewrite A_bytes_app'. (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes fst snd] in G in change_no_check G' end). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sbm_vmmaps : forall m m', same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m.
Proof. intros m m' H. pose proof (same_but_materialized_frame m m' H) as (_ & H1 & H2 & _). split; assumption. Qed.
Lemma model_ivs_wf_sbm7 : forall m m', same_but_materialized m m' -> model_ivs_wf m -> model_ivs_wf m'.
Proof. intros m m' H W. destruct (sbm_vmmaps m m' H) as [E1 E2]. unfold model_ivs_wf in *. rewrite E1, E2. exact W. Qed.
End AsKSys7.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Madvise.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.NoReserve OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhK MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK AsKSys.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocEd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition madvise_args_ok (ms : machine_state) (model : Model) : Prop :=
  (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
  madvise_dontneed_b (int32 (ms_gpr ms 2)) = true /\
  ms_gpr ms 1 <> Z_to_bv 64 0 /\
  (bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) < two_pow_64)%Z /\
  madvise_dontneed_ok (m_vmmaps model) (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) = true.

Definition madvise_eff (ms : machine_state) : SyscallEffect :=
  mkEffect (Z_to_bv 64 0) [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))].

Definition madvise_model (ms : machine_state) (model : Model) : Model :=
  madvise_dontneed_next model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)).

Lemma madvise_model_halted : forall ms m, m_halted (madvise_model ms m) = m_halted m.
Proof. reflexivity. Qed.




(* [comment removed for export] *)
Lemma materialize_madvise_eff_nil : forall (m : Model) (ms : machine_state),
  materialize_model_accesses m (syscall_effect_accesses (madvise_eff ms)) = Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma syscall_spec_madvise : forall ms x8 model o,
  bv_unsigned x8 = 233%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> madvise_spec (ms_gpr ms 0) (ms_gpr ms 1) (int32 (ms_gpr ms 2)) (sys_input segs ms x8) model o).
Proof.
  intros ms x8 model o Hno.
  (lazymatch goal with |- ?G => let G' := eval unfold syscall_spec, dispatch in G in change_no_check G' end).
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

Lemma madvise_check_modeled : forall ms model eff,
  madvise_args_ok ms model ->
  check_madvise (ms_gpr ms 0) (ms_gpr ms 1) (int32 (ms_gpr ms 2)) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if w_is0 r && listNN_eqb zs [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (madvise_model ms model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms model eff (Hal & Hadv & Hlen & Hnw & Hok).
  (lazymatch goal with |- ?G => let G' := eval unfold check_madvise in G in change_no_check G' end).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite Hadv.
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
  rewrite (proj2 (Z.leb_gt _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hok. rewrite Hok. reflexivity.
Qed.

Lemma madvise_ok : forall ms x8 model,
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok (madvise_eff ms) (madvise_model ms model) []).
Proof.
  intros ms x8 model Hno Ha.
  apply (proj2 (syscall_spec_madvise _ _ _ _ Hno)). apply check_madvise_sound_ok.
  rewrite (madvise_check_modeled ms model _ Ha).
  (lazymatch goal with |- ?G => let G' := eval unfold madvise_eff, w_is0 in G in change_no_check G' end). rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma madvise_ok_inv : forall ms x8 model eff model' evs,
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = madvise_eff ms /\ model' = madvise_model ms model /\ evs = [].
Proof.
  intros ms x8 model eff model' evs Hno Ha Hspec.
  apply (proj1 (syscall_spec_madvise _ _ _ _ Hno)) in Hspec.
  apply check_madvise_complete_ok in Hspec.
  rewrite (madvise_check_modeled ms model eff Ha) in Hspec.
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate]. destruct cs as [|? ?]; [|discriminate]. destruct copyins as [|? ?]; [|discriminate].
  destruct (w_is0 r && listNN_eqb zs [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]) eqn:HC; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in HC as [Hr Hzs].
  unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
  apply listNN_eqb_eq in Hzs; subst zs.
  (lazymatch goal with |- ?G => let G' := eval unfold madvise_eff in G in change_no_check G' end). auto.
Qed.

Lemma madvise_no_unmodeled : forall ms x8 model,
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros ms x8 model Hno Ha Hspec.
  apply (proj1 (syscall_spec_madvise _ _ _ _ Hno)) in Hspec.
  apply (check_madvise_complete_unmodeled _ _ _ _ _ (madvise_eff ms)) in Hspec.
  rewrite (madvise_check_modeled ms model _ Ha) in Hspec.
  unfold madvise_eff in Hspec.
  destruct (w_is0 (Z_to_bv 64 0) && listNN_eqb [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
    discriminate.
Qed.

Lemma sstep_madvise_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms (madvise_eff ms))) (madvise_model ms model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (madvise_ok_inv ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
      subst eff model' evs0
    end.
    match goal with
    | Hmat : materialize_model_accesses (madvise_model ms model) _ = Some _ |- _ =>
      rewrite materialize_madvise_eff_nil in Hmat; inversion Hmat; subst
    end.
    split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (madvise_ok_inv ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs); subst eff model' evs0;
      rewrite materialize_madvise_eff_nil in Hmat; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (madvise_ok_inv ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite madvise_model_halted, Hh in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (madvise_ok_inv ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
      subst model'; rewrite m_killed_of_m_halted_none in H6;
        [ discriminate | rewrite madvise_model_halted; exact Hh ]
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (madvise_no_unmodeled ms x8 model Hno Hargs H3)
    end.
Qed.

(* [comment removed for export] *)
Lemma node_madvise : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 233%Z ->
  madvise_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (madvise_eff ms))) (madvise_model ms model)).
Proof.
  intros ms model x8 Hh Hsvc Hno Hargs.
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 233 Hsvc Hno eq_refl) |].
  split.
  - intros []. apply (sstep_syscall segs ms model x8 (madvise_eff ms) (madvise_model ms model) (madvise_model ms model) []).
    + exact Hh.
    + exact Hsvc.
    + apply madvise_ok; assumption.
    + rewrite madvise_model_halted; exact Hh.
    + apply materialize_madvise_eff_nil.
  - intros e st Hss.
    destruct (sstep_madvise_inv ms model x8 e st Hh Hsvc Hno Hargs Hss) as [-> ->].
    exists tt. split; reflexivity.
Qed.

#[local] Notation kclosedD := (kclosedD segs).
#[local] Notation katD := (katD segs).

Lemma K_madvise : forall (K : config -> Prop) ms model x8,
  kclosedD K ->
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 233 ->
  madvise_args_ok ms model ->
  K (mkCfg (advance_past_svc (apply_effect ms (madvise_eff ms))) (madvise_model ms model)) ->
  K (mkCfg ms model).
Proof.
  intros K ms model x8 HK Hh Hsvc Hno Hargs Hk.
  apply (HK _ unit tt _ (node_madvise ms model x8 Hh Hsvc Hno Hargs)); [exact Hk | intros []; left; exact Hk].
Qed.

Lemma katD_madvise : forall ms model x8 Q,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 233 ->
  madvise_args_ok ms model ->
  katD (mkCfg (advance_past_svc (apply_effect ms (madvise_eff ms))) (madvise_model ms model)) Q ->
  katD (mkCfg ms model) Q.
Proof. intros ms model x8 Q Hh Hsvc Hno Hargs Hk K HK HQ. apply (K_madvise K ms model x8 HK Hh Hsvc Hno Hargs). exact (Hk K HK HQ). Qed.


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ivs_pos (l : list (word * word)) : Prop := Forall (fun e : word * word => 0 < bv_unsigned (snd e)) l.


Lemma ivs_pos_subtract : forall l lo hi, ivs_pos l -> ivs_pos (maps_subtract l lo hi).
Proof.
  intros l lo hi H. induction H as [|[a sz] t Ha Ht IH]; [constructor|].
  (lazymatch goal with |- ?G => let G' := eval cbn [maps_subtract] in G in change_no_check G' end). apply Forall_app. split; [|exact IH].
  cbn [snd] in Ha. pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs.
  (lazymatch goal with |- ?G => let G' := eval unfold iv_subtract in G in change_no_check G' end). apply Forall_app. split.
  - destruct (bv_unsigned a <? lo) eqn:E; [|constructor]. apply Z.ltb_lt in E. constructor; [|constructor]. (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end).
    unfold bv_modulus in *; rewrite Z_to_bv_small; [lia | (lazymatch goal with |- ?G => let G' := eval unfold bv_modulus in G in change_no_check G' end); lia].
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor]. apply Z.ltb_lt in E. constructor; [|constructor]. (lazymatch goal with |- ?G => let G' := eval cbn [snd] in G in change_no_check G' end).
    unfold bv_modulus in *; rewrite Z_to_bv_small; [lia | (lazymatch goal with |- ?G => let G' := eval unfold bv_modulus in G in change_no_check G' end); lia].
Qed.

(* [comment removed for export] *)
Lemma region_free_of_bytes : forall l (lo n : word),
  ivs_pos l -> 0 < bv_unsigned n ->
  (forall a, bv_unsigned lo <= a < bv_unsigned lo + bv_unsigned n ->
             ~ exists b m, In (b, m) l /\ bv_unsigned b <= a < bv_unsigned b + bv_unsigned m) ->
  region_free l lo n = true.
Proof.
  intros l lo n H Hn. induction H as [|[a sz] t Ha Ht IH]; intros Hb; [reflexivity|].
  (lazymatch goal with |- ?G => let G' := eval cbn [region_free] in G in change_no_check G' end). cbn [snd] in Ha. apply andb_true_intro. split.
  - apply Bool.negb_true_iff. (lazymatch goal with |- ?G => let G' := eval unfold iv_overlap in G in change_no_check G' end). apply Bool.andb_false_iff.
    destruct (Z.lt_ge_cases (bv_unsigned lo) (bv_unsigned a + bv_unsigned sz)) as [L1|L1]; [|left; apply Z.ltb_ge; exact L1].
    destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned lo + bv_unsigned n)) as [L2|L2]; [|right; apply Z.ltb_ge; exact L2].
    exfalso. apply (Hb (Z.max (bv_unsigned lo) (bv_unsigned a))); [lia|].
    exists a, sz. split; [left; reflexivity | lia].
  - apply IH. intros x Hx (b & m & Hin & Hr). apply (Hb x Hx). exists b, m. split; [right; exact Hin | exact Hr].
Qed.

Lemma madvise_model_lazy : forall ms m, m_vm_lazy (madvise_model ms m) = m_vm_lazy m.
Proof. intros ms [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

