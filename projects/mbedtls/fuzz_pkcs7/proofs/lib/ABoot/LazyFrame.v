(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LazyFrame () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.newly_materialized_pages"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_accesses"; "Corelib.Init.Datatypes.Some"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.State.access_pages_acc"; "Corelib.Init.Logic.ex"; "Corelib.Init.Peano.lt"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "LinuxProcessSemantics.LinuxProcessSem.State.accesses_pages"; "Corelib.Init.Datatypes.pair"; "access_outside_range"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "accesses_outside_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_access"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.access_report"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step_accesses"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.mkAccessReport"; "LinuxProcessSemantics.LinuxProcessSem.Run.mi_account_step"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.DivergeSim.to_spin"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "(0.(1.(2.(3.&40.O4.)(4.O3.))(5.+2.+40.))(6.(1.(2.(3.&40.O4.)(4.O3.))(3.&40.O2.))(1.(2.(3.&40.O2.)(3.&40.O1.))(3.&40.O4.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition accesses_outside_lazy
    (accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
  forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
    access_outside_range a n lo sz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

Lemma materialize_accesses_no_new : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Plazy,(7.(8.(9.&40.)(9.&40.)))Pmaterialized,(7.(9.&40.))Pused,$:.Plimit,$:.Paccs,(7.(8.(9.&40.)$;.))P,(<.(7.(9.&40.))(=.R5.R4.R1.)(>.(9.&40.)))(<.(?.(7.(9.&40.)))(10.R6.R5.R4.R3.R2.)(11.(7.(9.&40.))R5.))")
(* [comment removed for export] *).
Proof.
  intros lazy materialized used limit accs Hnew.
  unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

(* [comment removed for export] *)
Lemma access_pages_acc_in : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Pn,$;.Pbase,$:.Ppages,(7.(9.&40.))Pp,(9.&40.)P,(12.(9.&40.)R1.(13.R3.R4.R2.))(6.(12.(9.&40.)R2.R3.)(14.$;.Lk,$;.(0.(15.R1.R6.)(<.(9.&40.)R3.(16.(2.R5.(4.R1.)))))))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Paccs,(7.(8.(9.&40.)$;.))Ppages,(7.(9.&40.))Pp,(9.&40.)P,(12.(9.&40.)R1.(17.R3.R2.))(6.(12.(9.&40.)R2.R3.)(14.(9.&40.)La,(9.&40.)(14.$;.Ln,$;.(14.$;.Lk,$;.(0.(12.(8.(9.&40.)$;.)(18.(9.&40.)$;.R3.R2.)R7.)(0.(15.R1.R2.)(<.(9.&40.)R5.(16.(2.(3.&40.R3.)(4.R1.))))))))))")
(* [comment removed for export] *).
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_outside : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Plazy,(7.(8.(9.&40.)(9.&40.)))Pa,(9.&40.)Pn,$;.Pk,$;.P,(15.R1.R2.)P,Plo,(9.&40.)Psz,(9.&40.)P,(12.(8.(9.&40.)(9.&40.))(18.(9.&40.)(9.&40.)R2.R1.)R7.)(19.R7.R6.R3.R2.)(<.$1:.(1;.(16.(2.(3.&40.R5.)(4.R3.)))R6.)$1<.)")
(* [comment removed for export] *).
Proof.
  intros lazy a n k Hk Hout.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  apply Bool.not_true_is_false. intro Htrue.
  unfold page_in_ranges in Htrue.
  apply existsb_exists in Htrue.
  destruct Htrue as ([lo sz] & Hin & Htest).
  cbn [fst snd] in Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (Hout lo sz Hin) as [Hnw Hdisj].
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg.
  pose proof (bv_unsigned_in_range 64 sz) as Hsz_rg.
  assert (Hz0 : (0 <= z)%Z) by (unfold z; lia).
  (* [comment removed for export] *)
  assert (Hq0 : (0 <= z / page_size)%Z)
    by (apply Z.div_pos; [exact Hz0 | unfold page_size; lia]).
  pose proof (Z.div_mod z page_size
                ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound z page_size
                ltac:(unfold page_size; lia)) as Hmb.
  assert (Hpb : bv_unsigned (page_base_of z)
                = ((z / page_size) * page_size)%Z).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64)%Z.
    unfold page_size in *. unfold z in *. lia. }
  rewrite Hpb in Hlo, Hhi.
  (* [comment removed for export] *)
  unfold page_size in *. unfold z in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem materialize_model_accesses_disjoint : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Pm,$1=.Paccs,(7.(8.(9.&40.)$;.))P,(1>.R1.(1?.R2.))(<.(?.$1=.)(20.R3.R2.)(11.$1=.R3.))")
(* [comment removed for export] *).
Proof.
  intros m accs Hout.
  assert (Hnew : newly_materialized_pages
                   (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages. apply filter_all_false.
    intros p Hp.
    destruct (accesses_pages_in accs [] p Hp)
      as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
    - reflexivity.
    - intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
  unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
             (vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
  cbv iota beta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mi_account_step_disjoint : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Psegs,(7.$21.)Pms,$22.Pmodel,$1=.Pms',$22.Pranges,(7.$23.)P,(<.(24.(25.$22.))(26.R5.R4.)(27.(25.$22.)(28.$22.R2.R1.)))P,(1>.R2.(1?.R4.))(<.(24.(8.$22.$1=.))(29.R7.R6.R5.)(27.(8.$22.$1=.)(18.$22.$1=.R4.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms model ms' ranges Hstep Hout.
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
  rewrite (materialize_model_accesses_disjoint model ranges Hout).
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ts_spin_disjoint : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Psegs,(7.$21.)Pms,$22.Pmodel,$1=.Pranges,(7.$23.)P,(<.(?.(9.&40.))(2:.R3.)(2;.(9.&40.)))P,(<.(24.(25.$22.))(26.R5.R4.)(27.(25.$22.)(28.$22.R4.R2.)))P,(1>.R3.(1?.R4.))(2<.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs ms model ranges Hsvc Hstep Hout.
  apply ts_spin; [exact Hsvc|].
  exact (mi_account_step_disjoint segs ms model ms ranges Hstep Hout).
Qed.

(* [comment removed for export] *)
Lemma ts_step_disjoint : ltac2:(CDefT.buildp (gd_tbl_LazyFrame ()) "Psegs,(7.$21.)Pms,$22.Pmodel,$1=.Pms',$22.Pranges,(7.$23.)P,(<.(?.(9.&40.))(2:.R4.)(2;.(9.&40.)))P,(<.(24.(25.$22.))(26.R6.R5.)(27.(25.$22.)(28.$22.R3.R2.)))P,(1>.R3.(1?.R5.))P,(2<.R8.R5.R6.)(2<.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros segs ms model ms' ranges Hsvc Hstep Hout Hspin.
  exact (ts_step segs ms model ms' model Hsvc
           (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
           Hspin).
Qed.
