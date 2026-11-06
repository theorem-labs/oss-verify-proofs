(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ALazy () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vm_backing"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.State.FdState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fd"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.IoState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_io"; "LinuxProcessSemantics.LinuxProcessSem.State.FsState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fsys"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_proc"; "LinuxProcessSemantics.LinuxProcessSem.State.LimState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_lim"; "LinuxProcessSemantics.LinuxProcessSem.State.TimeState"; "LinuxProcessSemantics.LinuxProcessSem.State.m_time"; "Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.State.access_pages_acc"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.accesses_pages"; "byte_of"; "LinuxProcessSemantics.LinuxProcessSem.State.newly_materialized_pages"; "Stdlib.Lists.List.NoDup"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.page_mem"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.materialize_model_accesses"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "Corelib.Init.Datatypes.app"; "eager_bytes"; "asan_layout"; "crange"; "stdpp.bitvector.definitions.bv_unsigned"; "acc_ok"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "shadow_of"; "al_img_lo"; "al_img_hi"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Lists.ListDef.Forall"; "ap_good"; "aok_addr"; "ap_nb"; "Corelib.Lists.ListDef.map"; "Stdlib.ZArith.BinInt.Z.div"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma model_eta : forall mo,
  with_vm_backing (m_vm_lazy mo) (m_vm_materialized mo) mo = mo.
Proof. intros [fd [maps lazy mat] io fs pr lim tm]; reflexivity. Qed.   (* [comment removed for export] *)

Lemma with_vm_backing_fields : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Plz,(0.(1.(2.&40.)(2.&40.)))Ppages,(0.(2.&40.))Pmo,$3.Zmo',$3.(4.R3.R2.R1.)(5.(6.$7.(8.R1.)(8.R2.))(5.(6.$9.(:.R1.)(:.R2.))(5.(6.(0.(1.(2.&40.)(2.&40.)))(;.R1.)R4.)(5.(6.(0.(2.&40.))(<.R1.)R3.)(5.(6.$=.(>.R1.)(>.R2.))(5.(6.$?.(10.R1.)(10.R2.))(5.(6.$11.(12.R1.)(12.R2.))(5.(6.$13.(14.R1.)(14.R2.))(6.$15.(16.R1.)(16.R2.))))))))))")
(* [comment removed for export] *).
Proof. intros; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition mo_mat (mo mo' : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "(5.(6.$7.(8.O1.)(8.O2.))(5.(6.$9.(:.O1.)(:.O2.))(5.(6.(0.(1.(2.&40.)(2.&40.)))(;.O1.)(;.O2.))(5.(6.$=.(>.O1.)(>.O2.))(5.(6.$?.(10.O1.)(10.O2.))(5.(6.$11.(12.O1.)(12.O2.))(5.(6.$13.(14.O1.)(14.O2.))(6.$15.(16.O1.)(16.O2.)))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

Lemma mo_mat_refl : forall mo, mo_mat mo mo.
Proof. intros; repeat split; reflexivity. Qed.
Lemma mo_mat_trans : forall a b c, mo_mat a b -> mo_mat b c -> mo_mat a c.
Proof. unfold mo_mat; intros a b c H1 H2; intuition congruence. Qed.
Lemma mo_mat_backing : forall mo pages, mo_mat mo (with_vm_backing (m_vm_lazy mo) pages mo).
Proof. intros; repeat split; reflexivity. Qed.
Lemma mo_mat_halted : forall mo mo', mo_mat mo mo' -> m_halted mo' = m_halted mo.
Proof. unfold mo_mat, m_halted; intros mo mo' H; intuition congruence. Qed.
Lemma mo_mat_fs : forall mo mo', mo_mat mo mo' -> m_fs mo' = m_fs mo.
Proof. unfold mo_mat, m_fs; intros mo mo' H; intuition congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition byte_of (acc : list (word * nat)) (z : Z) : Prop :=
  exists a n, In (a, n) acc /\ bv_unsigned a <= z < bv_unsigned a + Z.of_nat n.

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> In p pages.
Proof.
  intros p pages. unfold page_mem. induction pages as [|q r IH]; cbn.
  - split; [discriminate| tauto].
  - rewrite Bool.orb_true_iff, IH. split.
    + intros [H|H]; [left| right; exact H]. apply bv_eqb_eq in H. congruence.
    + intros [->|H]; [left; apply bv_eqb_eq; reflexivity | right; exact H].
Qed.

Lemma page_insert_In : forall q p pages, In q (page_insert p pages) <-> q = p \/ In q pages.
Proof.
  intros q p pages. unfold page_insert. destruct (page_mem p pages) eqn:E.
  - apply page_mem_In in E. split; [tauto|]. intros [->|H]; assumption.
  - cbn. split; intros [H|H]; auto.
Qed.

Lemma page_insert_NoDup : forall p pages, List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages ND. unfold page_insert. destruct (page_mem p pages) eqn:E; [exact ND|].
  constructor; [|exact ND]. intros H. apply (proj2 (page_mem_In p pages)) in H; congruence.
Qed.

Lemma access_pages_acc_spec : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pn,$17.Pbase,$18.Ppages,(0.(2.&40.))Pq,(2.&40.)P,(19.(2.&40.)R1.(1:.R3.R4.R2.))(1;.(19.(2.&40.)R2.R3.)(1<.$18.Li,$18.(5.(5.(1=.=R1.)(1>.R1.(1?.R6.)))(6.(2.&40.)R3.(20.(21.R5.R1.))))))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; cbn; intros base pages q H; [left; exact H|].
  destruct (IH _ _ _ H) as [H1|(i & Hi & ->)].
  - apply page_insert_In in H1. destruct H1 as [->|H1]; [|left; exact H1].
    right. exists 0. split; [lia|]. rewrite Z.add_0_r. reflexivity.
  - right. exists (i + 1). split; [lia|]. f_equal. lia.
Qed.

Lemma access_pages_acc_NoDup : forall n base pages, List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof. induction n as [|n IH]; cbn; intros; [assumption|]. apply IH. apply page_insert_NoDup. assumption. Qed.

Lemma accesses_pages_spec : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pacc,(0.(1.(2.&40.)$17.))Ppages,(0.(2.&40.))Pq,(2.&40.)P,(19.(2.&40.)R1.(22.R3.R2.))(1;.(19.(2.&40.)R2.R3.)(1<.$18.Lz,$18.(5.(23.R5.R1.)(6.(2.&40.)R3.(20.R1.)))))")
(* [comment removed for export] *).
Proof.
  induction acc as [|[a n] acc IH]; cbn; intros pages q H; [left; exact H|].
  destruct (IH _ _ H) as [H1|(z & Hz & ->)].
  - destruct (access_pages_acc_spec _ _ _ _ H1) as [H2|(i & Hi & ->)]; [left; exact H2|].
    right. exists (bv_unsigned a + i). split; [|reflexivity].
    exists a, n. split; [left; reflexivity| lia].
  - right. exists z. split; [|reflexivity]. destruct Hz as (a' & n' & Hin & Hr).
    exists a', n'. split; [right; exact Hin| exact Hr].
Qed.

Lemma accesses_pages_NoDup : forall acc pages, List.NoDup pages -> List.NoDup (accesses_pages acc pages).
Proof.
  induction acc as [|[a n] acc IH]; cbn; intros; [assumption|]. apply IH. apply access_pages_acc_NoDup. assumption.
Qed.

(* [comment removed for export] *)
Lemma newly_pages_spec : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Plazy,(0.(1.(2.&40.)(2.&40.)))Pmat,(0.(2.&40.))Pacc,(0.(1.(2.&40.)$17.))Znew,(0.(2.&40.))(24.R3.R2.R1.)(5.(25.(2.&40.)R1.)Pp,(2.&40.)P,(19.(2.&40.)R1.R2.)(5.(6.$26.(27.R2.R6.)$28.)(5.(6.$26.(29.R2.R5.)$2:.)(1<.$18.Lz,$18.(5.(23.R5.R1.)(6.(2.&40.)R3.(20.R1.)))))))")
(* [comment removed for export] *).
Proof.
  intros lazy mat acc. cbn. split.
  - apply NoDup_filter. apply accesses_pages_NoDup. constructor.
  - intros p H. apply filter_In in H. destruct H as [Hin Hf].
    apply Bool.andb_true_iff in Hf. destruct Hf as [H1 H2].
    split; [exact H1|]. split; [destruct (page_mem p mat); [discriminate| reflexivity]|].
    destruct (accesses_pages_spec _ _ _ Hin) as [[]|E]. exact E.
Qed.

Lemma newly_pages_NoDup_app : forall lazy mat acc,
  List.NoDup mat -> List.NoDup (newly_materialized_pages lazy mat acc ++ mat).
Proof.
  intros lazy mat acc ND. destruct (newly_pages_spec lazy mat acc) as [NDn Hn].
  apply NoDup_app; [exact NDn| exact ND|].
  intros p Hp Hm. destruct (Hn p Hp) as (_ & Hpm & _).
  apply (proj2 (page_mem_In p mat)) in Hm. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma newly_nil_materialize : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pmo,$3.Pacc,(0.(1.(2.&40.)$17.))P,(6.(0.(2.&40.))(24.(;.R2.)(<.R2.)R1.)(2;.(2.&40.)))(6.(2<.$3.)(2=.R3.R2.)(2>.$3.R3.))")
(* [comment removed for export] *).
Proof.
  intros mo acc H. unfold materialize_model_accesses, materialize_accesses. rewrite H.
  rewrite model_eta. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma newly_nil_of : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Plazy,(0.(1.(2.&40.)(2.&40.)))Pmat,(0.(2.&40.))Pacc,(0.(1.(2.&40.)$17.))P,Pz,$18.P,(23.R2.R1.)(1;.(6.$26.(27.(20.R2.)R5.)$2:.)(6.$26.(29.(20.R2.)R4.)$28.))(6.(0.(2.&40.))(24.R4.R3.R2.)(2;.(2.&40.)))")
(* [comment removed for export] *).
Proof.
  intros lazy mat acc H. destruct (newly_pages_spec lazy mat acc) as [_ Hn].
  destruct (newly_materialized_pages lazy mat acc) as [|p r] eqn:E; [reflexivity|].
  exfalso. destruct (Hn p ltac:(left; reflexivity)) as (H1 & H2 & z & Hz & ->).
  destruct (H z Hz); congruence.
Qed.

(* [comment removed for export] *)
Lemma materialize_nonlazy : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pmo,$3.Pacc,(0.(1.(2.&40.)$17.))P,Pz,$18.P,(23.R2.R1.)(6.$26.(27.(20.R2.)(;.R4.))$2:.)(6.(2<.$3.)(2=.R3.R2.)(2>.$3.R3.))")
(* [comment removed for export] *).
Proof. intros mo acc H. apply newly_nil_materialize, newly_nil_of. intros z Hz. left. apply H, Hz. Qed.

(* [comment removed for export] *)
Lemma materialize_some : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pmo,$3.Pacc,(0.(1.(2.&40.)$17.))Znew,(0.(2.&40.))(24.(;.R2.)(<.R2.)R1.)P,P,(2?.(6.(0.(2.&40.))R1.(2;.(2.&40.))))(1=.(21.(30.R4.)(31.(1?.(32.(2.&40.)R2.))$33.))(34.(:.R4.)))(6.(2<.$3.)(2=.R4.R3.)(2>.$3.(4.(;.R4.)(35.(2.&40.)R2.(<.R4.))R4.)))")
(* [comment removed for export] *).
Proof.
  intros mo acc new Hb. unfold materialize_model_accesses, materialize_accesses. fold new.
  destruct new as [|p r] eqn:E.
  - cbn [app]. rewrite model_eta. reflexivity.
  - destruct (Z.leb_spec0 (vm_backing_used mo + Z.of_nat (length (p :: r)) * page_size) (vm_limit (m_vmmaps mo))) as [L|L].
    + reflexivity.
    + exfalso. apply L, Hb. discriminate.
Qed.

(* [comment removed for export] *)
Definition eager_bytes (mo : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo)).

Lemma vm_backing_used_split : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pmo,$3.(6.$18.(30.R1.)(21.(36.R1.)(31.(1?.(32.(2.&40.)(<.R1.)))$33.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma vm_backing_used_backing : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pmo,$3.Ppages,(0.(2.&40.))(6.$18.(30.(4.(;.R2.)R1.R2.))(21.(36.R2.)(31.(1?.(32.(2.&40.)R1.))$33.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record asan_layout := AL {
  al_sb   : Z;    (* [comment removed for export] *)
  al_got  : Z;    (* [comment removed for export] *)
  al_gsb  : Z;    (* [comment removed for export] *)
  al_img_lo : Z; al_img_hi : Z   (* [comment removed for export] *)
}.

Definition shadow_of (L : asan_layout) (c : Z) : Z := al_sb L + c / 8.

(* [comment removed for export] *)
Definition aok_addr (L : asan_layout) (CS : Z -> Prop) (x : Z) : Prop :=
  CS x \/ (exists c, CS c /\ x = shadow_of L c) \/ (al_img_lo L <= x < al_img_hi L).

Definition acc_ok (L : asan_layout) (CS : Z -> Prop) (acc : list (word * nat)) : Prop :=
  forall z, byte_of acc z -> aok_addr L CS z.

Lemma acc_ok_nil : forall L CS, acc_ok L CS [].
Proof. intros L CS z (a & n & [] & _). Qed.

(* [comment removed for export] *)
Definition crange (CS : Z -> Prop) (A n : Z) : Prop := forall x, A <= x < A + n -> CS x.

Lemma crange_sub : forall CS A n B k, crange CS A n -> A <= B -> B + k <= A + n -> crange CS B k.
Proof. intros CS A n B k H H1 H2 x Hx. apply H. lia. Qed.

Lemma crange_mono : forall (CS CS' : Z -> Prop) A n, (forall x, CS x -> CS' x) -> crange CS A n -> crange CS' A n.
Proof. intros CS CS' A n HS H x Hx. apply HS, H, Hx. Qed.

Lemma acc_ok_client1 : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "PL,$37.PCS,P,$18.SpPa,(2.&40.)Pn,$17.PA,$18.Pk,$18.P,(38.R5.R2.R1.)P,(1=.R3.(39.&40.R5.))P,(1=.(21.(39.&40.R6.)(1?.R5.))(21.R4.R3.))(3:.R9.R8.(3;.(1.(2.&40.)$17.)(3<.(2.&40.)$17.R7.R6.)(2;.(1.(2.&40.)$17.))))")
(* [comment removed for export] *).
Proof.
  intros L CS a n A k HC H1 H2 z (a' & n' & Hin & Hr). destruct Hin as [E|[]]. injection E; intros <- <-.
  left. apply HC. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_ok_shadow : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "PL,$37.PCS,P,$18.SpPs,(2.&40.)Pn,$17.PA,$18.Pk,$18.Pc,$18.P,(38.R6.R3.R2.)P,(1=.R4.R2.)P,(1>.(21.R3.(31.+8.(3=.(1?.R6.)+1.)))(21.R5.R4.))P,(6.$18.(3>.R4.+8.)=)P,(6.$18.(39.&40.R9.)(3?.R;.R5.))(3:.R<.R;.(3;.(1.(2.&40.)$17.)(3<.(2.&40.)$17.R:.R9.)(2;.(1.(2.&40.)$17.))))")
(* [comment removed for export] *).
Proof.
  intros L CS s n A k c HC H1 H2 Hal Hs z (a' & n' & Hin & Hr). destruct Hin as [E|[]]. injection E; intros <- <-.
  right; left. exists (c + 8 * (z - bv_unsigned s)). split.
  - apply HC. lia.
  - unfold shadow_of in *. rewrite Hs.
    replace (c + 8 * (z - (al_sb L + c / 8))) with ((z - al_sb L - c / 8) * 8 + c) by lia.
    rewrite Z.div_add_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_ok_shadow1 : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "PL,$37.PCS,P,$18.SpPs,(2.&40.)PA,$18.Pk,$18.Pc,$18.P,(38.R5.R3.R2.)P,(5.(1=.R4.R2.)(1>.R2.(21.R4.R3.)))P,(6.$18.(39.&40.R6.)(3?.R8.R3.))(3:.R9.R8.(3;.(1.(2.&40.)$17.)(3<.(2.&40.)$17.R7.#1.)(2;.(1.(2.&40.)$17.))))")
(* [comment removed for export] *).
Proof.
  intros L CS s A k c HC H1 Hs z (a' & n' & Hin & Hr). destruct Hin as [E|[]]. injection E; intros <- <-.
  right; left. exists c. split; [apply HC; lia|]. cbn in Hr. lia.
Qed.

Lemma acc_ok_mono : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "PL,$37.PCS,P,$18.SpPCS',P,$18.SpPacc,(0.(1.(2.&40.)$17.))P,Px,$18.P,A1.R4.R1.A1.R4.R2.P,(3:.R5.R4.R2.)(3:.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L CS CS' acc HS H z Hz. destruct (H z Hz) as [H1|[(c & Hc & E)|H3]]; [left; auto| right; left; eauto| right; right; exact H3].
Qed.

Lemma acc_ok_img : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "PL,$37.PCS,P,$18.SpPa,(2.&40.)Pn,$17.P,(1=.(40.R4.)(39.&40.R2.))P,(1=.(21.(39.&40.R3.)(1?.R2.))(41.R5.))(3:.R6.R5.(3;.(1.(2.&40.)$17.)(3<.(2.&40.)$17.R4.R3.)(2;.(1.(2.&40.)$17.))))")
(* [comment removed for export] *).
Proof.
  intros L CS a n H1 H2 z (a' & n' & Hin & Hr). destruct Hin as [E|[]]. injection E; intros <- <-.
  right; right. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_ok_cons : forall L CS a n acc,
  acc_ok L CS [(a, n)] -> acc_ok L CS acc -> acc_ok L CS ((a, n) :: acc).
Proof.
  intros L CS a n acc H1 H2 z (a' & n' & Hin & Hr). destruct Hin as [E|Hin].
  - apply H1. exists a', n'. split; [left; exact E| exact Hr].
  - apply H2. exists a', n'. split; [exact Hin| exact Hr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ainv_laws (L : asan_layout) (AI : (Z -> Prop) -> Model -> Prop) := {
  ai_halted : forall CS mo, AI CS mo -> m_halted mo = None;
  ai_mat : forall CS mo acc, AI CS mo -> acc_ok L CS acc ->
      exists mo', materialize_model_accesses mo acc = Some mo' /\ AI CS mo' /\ mo_mat mo mo';
  ai_mono : forall (CS CS' : Z -> Prop) mo, (forall x, CS' x -> CS x) -> AI CS mo -> AI CS' mo
}.

Arguments ai_halted {L AI}.
Arguments ai_mat {L AI}.
Arguments ai_mono {L AI}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record apot := APOT {
  ap_good : word -> Prop;
  ap_nb : Z;
  ap_card : forall l, List.NoDup l -> Forall ap_good l -> Z.of_nat (length l) <= ap_nb
}.

Definition ainv_std (L : asan_layout) (P : apot) (CS : Z -> Prop) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "(5.(6.(2<.(2.&40.))(42.O1.)(43.(2.&40.)))(5.(25.(2.&40.)(<.O1.))(5.(44.(2.&40.)(45.O3.)(<.O1.))(5.Px,$18.P,(46.O4.O2.R1.)P,(6.$26.(27.(20.R2.)(;.O1.))$28.)(45.O3.(20.R3.))(1=.(21.(36.O1.)(31.(47.O3.)$33.))(34.(:.O1.)))))))")
(* [comment removed for export] *).

Lemma ainv_std_laws : forall L P, ainv_laws L (ainv_std L P).
Proof.
  intros L P. split.
  - intros CS mo (H & _). exact H.
  - intros CS mo acc (Hh & ND & GD & LZ & BG) OK.
    set (new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) acc).
    destruct (newly_pages_spec (m_vm_lazy mo) (m_vm_materialized mo) acc) as [NDn Hn]. fold new in NDn, Hn.
    assert (GDn : Forall (ap_good P) new).
    { apply Forall_forall. intros p Hp. destruct (Hn p Hp) as (H1 & _ & z & Hz & ->).
      apply LZ; [| exact H1]. apply OK, Hz. }
    assert (ND' : List.NoDup (new ++ m_vm_materialized mo)) by (apply newly_pages_NoDup_app; exact ND).
    assert (GD' : Forall (ap_good P) (new ++ m_vm_materialized mo)) by (apply Forall_app; split; assumption).
    pose proof (ap_card P _ ND' GD') as CARD. rewrite length_app, Nat2Z.inj_add in CARD.
    exists (with_vm_backing (m_vm_lazy mo) (new ++ m_vm_materialized mo) mo). split; [|split].
    + apply materialize_some. intros _. rewrite vm_backing_used_split. fold new.
      assert (E : Z.of_nat (length new) + Z.of_nat (length (m_vm_materialized mo)) <= ap_nb P) by exact CARD.
      unfold page_size in *. nia.
    + split; [exact Hh|]. split; [exact ND'|]. split; [exact GD'|]. split; [exact LZ| exact BG].
    + apply mo_mat_backing.
  - intros CS CS' mo HS (Hh & ND & GD & LZ & BG). split; [exact Hh|]. split; [exact ND|]. split; [exact GD|]. split; [|exact BG].
    intros x Hx Hl. apply LZ; [|exact Hl]. destruct Hx as [H|[(c & Hc & E)|H3]]; [left; auto| right; left; eauto| right; right; exact H3].
Qed.

(* [comment removed for export] *)
Fixpoint ivls_pages (iv : list (Z * Z)) : Z :=
  match iv with [] => 0 | (lo, hi) :: r => (hi - lo) / page_size + 1 + ivls_pages r end.

Definition in_ivls (iv : list (Z * Z)) (z : Z) : Prop := exists lo hi, In (lo, hi) iv /\ lo <= z < hi.

Lemma NoDup_map_inj_on : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "PA,StPB,StPf,P,R2.R2.Pl,(0.R3.)P,(25.R4.R1.)P,Px,R5.Py,R6.P,(19.R7.R2.R4.)P,(19.R8.R2.R5.)P,(6.R8.A1.R7.R4.A1.R7.R3.)(6.R:.R5.R4.)(25.R5.(48.R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros A B f l ND. induction ND as [|x r Hx ND IH]; cbn; intros INJ; [constructor|].
  constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & E & Hy).
    assert (y = x) by (apply INJ; [right; exact Hy| left; reflexivity| exact E]). subst y. contradiction.
  - apply IH. intros a b Ha Hb. apply INJ; right; assumption.
Qed.

(* [comment removed for export] *)
Lemma NoDup_pages_interval : ltac2:(CDefT.buildp (gd_tbl_ALazy ()) "Pl,(0.$18.)Plo,$18.Phi,$18.P,(25.$18.R3.)P,Pz,$18.P,(19.$18.R1.R5.)(5.(5.(1=.R5.R2.)(1>.R2.R4.))(6.$18.(3>.R2.$33.)=))P,(1=.R4.R3.)(1=.(1?.(32.$18.R6.))(21.(49.(3=.R4.R5.)$33.)+1.))")
(* [comment removed for export] *).
Proof.
  intros l lo hi ND H Hle.
  set (f := fun z : Z => Z.to_nat ((z - lo) / page_size)).
  set (n := Z.to_nat ((hi - lo) / page_size + 1)).
  assert (INJ : forall x y, In x l -> In y l -> f x = f y -> x = y).
  { intros x y Hx Hy E. destruct (H x Hx) as [Rx Mx]. destruct (H y Hy) as [Ry My]. unfold f in E.
    unfold page_size in *.
    assert (0 <= (x - lo) / 4096) by (apply Z.div_pos; lia).
    assert (0 <= (y - lo) / 4096) by (apply Z.div_pos; lia).
    apply Z2Nat.inj in E; [|lia|lia].
    pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.div_mod y 4096 ltac:(lia)).
    pose proof (Z.div_mod (x - lo) 4096 ltac:(lia)). pose proof (Z.div_mod (y - lo) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (x - lo) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (y - lo) 4096 ltac:(lia)).
    nia. }
  assert (BND : forall x, In x l -> (f x < n)%nat).
  { intros x Hx. destruct (H x Hx) as [Rx Mx]. unfold f, n, page_size in *.
    assert ((x - lo) / 4096 <= (hi - lo) / 4096) by (apply Z.div_le_mono; lia).
    assert (0 <= (x - lo) / 4096) by (apply Z.div_pos; lia). lia. }
  assert (LEN : (length l <= n)%nat).
  { assert (ND' : List.NoDup (map f l)) by (apply NoDup_map_inj_on; assumption).
    assert (INC : incl (map f l) (seq 0 n)).
    { intros k Hk. apply in_map_iff in Hk. destruct Hk as (x & <- & Hx). apply in_seq. pose proof (BND x Hx). lia. }
    pose proof (NoDup_incl_length ND' INC) as LL. rewrite length_map, length_seq in LL. exact LL. }
  unfold n in LEN. unfold page_size in *.
  assert (0 <= (hi - lo) / 4096) by (apply Z.div_pos; lia). lia.
Qed.
