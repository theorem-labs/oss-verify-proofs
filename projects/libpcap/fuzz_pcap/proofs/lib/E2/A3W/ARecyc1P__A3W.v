(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From Stdlib Require Sorting.Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ARecyc1P.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (SHUB, SHUB + gr); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' AB S rz gr SHLO SHUB SHHI SHF0 SHF1 : Z).
Let HB := AB + rz - 16.
Definition reckf : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (RB <= AB /\ AB + S <= RB + au /\ 16 <= rz /\ rz <= S)
  /\ (2201439137792 <= SHLO /\ SHLO <= SHUB /\ 0 <= gr /\ SHUB + gr <= SHHI /\ SHHI <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf.

(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with CA => constr:(t) | RB => constr:(SB) | FA => constr:(SB) | RI => constr:(SB) | AB => constr:(SB) | _ => X end.
Ltac kdrop_all := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.   (* [comment removed for export] *)
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in
      first [ solve [ kkeep2 X Y; klia ] | lia ]
  | |- _ => lia end.
Ltac kind := pose proof KF as KF'; unfold reckf, AIMG_HI in *; subst HB;
  sg_set; (nd_pre KF' 9%nat; intros F_lo sgk1 F_c F_sb F_tsb F_csb F_mu F_ab F_sh; nd_post); (nd_pre sgk1 7%nat; intros Ft1 Ft2 Ft3 Fc1 Fc2 Fc3 Ftc; nd_post);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1|]); first [kind1 | exact I].

#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6303744 -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="lo ctx c RB mu au mfa S SHLO SHHI KF"] Lemma RK_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="lo ctx c RB mu au mfa S SHLO SHHI KF"] Lemma RK_objL : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx c mu au mfa S SHLO SHHI KF"] Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="rc lo ctx SB c au mfa S SHLO SHHI KF"] Lemma RK_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  (A + k <= AB \/ AB + 8 <= A) -> (A + k <= HB \/ HB + 4 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c au mfa S SHLO SHHI KF"] Lemma RK_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx c RB mu au mfa S SHLO SHHI KF"] Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHUB \/ SHUB + gr <= A) -> (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
End Kinds.

#[using="Type"] Lemma upd_app_right : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [rewrite Nat.sub_0_r; reflexivity|].
  destruct i as [|i]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.
#[using="Type"] Lemma upd_app_left : forall {X} (l1 l2 : list X) i x, (i < length l1)%nat -> upd (l1 ++ l2) i x = upd l1 i x ++ l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. rewrite IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_drop_prim : forall R L st X m c k n b1 ctx l1 l2 drained pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_drop R pend') 0 0 L st (xrec st X c k l1 l2 drained) m.
Proof.
  intros R L st X m c k n b1 ctx l1 l2 drained pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP XB WF.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_drop_prim L st st X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF eq_refl eq_refl).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Definition AHr (R : qrconc) (cs : list achunk) : aholes := mkAHoles (AQdr R 0 0) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition rec_W (L : alayout) (sp : Z) (c k n nf mfa mfa' : Z) : list (Z * Z) :=
  let AB := aslot_addr L c k in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (shad UB, shad UB + granules n); (al_t L + 2800, al_t L + 3168)]%Z)
  ++ cd_W L sp c nf mfa mfa'.

(* [comment removed for export] *)
Definition arecyc1_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk) (c k n lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_rec1_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (pend' : list (achunk * Z)) (cs : list achunk) (c k n b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, k) :: pend' -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  recyc1_ret L RNG sp st c k n b1 ctx lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma read_qchunk : forall L st X m c k n b1 ctx l1 l2,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  aslots L st X m c -> aslot_shadow L st X m c ->
  let S := size_of_class c in let AB := aslot_addr L c k in let rz := rz_size n in let UB := AB + rz in
     rw_cells asegs m (UB - 16) [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ junk_at m UB (S - rz)
  /\ (16 < rz -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz - 32))
  /\ rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)))]
  /\ rw_cells asegs m (shad UB) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)))]
  /\ rw_cells asegs m (shad UB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n)))].
Proof.
  intros L st X m c k n b1 ctx l1 l2 ALO WF XB [SL _] [SH _]. cbv zeta.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  (nd_pre SL 3%nat; intros LH [stb [E HDR]] UJ; nd_post). injection E as <-.
  replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact HDR|]. split; [exact UJ|]. split; [exact LH|].
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 6%nat; intros SE G2 GE G0 GF _; nd_post).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  (nd_pre (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) ltac:(apply repeat_length) ltac:(apply repeat_length) SH) 3%nat; intros SHA SHU SHR; nd_post).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR.
  split; [exact SHA|]. split; [exact SHU| exact SHR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pend_head_busy : forall L st X R m c n k pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  exists b1 ctx l1 l2, x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Proof.
  intros L st X R m c n k pend' (_ & _ & _ & _ & _ & _ & CP & _) EP.
  (nd_pre CP 4%nat; intros _ _ OK _; nd_post). unfold qr_entries in OK. rewrite EP in OK.
  assert (HOK : qentry_ok X (CPrim c n, k)).
  { eapply (proj1 (Forall_forall _ _) OK). rewrite !in_app_iff. right. right. right. left. reflexivity. }
  unfold qentry_ok in HOK. cbn [fst snd] in HOK. (nd_pre HOK 3%nat; intros b1 ctx Hin; nd_post).
  (nd_pre (in_split _ _ Hin) 3%nat; intros l1 l2 E; nd_post). exists b1, ctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nf_bound : forall L st X c, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c
  /\ 4 * (c_num_freed (get_cls st c) + max_cached c / 2) <= K_FREEARR_MAX.
Proof.
  intros L st X c WF HC. (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  split; [exact NFA|].
  pose proof (size_of_class_pos c HC) as [SZ _]. (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.max_cached_range c) as ndP__; nd_pre ndP__ 3%nat; intros _ MC _; nd_post).
  unfold K_FREEARR_MAX, K_FREEARR_OFF in *. generalize NFA A1 A2 SZ MC. clear. intros. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_vals_lt : forall L st X c tail, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  Forall (fun w : word => bv_unsigned w < 2^31)
         (firstn (Z.to_nat (c_count (get_cls st c))) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail)).
Proof.
  intros L st X c tail WF HC LEN. (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  rewrite firstn_app, length_map. replace (Z.to_nat (c_count (get_cls st c)) - length (xc_cache (x_cls X c)))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply Forall_forall. intros w Hw.
  assert (Hw' : In w (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)))).
  { rewrite <- (firstn_skipn (Z.to_nat (c_count (get_cls st c))) (map _ _)). apply in_app_iff. left. exact Hw. }
  apply in_map_iff in Hw'. (nd_pre Hw' 2%nat; intros k0 ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hk).
  pose proof (RANGE k0 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
  assert (B : 0 <= acompact c k0 < 2^28).
  { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
  rewrite unsigned_lit; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rec1_store__stmt : Prop := store_rec1_stmt.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 1).
Variable RNG' : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 5).
Variable st : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 6).
Variable stX : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 7).
Variable X : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 8).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 9).
Variable pend' : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 10).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 11).
Variable c : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 12).
Variable k : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 13).
Variable n : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 14).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 15).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 16).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 17).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 18).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 19).
Variable tail : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 20).
Let S := size_of_class c.
Let half := max_cached c / 2.
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
Let cnt := c_count (get_cls st c).
Let nd := ndist st c.
Let AB := aslot_addr L c k.
Let rz := rz_size n.
Let RB := aregion L c.
Let FA := afreearr L c.
Let RI := aregion_info L c.
Let CA := acache_addr L c.
Let SHUB := shad (AB + rz).
Let SHF0 := shad (FA + mfa).
#[using="HL S half mu au nf mfa cnt nd AB rz RB FA RI CA SHUB SHF0"] Lemma rec1_store__body : ltac:(let T := type of (fun (h : rec1_store__stmt) => h L RNG RNG' sp m m' st stX X R pend' cs c k n b1 ctx lo l1 l2 tail) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (RNG', (sp, (m, (m', (st, (stX, (X, (R, (pend', (cs, (c, (k, (n, (b1, (ctx, (lo, (l1, (l2, tail))))))))))))))))))))) as _.
  unfold store_rec1_stmt. intros ALO ARNG AR EP XB CEIL LO CH LCH RR.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.max_cached_range c) as ndP__; nd_pre ndP__ 3%nat; intros MCR MCH MCE; nd_post).
  (* [comment removed for export] *)
  (nd_pre RR 7%nat; intros m1 MU1 WM1 CDR MAG' HDR' SHU'; nd_post). cbv zeta in MU1.
  (nd_pre CDR 29%nat; intros FPLE drained mfa' sj' sta' DR GCX STE MFD NEWB NEWM NEWMOD MU2 WM2 MI' ST' RECS' RECc' CH' MTX' REG' J72' STATS' LSJ' STA' DRA FJ' AZF' MC'; nd_post).
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  chg (size_of_class c) S. chg (max_cached c / 2) half.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa. chg (c_count (get_cls st c)) cnt.
  chg (ndist st c) nd.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  chg (aslot_addr L c k) AB. chg (rz_size n) rz.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 4%nat; intros RIE RBE FAE CAE; nd_post).
  chg (aregion L c) RB. chg (afreearr L c) FA. chg (aregion_info L c) RI. chg (acache_addr L c) CA.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  (nd_pre CNT16 5%nat; intros CNT16 CNTle CNT1 LENCc NFle; nd_post).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  (pose proof (init_cache_fields st) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. (nd_pre (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) 11%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 _; nd_post).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  (nd_pre EF 10%nat; intros EF1 EF2 EF3 EF4 EF5 EF6 EF7 EF8 EF9 EF10; nd_post).
  (* [comment removed for export] *)
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros _ _ AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2]. fold rz in RZ1, RZ2.
  (pose proof (rounded_size_facts n (proj1 N0)) as ndP__; nd_pre ndP__ 5%nat; intros RS1 RS2 RS3 RS4 RS5; nd_post).
  assert (FITr : rz + n <= S /\ rz <= S) by (subst S rz; clear -FIT0 RS1 RZ1 N0; lia). destruct FITr as [FITr RZS].
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE SG2 GE SG0 SGF SHLO1 SHHI1 SHR1 SHR2; nd_post).
  fold S AB rz RB mu in SE, SG2, GE, SG0, SGF, SHLO1, SHHI1, SHR1, SHR2.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  chg (shad (AB + rz)) SHUB. chg (shad (FA + mfa)) SHF0. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA /\ SHUB = shad AB + shlen rz).
  { subst SHUB SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB rz half cnt nf' cnt'.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 SE RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  (nd_pre SHE 17%nat; intros SHE1 SHE4 SH1 SH2 SH3 SH4 SH5 SH6 SH9 SH10 SH11 SH12 SH13 SH14 SH15 SH16 SHE0; nd_post).
  assert (KF : reckf (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' AB S rz (granules n) (shad AB) SHUB (shad AB + shlen S) SHF0 SHF1).
  { unfold reckf. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL1u TL4u TL2 TL4 CL1 CL1u CL2 CL3 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 RZ1 RZS SHLO1 SE SG2 SG0 GE SGF SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). unfold granules in *.
    unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst AB rz SHUB. cbn [outside] in H13 |- *.
      pose proof (bv_unsigned_in_range 64 sp). clear -H13 H. lia.
    - unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
      apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
      subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  (nd_pre (read_qchunk L st X m c k n b1 ctx l1 l2 ALO WF XB SLOTS0 SSH0) 6%nat; intros _ UJ LH SHA _ SHR; nd_post).
  fold S AB rz in UJ, LH, SHA, SHR. rewrite <- ?SHE0 in SHR.
  assert (HBE : AB + rz + -16 = AB + rz - 16) by (clear; lia).
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      (nd_pre TL 3%nat; intros tw tail' ndR1__; nd_post; revert ndR1__; intros ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ SHUB + granules n <= shad FA /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SGF SHE0 SG0 GE. lia. }
  (nd_pre FAB 7%nat; intros FB1 FB2 FB3 FB4 FB5 FB6 FB7; nd_post).
  assert (SHB : shad RB <= SHUB /\ SHF1 <= shad (RB + 4294967296) /\ 0 <= granules n) by (clear -SH13 SHE0 SG2 SH5 FB2 GE SG0 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  (nd_pre SHB 3%nat; intros SB1 SB2 SB3; nd_post).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr asegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB3 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB2 SHE4 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (HBK : 16 < rz -> 32 <= rz) by (intros H16; clear -RZ2 H16; Z.div_mod_to_equations; lia).
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
        pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16 DJ RZ1 RZS; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; lia].
      + intros b Hb. (nd_pre (busy_of_Some_facts X c k' b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16 RZ1 RZS; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      assert (UJ' : junk_at m' (AB + rz) (S - rz)).
      { eapply junk_frame; [exact UJ | exact MUALL | exact WMALL |]. intros POS.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
      pose proof (junk_of_cells m' _ _ HDR') as JH. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JH. fold AB rz in JH. rewrite ?HBE in JH.
      change (Z.of_nat 16) with 16 in JH.
      destruct (Z.lt_ge_cases 16 rz) as [RZG|RZE].
      + specialize (HBK RZG). destruct (LH RZG) as [_ LJ]. pose proof (junk_of_cells m' _ _ (MAG' RZG)) as JM. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JM. change (Z.of_nat 16) with 16 in JM.
        assert (LJ' : junk_at m' (AB + 16) (rz - 32)).
        { eapply junk_frame; [exact LJ | exact MUALL | exact WMALL |]. intros POS.
          apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
        replace S with (16 + ((rz - 32) + (16 + (S - rz)))) by (clear; lia).
        apply junk_merge; [exact JM | | clear; lia | clear -HBK RZS; lia].
        apply junk_merge; [exact LJ' | | clear -HBK; lia | clear -RZS; lia].
        replace (AB + 16 + (rz - 32)) with (AB + rz - 16) by (clear; lia).
        apply junk_merge; [exact JH | | clear; lia | clear -RZS; lia].
        replace (AB + rz - 16 + 16) with (AB + rz) by (clear; lia). exact UJ'.
      + assert (RZ16 : rz = 16) by (clear -RZE RZ1; lia). rewrite RZ16 in JH, UJ'.
        replace (AB + 16 - 16) with AB in JH by (clear; lia).
        replace S with (16 + (S - 16)) by (clear; lia). apply junk_merge; [exact JH | exact UJ' | clear; lia | clear -RZS RZ16; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
      pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)
                  /\ (shad (aslot_addr L c k') + shlen S <= shad AB \/ shad AB + shlen S <= shad (aslot_addr L c k'))).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 DJ AL' AL16 SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4 SGF SHE0 SG2; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB1 FB2 FB3 FB4 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH10 SH11 SH12 SH13 SH14 SH15 SGF SHE0 SG2 SG0 GE; lia
                                | apply ICW_far; clear -POS FB2 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      assert (SHA' : rw_cells asegs m' (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen rz)))]).
      { eapply cells_frame; [exact SHA | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SG2; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 FB5 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 GE SG0; lia]. }
      assert (SHR' : rw_cells asegs m' (SHUB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { eapply cells_frame; [exact SHR | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SGF GE SG0; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF GE SG0 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 SH12 SH13; lia]. }
      assert (C2pre : rw_cells asegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz))) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (granules n)))]).
      { rewrite Z2Nat.id by (clear -SG2; lia). rewrite <- SHE0. exact SHU'. }
      pose proof (cb_app m' _ _ _ _ _ SHA' C2pre) as C2.
      assert (C3pre : rw_cells asegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { replace (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) with (SHUB + granules n) by (rewrite SHE0; clear -SG2 GE SG0; lia). exact SHR'. }
      pose proof (cb_app m' _ _ _ _ _ C2 C3pre) as C3.
      rewrite <- !repeat_app in C3.
      replace (Z.to_nat (shlen rz) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen rz - granules n))%nat with (Z.to_nat (shlen S)) in C3 by (clear -SG2 GE SG0 SGF; lia).
      exact C3. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 SGF SHE0 SG2; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. (nd_pre (CLS c' Hc') 4%nat; intros RC2 FA2 SL2 SS2; nd_post). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    (nd_pre (PERC c' Hc') 12%nat; intros B1 B2 B3 B4 B5 B6 B7 BLENF BLENC BCNTB BND BRANGE; nd_post).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    (nd_pre REGD 11%nat; intros RD1 RD2 RD3 RD4 RD5 RD6 RD7 RD8 RD9 RD10 RD11; nd_post).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2; lia.
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2 SGF FB3; lia. }
    assert (DJI : disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. (nd_pre (busy_of_Some_facts X c' k0 b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ ((xb_alloc L b + size_of_class (xb_class b) <= RB + mu /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ AB + S <= xb_alloc L b))
          \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - assert (NK : xb_slot b <> k) by (intros EK; exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb EC EK)).
      pose proof (slots_disjoint L c (xb_slot b) k (proj1 KB) (proj1 KR) NK ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. split; [clear -P4 A1; lia| exact DJ].
    - (pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6303744 ->      (* [comment removed for export] *)
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL2 CL3 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  assert (DJtls : forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k ->      (* [comment removed for export] *)
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 TL2; pose proof atp_lin; tlsfar_expose; lia].
    eapply (RK_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 TL2 SP1; pose proof atp_lin; tlsfar_expose; lia. }
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BQuar c k n b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia | apply DJtls; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (AB, AB + S);
              (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. (nd_pre Hx 8%nat; intros O1 O2 O3 O4 O5 O6 O7 _; nd_post).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_drop R pend') 0 0 L st X' m) by (subst X'; eapply AQdr_drop_prim; [exact HQ | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      intros b Hb; (nd_pre (BB b Hb) 3%nat; intros Bb1 Bb2 Bb3; nd_post); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_drop R pend') 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [exact (iff_refl _) | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_drop R pend') cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    (pose proof (ao_nodes L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ ON1 ON3 ONs _; nd_post). (pose proof (ao_store L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OS1 OS3 OSs _; nd_post). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_drop R pend') cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - (nd_pre (CLS' c' Hc' NE) 6%nat; intros Y1 Y2 Y3 Y4 Y5 Y6; nd_post). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    (nd_pre AM 14%nat; intros Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 RC RPA RSC RPSH RTLS; nd_post).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| split; [exact RPSH | exact RTLS]]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      (nd_pre (RC c HC) 4%nat; intros Q1 Q2 Q3 Q4; nd_post). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split. { unfold rec_W. cbv zeta. fold AB rz. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H5 _]. cbn [outside] in H5 |- *. subst SHUB. clear -H5. lia.
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [_ HW]. exact HW. }
  split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BQuar c k n b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.
End Zd1.
#[using="HL"] Lemma rec1_store : ltac:(let t := eval cbv delta [rec1_store__stmt] in rec1_store__stmt in exact t).
Proof. exact rec1_store__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arecyc1__stmt : Prop := forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells asegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 0).
Variable k : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 39).
Variable X : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 40).
Variable R : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 41).
Variable pend' : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 42).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 43).
Variable c : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 44).
Variable kk : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 45).
Variable n : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 46).
Variable CBA : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 47).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 48).
Variable cbs : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 49).
#[using="HL"] Lemma arecyc1__body : ltac:(let T := type of (fun (h : arecyc1__stmt) => h RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R pend' cs c kk n CBA lo cbs) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (k, (Q, (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (X, (R, (pend', (cs, (c, (kk, (n, (CBA, (lo, cbs)))))))))))))))))))))))))))))))))))))))))))))))))) as _.
  intros ALO ARNG AR EP MI ST CEIL LO TP Ha0 Ha1 CBC CB0 CB1 RSTK RCB KONT.
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT0 INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  (nd_pre (pend_head_busy L st X R m c n kk pend' HQ EP) 5%nat; intros b1 ctx l1 l2 XB; nd_post).
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  (nd_pre (RCLS c HC) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  pose proof RT0 as RT1.
  (nd_pre RT1 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  (nd_pre RT2 3%nat; intros DPM MLIM RWCS; nd_post).
  (nd_pre INST 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  (* [comment removed for export] *)
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  (nd_pre (read_qchunk L st X m c kk n b1 ctx l1 l2 ALO WF XB SLOTS SSH) 6%nat; intros HDR UJ MAG SHA SHU SHR; nd_post).
  destruct (slot_rng L st X c kk ALO WF HC KR RNG ARNG) as [RAB RSAB].
  (pose proof (slot_geo L st X c kk ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (* [comment removed for export] *)
  eapply (recyc1_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c kk n b1 ctx CBA lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta cbs (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))));
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ CBA _ => exact CBC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- rw_cells _ _ (aslot_addr _ _ _ + rz_size _ - 16) _ => exact HDR
       | |- 16 < _ -> _ => intros H16; exact (proj1 (MAG H16))
       | |- rw_cells _ _ (shad _) _ => exact SHU
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ CBA _ => exact RCB
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (aslot_addr _ _ _) _ => exact RAB
       | |- rng _ (shad (aslot_addr _ _ _)) _ => exact RSAB
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | rewrite Ha1; unfold qhdr; reflexivity]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; (nd_pre (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) 11%nat; intros _ _ _ _ _ _ _ _ _ CB2 _; nd_post); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- (_ + 1) * _ <= _ =>
           unfold ndist in KR; transitivity (c_allocated_user (get_cls st c) / size_of_class c * size_of_class c);
           [apply Z.mul_le_mono_nonneg_r; [clear -S1; lia| clear -KR; lia]
           | rewrite Z.mul_comm; pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) (size_of_class c) ltac:(clear -S1; lia)); clear -A1 H; lia]
       | |- 1 <= _ => first [assumption | idtac]; destruct (BUSY (bany BQuar c kk n b1 ctx) ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]; cbn in M; clear -M; lia
       | |- rz_size _ + _ <= _ => pose proof (rounded_size_ge n); clear -FIT0 H; lia
       | |- 0 <= _ < _ => first [assumption | clear -CTX0; lia]
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- 0 <= _ => first [assumption | exact (proj1 KR)]
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  (nd_pre (rec1_store L RNG RNG' sp m m' st stX X R pend' cs c kk n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR) 23%nat; intros X' mfa' MU WM MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC MU1 AU1 XS XL; nd_post).
  (nd_pre RR 5%nat; intros m1 _ _ CDR _; nd_post). (nd_pre CDR 17%nat; intros FPLE dr mfa2 sj2 sta2 _ _ _ _ _ _ _ _ _ MIT STT _; nd_post).
  eapply KONT. unfold arecyc1_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|]. split; [exact MU1|]. split; [exact AU1|].
  split; [exact XS| exact XL].
Qed.
End Zd2.
#[using="HL"] Theorem arecyc1 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells asegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom asegs)).
Proof. exact arecyc1__body. Qed.
End P.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (SHUB, SHUB + gr); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' AB S rz gr SHLO SHUB SHHI SHF0 SHF1 : Z).
Let HB := AB + rz - 16.
Definition reckf : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (RB <= AB /\ AB + S <= RB + au /\ 16 <= rz /\ rz <= S)
  /\ (2201439137792 <= SHLO /\ SHLO <= SHUB /\ 0 <= gr /\ SHUB + gr <= SHHI /\ SHHI <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf.

(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with CA => constr:(t) | RB => constr:(SB) | FA => constr:(SB) | RI => constr:(SB) | AB => constr:(SB) | _ => X end.
Ltac kdrop_all := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.   (* [comment removed for export] *)
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in
      first [ solve [ kkeep2 X Y; klia ] | lia ]
  | |- _ => lia end.
Ltac kind := pose proof KF as KF'; unfold reckf, AIMG_HI in *; subst HB;
  sg_set; (nd_pre KF' 9%nat; intros F_lo sgk1 F_c F_sb F_tsb F_csb F_mu F_ab F_sh; nd_post); (nd_pre sgk1 7%nat; intros Ft1 Ft2 Ft3 Fc1 Fc2 Fc3 Ftc; nd_post);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1|]); first [kind1 | exact I].

#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6307840 -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="lo ctx c RB mu au mfa S SHLO SHHI KF"] Lemma RK_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="lo ctx c RB mu au mfa S SHLO SHHI KF"] Lemma RK_objL : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx c mu au mfa S SHLO SHHI KF"] Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="rc lo ctx SB c au mfa S SHLO SHHI KF"] Lemma RK_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  (A + k <= AB \/ AB + 8 <= A) -> (A + k <= HB \/ HB + 4 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c au mfa S SHLO SHHI KF"] Lemma RK_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx c RB mu au mfa S SHLO SHHI KF"] Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHUB \/ SHUB + gr <= A) -> (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
#[using="rc lo ctx SB c RB mu au mfa S SHLO SHHI KF"] Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
End Kinds.

#[using="Type"] Lemma upd_app_right : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [rewrite Nat.sub_0_r; reflexivity|].
  destruct i as [|i]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.
#[using="Type"] Lemma upd_app_left : forall {X} (l1 l2 : list X) i x, (i < length l1)%nat -> upd (l1 ++ l2) i x = upd l1 i x ++ l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. rewrite IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_drop_prim : forall R L st X m c k n b1 ctx l1 l2 drained pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_drop R pend') 0 0 L st (xrec st X c k l1 l2 drained) m.
Proof.
  intros R L st X m c k n b1 ctx l1 l2 drained pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP XB WF.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_drop_prim L st st X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF eq_refl eq_refl).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Definition AHr (R : qrconc) (cs : list achunk) : aholes := mkAHoles (AQdr R 0 0) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition rec_W (L : alayout) (sp : Z) (c k n nf mfa mfa' : Z) : list (Z * Z) :=
  let AB := aslot_addr L c k in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (shad UB, shad UB + granules n); (al_t L + 2800, al_t L + 3168)]%Z)
  ++ cd_W L sp c nf mfa mfa'.

(* [comment removed for export] *)
Definition arecyc1_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk) (c k n lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_rec1_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (pend' : list (achunk * Z)) (cs : list achunk) (c k n b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, k) :: pend' -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  recyc1_ret L RNG sp st c k n b1 ctx lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma read_qchunk : forall L st X m c k n b1 ctx l1 l2,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  aslots L st X m c -> aslot_shadow L st X m c ->
  let S := size_of_class c in let AB := aslot_addr L c k in let rz := rz_size n in let UB := AB + rz in
     rw_cells asegs m (UB - 16) [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ junk_at m UB (S - rz)
  /\ (16 < rz -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz - 32))
  /\ rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)))]
  /\ rw_cells asegs m (shad UB) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)))]
  /\ rw_cells asegs m (shad UB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n)))].
Proof.
  intros L st X m c k n b1 ctx l1 l2 ALO WF XB [SL _] [SH _]. cbv zeta.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  (nd_pre SL 3%nat; intros LH [stb [E HDR]] UJ; nd_post). injection E as <-.
  replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact HDR|]. split; [exact UJ|]. split; [exact LH|].
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 6%nat; intros SE G2 GE G0 GF _; nd_post).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  (nd_pre (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) ltac:(apply repeat_length) ltac:(apply repeat_length) SH) 3%nat; intros SHA SHU SHR; nd_post).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR.
  split; [exact SHA|]. split; [exact SHU| exact SHR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pend_head_busy : forall L st X R m c n k pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  exists b1 ctx l1 l2, x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Proof.
  intros L st X R m c n k pend' (_ & _ & _ & _ & _ & _ & CP & _) EP.
  (nd_pre CP 4%nat; intros _ _ OK _; nd_post). unfold qr_entries in OK. rewrite EP in OK.
  assert (HOK : qentry_ok X (CPrim c n, k)).
  { eapply (proj1 (Forall_forall _ _) OK). rewrite !in_app_iff. right. right. right. left. reflexivity. }
  unfold qentry_ok in HOK. cbn [fst snd] in HOK. (nd_pre HOK 3%nat; intros b1 ctx Hin; nd_post).
  (nd_pre (in_split _ _ Hin) 3%nat; intros l1 l2 E; nd_post). exists b1, ctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nf_bound : forall L st X c, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c
  /\ 4 * (c_num_freed (get_cls st c) + max_cached c / 2) <= K_FREEARR_MAX.
Proof.
  intros L st X c WF HC. (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  split; [exact NFA|].
  pose proof (size_of_class_pos c HC) as [SZ _]. (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB.max_cached_range c) as ndP__; nd_pre ndP__ 3%nat; intros _ MC _; nd_post).
  unfold K_FREEARR_MAX, K_FREEARR_OFF in *. generalize NFA A1 A2 SZ MC. clear. intros. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_vals_lt : forall L st X c tail, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  Forall (fun w : word => bv_unsigned w < 2^31)
         (firstn (Z.to_nat (c_count (get_cls st c))) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail)).
Proof.
  intros L st X c tail WF HC LEN. (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  rewrite firstn_app, length_map. replace (Z.to_nat (c_count (get_cls st c)) - length (xc_cache (x_cls X c)))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply Forall_forall. intros w Hw.
  assert (Hw' : In w (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)))).
  { rewrite <- (firstn_skipn (Z.to_nat (c_count (get_cls st c))) (map _ _)). apply in_app_iff. left. exact Hw. }
  apply in_map_iff in Hw'. (nd_pre Hw' 2%nat; intros k0 ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hk).
  pose proof (RANGE k0 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
  assert (B : 0 <= acompact c k0 < 2^28).
  { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
  rewrite unsigned_lit; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rec1_store__stmt : Prop := store_rec1_stmt.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 1).
Variable RNG' : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 5).
Variable st : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 6).
Variable stX : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 7).
Variable X : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 8).
Variable R : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 9).
Variable pend' : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 10).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 11).
Variable c : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 12).
Variable k : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 13).
Variable n : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 14).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 15).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 16).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 17).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 18).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 19).
Variable tail : ltac2:(SecDietF.SzSecF.ty 'rec1_store__stmt 20).
Let S := size_of_class c.
Let half := max_cached c / 2.
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
Let cnt := c_count (get_cls st c).
Let nd := ndist st c.
Let AB := aslot_addr L c k.
Let rz := rz_size n.
Let RB := aregion L c.
Let FA := afreearr L c.
Let RI := aregion_info L c.
Let CA := acache_addr L c.
Let SHUB := shad (AB + rz).
Let SHF0 := shad (FA + mfa).
#[using="HL S half mu au nf mfa cnt nd AB rz RB FA RI CA SHUB SHF0"] Lemma rec1_store__body : ltac:(let T := type of (fun (h : rec1_store__stmt) => h L RNG RNG' sp m m' st stX X R pend' cs c k n b1 ctx lo l1 l2 tail) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (RNG', (sp, (m, (m', (st, (stX, (X, (R, (pend', (cs, (c, (k, (n, (b1, (ctx, (lo, (l1, (l2, tail))))))))))))))))))))) as _.
  unfold store_rec1_stmt. intros ALO ARNG AR EP XB CEIL LO CH LCH RR.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB.max_cached_range c) as ndP__; nd_pre ndP__ 3%nat; intros MCR MCH MCE; nd_post).
  (* [comment removed for export] *)
  (nd_pre RR 7%nat; intros m1 MU1 WM1 CDR MAG' HDR' SHU'; nd_post). cbv zeta in MU1.
  (nd_pre CDR 29%nat; intros FPLE drained mfa' sj' sta' DR GCX STE MFD NEWB NEWM NEWMOD MU2 WM2 MI' ST' RECS' RECc' CH' MTX' REG' J72' STATS' LSJ' STA' DRA FJ' AZF' MC'; nd_post).
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  chg (size_of_class c) S. chg (max_cached c / 2) half.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa. chg (c_count (get_cls st c)) cnt.
  chg (ndist st c) nd.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  chg (aslot_addr L c k) AB. chg (rz_size n) rz.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 4%nat; intros RIE RBE FAE CAE; nd_post).
  chg (aregion L c) RB. chg (afreearr L c) FA. chg (aregion_info L c) RI. chg (acache_addr L c) CA.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  (nd_pre CNT16 5%nat; intros CNT16 CNTle CNT1 LENCc NFle; nd_post).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  (pose proof (init_cache_fields st) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. (nd_pre (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) 11%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 _; nd_post).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  (nd_pre EF 10%nat; intros EF1 EF2 EF3 EF4 EF5 EF6 EF7 EF8 EF9 EF10; nd_post).
  (* [comment removed for export] *)
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros _ _ AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2]. fold rz in RZ1, RZ2.
  (pose proof (rounded_size_facts n (proj1 N0)) as ndP__; nd_pre ndP__ 5%nat; intros RS1 RS2 RS3 RS4 RS5; nd_post).
  assert (FITr : rz + n <= S /\ rz <= S) by (subst S rz; clear -FIT0 RS1 RZ1 N0; lia). destruct FITr as [FITr RZS].
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE SG2 GE SG0 SGF SHLO1 SHHI1 SHR1 SHR2; nd_post).
  fold S AB rz RB mu in SE, SG2, GE, SG0, SGF, SHLO1, SHHI1, SHR1, SHR2.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  chg (shad (AB + rz)) SHUB. chg (shad (FA + mfa)) SHF0. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA /\ SHUB = shad AB + shlen rz).
  { subst SHUB SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB rz half cnt nf' cnt'.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 SE RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  (nd_pre SHE 17%nat; intros SHE1 SHE4 SH1 SH2 SH3 SH4 SH5 SH6 SH9 SH10 SH11 SH12 SH13 SH14 SH15 SH16 SHE0; nd_post).
  assert (KF : reckf (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' AB S rz (granules n) (shad AB) SHUB (shad AB + shlen S) SHF0 SHF1).
  { unfold reckf. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL1u TL4u TL2 TL4 CL1 CL1u CL2 CL3 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 RZ1 RZS SHLO1 SE SG2 SG0 GE SGF SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). unfold granules in *.
    unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst AB rz SHUB. cbn [outside] in H13 |- *.
      pose proof (bv_unsigned_in_range 64 sp). clear -H13 H. lia.
    - unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
      apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
      subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  (nd_pre (read_qchunk L st X m c k n b1 ctx l1 l2 ALO WF XB SLOTS0 SSH0) 6%nat; intros _ UJ LH SHA _ SHR; nd_post).
  fold S AB rz in UJ, LH, SHA, SHR. rewrite <- ?SHE0 in SHR.
  assert (HBE : AB + rz + -16 = AB + rz - 16) by (clear; lia).
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      (nd_pre TL 3%nat; intros tw tail' ndR1__; nd_post; revert ndR1__; intros ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ SHUB + granules n <= shad FA /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SGF SHE0 SG0 GE. lia. }
  (nd_pre FAB 7%nat; intros FB1 FB2 FB3 FB4 FB5 FB6 FB7; nd_post).
  assert (SHB : shad RB <= SHUB /\ SHF1 <= shad (RB + 4294967296) /\ 0 <= granules n) by (clear -SH13 SHE0 SG2 SH5 FB2 GE SG0 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  (nd_pre SHB 3%nat; intros SB1 SB2 SB3; nd_post).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr asegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB3 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB2 SHE4 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (HBK : 16 < rz -> 32 <= rz) by (intros H16; clear -RZ2 H16; Z.div_mod_to_equations; lia).
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
        pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16 DJ RZ1 RZS; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; lia].
      + intros b Hb. (nd_pre (busy_of_Some_facts X c k' b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16 RZ1 RZS; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      assert (UJ' : junk_at m' (AB + rz) (S - rz)).
      { eapply junk_frame; [exact UJ | exact MUALL | exact WMALL |]. intros POS.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
      pose proof (junk_of_cells m' _ _ HDR') as JH. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JH. fold AB rz in JH. rewrite ?HBE in JH.
      change (Z.of_nat 16) with 16 in JH.
      destruct (Z.lt_ge_cases 16 rz) as [RZG|RZE].
      + specialize (HBK RZG). destruct (LH RZG) as [_ LJ]. pose proof (junk_of_cells m' _ _ (MAG' RZG)) as JM. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JM. change (Z.of_nat 16) with 16 in JM.
        assert (LJ' : junk_at m' (AB + 16) (rz - 32)).
        { eapply junk_frame; [exact LJ | exact MUALL | exact WMALL |]. intros POS.
          apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
        replace S with (16 + ((rz - 32) + (16 + (S - rz)))) by (clear; lia).
        apply junk_merge; [exact JM | | clear; lia | clear -HBK RZS; lia].
        apply junk_merge; [exact LJ' | | clear -HBK; lia | clear -RZS; lia].
        replace (AB + 16 + (rz - 32)) with (AB + rz - 16) by (clear; lia).
        apply junk_merge; [exact JH | | clear; lia | clear -RZS; lia].
        replace (AB + rz - 16 + 16) with (AB + rz) by (clear; lia). exact UJ'.
      + assert (RZ16 : rz = 16) by (clear -RZE RZ1; lia). rewrite RZ16 in JH, UJ'.
        replace (AB + 16 - 16) with AB in JH by (clear; lia).
        replace S with (16 + (S - 16)) by (clear; lia). apply junk_merge; [exact JH | exact UJ' | clear; lia | clear -RZS RZ16; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
      pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)
                  /\ (shad (aslot_addr L c k') + shlen S <= shad AB \/ shad AB + shlen S <= shad (aslot_addr L c k'))).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 DJ AL' AL16 SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4 SGF SHE0 SG2; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB1 FB2 FB3 FB4 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH10 SH11 SH12 SH13 SH14 SH15 SGF SHE0 SG2 SG0 GE; lia
                                | apply ICW_far; clear -POS FB2 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      assert (SHA' : rw_cells asegs m' (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen rz)))]).
      { eapply cells_frame; [exact SHA | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SG2; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 FB5 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 GE SG0; lia]. }
      assert (SHR' : rw_cells asegs m' (SHUB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { eapply cells_frame; [exact SHR | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SGF GE SG0; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF GE SG0 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 SH12 SH13; lia]. }
      assert (C2pre : rw_cells asegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz))) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (granules n)))]).
      { rewrite Z2Nat.id by (clear -SG2; lia). rewrite <- SHE0. exact SHU'. }
      pose proof (cb_app m' _ _ _ _ _ SHA' C2pre) as C2.
      assert (C3pre : rw_cells asegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { replace (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) with (SHUB + granules n) by (rewrite SHE0; clear -SG2 GE SG0; lia). exact SHR'. }
      pose proof (cb_app m' _ _ _ _ _ C2 C3pre) as C3.
      rewrite <- !repeat_app in C3.
      replace (Z.to_nat (shlen rz) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen rz - granules n))%nat with (Z.to_nat (shlen S)) in C3 by (clear -SG2 GE SG0 SGF; lia).
      exact C3. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 SGF SHE0 SG2; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. (nd_pre (CLS c' Hc') 4%nat; intros RC2 FA2 SL2 SS2; nd_post). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    (nd_pre (PERC c' Hc') 12%nat; intros B1 B2 B3 B4 B5 B6 B7 BLENF BLENC BCNTB BND BRANGE; nd_post).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    (nd_pre REGD 11%nat; intros RD1 RD2 RD3 RD4 RD5 RD6 RD7 RD8 RD9 RD10 RD11; nd_post).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2; lia.
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2 SGF FB3; lia. }
    assert (DJI : disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. (nd_pre (busy_of_Some_facts X c' k0 b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ ((xb_alloc L b + size_of_class (xb_class b) <= RB + mu /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ AB + S <= xb_alloc L b))
          \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - assert (NK : xb_slot b <> k) by (intros EK; exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb EC EK)).
      pose proof (slots_disjoint L c (xb_slot b) k (proj1 KB) (proj1 KR) NK ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. split; [clear -P4 A1; lia| exact DJ].
    - (pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6307840 ->      (* [comment removed for export] *)
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL2 CL3 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  assert (DJtls : forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k ->      (* [comment removed for export] *)
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 TL2; pose proof atp_lin; tlsfar_expose; lia].
    eapply (RK_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 TL2 SP1; pose proof atp_lin; tlsfar_expose; lia. }
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BQuar c k n b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia | apply DJtls; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (AB, AB + S);
              (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. (nd_pre Hx 8%nat; intros O1 O2 O3 O4 O5 O6 O7 _; nd_post).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_drop R pend') 0 0 L st X' m) by (subst X'; eapply AQdr_drop_prim; [exact HQ | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      intros b Hb; (nd_pre (BB b Hb) 3%nat; intros Bb1 Bb2 Bb3; nd_post); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_drop R pend') 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [exact (iff_refl _) | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_drop R pend') cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    (pose proof (ao_nodes L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ ON1 ON3 ONs _; nd_post). (pose proof (ao_store L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OS1 OS3 OSs _; nd_post). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_drop R pend') cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - (nd_pre (CLS' c' Hc' NE) 6%nat; intros Y1 Y2 Y3 Y4 Y5 Y6; nd_post). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    (nd_pre AM 14%nat; intros Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 RC RPA RSC RPSH RTLS; nd_post).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| split; [exact RPSH | exact RTLS]]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      (nd_pre (RC c HC) 4%nat; intros Q1 Q2 Q3 Q4; nd_post). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split. { unfold rec_W. cbv zeta. fold AB rz. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H5 _]. cbn [outside] in H5 |- *. subst SHUB. clear -H5. lia.
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [_ HW]. exact HW. }
  split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BQuar c k n b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.
End Zd1.
#[using="HL"] Lemma rec1_store : ltac:(let t := eval cbv delta [rec1_store__stmt] in rec1_store__stmt in exact t).
Proof. exact rec1_store__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arecyc1__stmt : Prop := forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells asegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 0).
Variable k : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 39).
Variable X : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 40).
Variable R : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 41).
Variable pend' : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 42).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 43).
Variable c : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 44).
Variable kk : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 45).
Variable n : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 46).
Variable CBA : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 47).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 48).
Variable cbs : ltac2:(SecDietF.SzSecF.ty 'arecyc1__stmt 49).
#[using="HL"] Lemma arecyc1__body : ltac:(let T := type of (fun (h : arecyc1__stmt) => h RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R pend' cs c kk n CBA lo cbs) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (k, (Q, (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (X, (R, (pend', (cs, (c, (kk, (n, (CBA, (lo, cbs)))))))))))))))))))))))))))))))))))))))))))))))))) as _.
  intros ALO ARNG AR EP MI ST CEIL LO TP Ha0 Ha1 CBC CB0 CB1 RSTK RCB KONT.
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT0 INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  (nd_pre (pend_head_busy L st X R m c n kk pend' HQ EP) 5%nat; intros b1 ctx l1 l2 XB; nd_post).
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  (nd_pre (RCLS c HC) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  pose proof RT0 as RT1.
  (nd_pre RT1 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  (nd_pre RT2 3%nat; intros DPM MLIM RWCS; nd_post).
  (nd_pre INST 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  (* [comment removed for export] *)
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  (nd_pre (read_qchunk L st X m c kk n b1 ctx l1 l2 ALO WF XB SLOTS SSH) 6%nat; intros HDR UJ MAG SHA SHU SHR; nd_post).
  destruct (slot_rng L st X c kk ALO WF HC KR RNG ARNG) as [RAB RSAB].
  (pose proof (slot_geo L st X c kk ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (* [comment removed for export] *)
  eapply (recyc1_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c kk n b1 ctx CBA lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta cbs (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))));
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ CBA _ => exact CBC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- rw_cells _ _ (aslot_addr _ _ _ + rz_size _ - 16) _ => exact HDR
       | |- 16 < _ -> _ => intros H16; exact (proj1 (MAG H16))
       | |- rw_cells _ _ (shad _) _ => exact SHU
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ CBA _ => exact RCB
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (aslot_addr _ _ _) _ => exact RAB
       | |- rng _ (shad (aslot_addr _ _ _)) _ => exact RSAB
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | rewrite Ha1; unfold qhdr; reflexivity]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; (nd_pre (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) 11%nat; intros _ _ _ _ _ _ _ _ _ CB2 _; nd_post); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- (_ + 1) * _ <= _ =>
           unfold ndist in KR; transitivity (c_allocated_user (get_cls st c) / size_of_class c * size_of_class c);
           [apply Z.mul_le_mono_nonneg_r; [clear -S1; lia| clear -KR; lia]
           | rewrite Z.mul_comm; pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) (size_of_class c) ltac:(clear -S1; lia)); clear -A1 H; lia]
       | |- 1 <= _ => first [assumption | idtac]; destruct (BUSY (bany BQuar c kk n b1 ctx) ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]; cbn in M; clear -M; lia
       | |- rz_size _ + _ <= _ => pose proof (rounded_size_ge n); clear -FIT0 H; lia
       | |- 0 <= _ < _ => first [assumption | clear -CTX0; lia]
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- 0 <= _ => first [assumption | exact (proj1 KR)]
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  (nd_pre (rec1_store L RNG RNG' sp m m' st stX X R pend' cs c kk n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR) 23%nat; intros X' mfa' MU WM MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC MU1 AU1 XS XL; nd_post).
  (nd_pre RR 5%nat; intros m1 _ _ CDR _; nd_post). (nd_pre CDR 17%nat; intros FPLE dr mfa2 sj2 sta2 _ _ _ _ _ _ _ _ _ MIT STT _; nd_post).
  eapply KONT. unfold arecyc1_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|]. split; [exact MU1|]. split; [exact AU1|].
  split; [exact XS| exact XL].
Qed.
End Zd2.
#[using="HL"] Theorem arecyc1 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells asegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom asegs)).
Proof. exact arecyc1__body. Qed.
End P.
End CANSEC1.
End TwB.
End ARecyc1P.

(* [comment removed for export] *)
Module ACdeallocP.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Kinds0.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1 : Z).
Definition reckf0 : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf0.

(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with CA => constr:(t) | RB => constr:(SB) | FA => constr:(SB) | RI => constr:(SB) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.   (* [comment removed for export] *)
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in
      first [ solve [ kkeep2 X Y; klia ] | lia ]
  | |- _ => lia end.
Ltac kind0 := pose proof KF as KF'; unfold reckf0, AIMG_HI in *;
  sg_set; (nd_pre KF' 8%nat; intros F_lo sgk1 F_c F_sb F_tsb F_csb F_mu F_sh; nd_post); (nd_pre sgk1 7%nat; intros Ft1 Ft2 Ft3 Fc1 Fc2 Fc3 Ftc; nd_post);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1|]); first [kind1 | exact I].

#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6303744 -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="lo ctx c RB mu au mfa KF"] Lemma RK0_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
(* [comment removed for export] *)
#[using="lo ctx c RB mu au mfa KF"] Lemma RK0_objL : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx c mu au mfa KF"] Lemma RK0_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
(* [comment removed for export] *)
#[using="rc lo ctx SB c au mfa KF"] Lemma RK0_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c au mfa KF"] Lemma RK0_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx c RB mu au mfa KF"] Lemma RK0_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
End Kinds0.


#[using="Type"] Lemma repeat_app3 : forall {X} (x : X) a b c, repeat x a ++ repeat x b ++ repeat x c = repeat x (a + b + c).
Proof. intros. rewrite !repeat_app. rewrite app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_unbatch : forall R L st X m kb nb b1 ctx l1 l2 drained,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_unbatch R) 0 0 L st (xrec st X K_BATCH_CLASS kb l1 l2 drained) m.
Proof.
  intros R L st X m kb nb b1 ctx l1 l2 drained (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EB EP XB WF.
  unfold AQdr, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_unbatch L st st X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let AHr := AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition acd24_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (cs : list achunk) (lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let c := K_BATCH_CLASS in
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_cd24_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (cs : list achunk) (kb nb b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  let c := K_BATCH_CLASS in
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] -> x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  cdealloc_ret L RNG sp st c (abatch_addr L kb) lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cd24_store__stmt : Prop := store_cd24_stmt.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 1).
Variable RNG' : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 5).
Variable st : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 6).
Variable stX : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 7).
Variable X : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 8).
Variable R : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 9).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 10).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 11).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 12).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 13).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 14).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 15).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 16).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 17).
Variable tail : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 18).
Let c := K_BATCH_CLASS.
Let k := kb.
Let S := size_of_class c.
Let half := max_cached c / 2.
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
Let cnt := c_count (get_cls st c).
Let nd := ndist st c.
Let AB := aslot_addr L c k.
Let RB := aregion L c.
Let FA := afreearr L c.
Let RI := aregion_info L c.
Let CA := acache_addr L c.
Let SHF0 := shad (FA + mfa).
#[using="HL c k S half mu au nf mfa cnt nd AB RB FA RI CA SHF0"] Lemma cd24_store__body : ltac:(let T := type of (fun (h : cd24_store__stmt) => h L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (RNG', (sp, (m, (m', (st, (stX, (X, (R, (cs, (kb, (nb, (b1, (ctx, (lo, (l1, (l2, tail))))))))))))))))))) as _.
  unfold store_cd24_stmt. intros ALO ARNG AR EB EP XB CEIL LO CH LCH CDR.
  chg (K_BATCH_CLASS) c. chg (kb) k.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (any_range L st X BBatch c k nb b1 ctx l1 l2 XB WF) as [HC KR].
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.max_cached_range c) as ndP__; nd_pre ndP__ 3%nat; intros MCR MCH MCE; nd_post).
  (* [comment removed for export] *)
  (nd_pre CDR 29%nat; intros FPLE drained mfa' sj' sta' DR GCX STE MFD NEWB NEWM NEWMOD MU2 WM2 MI' ST' RECS' RECc' CH' MTX' REG' J72' STATS' LSJ' STA' DRA FJ' AZF' MC'; nd_post).
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  chg (size_of_class c) S. chg (max_cached c / 2) half.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa. chg (c_count (get_cls st c)) cnt.
  chg (ndist st c) nd.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  chg (aslot_addr L c k) AB.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 4%nat; intros RIE RBE FAE CAE; nd_post).
  chg (aregion L c) RB. chg (afreearr L c) FA. chg (aregion_info L c) RI. chg (acache_addr L c) CA.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  (nd_pre CNT16 5%nat; intros CNT16 CNTle CNT1 LENCc NFle; nd_post).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  (pose proof (init_cache_fields st) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. (nd_pre (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) 11%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 _; nd_post).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  (nd_pre EF 10%nat; intros EF1 EF2 EF3 EF4 EF5 EF6 EF7 EF8 EF9 EF10; nd_post).
  (* [comment removed for export] *)
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros _ _ AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  chg (shad (FA + mfa)) SHF0. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA).
  { subst SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB half cnt nf' cnt' c k.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  (nd_pre SHE 16%nat; intros SHE1 SHE4 SH1 SH2 SH3 SH4 SH5 SH6 SH9 SH10 SH11 SH12 SH13 SH14 SH15 SH16; nd_post).
  assert (KF : reckf0 (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1).
  { unfold reckf0. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)).
    clear -H H0 CEIL LO SPR TL1 TL1u TL4u TL2 CL1 CL1u CL3 CL2 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    unfold c, K_BATCH_CLASS in *. unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_weaken; [| exact MU2].
    unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
    apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
    subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof WM2 as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  unfold abatch_addr in CH'. fold c AB in CH'. rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      (nd_pre TL 3%nat; intros tw tail' ndR1__; nd_post; revert ndR1__; intros ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6. lia. }
  (nd_pre FAB 6%nat; intros FB1 FB2 FB4 FB5 FB6 FB7; nd_post).
  assert (SB2 : SHF1 <= shad (RB + 4294967296)) by (clear -SH5 FB2 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr asegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK0_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB1 FB2 SHE4 SH3 SH4 TL1u; lia]. }   (* [comment removed for export] *)
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
        apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
      + intros b Hb. (nd_pre (busy_of_Some_facts X c k' b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      specialize (SL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SL.
      unfold aslot_busy in SL. cbn [xb_st xb_class xb_slot bany xb_alloc] in SL. fold S AB in SL.
      eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros POS.
      apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1; lia | apply ICW_far; clear -G1 G2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 AL' SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15; lia
                                | apply ICW_far; clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1u; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      specialize (SSL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SSL.
      cbn [slot_shadow_bytes xb_n xb_st bany] in SSL. fold S AB in SSL. rewrite <- !repeat_app in SSL.
      destruct (proj1 (proj1 SSL)) as [LWF _]. cbn [cell_wf] in LWF. rewrite repeat_length in LWF. rewrite LWF in SSL.
      eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact FB5.
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SH12 SH13 FB2 SH1 SH2 SH3 SH4 FB5; lia
                    | apply ICW_far; clear -SH12 SH13 FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. (nd_pre (CLS c' Hc') 4%nat; intros RC2 FA2 SL2 SS2; nd_post). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    (nd_pre (PERC c' Hc') 12%nat; intros B1 B2 B3 B4 B5 B6 B7 BLENF BLENC BCNTB BND BRANGE; nd_post).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    (nd_pre REGD 11%nat; intros RD1 RD2 RD3 RD4 RD5 RD6 RD7 RD8 RD9 RD10 RD11; nd_post).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK0_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia.
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia. }
    assert (DJI : disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. (nd_pre (busy_of_Some_facts X c' k0 b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK0_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. split; [clear -P4 A1 A2 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. left. clear -P4 A1; lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6303744 ->      (* [comment removed for export] *)
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK0_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK0_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK0_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL3 CL2 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  assert (DJtls : forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k ->      (* [comment removed for export] *)
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 TL2; pose proof atp_lin; tlsfar_expose; lia].
    eapply (RK0_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 TL2 SP1; pose proof atp_lin; tlsfar_expose; lia. }
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BBatch c k nb b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia | apply DJtls; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128);
              (FA + 4 * nf, FA + 536870912); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. (nd_pre Hx 6%nat; intros O1 O2 O3 O4 O5 _; nd_post).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SH5 FB2 NEWB CAE HC SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). unfold c, K_BATCH_CLASS in *. repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_unbatch R) 0 0 L st X' m) by (subst X'; eapply AQdr_unbatch; [exact HQ | exact EB | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      intros b Hb; (nd_pre (BB b Hb) 3%nat; intros Bb1 Bb2 Bb3; nd_post); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_unbatch R) 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [exact (iff_refl _) | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_unbatch R) cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    (pose proof (ao_nodes L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ ON1 ON3 ONs _; nd_post). (pose proof (ao_store L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OS1 OS3 OSs _; nd_post). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; unfold c, K_BATCH_CLASS in *; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_unbatch R) cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - (nd_pre (CLS' c' Hc' NE) 6%nat; intros Y1 Y2 Y3 Y4 Y5 Y6; nd_post). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    (nd_pre AM 14%nat; intros Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 RC RPA RSC RPSH RTLS; nd_post).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| split; [exact RPSH | exact RTLS]]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      (nd_pre (RC c HC) 4%nat; intros Q1 Q2 Q3 Q4; nd_post). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split; [exact MU2|]. split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BBatch c k nb b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.
End Zd1.
#[using="HL"] Lemma cd24_store : ltac:(let t := eval cbv delta [cd24_store__stmt] in cd24_store__stmt in exact t).
Proof. exact cd24_store__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pendb_busy : forall L st X R m kb,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] ->
  exists nb b1 ctx l1 l2, x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2.
Proof.
  intros L st X R m kb (_ & _ & _ & _ & _ & _ & CP & _) EB.
  (nd_pre (qcoupled_rec_bslot_busy L st X R kb CP ltac:(unfold qr_bslots; rewrite EB; apply in_app_iff; right; left; reflexivity)) 5%nat; intros b Hb Sb Cb Kb; nd_post).
  (nd_pre (in_split _ _ Hb) 3%nat; intros l1 l2 E; nd_post). destruct b as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
  exists bn, bb1, bctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition acdealloc24__stmt : Prop := forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 0).
Variable k : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 39).
Variable X : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 40).
Variable R : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 41).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 42).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 44).
Let c := K_BATCH_CLASS.
#[using="HL c"] Lemma acdealloc24__body : ltac:(let T := type of (fun (h : acdealloc24__stmt) => h RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R cs kb lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (k, (Q, (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (X, (R, (cs, (kb, lo))))))))))))))))))))))))))))))))))))))))))))) as _.
  intros ALO ARNG AR EB EP MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 RSTK KONT.
  chg (K_BATCH_CLASS) c.
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT0 INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr] in HQ, HS, HD.
  (nd_pre (pendb_busy L st X R m kb HQ EB) 6%nat; intros nb b1 ctx l1 l2 XB; nd_post). fold c in XB.
  destruct (any_range L st X BBatch c kb nb b1 ctx l1 l2 XB WF) as [HC KR].
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  (nd_pre (RCLS c HC) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  pose proof RT0 as RT1.
  (nd_pre RT1 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  (nd_pre RT2 3%nat; intros DPM MLIM RWCS; nd_post).
  (nd_pre INST 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  (pose proof (slot_geo L st X c kb ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (* [comment removed for export] *)
  eapply (cdealloc_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c (abatch_addr L kb) lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta);
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; (nd_pre (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) 11%nat; intros _ _ _ _ _ _ _ _ _ CB2 _; nd_post); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- aregion _ _ <= abatch_addr _ _ => exact G1
       | |- abatch_addr _ _ < aregion _ _ + _ => unfold ndist in KR; unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; unfold abatch_addr; fold c; clear -G1 G2 G3 G4 S1; lia
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CDR.
  (nd_pre (cd24_store L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR) 21%nat; intros X' mfa' MU WM MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC XS XL; nd_post).
  (nd_pre CDR 17%nat; intros FPLE dr mfa2 sj2 sta2 _ _ _ _ _ _ _ _ _ MIT STT _; nd_post).
  eapply KONT. unfold acd24_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|].
  split; [exact XS| exact XL].
Qed.
End Zd2.
#[using="HL"] Theorem acdealloc24 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof. exact acdealloc24__body. Qed.
End P.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Kinds0.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1 : Z).
Definition reckf0 : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf0.

(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with CA => constr:(t) | RB => constr:(SB) | FA => constr:(SB) | RI => constr:(SB) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.   (* [comment removed for export] *)
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in
      first [ solve [ kkeep2 X Y; klia ] | lia ]
  | |- _ => lia end.
Ltac kind0 := pose proof KF as KF'; unfold reckf0, AIMG_HI in *;
  sg_set; (nd_pre KF' 8%nat; intros F_lo sgk1 F_c F_sb F_tsb F_csb F_mu F_sh; nd_post); (nd_pre sgk1 7%nat; intros Ft1 Ft2 Ft3 Fc1 Fc2 Fc3 Ftc; nd_post);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1|]); first [kind1 | exact I].

#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6307840 -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="lo ctx c RB mu au mfa KF"] Lemma RK0_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
(* [comment removed for export] *)
#[using="lo ctx c RB mu au mfa KF"] Lemma RK0_objL : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx c mu au mfa KF"] Lemma RK0_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
(* [comment removed for export] *)
#[using="rc lo ctx SB c au mfa KF"] Lemma RK0_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c au mfa KF"] Lemma RK0_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx c RB mu au mfa KF"] Lemma RK0_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
#[using="rc lo ctx SB c RB mu au mfa KF"] Lemma RK0_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
End Kinds0.


#[using="Type"] Lemma repeat_app3 : forall {X} (x : X) a b c, repeat x a ++ repeat x b ++ repeat x c = repeat x (a + b + c).
Proof. intros. rewrite !repeat_app. rewrite app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_unbatch : forall R L st X m kb nb b1 ctx l1 l2 drained,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_unbatch R) 0 0 L st (xrec st X K_BATCH_CLASS kb l1 l2 drained) m.
Proof.
  intros R L st X m kb nb b1 ctx l1 l2 drained (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EB EP XB WF.
  unfold AQdr, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_unbatch L st st X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let AHr := AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition acd24_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (cs : list achunk) (lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let c := K_BATCH_CLASS in
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_cd24_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (cs : list achunk) (kb nb b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  let c := K_BATCH_CLASS in
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] -> x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  cdealloc_ret L RNG sp st c (abatch_addr L kb) lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cd24_store__stmt : Prop := store_cd24_stmt.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 1).
Variable RNG' : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 5).
Variable st : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 6).
Variable stX : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 7).
Variable X : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 8).
Variable R : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 9).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 10).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 11).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 12).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 13).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 14).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 15).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 16).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 17).
Variable tail : ltac2:(SecDietF.SzSecF.ty 'cd24_store__stmt 18).
Let c := K_BATCH_CLASS.
Let k := kb.
Let S := size_of_class c.
Let half := max_cached c / 2.
Let mu := c_mapped_user (get_cls st c).
Let au := c_allocated_user (get_cls st c).
Let nf := c_num_freed (get_cls st c).
Let mfa := c_mapped_free_array (get_cls st c).
Let cnt := c_count (get_cls st c).
Let nd := ndist st c.
Let AB := aslot_addr L c k.
Let RB := aregion L c.
Let FA := afreearr L c.
Let RI := aregion_info L c.
Let CA := acache_addr L c.
Let SHF0 := shad (FA + mfa).
#[using="HL c k S half mu au nf mfa cnt nd AB RB FA RI CA SHF0"] Lemma cd24_store__body : ltac:(let T := type of (fun (h : cd24_store__stmt) => h L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (RNG', (sp, (m, (m', (st, (stX, (X, (R, (cs, (kb, (nb, (b1, (ctx, (lo, (l1, (l2, tail))))))))))))))))))) as _.
  unfold store_cd24_stmt. intros ALO ARNG AR EB EP XB CEIL LO CH LCH CDR.
  chg (K_BATCH_CLASS) c. chg (kb) k.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  destruct (any_range L st X BBatch c k nb b1 ctx l1 l2 XB WF) as [HC KR].
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB.max_cached_range c) as ndP__; nd_pre ndP__ 3%nat; intros MCR MCH MCE; nd_post).
  (* [comment removed for export] *)
  (nd_pre CDR 29%nat; intros FPLE drained mfa' sj' sta' DR GCX STE MFD NEWB NEWM NEWMOD MU2 WM2 MI' ST' RECS' RECc' CH' MTX' REG' J72' STATS' LSJ' STA' DRA FJ' AZF' MC'; nd_post).
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  chg (size_of_class c) S. chg (max_cached c / 2) half.
  chg (c_mapped_user (get_cls st c)) mu. chg (c_allocated_user (get_cls st c)) au.
  chg (c_num_freed (get_cls st c)) nf. chg (c_mapped_free_array (get_cls st c)) mfa. chg (c_count (get_cls st c)) cnt.
  chg (ndist st c) nd.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  chg (aslot_addr L c k) AB.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  (nd_pre GEO 4%nat; intros RIE RBE FAE CAE; nd_post).
  chg (aregion L c) RB. chg (afreearr L c) FA. chg (aregion_info L c) RI. chg (acache_addr L c) CA.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  (nd_pre CNT16 5%nat; intros CNT16 CNTle CNT1 LENCc NFle; nd_post).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  (pose proof (init_cache_fields st) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. (nd_pre (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) 11%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 _; nd_post).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  (nd_pre EF 10%nat; intros EF1 EF2 EF3 EF4 EF5 EF6 EF7 EF8 EF9 EF10; nd_post).
  (* [comment removed for export] *)
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros _ _ AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  chg (shad (FA + mfa)) SHF0. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA).
  { subst SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB half cnt nf' cnt' c k.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  (nd_pre SHE 16%nat; intros SHE1 SHE4 SH1 SH2 SH3 SH4 SH5 SH6 SH9 SH10 SH11 SH12 SH13 SH14 SH15 SH16; nd_post).
  assert (KF : reckf0 (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1).
  { unfold reckf0. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)).
    clear -H H0 CEIL LO SPR TL1 TL1u TL4u TL2 CL1 CL1u CL3 CL2 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    unfold c, K_BATCH_CLASS in *. unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_weaken; [| exact MU2].
    unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
    apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
    subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof WM2 as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  unfold abatch_addr in CH'. fold c AB in CH'. rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      (nd_pre TL 3%nat; intros tw tail' ndR1__; nd_post; revert ndR1__; intros ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6. lia. }
  (nd_pre FAB 6%nat; intros FB1 FB2 FB4 FB5 FB6 FB7; nd_post).
  assert (SB2 : SHF1 <= shad (RB + 4294967296)) by (clear -SH5 FB2 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr asegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK0_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      (nd_pre (RC eq_refl) 3%nat; intros RC1 RC2 RC3; nd_post). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB1 FB2 SHE4 SH3 SH4 TL1u; lia]. }   (* [comment removed for export] *)
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
        apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
      + intros b Hb. (nd_pre (busy_of_Some_facts X c k' b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      specialize (SL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SL.
      unfold aslot_busy in SL. cbn [xb_st xb_class xb_slot bany xb_alloc] in SL. fold S AB in SL.
      eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros POS.
      apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1; lia | apply ICW_far; clear -G1 G2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      (nd_pre (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') 3%nat; intros Q1 Q2 Q3; nd_post). fold RB S au in Q1, Q2, Q3.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 AL' SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15; lia
                                | apply ICW_far; clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1u; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      specialize (SSL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SSL.
      cbn [slot_shadow_bytes xb_n xb_st bany] in SSL. fold S AB in SSL. rewrite <- !repeat_app in SSL.
      destruct (proj1 (proj1 SSL)) as [LWF _]. cbn [cell_wf] in LWF. rewrite repeat_length in LWF. rewrite LWF in SSL.
      eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact FB5.
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SH12 SH13 FB2 SH1 SH2 SH3 SH4 FB5; lia
                    | apply ICW_far; clear -SH12 SH13 FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. (nd_pre (CLS c' Hc') 4%nat; intros RC2 FA2 SL2 SS2; nd_post). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    (nd_pre (PERC c' Hc') 12%nat; intros B1 B2 B3 B4 B5 B6 B7 BLENF BLENC BCNTB BND BRANGE; nd_post).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    (nd_pre REGD 11%nat; intros RD1 RD2 RD3 RD4 RD5 RD6 RD7 RD8 RD9 RD10 RD11; nd_post).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK0_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia.
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia. }
    assert (DJI : disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. (nd_pre (busy_of_Some_facts X c' k0 b Hb) 3%nat; intros BIn BC BK; nd_post). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        (nd_pre (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) 3%nat; intros Q1 Q2 Q3; nd_post).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK0_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. split; [clear -P4 A1 A2 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. left. clear -P4 A1; lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6307840 ->      (* [comment removed for export] *)
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK0_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK0_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK0_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL3 CL2 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  assert (DJtls : forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k ->      (* [comment removed for export] *)
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 TL2; pose proof atp_lin; tlsfar_expose; lia].
    eapply (RK0_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 TL2 SP1; pose proof atp_lin; tlsfar_expose; lia. }
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BBatch c k nb b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia | apply DJtls; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128);
              (FA + 4 * nf, FA + 536870912); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. (nd_pre Hx 6%nat; intros O1 O2 O3 O4 O5 _; nd_post).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SH5 FB2 NEWB CAE HC SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). unfold c, K_BATCH_CLASS in *. repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_unbatch R) 0 0 L st X' m) by (subst X'; eapply AQdr_unbatch; [exact HQ | exact EB | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      intros b Hb; (nd_pre (BB b Hb) 3%nat; intros Bb1 Bb2 Bb3; nd_post); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_unbatch R) 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [exact (iff_refl _) | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_unbatch R) cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    (pose proof (ao_nodes L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ ON1 ON3 ONs _; nd_post). (pose proof (ao_store L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OS1 OS3 OSs _; nd_post). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; unfold c, K_BATCH_CLASS in *; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_unbatch R) cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - (nd_pre (CLS' c' Hc' NE) 6%nat; intros Y1 Y2 Y3 Y4 Y5 Y6; nd_post). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    (nd_pre AM 14%nat; intros Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 RC RPA RSC RPSH RTLS; nd_post).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| split; [exact RPSH | exact RTLS]]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      (nd_pre (RC c HC) 4%nat; intros Q1 Q2 Q3 Q4; nd_post). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split; [exact MU2|]. split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BBatch c k nb b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.
End Zd1.
#[using="HL"] Lemma cd24_store : ltac:(let t := eval cbv delta [cd24_store__stmt] in cd24_store__stmt in exact t).
Proof. exact cd24_store__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pendb_busy : forall L st X R m kb,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] ->
  exists nb b1 ctx l1 l2, x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2.
Proof.
  intros L st X R m kb (_ & _ & _ & _ & _ & _ & CP & _) EB.
  (nd_pre (qcoupled_rec_bslot_busy L st X R kb CP ltac:(unfold qr_bslots; rewrite EB; apply in_app_iff; right; left; reflexivity)) 5%nat; intros b Hb Sb Cb Kb; nd_post).
  (nd_pre (in_split _ _ Hb) 3%nat; intros l1 l2 E; nd_post). destruct b as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
  exists bn, bb1, bctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition acdealloc24__stmt : Prop := forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 0).
Variable k : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 39).
Variable X : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 40).
Variable R : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 41).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 42).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'acdealloc24__stmt 44).
Let c := K_BATCH_CLASS.
#[using="HL c"] Lemma acdealloc24__body : ltac:(let T := type of (fun (h : acdealloc24__stmt) => h RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R cs kb lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (k, (Q, (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (X, (R, (cs, (kb, lo))))))))))))))))))))))))))))))))))))))))))))) as _.
  intros ALO ARNG AR EB EP MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 RSTK KONT.
  chg (K_BATCH_CLASS) c.
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT0 INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr] in HQ, HS, HD.
  (nd_pre (pendb_busy L st X R m kb HQ EB) 6%nat; intros nb b1 ctx l1 l2 XB; nd_post). fold c in XB.
  destruct (any_range L st X BBatch c kb nb b1 ctx l1 l2 XB WF) as [HC KR].
  (nd_pre THR 6%nat; intros T0c T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (nd_pre (CLS c HC) 4%nat; intros RCELLS FARR SLOTS SSH; nd_post). destruct (AVL c HC) as [AZU AZF].
  (nd_pre RCELLS 5%nat; intros MTX16 REG RJ4 EXH RJ56; nd_post). (nd_pre FARR 3%nat; intros FL FJ FSJ; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  (nd_pre (RCLS c HC) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  pose proof RT0 as RT1.
  (nd_pre RT1 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  (nd_pre RT2 3%nat; intros DPM MLIM RWCS; nd_post).
  (nd_pre INST 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  (pose proof (slot_geo L st X c kb ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S1 S2 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (* [comment removed for export] *)
  eapply (cdealloc_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c (abatch_addr L kb) lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta);
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; (nd_pre (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) 11%nat; intros _ _ _ _ _ _ _ _ _ CB2 _; nd_post); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- aregion _ _ <= abatch_addr _ _ => exact G1
       | |- abatch_addr _ _ < aregion _ _ + _ => unfold ndist in KR; unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; unfold abatch_addr; fold c; clear -G1 G2 G3 G4 S1; lia
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CDR.
  (nd_pre (cd24_store L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR) 21%nat; intros X' mfa' MU WM MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC XS XL; nd_post).
  (nd_pre CDR 17%nat; intros FPLE dr mfa2 sj2 sta2 _ _ _ _ _ _ _ _ _ MIT STT _; nd_post).
  eapply KONT. unfold acd24_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|].
  split; [exact XS| exact XL].
Qed.
End Zd2.
#[using="HL"] Theorem acdealloc24 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof. exact acdealloc24__body. Qed.
End P.
End CANSEC1.
End TwB.
End ACdeallocP.

(* [comment removed for export] *)
Module ARecGeo.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma outside_of_In : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn; [exact I|]. split; [exact (H (lo, hi) (or_introl eq_refl))|].
  apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Geo.
Variables (L : alayout) (st : astate) (X : aconc).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.

(* [comment removed for export] *)
#[using="tlsI ALO WF"] Lemma busy_slot_geo : forall b, In b (x_busy X) ->
     1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b)
  /\ aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
  /\ (al_space_beg L <= aregion L (xb_class b) /\ c_allocated_user (get_cls st (xb_class b)) <= c_mapped_user (get_cls st (xb_class b)) <= K_FREEARR_OFF
      /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE)
  /\ 0x10007fff8000 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= ATOP
  /\ al_res L + 4096 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104.
Proof.
  intros b Hb. (pose proof WF as ndP__; nd_pre ndP__ 9%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY _; nd_post).
  destruct (BUSY b Hb) as [CLB _]. (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  (pose proof (slot_geo L st X (xb_class b) (xb_slot b) ALO WF CLB KB) as ndP__; nd_pre ndP__ 12%nat; intros S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 _; nd_post).
  pose proof (ao_space L ALO) as RSP.
  assert (RS : al_space_beg L <= aregion L (xb_class b) /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize CLB. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  unfold xb_alloc. split; [exact CLB|]. split; [exact KB|]. split; [exact G1|]. split; [exact G2|]. split; [split; [exact (proj1 RS)| split; [clear -G3 G4; lia| exact (proj2 RS)]]|].
  split; [exact G7|]. split; [exact G8|]. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *. split; lia.
Qed.
End Geo.

#[using="Type"] Lemma in_ic_W : forall L i d iv, In iv (ic_W L i d) -> exists j, i <= j /\ j < i + Z.of_nat d /\ iv = (acache_addr L j + 4, acache_addr L j + 16).
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i iv Hin; cbn [ic_W] in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists i; split; [lia| split; [lia| reflexivity]]|].
  (nd_pre (IH (i + 1) iv Hin) 4%nat; intros j A B E; nd_post). exists j. split; [lia| split; [lia| exact E]].
Qed.

(* [comment removed for export] *)
Definition lowpiece (L : alayout) (c : Z) (iv : Z * Z) : Prop :=
  0 <= fst iv /\ snd iv <= ATOP /\ ((shad (al_space_beg L) <= fst iv /\ snd iv <= shad (al_space_beg L + K_SPACE_SIZE) /\ snd iv <= 0x10007fff8000)
                                    \/ al_t L <= fst iv /\ snd iv <= al_t L + 4096
                     \/ aregion L c + K_FREEARR_OFF <= fst iv /\ snd iv <= aregion L c + K_REGION
                     \/ al_space_beg L + K_SPACE_SIZE <= fst iv /\ snd iv <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA).

#[using="Type"] Lemma cd_W_cases : forall L sp c nf mfa mfa' iv,
  alayout_ok L -> 1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  In iv (cd_W L sp c nf mfa mfa') -> iv = (sp - 688, sp) \/ lowpiece L c iv.
Proof.
  intros L sp c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hin. unfold lowpiece.
  pose proof (alayout_t_lin L ALO) as (TL1 & TL2). (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 _; nd_post).   (* [comment removed for export] *)
  assert (FAS : shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000 /\ 0x10007fff8000 <= afreearr L c /\ afreearr L c + mfa' <= aregion L c + K_REGION
                /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                /\ shad (al_space_beg L) <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= shad (al_space_beg L + K_SPACE_SIZE)).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE, K_SPACE_EXTRA, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
    rewrite !shad_div, shlen_div. unfold ASHOFF. clear -HC SP1 SP2 NF0 NF4 MFA. Z.div_mod_to_equations. lia. }
  (nd_pre FAS 6%nat; intros FA1 FA2 FA3 FA4 FA5 FA6; nd_post).
  unfold cd_W in Hin. cbv zeta in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (CAB : forall j, 1 <= j -> j <= 32 -> al_t L <= acache_addr L j /\ acache_addr L j + 80 <= al_t L + 4096) by (intros j A B; unfold acache_addr; clear -A B; lia).
  assert (RIB : al_space_beg L + 137438953472 <= aregion_info L c /\ aregion_info L c + 128 <= al_space_beg L + 137438953472 + 4096).
  { unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. unfold K_NUM_CLASSES in HC. clear -HC. lia. }
  destruct Hin as [[E|F] | [Hic | H9]]; try (destruct F); try subst iv; cbn [fst snd].
  - left. reflexivity.
  - right. apply in_ic_W in Hic. (nd_pre Hic 4%nat; intros j J1 J2 ndR1__; nd_post; revert ndR1__; intros ->). cbn [fst snd]. destruct (CAB j ltac:(clear -J1; lia) ltac:(clear -J2; cbn in J2; lia)) as [C1 C2].
    split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
  - destruct H9 as [E|[E|[E|[E|[E|[E|[E|[E|[E|F]]]]]]]]]; try (destruct F); subst iv; cbn [fst snd]; right.
    + destruct (CAB c ltac:(clear -HC; lia) ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [C1 C2]. split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
    + destruct (CAB c ltac:(clear -HC; lia) ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [C1 C2]. split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
    + split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
    + split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
    + split; [unfold afreearr, K_FREEARR_OFF in *; clear -NF0 FA2; lia|]. split; [clear -FA3 FA4 SP2; lia| right; right; left; unfold afreearr, K_FREEARR_OFF in *; clear -NF0 FA3; lia].
    + split; [rewrite shad_div; unfold ASHOFF; clear -FA2 NF0 NF4; Z.div_mod_to_equations; lia|]. split; [clear -FA1; lia| left; clear -FA1 FA5 FA6; unfold K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; repeat split; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rec_W_cases : forall L st X sp c kk n b1 ctx l1 l2 nf mfa mfa' iv,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  In iv (rec_W L sp c kk n nf mfa mfa') ->
  let AB := aslot_addr L c kk in let S := size_of_class c in
  iv = (sp - 688, sp) \/ (AB <= fst iv /\ snd iv <= AB + S) \/ lowpiece L c iv.
Proof.
  intros L st X sp c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hin. cbv zeta.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 3%nat; intros N0 FIT0 _; nd_post).
  (pose proof (chunk_geo L st X c kk n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros _ _ G3 G4 _ G6 G7 _; nd_post).
  (pose proof (chunk_shadow_geo L st X c kk n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros SE _ GE SG0 SGF SHLO SHHI _; nd_post).
  pose proof (alayout_t_lin L ALO) as (TL1 & TL2). pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].   (* [comment removed for export] *)
  unfold rec_W in Hin. cbv zeta in Hin. apply in_app_iff in Hin.
  destruct Hin as [Hin|Hin]; [| destruct (cd_W_cases L sp c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hin) as [E|P]; [left; exact E| right; right; exact P]].
  unfold lowpiece in *. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|F]]]]]; try (destruct F); subst iv; cbn [fst snd].
  - left. reflexivity.
  - right. left. clear -RZ1 G6 N0; unfold rup in *; split; lia.
  - right. left. clear -RZ1 G3 G6 N0; unfold rup in *; split; lia.
  - (pose proof (slot_geo L st X c kk ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ Q5 Q6 _; nd_post).
    assert (SB : shad (al_space_beg L) <= shad (aslot_addr L c kk) /\ shad (aslot_addr L c kk) + shlen (size_of_class c) <= shad (al_space_beg L + K_SPACE_SIZE)).
    { rewrite !shad_div, shlen_div. clear -Q5 Q6. Z.div_mod_to_equations. lia. }
    right. right. split; [clear -SE SHLO SG0 GE RZ1; pose proof (shlen_nonneg (rz_size n) ltac:(lia)); lia|].
    split; [clear -SE SGF SHHI SG0 GE TL1 TL2; lia| left; clear -SE SGF SHHI SG0 GE SB RZ1; pose proof (shlen_nonneg (rz_size n) ltac:(lia)); repeat split; lia].
  - right. right. split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lowpiece_vs_slot : forall L st X c b iv, alayout_ok L -> awf L st X -> 1 <= c < K_NUM_CLASSES -> In b (x_busy X) ->
  lowpiece L c iv -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b.
Proof.
  intros L st X c b iv ALO WF HC Hb (Pz & P0 & P).
  (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros CLB KB G1 G2 (G3a & G3 & G3b) G4 G5 G6 G7; nd_post).
  pose proof (ad_t_res L ALO) as DTR. pose proof (ao_space L ALO) as RSP. unfold adisj in DTR.
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  destruct P as [(_ & _ & P)|[P|[P|P]]].
  - right. clear -P G4. lia.
  - clear -P DTR RSP G6 G7. lia.
  - destruct (Z.eq_dec (xb_class b) c) as [<-|NC].
    + left. clear -P G2 G3. lia.
    + (pose proof (region_other_geo L c (xb_class b) ALO ltac:(unfold K_NUM_CLASSES in HC; exact HC) ltac:(unfold K_NUM_CLASSES in CLB; exact CLB) NC) as ndP__; nd_pre ndP__ 3%nat; intros _ RD _; nd_post).
      clear -P G1 G2 G3 RD. lia.
  - left. clear -P G2 G3 G3b. lia.
Qed.

(* [comment removed for export] *)
Definition wpiece (L : alayout) (lo SP : Z) (iv : Z * Z) : Prop :=
     (lo <= fst iv /\ snd iv <= SP)
  \/ (shad (al_space_beg L) <= fst iv /\ snd iv <= shad (al_space_beg L + K_SPACE_SIZE) /\ snd iv <= 0x10007fff8000)
  \/ (al_t L <= fst iv /\ snd iv <= al_t L + 4096)
  \/ (al_space_beg L <= fst iv /\ snd iv <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA).

#[using="Type"] Lemma lowpiece_wpiece : forall L lo SP c iv, 1 <= c < K_NUM_CLASSES -> lowpiece L c iv -> wpiece L lo SP iv.
Proof.
  intros L lo SP c iv HC (_ & _ & P). unfold wpiece.
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  destruct P as [P|[P|[P|P]]]; [right; left; exact P| right; right; left; exact P| right; right; right; clear -P RS; lia| right; right; right; clear -P; lia].
Qed.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.

#[using="Type"] Lemma wpiece_fake : forall L lo SP iv, alayout_ok L -> ATOP <= lo -> wpiece L lo SP iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xa7288 \/ 0xa7288 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
  /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
  /\ (snd iv <= 0x1401b1 \/ 0x1401b1 + 1 <= fst iv) /\ (snd iv <= 0x13e098 \/ 0x13e098 + 4 <= fst iv).
Proof.
  intros L lo SP iv ALO CEIL P. unfold wpiece in P.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_space_al L ALO) as SAL.
  pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_t_dtls L ALO) as DTD.
  pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold aobj in OF, OD, OT, ORS. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OD, OT.   (* [comment removed for export] *)
  unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (SHF : shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L) \/ shad (al_space_beg L + 137438953472) <= shad (al_fake L)).
  { rewrite !shad_div, shlen_div. clear -DFR RSP OF SAL. Z.div_mod_to_equations. lia. }
  assert (SHB : 2201439137792 <= shad (al_space_beg L) /\ 2147450880 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF. clear -RSP ORS RHI OF AR. Z.div_mod_to_equations. lia. }
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. unfold adisj in D_l_t, D_l_r. pose proof atp_lin as TLN.      (* [comment removed for export] *)
  (nd_pre SHB 3%nat; intros SB1 SB2 SB3; nd_post).
  destruct P as [P|[P|[P|P]]]; clear -P OF OD OT ORS RHI AR RSP DFR DDR DTF DTD CEIL SHF SB1 SB2 SB3 D_l_t D_l_r TLN; repeat split; fu_focus; lia.
Qed.

#[using="Type"] Lemma fake_untouched_of : forall L W,
  (forall iv, In iv W ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xa7288 \/ 0xa7288 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
  /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
  /\ (snd iv <= 0x1401b1 \/ 0x1401b1 + 1 <= fst iv) /\ (snd iv <= 0x13e098 \/ 0x13e098 + 4 <= fst iv)) ->
  fake_untouched L W.
Proof. intros L W H. unfold fake_untouched. apply Forall_forall. exact H. Qed.

#[using="Type"] Lemma rec_W_wpiece : forall L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa' iv,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> lo <= SP - 688 ->
  In iv (rec_W L SP c kk n nf mfa mfa') -> wpiece L lo SP iv.
Proof.
  intros L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA LO Hin.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hin) as [E|[SL|LP]].
  - left. subst iv. cbn. lia.
  - right. right. right. (pose proof (slot_geo L st X c kk ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ G5 G6 _; nd_post). unfold K_SPACE_EXTRA. clear -SL G5 G6. lia.
  - eapply lowpiece_wpiece; [exact HC| exact LP].
Qed.

#[using="Type"] Lemma rec_W_fake : forall L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa',
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> ATOP <= lo -> lo <= SP - 688 ->
  fake_untouched L (rec_W L SP c kk n nf mfa mfa').
Proof.
  intros. apply fake_untouched_of. intros iv Hiv. eapply wpiece_fake; [eassumption| eassumption|]. eapply rec_W_wpiece; eassumption.
Qed.

#[using="Type"] Lemma cd_W_fake : forall L lo SP c nf mfa mfa',
  alayout_ok L -> 1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> ATOP <= lo -> lo <= SP - 688 ->
  fake_untouched L (cd_W L SP c nf mfa mfa').
Proof.
  intros L lo SP c nf mfa mfa' ALO HC NF0 NF4 MFA CEIL LO. apply fake_untouched_of. intros iv Hiv. eapply (wpiece_fake L lo SP); [exact ALO| exact CEIL|].
  destruct (cd_W_cases L SP c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hiv) as [->|P]; [left; cbn [fst snd]; clear -LO; lia| eapply lowpiece_wpiece; [exact HC| exact P]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srec_W_pieces : forall L st X lo SP mb ms n nres hl iv,
  alayout_ok L -> awf L st X -> sec_wf1 L (CSec mb ms n) -> srec_hl_ok L hl -> 0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 ->
  In iv (srec_W L SP mb ms nres ++ [(hl, hl + 8)]) ->
     ((lo <= fst iv /\ snd iv <= SP)
      \/ (forall b, In b (x_busy X) -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP)
  /\ ((snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
      /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
      /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
      /\ (snd iv <= 0xa7288 \/ 0xa7288 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
      /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
      /\ (snd iv <= 0x1401b1 \/ 0x1401b1 + 1 <= fst iv) /\ (snd iv <= 0x13e098 \/ 0x13e098 + 4 <= fst iv)).
Proof.
  intros L st X lo SP mb ms n nres hl iv ALO WF SW HLOK NR0 NR1 CEIL LO Hin.
  unfold srec_W in Hin. rewrite in_app_iff in Hin. cbn [In] in Hin.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_t_dtls L ALO) as DTD.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_ptr_res L ALO) as DPR. pose proof (ad_fake_ptr L ALO) as DFP. pose proof (ad_dtls_ptr L ALO) as DDP.
  (nd_pre SW 7%nat; intros MB KH MCE _ _ _ SC; nd_post). (nd_pre SC 9%nat; intros SCt SCc SCr SCp SCn SCs SCf SCd SCl; nd_post).
  (nd_pre HLOK 3%nat; intros HK HC8 (HCt & HCc & HCr & HCp & HCn & HCs & HCf & HCd & HCl); nd_post).
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_res L ALO) as D_l_r. pose proof atp_lin as TLN.      (* [comment removed for export] *)
  pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold aobj, sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI, adisj, K_HIGH_MEM, AINSTANCE in *.
  assert (SHB : shad (al_fake L) + shlen 11571200 <= 17594332446720 /\ 0 <= shad mb /\ shad mb + shlen ms <= shad (mb + ms) /\ shad (mb + ms) <= 17594332446720
                /\ (shad (mb + ms) <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb) /\ 2148238848 <= shad mb /\ 2148238848 <= shad (al_fake L)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -OF MCE KH SCf AR. Z.div_mod_to_equations. lia. }
  (nd_pre SHB 7%nat; intros SH1 SH2 SH3 SH4 SH5 SH6 SH7; nd_post).
  assert (BB : forall b, In b (x_busy X) -> al_res L + 4096 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104 /\ 17594333495296 <= xb_alloc L b).
  { intros b Hb. (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ G4 _ G6 G7; nd_post). unfold K_HIGH_MEM in *. clear -G4 G6 G7. lia. }
  destruct Hin as [[E|[E|[E|[E|[E|[E|F]]]]]] | [E|F]]; try (destruct F); subst iv; cbn [fst snd].
  - split; [left; clear -LO; lia|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD CEIL LO SH1 SH7 AR. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 DTR; lia| clear -OT; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD OT DTF DTD SH1 SH7. repeat split; fu_focus; lia.
  - unfold AINSTANCE. split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B3; lia| clear -AR; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD SH1 SH7. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 DPR NR0 NR1; lia| clear -OP NR0 NR1; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD OP DFP DDP SH1 SH7 NR0 NR1. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 SCr; lia| clear -KH MCE; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD KH MCE SCf SCd SH1 SH7. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B3 SH3 SH4; lia| clear -SH2 SH3 SH4 AR; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD SH1 SH2 SH3 SH4 SH5 SH6. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 HCr; lia| clear -HK HC8; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD HK HC8 HCf HCd SH1 SH7. repeat split; fu_focus; lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma srec_W_t48 : forall L (st : astate) (X : aconc) lo SP mb ms n nres hl iv,
  alayout_ok L -> sec_wf1 L (CSec mb ms n) -> srec_hl_ok L hl -> 0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 ->
  In iv (srec_W L SP mb ms nres ++ [(hl, hl + 8)]) -> snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv.
Proof.
  intros L st X lo SP mb ms n nres hl iv ALO SW HLOK NR0 NR1 CEIL LO Hin.
  unfold srec_W in Hin. rewrite in_app_iff in Hin. cbn [In] in Hin.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ptr L ALO) as OP. pose proof (ad_t_ptr L ALO) as DTP. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OT, OP, DTP.   (* [comment removed for export] *)
  (nd_pre SW 7%nat; intros MAL MLO MCE _ _ _ (SCt & _); nd_post). (nd_pre HLOK 3%nat; intros HK HC8 (HCt & _); nd_post). unfold ablk, AIMG_HI, KLS in MLO.
  assert (SHB : 2148238848 <= shad mb /\ shad mb + shlen ms <= 17594332446720) by (pose proof atop_range as AR; rewrite shad_div, shlen_div; unfold ASHOFF in *; clear -MLO MCE AR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM, AINSTANCE in *.
  destruct Hin as [[E|[E|[E|[E|[E|[E|F]]]]]] | [E|F]]; try (destruct F); subst iv; cbn [fst snd];
    first [clear -CEIL LO OT; lia| clear -OT; lia| clear -OT OP DTP NR0 NR1; lia| clear -SCt; lia| clear -SHB OT; lia| clear -HCt; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition astatic (a : Z) : Prop :=
  a < 0x10000 \/ (AINSTANCE <= a < 0xab330) \/ (0x1804c8 <= a < 0x5d0510) \/ (0xaf800 <= a < 0x130830) \/ (0x13e088 <= a < 0x13e08c).

(* [comment removed for export] *)
Definition cprot (L : alayout) (HI : Z) (LB : list ablock) (a : Z) : Prop :=
     atls_addr a                            (* [comment removed for export] *)
  \/ (AAHMv <= a < AAHMv + AAHM_SZ)          (* [comment removed for export] *)
  \/ HI <= a
  \/ (a < AIMG_HI /\ ~ astatic a)
  \/ in_block LB a
  \/ (al_fake L <= a < al_fake L + 11571200)
  \/ (shad ATOP <= a < shad (2^47))
  \/ (ASHOFF <= a < shad AIMG_HI)
  \/ (shad (al_fake L) <= a < shad (al_fake L + 11571200)).

Definition cpres (L : alayout) (HI : Z) (LB : list ablock) (m m' : amem) : Prop :=
  forall x : word, cprot L HI LB (bv_unsigned x) -> m' x = m x.

#[using="Type"] Lemma cpres_refl : forall L HI LB m, cpres L HI LB m m.
Proof. intros L HI LB m x _. reflexivity. Qed.
#[using="Type"] Lemma cpres_trans : forall L HI LB m1 m2 m3, cpres L HI LB m1 m2 -> cpres L HI LB m2 m3 -> cpres L HI LB m1 m3.
Proof. intros L HI LB m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

(* [comment removed for export] *)
Definition np_fp (L : alayout) (HI : Z) (LB : list ablock) (W : list (Z * Z)) : Prop :=
  forall iv, In iv W -> forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a.

#[using="Type"] Lemma cpres_of_munch : forall L HI LB W m m', munch W m m' -> np_fp L HI LB W -> cpres L HI LB m m'.
Proof.
  intros L HI LB W m m' MU NP x Hx. apply MU. apply outside_of_In. intros iv Hiv R. exact (NP iv Hiv _ R Hx).
Qed.
#[using="Type"] Lemma np_fp_app : forall L HI LB W1 W2, np_fp L HI LB W1 -> np_fp L HI LB W2 -> np_fp L HI LB (W1 ++ W2).
Proof. intros L HI LB W1 W2 H1 H2 iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [H|H]; [exact (H1 iv H)| exact (H2 iv H)]. Qed.
#[using="Type"] Lemma np_fp_cons : forall L HI LB iv W, (forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a) -> np_fp L HI LB W -> np_fp L HI LB (iv :: W).
Proof. intros L HI LB iv W H1 H2 iv' [<-|H]; [exact H1| exact (H2 iv' H)]. Qed.
#[using="Type"] Lemma np_fp_nil : forall L HI LB, np_fp L HI LB [].
Proof. intros L HI LB iv []. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shad_consts : (17594064011264 <= shad ATOP <= 17594332446720) /\ shad (2^47) = 17594333495296 /\ shad AIMG_HI = 2148238848 /\ ASHOFF = 2147450880.
Proof. split; [pose proof atop_range as AR; rewrite shad_div; unfold ASHOFF; lia|]. repeat split; reflexivity. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma lb_geo : forall L st X LB blk, alayout_ok L -> awf L st X -> ablocks L st X LB -> In blk LB ->
  match ab_kind blk with
  | ABHeap p =>
         (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_alloc L b <= ab_addr blk /\ ab_addr blk + ab_size blk <= xb_alloc L b + size_of_class (xb_class b))
      \/ (exists mb ms n, (a_live st) !! p = Some (CSec mb ms n) /\ sec_wf1 L (CSec mb ms n) /\ mb + SEC_UOFF <= ab_addr blk /\ ab_addr blk + ab_size blk <= mb + ms)
  | ABFake _ => al_fake L <= ab_addr blk /\ ab_addr blk + ab_size blk <= al_fake L + 11571200
  end.
Proof.
  intros L st X LB [[p|cls] A n] ALO WF (B1 & B2 & _) Hin; cbn [ab_kind ab_addr ab_size].
  - destruct (B1 p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
    + left. exists b. split; [exact Hb|]. split; [exact Sb|].
      pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n.
      clear -FIT. lia.
    + right. exists mb, ms, n. split; [exact Lp|]. split; [exact G|]. subst A.
      (nd_pre G 7%nat; intros MAL MLO MCE MSE NB NPR SCL; nd_post).
      (pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as ndP__; nd_pre ndP__ 9%nat; intros _ RZ _ RS1 _ NS _ MSB _; nd_post). rewrite <- MSE in MSB.
      unfold SEC_UOFF. clear -RS1 NS MSB. lia.
  - exact (conj (proj1 (B2 cls A n Hin)) (proj2 (proj2 (B2 cls A n Hin)))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma lb_high : forall L st X LB blk, alayout_ok L -> awf L st X -> ablocks L st X LB -> In blk LB ->
  ab_addr blk < ab_addr blk + ab_size blk ->
  AIMG_HI <= ab_addr blk /\ ab_addr blk + ab_size blk <= ATOP /\ (ab_addr blk + ab_size blk <= KLS \/ K_HIGH_MEM <= ab_addr blk).
Proof.
  intros L st X LB blk ALO WF BL Hin NE. pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A n]; cbn [ab_kind ab_addr ab_size] in G |- *.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n' & _ & SW & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ Q4 Q5 _; nd_post). unfold K_HIGH_MEM, AIMG_HI, KLS. clear -G1 G2 Q4 Q5. lia.
    + (nd_pre SW 4%nat; intros _ MLO MCE _; nd_post). unfold ablk, K_HIGH_MEM, AIMG_HI, KLS in *. unfold SEC_UOFF in G1. clear -G1 G2 MLO MCE. lia.
  - pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, K_HIGH_MEM, AIMG_LO, AIMG_HI, KLS in *. clear -G OF NE. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_high : forall L st X LB HI A B, alayout_ok L -> awf L st X -> ablocks L st X LB ->
  ATOP <= A -> B <= HI -> forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI A B ALO WF BL HA HB a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). pose proof atop_range as AR.   (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF.
  assert (SF : shad (al_fake L + 11571200) <= shad ATOP) by (apply shad_mono; clear -OF; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a) by (apply (atls_not_app A B a); [right; pose proof atp_below_atop as TB; clear -TB HA; lia | right; clear -AR HA; lia | exact Ha]).
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; clear -CH OAH Ha HA; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha HA HB OF S1 S2 S3 S4 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). (pose proof (lb_high L st X LB blk ALO WF BL Hin ltac:(clear -R; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ G _; nd_post). clear -R G Ha HA. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_low : forall L st X LB HI c iv, alayout_ok L -> awf L st X -> ablocks L st X LB -> 1 <= c < K_NUM_CLASSES -> ATOP <= HI ->
  lowpiece L c iv -> forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI c iv ALO WF BL HC HHI (Pz & P0 & P) a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS, OT.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_res L ALO) as DTR. unfold adisj in DTF, DFR, DTR.
  pose proof (ao_space L ALO) as RSP. (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 3%nat; intros SP1 SP2 _; nd_post).
  assert (RR : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  assert (SHB : shad AIMG_HI <= shad (al_space_beg L) /\ shad (al_space_beg L + K_SPACE_SIZE) <= shad ATOP
                /\ (shad (al_fake L + 11571200) <= shad (al_space_beg L) \/ shad (al_space_beg L + K_SPACE_SIZE) <= shad (al_fake L))).
  { rewrite !shad_div. unfold AIMG_HI, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -OF ORS RSP DFR SP1 SP2. Z.div_mod_to_equations. lia. }
  (nd_pre SHB 3%nat; intros SB1 SB2 SB3; nd_post).
  unfold cprot, astatic, AINSTANCE, AIMG_HI, K_HIGH_MEM, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  assert (NT : ~ atls_addr a).
  { pose proof (ad_tls_res L ALO) as DLR. pose proof (ad_tls_t L ALO) as DLT. unfold adisj in DLR, DLT. pose proof (ao_res_hi L ALO) as RHI0. pose proof (ao_space_al L ALO) as SAL0.
    pose proof atp_lin as TLN. pose proof atop_range as AR0.
    destruct P as [P|[P|[P|P]]].
    - (* [comment removed for export] *)
      intros [T|(a' & Ha' & ->)]; [clear -T P Ha TLN SB1 S3; lia|].
      destruct (tls_shadow_apart a' (al_space_beg L) 137438953472 Ha' ltac:(clear; lia)) as [D|D].
      { destruct DLR as [D|D]; [left; clear -D RSP; lia| right; split; [clear -D RSP; lia| clear -SAL0; Z.div_mod_to_equations; lia]]. }
      + clear -D P Ha. lia.
      + rewrite <- (shad_add_shlen (al_space_beg L) 137438953472) in D by (clear -SAL0; Z.div_mod_to_equations; lia). clear -D P Ha. lia.
    - apply (atls_not_app (fst iv) (snd iv) a); [clear -P DLT; lia | clear -P OT; lia | exact Ha].
    - apply (atls_not_app (fst iv) (snd iv) a); [clear -P DLR RR RSP; lia | right; clear -P RR RSP RHI0; lia | exact Ha].
    - apply (atls_not_app (fst iv) (snd iv) a); [clear -P DLR RSP; lia | right; clear -P RSP RHI0; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; unfold adisj in DA1, DA2; destruct P as [P|[P|[P|P]]]; clear -CH OAH OAHI DA1 DA2 P Ha SB1 S3 RR RSP ORS; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
  - clear -C Ha P0 HHI. lia.
  - destruct P as [P|[P|[P|P]]]; clear -C Ha P S1 S2 S3 S4 SB1 OT RR SP1; lia.
  - (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
    destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n0 & _ & SW & G1 & G2)].
      * pose proof (lowpiece_vs_slot L st X c b iv ALO WF HC Hb (conj Pz (conj P0 P))) as D. clear -D G1 G2 R Ha. lia.
      * (nd_pre SW 7%nat; intros _ MLO MCE _ _ _ (SCt & _ & SCr & _); nd_post). unfold ablk, AIMG_HI, KLS, K_HIGH_MEM, SEC_UOFF in *.
        destruct P as [P|[P|[P|P]]]; clear -P R Ha G1 G2 MLO MCE SCt SCr S2 S3 SB1 SB2 RR RSP ORS; lia.
    + destruct P as [P|[P|[P|P]]]; clear -P R Ha G OF S1 S3 SB1 SB2 DTF DFR RR RSP ORS; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha OF S1 S3 SB1 SB2 DTF DFR RR RSP ORS; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha S1 S2 SB2 OT RR SP1; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha S3 S4 SB1 OT RR SP1 S2; lia.
  - assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720)
      by (pose proof atop_range as AR; rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    destruct P as [P|[P|[P|P]]]; clear -P C Ha SF SB3 OT RR SP1 S2; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_slot : forall L st X LB HI stt c k n b1 ctx l1 l2 A B, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  x_busy X = l1 ++ bany stt c k n b1 ctx :: l2 -> (forall p, stt <> BLive p) ->
  aslot_addr L c k <= A -> B <= aslot_addr L c k + size_of_class c ->
  forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI stt c k n b1 ctx l1 l2 A B ALO WF BL HHI XB NL HA HB a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  assert (IN0 : In (bany stt c k n b1 ctx) (x_busy X)) by (rewrite XB; apply in_app_iff; right; left; reflexivity).
  (pose proof (busy_slot_geo L st X ALO WF _ IN0) as ndP__; nd_pre ndP__ 9%nat; intros HC KR G1 G2 (G3a & G3 & G3b) G4 G5 G6 G7; nd_post).
  unfold xb_alloc in *. cbn [xb_class xb_slot bany] in *.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS. pose proof (ad_fake_res L ALO) as DFR. unfold adisj in DFR.   (* [comment removed for export] *)
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLR. pose proof (ao_res_hi L ALO) as RHI0.
    apply (atls_not_app A B a); [clear -DLR HA HB G6 G7; lia | right; clear -HA G6 RHI0; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; pose proof (ad_ahm_res L ALO) as DA2; unfold adisj in DA2; clear -CH OAH DA2 Ha HA HB G6 G7; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
  - clear -C Ha HB G5 HHI. lia.
  - clear -C Ha HA G4. lia.
  - (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
    destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(b & Hb & Sb & Q1 & Q2)|(mb & ms & n0 & _ & SW & Q1 & Q2)].
      * assert (NEQ : c <> xb_class b \/ k <> xb_slot b).
        { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
          destruct (proj1 (In_X_g X stt c k n b1 ctx l1 l2 XB b) Hb) as [Hl| ->]; [| cbn in Sb; exact (NL p Sb)].
          exact (key_fresh_g L st X stt c k n b1 ctx l1 l2 XB WF b Hl (eq_sym EC) (eq_sym EK)). }
        (nd_pre (busy_slot_geo L st X ALO WF b Hb) 3%nat; intros CLB KB _; nd_post).
        pose proof (slots_sep_any L st X c k (xb_class b) (xb_slot b) ALO WF HC CLB KR KB NEQ) as D.
        unfold xb_alloc in Q1, Q2. clear -D Q1 Q2 R Ha HA HB. lia.
      * (nd_pre SW 7%nat; intros _ MLO MCE _ _ _ (_ & _ & SCr & _); nd_post). unfold SEC_UOFF in *. clear -R Ha HA HB Q1 Q2 SCr G6 G7. lia.
    + clear -R Ha HA HB G G6 G7 DFR. lia.
  - clear -C Ha HA HB G6 G7 DFR. lia.
  - clear -C Ha HA G4 S2. lia.
  - clear -C Ha HA G4 S3. lia.
  - assert (SF : shad (al_fake L + 11571200) <= 17594332446720) by (pose proof atop_range as AR; rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    clear -C Ha HA G4 SF. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_static : forall L st X LB HI A B, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  (forall a, A <= a < B -> astatic a) -> 0x10000 <= A -> B <= AIMG_HI ->      (* [comment removed for export] *)
  forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI A B ALO WF BL HHI ST A0 BH a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). pose proof (ST a Ha) as SA.
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF. pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold cprot, astatic, AIMG_HI, AINSTANCE, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { pose proof ATPv_img as TI. apply (atls_not_app a (a + 1) a); [left; clear -TI SA; lia | left; clear -BH Ha; lia | clear; lia]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; clear -CH OAH OAHI Ha BH; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha SA HHI BH OF S1 S2 S3 S4 AR; lia).
  - (nd_pre C 3%nat; intros blk Hin R; nd_post). (pose proof (lb_high L st X LB blk ALO WF BL Hin ltac:(clear -R; lia)) as ndP__; nd_pre ndP__ 3%nat; intros G _ _; nd_post). unfold AIMG_HI in G. clear -R G Ha BH. lia.
  - assert (SF : 2147450880 <= shad (al_fake L)) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF; Z.div_mod_to_equations; lia). clear -C Ha BH SF. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_ptrarr : forall L st X LB HI nres, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  0 <= nres -> 8 * nres <= 8388608 ->
  forall a, al_ptr_array L <= a < al_ptr_array L + 8 * nres -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI nres ALO WF BL HHI N0 N1 a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_ptr L ALO) as OP. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OP, ORS.   (* [comment removed for export] *)
  pose proof (ad_fake_ptr L ALO) as DFP. pose proof (ad_ptr_res L ALO) as DPR. unfold adisj in DFP, DPR. pose proof atop_range as AR.
  assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { pose proof (ad_tls_ptr L ALO) as DLP. unfold adisj in DLP.
    apply (atls_not_app (al_ptr_array L) (al_ptr_array L + 8 * nres) a); [clear -DLP N0 N1; lia | clear -OP N0 N1; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; pose proof (ad_ahm_ptr L ALO) as DA2; unfold adisj in DA2; clear -CH DA2 Ha N0 N1; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha N0 N1 HHI OF OP DFP S1 S2 S3 S4 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n0 & _ & SW & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ Q6 Q7; nd_post). clear -R Ha N0 N1 G1 G2 Q6 Q7 DPR. lia.
    + (nd_pre SW 7%nat; intros _ MLO MCE _ _ _ (_ & _ & _ & SCp & _); nd_post). unfold SEC_UOFF in *. clear -R Ha N0 N1 G1 G2 SCp. lia.
  - clear -R Ha N0 N1 G DFP. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_secmap : forall L st X LB HI mb ms n, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  sec_wf1 L (CSec mb ms n) ->
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb') ->
  forall a, (mb <= a < mb + ms \/ shad mb <= a < shad mb + shlen ms) -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI mb ms n ALO WF BL HHI SW DJ a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS. pose proof atop_range as AR.   (* [comment removed for export] *)
  (nd_pre SW 7%nat; intros MAL MLO MCE MSE NB NPR SCL; nd_post). (pose proof SCL as ndP__; nd_pre ndP__ 8%nat; intros _ _ SCr _ _ _ SCf _; nd_post). unfold ablk, AIMG_HI, KLS in MLO.
  (pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ MSAL _; nd_post). rewrite <- MSE in MSAL.
  assert (SH : shad mb + shlen ms = shad (mb + ms) /\ shad (mb + ms) <= shad ATOP /\ 2148238848 <= shad mb
               /\ ((mb + ms <= 2147446784 /\ shad (mb + ms) <= 2415881728) \/ (K_HIGH_MEM <= mb /\ 2201439137792 <= shad mb))
               /\ (shad (mb + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb) /\ shad (al_fake L + 11571200) <= shad ATOP).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_HIGH_MEM in *. clear -MAL MLO MCE MSAL SCf OF. Z.div_mod_to_equations. lia. }
  (nd_pre SH 6%nat; intros SH1 SH2 SH3 SH4 SH5 SH6; nd_post).
  assert (SF : 2147450880 <= shad (al_fake L)) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ SCtls _; nd_post). pose proof atp_lin as TLN.
    assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
    destruct Ha as [Ha|Ha].
    - apply (atls_not_app mb (mb + ms) a); [clear -SCtls; lia | clear -MLO; lia | exact Ha].
    - intros [T|(a' & Ha' & ->)]; [clear -T Ha TLN SH1 SH2 SH3 S1; lia|].
      (pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSB0; nd_post). rewrite <- MSE in MSB0.
      destruct (tls_shadow_apart a' mb ms Ha' ltac:(clear -MSB0; lia)) as [D|D].
      { destruct SCtls as [D|D]; [right; split; [exact D| exact MAL8]| left; exact D]. }
      + clear -D Ha. lia.
      + clear -D Ha. lia. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SCahm; nd_post); destruct Ha as [Ha|Ha]; clear -CH OAH OAHI SCahm Ha SH1 SH2 SH3 S1; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha MLO MCE HHI OF SCf S1 S2 S3 S4 SH1 SH2 SH3 SH4 SH5 SH6 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb' & ms' & n0 & Lp & SW' & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ Q4 _ Q6 Q7; nd_post). clear -R Ha G1 G2 Q4 Q6 Q7 SCr MLO S1 SH1 SH2 AR. lia.
    + (nd_pre SW' 3%nat; intros _ MLO' _; nd_post). unfold ablk, AIMG_HI, KLS in MLO'. specialize (DJ _ _ _ _ Lp). unfold SEC_UOFF, K_HIGH_MEM in *. clear -R Ha G1 G2 DJ MLO MLO' S1 SH1 SH2 SH3 AR. lia.
  - clear -R Ha G SCf OF MLO S1 SH1 SH2 SH3 SF AR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_hl : forall L st X LB HI hl, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  ablk hl (hl + 8) -> hl + 8 <= ATOP -> sec_clear L hl 8 ->      (* [comment removed for export] *)
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl) ->
  forall a, hl <= a < hl + 8 -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI hl ALO WF BL HHI K1 K2 SCL HLS a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold ablk, AIMG_HI, KLS in K1. pose proof atop_range as AR.
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF. (pose proof SCL as ndP__; nd_pre ndP__ 8%nat; intros _ _ SCr _ _ _ SCf _; nd_post).
  assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ SCtls _; nd_post).
    apply (atls_not_app hl (hl + 8) a); [clear -SCtls; lia | clear -K1; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SCahm; nd_post); clear -CH SCahm Ha; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha K1 K2 HHI OF SCf S1 S2 S3 S4 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb' & ms' & n0 & Lp & SW' & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ Q6 Q7; nd_post). clear -R Ha G1 G2 Q6 Q7 SCr. lia.
    + specialize (HLS _ _ _ _ Lp). clear -R Ha G1 G2 HLS. lia.
  - clear -R Ha G SCf. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_cd_W : forall L st X LB HI lo SP c nf mfa mfa', alayout_ok L -> awf L st X -> ablocks L st X LB ->
  1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  ATOP <= lo -> lo <= SP - 688 -> SP <= HI ->
  np_fp L HI LB (cd_W L SP c nf mfa mfa').
Proof.
  intros L st X LB HI lo SP c nf mfa mfa' ALO WF BL HC NF0 NF4 MFA CEIL LO SPH iv Hiv.
  destruct (cd_W_cases L SP c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hiv) as [->|P].
  - cbn [fst snd]. eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - eapply (np_low L st X LB HI c iv); [exact ALO| exact WF| exact BL| exact HC| clear -CEIL LO SPH; lia| exact P].
Qed.

#[using="Type"] Lemma np_rec_W : forall L st X LB HI lo SP c kk n b1 ctx l1 l2 nf mfa mfa', alayout_ok L -> awf L st X -> ablocks L st X LB ->
  x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  ATOP <= lo -> lo <= SP - 688 -> SP <= HI ->
  np_fp L HI LB (rec_W L SP c kk n nf mfa mfa').
Proof.
  intros L st X LB HI lo SP c kk n b1 ctx l1 l2 nf mfa mfa' ALO WF BL XB NF0 NF4 MFA CEIL LO SPH iv Hiv.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hiv) as [->|[SL|P]].
  - cbn [fst snd]. eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - intros a Ha. eapply (np_slot L st X LB HI BQuar c kk n b1 ctx l1 l2 (fst iv) (snd iv));
      [exact ALO| exact WF| exact BL| clear -CEIL LO SPH; lia| exact XB| intros p; discriminate| exact (proj1 SL)| exact (proj2 SL)| exact Ha].
  - eapply (np_low L st X LB HI c iv); [exact ALO| exact WF| exact BL| exact HC| clear -CEIL LO SPH; lia| exact P].
Qed.

#[using="Type"] Lemma np_srec_W : forall L st X LB HI lo SP mb ms n nres hl, alayout_ok L -> awf L st X -> ablocks L st X LB ->
  sec_wf1 L (CSec mb ms n) ->
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb') ->
  ablk hl (hl + 8) -> hl + 8 <= ATOP -> sec_clear L hl 8 ->      (* [comment removed for export] *)
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl) ->
  0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 -> SP <= HI ->
  np_fp L HI LB (srec_W L SP mb ms nres ++ [(hl, hl + 8)]).
Proof.
  intros L st X LB HI lo SP mb ms n nres hl ALO WF BL SW DJ K1 K2 SCL HLS N0 N1 CEIL LO SPH.
  assert (HHI : ATOP <= HI) by (clear -CEIL LO SPH; lia).
  pose proof (alayout_t_lin L ALO) as OT.
  unfold srec_W. cbn [app].
  apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_nil]]]]]]]; cbn [fst snd].
  - eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - eapply (np_low L st X LB HI 1 (al_t L + 2800, al_t L + 3168)); [exact ALO| exact WF| exact BL| unfold K_NUM_CLASSES; clear; lia| exact HHI|].
    unfold lowpiece. cbn [fst snd]. split; [clear -OT; lia|]. split; [clear -OT; lia| right; left; clear; lia].
  - eapply (np_static L st X LB HI); [exact ALO| exact WF| exact BL| exact HHI| intros a Ha; unfold astatic, AINSTANCE in *; clear -Ha; lia| unfold AINSTANCE; clear; lia| unfold AINSTANCE, AIMG_HI; clear; lia].
  - eapply (np_ptrarr L st X LB HI nres); [exact ALO| exact WF| exact BL| exact HHI| exact N0| exact N1].
  - intros a Ha. eapply (np_secmap L st X LB HI mb ms n); [exact ALO| exact WF| exact BL| exact HHI| exact SW| exact DJ| left; exact Ha].
  - intros a Ha. eapply (np_secmap L st X LB HI mb ms n); [exact ALO| exact WF| exact BL| exact HHI| exact SW| exact DJ| right; exact Ha].
  - eapply (np_hl L st X LB HI hl); [exact ALO| exact WF| exact BL| exact HHI| exact K1| exact K2| exact SCL| exact HLS].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cpres_aheap_pres : forall (CI : list (Z * Z)) L HI LB SPc st X m m',
  alayout_ok L -> awf L st X -> ablocks L st X LB ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1804c8 \/ 0x5d0510 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv) /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv) /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  HI <= SPc -> cpres L HI LB m m' -> aheap_pres CI LB SPc m m'.
Proof.
  intros CI L HI LB SPc st X m m' ALO WF BL CI_OK CI_OK2 HS CP a Ha CL. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. unfold aobj in OF.
  assert (E : m' (wa a) = m (wa a)).
  { apply CP. rewrite wa_unsigned by exact Ha. unfold cprot.
    destruct CL as [CL|[TL|[IM|IM]]]; [right; right| left; exact TL| | right; left; exact IM].
    2:{ right; right; right; right; right; right; right; left. unfold AIMSH_LO, AIMSH_LEN in IM. rewrite S3. unfold ASHOFF. clear -IM. lia. }
    destruct CL as [ST | [CIa | [BLK | SHD]]].
    - left. clear -ST HS. lia.
    - right; left. (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. unfold astatic, AINSTANCE in *. clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7. lia.
    - right; right; left. exact BLK.
    - (nd_pre SHD 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). right; right; right; right.
      destruct Ha' as [STa | [CIa | FK]].
      + left. rewrite !shad_div. unfold ASHOFF in *. clear -STa. Z.div_mod_to_equations. lia.
      + right; left. (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 _ Q3 _; nd_post).
        rewrite !shad_div. unfold AIMG_HI, ASHOFF in *. clear -R Q1 Q3. Z.div_mod_to_equations. lia.
      + right; right. (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros F1 F2 F3; nd_post).
        rewrite !shad_div. unfold ASHOFF in *. clear -R F1 F3 OF. Z.div_mod_to_equations. lia. }
  split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw.
Qed.
End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma outside_of_In : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn; [exact I|]. split; [exact (H (lo, hi) (or_introl eq_refl))|].
  apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Geo.
Variables (L : alayout) (st : astate) (X : aconc).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.

(* [comment removed for export] *)
#[using="tlsI ALO WF"] Lemma busy_slot_geo : forall b, In b (x_busy X) ->
     1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b)
  /\ aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
  /\ (al_space_beg L <= aregion L (xb_class b) /\ c_allocated_user (get_cls st (xb_class b)) <= c_mapped_user (get_cls st (xb_class b)) <= K_FREEARR_OFF
      /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE)
  /\ 0x10007fff8000 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= ATOP
  /\ al_res L + 4096 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104.
Proof.
  intros b Hb. (pose proof WF as ndP__; nd_pre ndP__ 9%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY _; nd_post).
  destruct (BUSY b Hb) as [CLB _]. (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  (pose proof (slot_geo L st X (xb_class b) (xb_slot b) ALO WF CLB KB) as ndP__; nd_pre ndP__ 12%nat; intros S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 _; nd_post).
  pose proof (ao_space L ALO) as RSP.
  assert (RS : al_space_beg L <= aregion L (xb_class b) /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize CLB. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  unfold xb_alloc. split; [exact CLB|]. split; [exact KB|]. split; [exact G1|]. split; [exact G2|]. split; [split; [exact (proj1 RS)| split; [clear -G3 G4; lia| exact (proj2 RS)]]|].
  split; [exact G7|]. split; [exact G8|]. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *. split; lia.
Qed.
End Geo.

#[using="Type"] Lemma in_ic_W : forall L i d iv, In iv (ic_W L i d) -> exists j, i <= j /\ j < i + Z.of_nat d /\ iv = (acache_addr L j + 4, acache_addr L j + 16).
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i iv Hin; cbn [ic_W] in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists i; split; [lia| split; [lia| reflexivity]]|].
  (nd_pre (IH (i + 1) iv Hin) 4%nat; intros j A B E; nd_post). exists j. split; [lia| split; [lia| exact E]].
Qed.

(* [comment removed for export] *)
Definition lowpiece (L : alayout) (c : Z) (iv : Z * Z) : Prop :=
  0 <= fst iv /\ snd iv <= ATOP /\ ((shad (al_space_beg L) <= fst iv /\ snd iv <= shad (al_space_beg L + K_SPACE_SIZE) /\ snd iv <= 0x10007fff8000)
                                    \/ al_t L <= fst iv /\ snd iv <= al_t L + 4096
                     \/ aregion L c + K_FREEARR_OFF <= fst iv /\ snd iv <= aregion L c + K_REGION
                     \/ al_space_beg L + K_SPACE_SIZE <= fst iv /\ snd iv <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA).

#[using="Type"] Lemma cd_W_cases : forall L sp c nf mfa mfa' iv,
  alayout_ok L -> 1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  In iv (cd_W L sp c nf mfa mfa') -> iv = (sp - 688, sp) \/ lowpiece L c iv.
Proof.
  intros L sp c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hin. unfold lowpiece.
  pose proof (alayout_t_lin L ALO) as (TL1 & TL2). (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 _; nd_post).   (* [comment removed for export] *)
  assert (FAS : shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000 /\ 0x10007fff8000 <= afreearr L c /\ afreearr L c + mfa' <= aregion L c + K_REGION
                /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                /\ shad (al_space_beg L) <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= shad (al_space_beg L + K_SPACE_SIZE)).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE, K_SPACE_EXTRA, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
    rewrite !shad_div, shlen_div. unfold ASHOFF. clear -HC SP1 SP2 NF0 NF4 MFA. Z.div_mod_to_equations. lia. }
  (nd_pre FAS 6%nat; intros FA1 FA2 FA3 FA4 FA5 FA6; nd_post).
  unfold cd_W in Hin. cbv zeta in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (CAB : forall j, 1 <= j -> j <= 32 -> al_t L <= acache_addr L j /\ acache_addr L j + 80 <= al_t L + 4096) by (intros j A B; unfold acache_addr; clear -A B; lia).
  assert (RIB : al_space_beg L + 137438953472 <= aregion_info L c /\ aregion_info L c + 128 <= al_space_beg L + 137438953472 + 4096).
  { unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. unfold K_NUM_CLASSES in HC. clear -HC. lia. }
  destruct Hin as [[E|F] | [Hic | H9]]; try (destruct F); try subst iv; cbn [fst snd].
  - left. reflexivity.
  - right. apply in_ic_W in Hic. (nd_pre Hic 4%nat; intros j J1 J2 ndR1__; nd_post; revert ndR1__; intros ->). cbn [fst snd]. destruct (CAB j ltac:(clear -J1; lia) ltac:(clear -J2; cbn in J2; lia)) as [C1 C2].
    split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
  - destruct H9 as [E|[E|[E|[E|[E|[E|[E|[E|[E|F]]]]]]]]]; try (destruct F); subst iv; cbn [fst snd]; right.
    + destruct (CAB c ltac:(clear -HC; lia) ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [C1 C2]. split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
    + destruct (CAB c ltac:(clear -HC; lia) ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [C1 C2]. split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
    + split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
    + split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
    + split; [unfold afreearr, K_FREEARR_OFF in *; clear -NF0 FA2; lia|]. split; [clear -FA3 FA4 SP2; lia| right; right; left; unfold afreearr, K_FREEARR_OFF in *; clear -NF0 FA3; lia].
    + split; [rewrite shad_div; unfold ASHOFF; clear -FA2 NF0 NF4; Z.div_mod_to_equations; lia|]. split; [clear -FA1; lia| left; clear -FA1 FA5 FA6; unfold K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; repeat split; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rec_W_cases : forall L st X sp c kk n b1 ctx l1 l2 nf mfa mfa' iv,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  In iv (rec_W L sp c kk n nf mfa mfa') ->
  let AB := aslot_addr L c kk in let S := size_of_class c in
  iv = (sp - 688, sp) \/ (AB <= fst iv /\ snd iv <= AB + S) \/ lowpiece L c iv.
Proof.
  intros L st X sp c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hin. cbv zeta.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 3%nat; intros N0 FIT0 _; nd_post).
  (pose proof (chunk_geo L st X c kk n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros _ _ G3 G4 _ G6 G7 _; nd_post).
  (pose proof (chunk_shadow_geo L st X c kk n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros SE _ GE SG0 SGF SHLO SHHI _; nd_post).
  pose proof (alayout_t_lin L ALO) as (TL1 & TL2). pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].   (* [comment removed for export] *)
  unfold rec_W in Hin. cbv zeta in Hin. apply in_app_iff in Hin.
  destruct Hin as [Hin|Hin]; [| destruct (cd_W_cases L sp c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hin) as [E|P]; [left; exact E| right; right; exact P]].
  unfold lowpiece in *. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|F]]]]]; try (destruct F); subst iv; cbn [fst snd].
  - left. reflexivity.
  - right. left. clear -RZ1 G6 N0; unfold rup in *; split; lia.
  - right. left. clear -RZ1 G3 G6 N0; unfold rup in *; split; lia.
  - (pose proof (slot_geo L st X c kk ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ Q5 Q6 _; nd_post).
    assert (SB : shad (al_space_beg L) <= shad (aslot_addr L c kk) /\ shad (aslot_addr L c kk) + shlen (size_of_class c) <= shad (al_space_beg L + K_SPACE_SIZE)).
    { rewrite !shad_div, shlen_div. clear -Q5 Q6. Z.div_mod_to_equations. lia. }
    right. right. split; [clear -SE SHLO SG0 GE RZ1; pose proof (shlen_nonneg (rz_size n) ltac:(lia)); lia|].
    split; [clear -SE SGF SHHI SG0 GE TL1 TL2; lia| left; clear -SE SGF SHHI SG0 GE SB RZ1; pose proof (shlen_nonneg (rz_size n) ltac:(lia)); repeat split; lia].
  - right. right. split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lowpiece_vs_slot : forall L st X c b iv, alayout_ok L -> awf L st X -> 1 <= c < K_NUM_CLASSES -> In b (x_busy X) ->
  lowpiece L c iv -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b.
Proof.
  intros L st X c b iv ALO WF HC Hb (Pz & P0 & P).
  (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros CLB KB G1 G2 (G3a & G3 & G3b) G4 G5 G6 G7; nd_post).
  pose proof (ad_t_res L ALO) as DTR. pose proof (ao_space L ALO) as RSP. unfold adisj in DTR.
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  destruct P as [(_ & _ & P)|[P|[P|P]]].
  - right. clear -P G4. lia.
  - clear -P DTR RSP G6 G7. lia.
  - destruct (Z.eq_dec (xb_class b) c) as [<-|NC].
    + left. clear -P G2 G3. lia.
    + (pose proof (region_other_geo L c (xb_class b) ALO ltac:(unfold K_NUM_CLASSES in HC; exact HC) ltac:(unfold K_NUM_CLASSES in CLB; exact CLB) NC) as ndP__; nd_pre ndP__ 3%nat; intros _ RD _; nd_post).
      clear -P G1 G2 G3 RD. lia.
  - left. clear -P G2 G3 G3b. lia.
Qed.

(* [comment removed for export] *)
Definition wpiece (L : alayout) (lo SP : Z) (iv : Z * Z) : Prop :=
     (lo <= fst iv /\ snd iv <= SP)
  \/ (shad (al_space_beg L) <= fst iv /\ snd iv <= shad (al_space_beg L + K_SPACE_SIZE) /\ snd iv <= 0x10007fff8000)
  \/ (al_t L <= fst iv /\ snd iv <= al_t L + 4096)
  \/ (al_space_beg L <= fst iv /\ snd iv <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA).

#[using="Type"] Lemma lowpiece_wpiece : forall L lo SP c iv, 1 <= c < K_NUM_CLASSES -> lowpiece L c iv -> wpiece L lo SP iv.
Proof.
  intros L lo SP c iv HC (_ & _ & P). unfold wpiece.
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  destruct P as [P|[P|[P|P]]]; [right; left; exact P| right; right; left; exact P| right; right; right; clear -P RS; lia| right; right; right; clear -P; lia].
Qed.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.

#[using="Type"] Lemma wpiece_fake : forall L lo SP iv, alayout_ok L -> ATOP <= lo -> wpiece L lo SP iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xa7668 \/ 0xa7668 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
  /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
  /\ (snd iv <= 0x1405b1 \/ 0x1405b1 + 1 <= fst iv) /\ (snd iv <= 0x13e498 \/ 0x13e498 + 4 <= fst iv).
Proof.
  intros L lo SP iv ALO CEIL P. unfold wpiece in P.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_space_al L ALO) as SAL.
  pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_t_dtls L ALO) as DTD.
  pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold aobj in OF, OD, OT, ORS. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OD, OT.   (* [comment removed for export] *)
  unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (SHF : shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L) \/ shad (al_space_beg L + 137438953472) <= shad (al_fake L)).
  { rewrite !shad_div, shlen_div. clear -DFR RSP OF SAL. Z.div_mod_to_equations. lia. }
  assert (SHB : 2201439137792 <= shad (al_space_beg L) /\ 2147450880 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF. clear -RSP ORS RHI OF AR. Z.div_mod_to_equations. lia. }
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. unfold adisj in D_l_t, D_l_r. pose proof atp_lin as TLN.      (* [comment removed for export] *)
  (nd_pre SHB 3%nat; intros SB1 SB2 SB3; nd_post).
  destruct P as [P|[P|[P|P]]]; clear -P OF OD OT ORS RHI AR RSP DFR DDR DTF DTD CEIL SHF SB1 SB2 SB3 D_l_t D_l_r TLN; repeat split; fu_focus; lia.
Qed.

#[using="Type"] Lemma fake_untouched_of : forall L W,
  (forall iv, In iv W ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xa7668 \/ 0xa7668 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
  /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
  /\ (snd iv <= 0x1405b1 \/ 0x1405b1 + 1 <= fst iv) /\ (snd iv <= 0x13e498 \/ 0x13e498 + 4 <= fst iv)) ->
  fake_untouched L W.
Proof. intros L W H. unfold fake_untouched. apply Forall_forall. exact H. Qed.

#[using="Type"] Lemma rec_W_wpiece : forall L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa' iv,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> lo <= SP - 688 ->
  In iv (rec_W L SP c kk n nf mfa mfa') -> wpiece L lo SP iv.
Proof.
  intros L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA LO Hin.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hin) as [E|[SL|LP]].
  - left. subst iv. cbn. lia.
  - right. right. right. (pose proof (slot_geo L st X c kk ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ G5 G6 _; nd_post). unfold K_SPACE_EXTRA. clear -SL G5 G6. lia.
  - eapply lowpiece_wpiece; [exact HC| exact LP].
Qed.

#[using="Type"] Lemma rec_W_fake : forall L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa',
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> ATOP <= lo -> lo <= SP - 688 ->
  fake_untouched L (rec_W L SP c kk n nf mfa mfa').
Proof.
  intros. apply fake_untouched_of. intros iv Hiv. eapply wpiece_fake; [eassumption| eassumption|]. eapply rec_W_wpiece; eassumption.
Qed.

#[using="Type"] Lemma cd_W_fake : forall L lo SP c nf mfa mfa',
  alayout_ok L -> 1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> ATOP <= lo -> lo <= SP - 688 ->
  fake_untouched L (cd_W L SP c nf mfa mfa').
Proof.
  intros L lo SP c nf mfa mfa' ALO HC NF0 NF4 MFA CEIL LO. apply fake_untouched_of. intros iv Hiv. eapply (wpiece_fake L lo SP); [exact ALO| exact CEIL|].
  destruct (cd_W_cases L SP c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hiv) as [->|P]; [left; cbn [fst snd]; clear -LO; lia| eapply lowpiece_wpiece; [exact HC| exact P]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srec_W_pieces : forall L st X lo SP mb ms n nres hl iv,
  alayout_ok L -> awf L st X -> sec_wf1 L (CSec mb ms n) -> srec_hl_ok L hl -> 0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 ->
  In iv (srec_W L SP mb ms nres ++ [(hl, hl + 8)]) ->
     ((lo <= fst iv /\ snd iv <= SP)
      \/ (forall b, In b (x_busy X) -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP)
  /\ ((snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
      /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
      /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
      /\ (snd iv <= 0xa7668 \/ 0xa7668 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
      /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
      /\ (snd iv <= 0x1405b1 \/ 0x1405b1 + 1 <= fst iv) /\ (snd iv <= 0x13e498 \/ 0x13e498 + 4 <= fst iv)).
Proof.
  intros L st X lo SP mb ms n nres hl iv ALO WF SW HLOK NR0 NR1 CEIL LO Hin.
  unfold srec_W in Hin. rewrite in_app_iff in Hin. cbn [In] in Hin.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_t_dtls L ALO) as DTD.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_ptr_res L ALO) as DPR. pose proof (ad_fake_ptr L ALO) as DFP. pose proof (ad_dtls_ptr L ALO) as DDP.
  (nd_pre SW 7%nat; intros MB KH MCE _ _ _ SC; nd_post). (nd_pre SC 9%nat; intros SCt SCc SCr SCp SCn SCs SCf SCd SCl; nd_post).
  (nd_pre HLOK 3%nat; intros HK HC8 (HCt & HCc & HCr & HCp & HCn & HCs & HCf & HCd & HCl); nd_post).
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_res L ALO) as D_l_r. pose proof atp_lin as TLN.      (* [comment removed for export] *)
  pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold aobj, sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI, adisj, K_HIGH_MEM, AINSTANCE in *.
  assert (SHB : shad (al_fake L) + shlen 11571200 <= 17594332446720 /\ 0 <= shad mb /\ shad mb + shlen ms <= shad (mb + ms) /\ shad (mb + ms) <= 17594332446720
                /\ (shad (mb + ms) <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb) /\ 2148239360 <= shad mb /\ 2148239360 <= shad (al_fake L)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -OF MCE KH SCf AR. Z.div_mod_to_equations. lia. }
  (nd_pre SHB 7%nat; intros SH1 SH2 SH3 SH4 SH5 SH6 SH7; nd_post).
  assert (BB : forall b, In b (x_busy X) -> al_res L + 4096 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104 /\ 17594333495296 <= xb_alloc L b).
  { intros b Hb. (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ G4 _ G6 G7; nd_post). unfold K_HIGH_MEM in *. clear -G4 G6 G7. lia. }
  destruct Hin as [[E|[E|[E|[E|[E|[E|F]]]]]] | [E|F]]; try (destruct F); subst iv; cbn [fst snd].
  - split; [left; clear -LO; lia|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD CEIL LO SH1 SH7 AR. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 DTR; lia| clear -OT; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD OT DTF DTD SH1 SH7. repeat split; fu_focus; lia.
  - unfold AINSTANCE. split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B3; lia| clear -AR; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD SH1 SH7. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 DPR NR0 NR1; lia| clear -OP NR0 NR1; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD OP DFP DDP SH1 SH7 NR0 NR1. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 SCr; lia| clear -KH MCE; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD KH MCE SCf SCd SH1 SH7. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B3 SH3 SH4; lia| clear -SH2 SH3 SH4 AR; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD SH1 SH2 SH3 SH4 SH5 SH6. repeat split; fu_focus; lia.
  - split; [right; split; [intros b Hb; (nd_pre (BB b Hb) 3%nat; intros B1 B2 B3; nd_post); clear -B1 B2 HCr; lia| clear -HK HC8; lia]|]. clear -D_l_t D_l_p D_l_r TLN SCl HCl OF OD HK HC8 HCf HCd SH1 SH7. repeat split; fu_focus; lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma srec_W_t48 : forall L (st : astate) (X : aconc) lo SP mb ms n nres hl iv,
  alayout_ok L -> sec_wf1 L (CSec mb ms n) -> srec_hl_ok L hl -> 0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 ->
  In iv (srec_W L SP mb ms nres ++ [(hl, hl + 8)]) -> snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv.
Proof.
  intros L st X lo SP mb ms n nres hl iv ALO SW HLOK NR0 NR1 CEIL LO Hin.
  unfold srec_W in Hin. rewrite in_app_iff in Hin. cbn [In] in Hin.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ptr L ALO) as OP. pose proof (ad_t_ptr L ALO) as DTP. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OT, OP, DTP.   (* [comment removed for export] *)
  (nd_pre SW 7%nat; intros MAL MLO MCE _ _ _ (SCt & _); nd_post). (nd_pre HLOK 3%nat; intros HK HC8 (HCt & _); nd_post). unfold ablk, AIMG_HI, KLS in MLO.
  assert (SHB : 2148239360 <= shad mb /\ shad mb + shlen ms <= 17594332446720) by (pose proof atop_range as AR; rewrite shad_div, shlen_div; unfold ASHOFF in *; clear -MLO MCE AR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM, AINSTANCE in *.
  destruct Hin as [[E|[E|[E|[E|[E|[E|F]]]]]] | [E|F]]; try (destruct F); subst iv; cbn [fst snd];
    first [clear -CEIL LO OT; lia| clear -OT; lia| clear -OT OP DTP NR0 NR1; lia| clear -SCt; lia| clear -SHB OT; lia| clear -HCt; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition astatic (a : Z) : Prop :=
  a < 0x10000 \/ (AINSTANCE <= a < 0xab730) \/ (0x1808c8 <= a < 0x5d0910) \/ (0xafc00 <= a < 0x130c30) \/ (0x13e488 <= a < 0x13e48c).

(* [comment removed for export] *)
Definition cprot (L : alayout) (HI : Z) (LB : list ablock) (a : Z) : Prop :=
     atls_addr a                            (* [comment removed for export] *)
  \/ (AAHMv <= a < AAHMv + AAHM_SZ)          (* [comment removed for export] *)
  \/ HI <= a
  \/ (a < AIMG_HI /\ ~ astatic a)
  \/ in_block LB a
  \/ (al_fake L <= a < al_fake L + 11571200)
  \/ (shad ATOP <= a < shad (2^47))
  \/ (ASHOFF <= a < shad AIMG_HI)
  \/ (shad (al_fake L) <= a < shad (al_fake L + 11571200)).

Definition cpres (L : alayout) (HI : Z) (LB : list ablock) (m m' : amem) : Prop :=
  forall x : word, cprot L HI LB (bv_unsigned x) -> m' x = m x.

#[using="Type"] Lemma cpres_refl : forall L HI LB m, cpres L HI LB m m.
Proof. intros L HI LB m x _. reflexivity. Qed.
#[using="Type"] Lemma cpres_trans : forall L HI LB m1 m2 m3, cpres L HI LB m1 m2 -> cpres L HI LB m2 m3 -> cpres L HI LB m1 m3.
Proof. intros L HI LB m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

(* [comment removed for export] *)
Definition np_fp (L : alayout) (HI : Z) (LB : list ablock) (W : list (Z * Z)) : Prop :=
  forall iv, In iv W -> forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a.

#[using="Type"] Lemma cpres_of_munch : forall L HI LB W m m', munch W m m' -> np_fp L HI LB W -> cpres L HI LB m m'.
Proof.
  intros L HI LB W m m' MU NP x Hx. apply MU. apply outside_of_In. intros iv Hiv R. exact (NP iv Hiv _ R Hx).
Qed.
#[using="Type"] Lemma np_fp_app : forall L HI LB W1 W2, np_fp L HI LB W1 -> np_fp L HI LB W2 -> np_fp L HI LB (W1 ++ W2).
Proof. intros L HI LB W1 W2 H1 H2 iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [H|H]; [exact (H1 iv H)| exact (H2 iv H)]. Qed.
#[using="Type"] Lemma np_fp_cons : forall L HI LB iv W, (forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a) -> np_fp L HI LB W -> np_fp L HI LB (iv :: W).
Proof. intros L HI LB iv W H1 H2 iv' [<-|H]; [exact H1| exact (H2 iv' H)]. Qed.
#[using="Type"] Lemma np_fp_nil : forall L HI LB, np_fp L HI LB [].
Proof. intros L HI LB iv []. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma shad_consts : (17594064011264 <= shad ATOP <= 17594332446720) /\ shad (2^47) = 17594333495296 /\ shad AIMG_HI = 2148239360 /\ ASHOFF = 2147450880.
Proof. split; [pose proof atop_range as AR; rewrite shad_div; unfold ASHOFF; lia|]. repeat split; reflexivity. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma lb_geo : forall L st X LB blk, alayout_ok L -> awf L st X -> ablocks L st X LB -> In blk LB ->
  match ab_kind blk with
  | ABHeap p =>
         (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_alloc L b <= ab_addr blk /\ ab_addr blk + ab_size blk <= xb_alloc L b + size_of_class (xb_class b))
      \/ (exists mb ms n, (a_live st) !! p = Some (CSec mb ms n) /\ sec_wf1 L (CSec mb ms n) /\ mb + SEC_UOFF <= ab_addr blk /\ ab_addr blk + ab_size blk <= mb + ms)
  | ABFake _ => al_fake L <= ab_addr blk /\ ab_addr blk + ab_size blk <= al_fake L + 11571200
  end.
Proof.
  intros L st X LB [[p|cls] A n] ALO WF (B1 & B2 & _) Hin; cbn [ab_kind ab_addr ab_size].
  - destruct (B1 p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
    + left. exists b. split; [exact Hb|]. split; [exact Sb|].
      pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n.
      clear -FIT. lia.
    + right. exists mb, ms, n. split; [exact Lp|]. split; [exact G|]. subst A.
      (nd_pre G 7%nat; intros MAL MLO MCE MSE NB NPR SCL; nd_post).
      (pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as ndP__; nd_pre ndP__ 9%nat; intros _ RZ _ RS1 _ NS _ MSB _; nd_post). rewrite <- MSE in MSB.
      unfold SEC_UOFF. clear -RS1 NS MSB. lia.
  - exact (conj (proj1 (B2 cls A n Hin)) (proj2 (proj2 (B2 cls A n Hin)))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma lb_high : forall L st X LB blk, alayout_ok L -> awf L st X -> ablocks L st X LB -> In blk LB ->
  ab_addr blk < ab_addr blk + ab_size blk ->
  AIMG_HI <= ab_addr blk /\ ab_addr blk + ab_size blk <= ATOP /\ (ab_addr blk + ab_size blk <= KLS \/ K_HIGH_MEM <= ab_addr blk).
Proof.
  intros L st X LB blk ALO WF BL Hin NE. pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A n]; cbn [ab_kind ab_addr ab_size] in G |- *.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n' & _ & SW & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ Q4 Q5 _; nd_post). unfold K_HIGH_MEM, AIMG_HI, KLS. clear -G1 G2 Q4 Q5. lia.
    + (nd_pre SW 4%nat; intros _ MLO MCE _; nd_post). unfold ablk, K_HIGH_MEM, AIMG_HI, KLS in *. unfold SEC_UOFF in G1. clear -G1 G2 MLO MCE. lia.
  - pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, K_HIGH_MEM, AIMG_LO, AIMG_HI, KLS in *. clear -G OF NE. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_high : forall L st X LB HI A B, alayout_ok L -> awf L st X -> ablocks L st X LB ->
  ATOP <= A -> B <= HI -> forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI A B ALO WF BL HA HB a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). pose proof atop_range as AR.   (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF.
  assert (SF : shad (al_fake L + 11571200) <= shad ATOP) by (apply shad_mono; clear -OF; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a) by (apply (atls_not_app A B a); [right; pose proof atp_below_atop as TB; clear -TB HA; lia | right; clear -AR HA; lia | exact Ha]).
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; clear -CH OAH Ha HA; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha HA HB OF S1 S2 S3 S4 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). (pose proof (lb_high L st X LB blk ALO WF BL Hin ltac:(clear -R; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ G _; nd_post). clear -R G Ha HA. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_low : forall L st X LB HI c iv, alayout_ok L -> awf L st X -> ablocks L st X LB -> 1 <= c < K_NUM_CLASSES -> ATOP <= HI ->
  lowpiece L c iv -> forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI c iv ALO WF BL HC HHI (Pz & P0 & P) a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS, OT.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_res L ALO) as DTR. unfold adisj in DTF, DFR, DTR.
  pose proof (ao_space L ALO) as RSP. (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 3%nat; intros SP1 SP2 _; nd_post).
  assert (RR : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  assert (SHB : shad AIMG_HI <= shad (al_space_beg L) /\ shad (al_space_beg L + K_SPACE_SIZE) <= shad ATOP
                /\ (shad (al_fake L + 11571200) <= shad (al_space_beg L) \/ shad (al_space_beg L + K_SPACE_SIZE) <= shad (al_fake L))).
  { rewrite !shad_div. unfold AIMG_HI, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -OF ORS RSP DFR SP1 SP2. Z.div_mod_to_equations. lia. }
  (nd_pre SHB 3%nat; intros SB1 SB2 SB3; nd_post).
  unfold cprot, astatic, AINSTANCE, AIMG_HI, K_HIGH_MEM, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  assert (NT : ~ atls_addr a).
  { pose proof (ad_tls_res L ALO) as DLR. pose proof (ad_tls_t L ALO) as DLT. unfold adisj in DLR, DLT. pose proof (ao_res_hi L ALO) as RHI0. pose proof (ao_space_al L ALO) as SAL0.
    pose proof atp_lin as TLN. pose proof atop_range as AR0.
    destruct P as [P|[P|[P|P]]].
    - (* [comment removed for export] *)
      intros [T|(a' & Ha' & ->)]; [clear -T P Ha TLN SB1 S3; lia|].
      destruct (tls_shadow_apart a' (al_space_beg L) 137438953472 Ha' ltac:(clear; lia)) as [D|D].
      { destruct DLR as [D|D]; [left; clear -D RSP; lia| right; split; [clear -D RSP; lia| clear -SAL0; Z.div_mod_to_equations; lia]]. }
      + clear -D P Ha. lia.
      + rewrite <- (shad_add_shlen (al_space_beg L) 137438953472) in D by (clear -SAL0; Z.div_mod_to_equations; lia). clear -D P Ha. lia.
    - apply (atls_not_app (fst iv) (snd iv) a); [clear -P DLT; lia | clear -P OT; lia | exact Ha].
    - apply (atls_not_app (fst iv) (snd iv) a); [clear -P DLR RR RSP; lia | right; clear -P RR RSP RHI0; lia | exact Ha].
    - apply (atls_not_app (fst iv) (snd iv) a); [clear -P DLR RSP; lia | right; clear -P RSP RHI0; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; unfold adisj in DA1, DA2; destruct P as [P|[P|[P|P]]]; clear -CH OAH OAHI DA1 DA2 P Ha SB1 S3 RR RSP ORS; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
  - clear -C Ha P0 HHI. lia.
  - destruct P as [P|[P|[P|P]]]; clear -C Ha P S1 S2 S3 S4 SB1 OT RR SP1; lia.
  - (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
    destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n0 & _ & SW & G1 & G2)].
      * pose proof (lowpiece_vs_slot L st X c b iv ALO WF HC Hb (conj Pz (conj P0 P))) as D. clear -D G1 G2 R Ha. lia.
      * (nd_pre SW 7%nat; intros _ MLO MCE _ _ _ (SCt & _ & SCr & _); nd_post). unfold ablk, AIMG_HI, KLS, K_HIGH_MEM, SEC_UOFF in *.
        destruct P as [P|[P|[P|P]]]; clear -P R Ha G1 G2 MLO MCE SCt SCr S2 S3 SB1 SB2 RR RSP ORS; lia.
    + destruct P as [P|[P|[P|P]]]; clear -P R Ha G OF S1 S3 SB1 SB2 DTF DFR RR RSP ORS; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha OF S1 S3 SB1 SB2 DTF DFR RR RSP ORS; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha S1 S2 SB2 OT RR SP1; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha S3 S4 SB1 OT RR SP1 S2; lia.
  - assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720)
      by (pose proof atop_range as AR; rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    destruct P as [P|[P|[P|P]]]; clear -P C Ha SF SB3 OT RR SP1 S2; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_slot : forall L st X LB HI stt c k n b1 ctx l1 l2 A B, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  x_busy X = l1 ++ bany stt c k n b1 ctx :: l2 -> (forall p, stt <> BLive p) ->
  aslot_addr L c k <= A -> B <= aslot_addr L c k + size_of_class c ->
  forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI stt c k n b1 ctx l1 l2 A B ALO WF BL HHI XB NL HA HB a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  assert (IN0 : In (bany stt c k n b1 ctx) (x_busy X)) by (rewrite XB; apply in_app_iff; right; left; reflexivity).
  (pose proof (busy_slot_geo L st X ALO WF _ IN0) as ndP__; nd_pre ndP__ 9%nat; intros HC KR G1 G2 (G3a & G3 & G3b) G4 G5 G6 G7; nd_post).
  unfold xb_alloc in *. cbn [xb_class xb_slot bany] in *.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS. pose proof (ad_fake_res L ALO) as DFR. unfold adisj in DFR.   (* [comment removed for export] *)
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLR. pose proof (ao_res_hi L ALO) as RHI0.
    apply (atls_not_app A B a); [clear -DLR HA HB G6 G7; lia | right; clear -HA G6 RHI0; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; pose proof (ad_ahm_res L ALO) as DA2; unfold adisj in DA2; clear -CH OAH DA2 Ha HA HB G6 G7; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
  - clear -C Ha HB G5 HHI. lia.
  - clear -C Ha HA G4. lia.
  - (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
    destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(b & Hb & Sb & Q1 & Q2)|(mb & ms & n0 & _ & SW & Q1 & Q2)].
      * assert (NEQ : c <> xb_class b \/ k <> xb_slot b).
        { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
          destruct (proj1 (In_X_g X stt c k n b1 ctx l1 l2 XB b) Hb) as [Hl| ->]; [| cbn in Sb; exact (NL p Sb)].
          exact (key_fresh_g L st X stt c k n b1 ctx l1 l2 XB WF b Hl (eq_sym EC) (eq_sym EK)). }
        (nd_pre (busy_slot_geo L st X ALO WF b Hb) 3%nat; intros CLB KB _; nd_post).
        pose proof (slots_sep_any L st X c k (xb_class b) (xb_slot b) ALO WF HC CLB KR KB NEQ) as D.
        unfold xb_alloc in Q1, Q2. clear -D Q1 Q2 R Ha HA HB. lia.
      * (nd_pre SW 7%nat; intros _ MLO MCE _ _ _ (_ & _ & SCr & _); nd_post). unfold SEC_UOFF in *. clear -R Ha HA HB Q1 Q2 SCr G6 G7. lia.
    + clear -R Ha HA HB G G6 G7 DFR. lia.
  - clear -C Ha HA HB G6 G7 DFR. lia.
  - clear -C Ha HA G4 S2. lia.
  - clear -C Ha HA G4 S3. lia.
  - assert (SF : shad (al_fake L + 11571200) <= 17594332446720) by (pose proof atop_range as AR; rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    clear -C Ha HA G4 SF. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_static : forall L st X LB HI A B, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  (forall a, A <= a < B -> astatic a) -> 0x10000 <= A -> B <= AIMG_HI ->      (* [comment removed for export] *)
  forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI A B ALO WF BL HHI ST A0 BH a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). pose proof (ST a Ha) as SA.
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF. pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold cprot, astatic, AIMG_HI, AINSTANCE, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { pose proof ATPv_img as TI. apply (atls_not_app a (a + 1) a); [left; clear -TI SA; lia | left; clear -BH Ha; lia | clear; lia]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; clear -CH OAH OAHI Ha BH; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha SA HHI BH OF S1 S2 S3 S4 AR; lia).
  - (nd_pre C 3%nat; intros blk Hin R; nd_post). (pose proof (lb_high L st X LB blk ALO WF BL Hin ltac:(clear -R; lia)) as ndP__; nd_pre ndP__ 3%nat; intros G _ _; nd_post). unfold AIMG_HI in G. clear -R G Ha BH. lia.
  - assert (SF : 2147450880 <= shad (al_fake L)) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF; Z.div_mod_to_equations; lia). clear -C Ha BH SF. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_ptrarr : forall L st X LB HI nres, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  0 <= nres -> 8 * nres <= 8388608 ->
  forall a, al_ptr_array L <= a < al_ptr_array L + 8 * nres -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI nres ALO WF BL HHI N0 N1 a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_ptr L ALO) as OP. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OP, ORS.   (* [comment removed for export] *)
  pose proof (ad_fake_ptr L ALO) as DFP. pose proof (ad_ptr_res L ALO) as DPR. unfold adisj in DFP, DPR. pose proof atop_range as AR.
  assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { pose proof (ad_tls_ptr L ALO) as DLP. unfold adisj in DLP.
    apply (atls_not_app (al_ptr_array L) (al_ptr_array L + 8 * nres) a); [clear -DLP N0 N1; lia | clear -OP N0 N1; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; pose proof (ad_ahm_ptr L ALO) as DA2; unfold adisj in DA2; clear -CH DA2 Ha N0 N1; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha N0 N1 HHI OF OP DFP S1 S2 S3 S4 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n0 & _ & SW & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ Q6 Q7; nd_post). clear -R Ha N0 N1 G1 G2 Q6 Q7 DPR. lia.
    + (nd_pre SW 7%nat; intros _ MLO MCE _ _ _ (_ & _ & _ & SCp & _); nd_post). unfold SEC_UOFF in *. clear -R Ha N0 N1 G1 G2 SCp. lia.
  - clear -R Ha N0 N1 G DFP. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_secmap : forall L st X LB HI mb ms n, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  sec_wf1 L (CSec mb ms n) ->
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb') ->
  forall a, (mb <= a < mb + ms \/ shad mb <= a < shad mb + shlen ms) -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI mb ms n ALO WF BL HHI SW DJ a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS. pose proof atop_range as AR.   (* [comment removed for export] *)
  (nd_pre SW 7%nat; intros MAL MLO MCE MSE NB NPR SCL; nd_post). (pose proof SCL as ndP__; nd_pre ndP__ 8%nat; intros _ _ SCr _ _ _ SCf _; nd_post). unfold ablk, AIMG_HI, KLS in MLO.
  (pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ MSAL _; nd_post). rewrite <- MSE in MSAL.
  assert (SH : shad mb + shlen ms = shad (mb + ms) /\ shad (mb + ms) <= shad ATOP /\ 2148239360 <= shad mb
               /\ ((mb + ms <= 2147446784 /\ shad (mb + ms) <= 2415881728) \/ (K_HIGH_MEM <= mb /\ 2201439137792 <= shad mb))
               /\ (shad (mb + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb) /\ shad (al_fake L + 11571200) <= shad ATOP).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_HIGH_MEM in *. clear -MAL MLO MCE MSAL SCf OF. Z.div_mod_to_equations. lia. }
  (nd_pre SH 6%nat; intros SH1 SH2 SH3 SH4 SH5 SH6; nd_post).
  assert (SF : 2147450880 <= shad (al_fake L)) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ SCtls _; nd_post). pose proof atp_lin as TLN.
    assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
    destruct Ha as [Ha|Ha].
    - apply (atls_not_app mb (mb + ms) a); [clear -SCtls; lia | clear -MLO; lia | exact Ha].
    - intros [T|(a' & Ha' & ->)]; [clear -T Ha TLN SH1 SH2 SH3 S1; lia|].
      (pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSB0; nd_post). rewrite <- MSE in MSB0.
      destruct (tls_shadow_apart a' mb ms Ha' ltac:(clear -MSB0; lia)) as [D|D].
      { destruct SCtls as [D|D]; [right; split; [exact D| exact MAL8]| left; exact D]. }
      + clear -D Ha. lia.
      + clear -D Ha. lia. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SCahm; nd_post); destruct Ha as [Ha|Ha]; clear -CH OAH OAHI SCahm Ha SH1 SH2 SH3 S1; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha MLO MCE HHI OF SCf S1 S2 S3 S4 SH1 SH2 SH3 SH4 SH5 SH6 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb' & ms' & n0 & Lp & SW' & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ Q4 _ Q6 Q7; nd_post). clear -R Ha G1 G2 Q4 Q6 Q7 SCr MLO S1 SH1 SH2 AR. lia.
    + (nd_pre SW' 3%nat; intros _ MLO' _; nd_post). unfold ablk, AIMG_HI, KLS in MLO'. specialize (DJ _ _ _ _ Lp). unfold SEC_UOFF, K_HIGH_MEM in *. clear -R Ha G1 G2 DJ MLO MLO' S1 SH1 SH2 SH3 AR. lia.
  - clear -R Ha G SCf OF MLO S1 SH1 SH2 SH3 SF AR. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_hl : forall L st X LB HI hl, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  ablk hl (hl + 8) -> hl + 8 <= ATOP -> sec_clear L hl 8 ->      (* [comment removed for export] *)
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl) ->
  forall a, hl <= a < hl + 8 -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI hl ALO WF BL HHI K1 K2 SCL HLS a Ha C. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). unfold ablk, AIMG_HI, KLS in K1. pose proof atop_range as AR.
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF. (pose proof SCL as ndP__; nd_pre ndP__ 8%nat; intros _ _ SCr _ _ _ SCf _; nd_post).
  assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  assert (NT : ~ atls_addr a).
  { (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ SCtls _; nd_post).
    apply (atls_not_app hl (hl + 8) a); [clear -SCtls; lia | clear -K1; lia | exact Ha]. }
  destruct C as [CT|C]; [exact (NT CT)|].
  destruct C as [CH|C]; [exfalso; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; rewrite <- (ao_ahm_eq L ALO) in CH; unfold AAHM_SZ in CH; (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SCahm; nd_post); clear -CH SCahm Ha; lia|].
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha K1 K2 HHI OF SCf S1 S2 S3 S4 SF AR; lia).
  (nd_pre C 3%nat; intros blk Hin R; nd_post). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb' & ms' & n0 & Lp & SW' & G1 & G2)].
    + (pose proof (busy_slot_geo L st X ALO WF b Hb) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ Q6 Q7; nd_post). clear -R Ha G1 G2 Q6 Q7 SCr. lia.
    + specialize (HLS _ _ _ _ Lp). clear -R Ha G1 G2 HLS. lia.
  - clear -R Ha G SCf. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma np_cd_W : forall L st X LB HI lo SP c nf mfa mfa', alayout_ok L -> awf L st X -> ablocks L st X LB ->
  1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  ATOP <= lo -> lo <= SP - 688 -> SP <= HI ->
  np_fp L HI LB (cd_W L SP c nf mfa mfa').
Proof.
  intros L st X LB HI lo SP c nf mfa mfa' ALO WF BL HC NF0 NF4 MFA CEIL LO SPH iv Hiv.
  destruct (cd_W_cases L SP c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hiv) as [->|P].
  - cbn [fst snd]. eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - eapply (np_low L st X LB HI c iv); [exact ALO| exact WF| exact BL| exact HC| clear -CEIL LO SPH; lia| exact P].
Qed.

#[using="Type"] Lemma np_rec_W : forall L st X LB HI lo SP c kk n b1 ctx l1 l2 nf mfa mfa', alayout_ok L -> awf L st X -> ablocks L st X LB ->
  x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  ATOP <= lo -> lo <= SP - 688 -> SP <= HI ->
  np_fp L HI LB (rec_W L SP c kk n nf mfa mfa').
Proof.
  intros L st X LB HI lo SP c kk n b1 ctx l1 l2 nf mfa mfa' ALO WF BL XB NF0 NF4 MFA CEIL LO SPH iv Hiv.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hiv) as [->|[SL|P]].
  - cbn [fst snd]. eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - intros a Ha. eapply (np_slot L st X LB HI BQuar c kk n b1 ctx l1 l2 (fst iv) (snd iv));
      [exact ALO| exact WF| exact BL| clear -CEIL LO SPH; lia| exact XB| intros p; discriminate| exact (proj1 SL)| exact (proj2 SL)| exact Ha].
  - eapply (np_low L st X LB HI c iv); [exact ALO| exact WF| exact BL| exact HC| clear -CEIL LO SPH; lia| exact P].
Qed.

#[using="Type"] Lemma np_srec_W : forall L st X LB HI lo SP mb ms n nres hl, alayout_ok L -> awf L st X -> ablocks L st X LB ->
  sec_wf1 L (CSec mb ms n) ->
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb') ->
  ablk hl (hl + 8) -> hl + 8 <= ATOP -> sec_clear L hl 8 ->      (* [comment removed for export] *)
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl) ->
  0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 -> SP <= HI ->
  np_fp L HI LB (srec_W L SP mb ms nres ++ [(hl, hl + 8)]).
Proof.
  intros L st X LB HI lo SP mb ms n nres hl ALO WF BL SW DJ K1 K2 SCL HLS N0 N1 CEIL LO SPH.
  assert (HHI : ATOP <= HI) by (clear -CEIL LO SPH; lia).
  pose proof (alayout_t_lin L ALO) as OT.
  unfold srec_W. cbn [app].
  apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_nil]]]]]]]; cbn [fst snd].
  - eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - eapply (np_low L st X LB HI 1 (al_t L + 2800, al_t L + 3168)); [exact ALO| exact WF| exact BL| unfold K_NUM_CLASSES; clear; lia| exact HHI|].
    unfold lowpiece. cbn [fst snd]. split; [clear -OT; lia|]. split; [clear -OT; lia| right; left; clear; lia].
  - eapply (np_static L st X LB HI); [exact ALO| exact WF| exact BL| exact HHI| intros a Ha; unfold astatic, AINSTANCE in *; clear -Ha; lia| unfold AINSTANCE; clear; lia| unfold AINSTANCE, AIMG_HI; clear; lia].
  - eapply (np_ptrarr L st X LB HI nres); [exact ALO| exact WF| exact BL| exact HHI| exact N0| exact N1].
  - intros a Ha. eapply (np_secmap L st X LB HI mb ms n); [exact ALO| exact WF| exact BL| exact HHI| exact SW| exact DJ| left; exact Ha].
  - intros a Ha. eapply (np_secmap L st X LB HI mb ms n); [exact ALO| exact WF| exact BL| exact HHI| exact SW| exact DJ| right; exact Ha].
  - eapply (np_hl L st X LB HI hl); [exact ALO| exact WF| exact BL| exact HHI| exact K1| exact K2| exact SCL| exact HLS].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cpres_aheap_pres : forall (CI : list (Z * Z)) L HI LB SPc st X m m',
  alayout_ok L -> awf L st X -> ablocks L st X LB ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1808c8 \/ 0x5d0910 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv) /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv) /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  HI <= SPc -> cpres L HI LB m m' -> aheap_pres CI LB SPc m m'.
Proof.
  intros CI L HI LB SPc st X m m' ALO WF BL CI_OK CI_OK2 HS CP a Ha CL. (pose proof shad_consts as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post).
  pose proof (ao_fake L ALO) as OF. unfold aobj in OF.
  assert (E : m' (wa a) = m (wa a)).
  { apply CP. rewrite wa_unsigned by exact Ha. unfold cprot.
    destruct CL as [CL|[TL|[IM|IM]]]; [right; right| left; exact TL| | right; left; exact IM].
    2:{ right; right; right; right; right; right; right; left. unfold AIMSH_LO, AIMSH_LEN in IM. rewrite S3. unfold ASHOFF. clear -IM. lia. }
    destruct CL as [ST | [CIa | [BLK | SHD]]].
    - left. clear -ST HS. lia.
    - right; left. (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. unfold astatic, AINSTANCE in *. clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7. lia.
    - right; right; left. exact BLK.
    - (nd_pre SHD 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). right; right; right; right.
      destruct Ha' as [STa | [CIa | FK]].
      + left. rewrite !shad_div. unfold ASHOFF in *. clear -STa. Z.div_mod_to_equations. lia.
      + right; left. (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 _ Q3 _; nd_post).
        rewrite !shad_div. unfold AIMG_HI, ASHOFF in *. clear -R Q1 Q3. Z.div_mod_to_equations. lia.
      + right; right. (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros F1 F2 F3; nd_post).
        rewrite !shad_div. unfold ASHOFF in *. clear -R F1 F3 OF. Z.div_mod_to_equations. lia. }
  split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw.
Qed.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End ARecGeo.

(* [comment removed for export] *)
Module F_adorec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apopulate. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agetfrom__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arefill__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_arecyc1. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ACdeallocP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition adorec_entry : Z := 0x35e08.
Definition adorec_lout : Z := 0x35e80.     (* [comment removed for export] *)
Definition adorec_lin : Z := 0x35ec0.      (* [comment removed for export] *)
Definition adorec_after : Z := 0x35ed8.    (* [comment removed for export] *)
Definition adorec_chk : Z := 0x35f04.      (* [comment removed for export] *)
End CANSEC1.
Notation DOREC_FRAME := 112 (only parsing).
Notation DOREC_STACK := 1136 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ehdr (L : alayout) (e : achunk * Z) : word := Z_to_bv 64 (qhdr L (fst e) (snd e)).

#[using="Type"] Lemma qhdrs_rev_combine : forall L chs ks, length ks = length chs ->
  map (Z_to_bv 64) (qhdrs L chs ks) = map (ehdr L) (rev (combine chs ks)).
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try reflexivity; try lia.
  rewrite map_app, map_app, IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition esecs (es : list (achunk * Z)) : list achunk := List.filter is_sec (map fst es).
#[using="Type"] Lemma esecs_app : forall a b, esecs (a ++ b) = esecs a ++ esecs b.
Proof. intros. unfold esecs. rewrite map_app. apply List.filter_app. Qed.
#[using="Type"] Lemma esecs_cons_prim : forall c n k es, esecs ((CPrim c n, k) :: es) = esecs es.
Proof. reflexivity. Qed.
#[using="Type"] Lemma esecs_cons_sec : forall mb ms n k es, esecs ((CSec mb ms n, k) :: es) = CSec mb ms n :: esecs es.
Proof. reflexivity. Qed.
#[using="Type"] Lemma esecs_perm : forall a b, Permutation a b -> Permutation (esecs a) (esecs b).
Proof.
  intros a b P. unfold esecs. induction P; cbn; [constructor| | | eapply Permutation_trans; eassumption].
  - destruct (is_sec (fst x)); [apply perm_skip|]; assumption.
  - destruct (is_sec (fst x)), (is_sec (fst y)); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Definition secsT (R : qrconc) : list achunk := esecs (qentries (map fst (qr_tmp R)) (map snd (qr_tmp R))).
Definition inflight (R : qrconc) : list achunk := secsT R ++ esecs (qr_pend R).
(* [comment removed for export] *)
Definition csx (st : astate) (R : qrconc) : list achunk := sec_chunks_of st ++ inflight R.

(* [comment removed for export] *)
Definition qr_popr (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (rev (combine (b_chunks b) (qb_ks q))) (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_popr : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_popr R b q T).
Proof.
  intros L st X R b q T CP ET EB EP. pose proof (qcoupled_rec_pop L st X R b q T CP ET EB EP) as CP1. (pose proof CP1 as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_perm; [exact CP1| exact LN1| exact LN2| | | reflexivity].
  - unfold qr_entries, qr_popr, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pend]. repeat apply Permutation_app_head. apply Permutation_sym. apply Permutation_rev.
  - unfold qr_bslots, qr_popr, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pendb]. apply Permutation_refl.
Qed.

#[using="Type"] Lemma inflight_popr : forall R b q T, qr_tmp R = (b, q) :: T -> qr_pend R = [] -> length (qb_ks q) = length (b_chunks b) ->
  Permutation (inflight (qr_popr R b q T)) (inflight R).
Proof.
  intros R b q T ET EP LEN. unfold inflight, secsT, qr_popr. cbn [qr_tmp qr_pend]. rewrite ET, EP. cbn [map fst snd qentries].
  rewrite esecs_app. replace (esecs []) with (@nil achunk) by reflexivity. rewrite app_nil_r.
  eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply esecs_perm. apply Permutation_sym. apply Permutation_rev.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma do_recycle_cons : forall {RT} st b bs (k : astate -> AM RT),
  do_recycle st (b :: bs) k = recycle_chunks st (rev (b_chunks b)) (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 bs k)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma recycle_chunks_prim : forall {RT} st c n l (k : astate -> AM RT),
  recycle_chunks st (CPrim c n :: l) k = cache_dealloc st c (fun st1 => recycle_chunks st1 l k).
Proof. reflexivity. Qed.
#[using="Type"] Lemma recycle_chunks_sec : forall {RT} st mb ms n l (k : astate -> AM RT),
  recycle_chunks st (CSec mb ms n :: l) k = large_dealloc st mb ms (fun st1 => recycle_chunks st1 l k).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_popr : forall R L st X m b q T,
  AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
     AQdr (qr_popr R b q T) 0 0 L st X m
  /\ abatch_cells L m b q (qfirst L (map snd T))
  /\ Q_BATCH_BYTES <= b_size b /\ qnum_tmp (map fst T).
Proof.
  intros R L st X m b q T (QC & MX & TC & GL & TB & IA & CP & NUM & NT) ET EB EP.
  rewrite ET in TB, NT. cbn [map fst snd] in TB, NT. destruct TB as [BC TB']. pose proof (Forall_inv NT) as NB. pose proof (Forall_inv_tail NT) as NT'. cbn beta in NB.
  split; [| split; [exact BC| split; [exact NB| exact NT']]].
  unfold AQdr, qr_popr. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB'|]. split; [exact IA|].
  split; [exact (qcoupled_rec_popr L st X R b q T CP ET EB EP)|]. split; [exact NUM| exact NT'].
Qed.

#[using="Type"] Lemma AQdr_drop_sec : forall R L st X m mb ms n kk pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CSec mb ms n, kk) :: pend' -> AQdr (qr_drop R pend') 0 0 L st X m.
Proof.
  intros R L st X m mb ms n kk pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [exact (qcoupled_rec_drop_sec L st X R mb ms n kk pend' CP EP)|]. exact (conj NUM NT).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_set_nsec : forall R L st X m v, AQdr R 0 0 L st X m -> AQdr R 0 0 L (set_nsec v st) X m.
Proof.
  intros R L st X m v (QC & MX & TC & GL & TB & IA & CP & NUM & NT). unfold AQdr. cbn.
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  eapply qcoupled_rec_same; [exact CP|]. unfold quar_same. cbn. repeat (split; [reflexivity|]).
  split; intros b Hb; destruct (xb_st b); first [exact I| exact Hb].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_head_geo : forall R L st X m b q T, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T ->
  17594333495296 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= ATOP.
Proof.
  intros R L st X m b q T ALO WF (_ & _ & _ & _ & _ & _ & CP & _) ET.
  (nd_pre (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP ltac:(apply In_qr_bslots; rewrite ET; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
  (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ G4 G5 _; nd_post).
  unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5. unfold abatch_addr. exact (conj G4 G5).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_sec_in' : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof.
  intros st p mb ms n Lp. unfold sec_chunks_of. apply List.filter_In. split; [| reflexivity].
  unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p _ Lp) as P. apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_in; [exact P| left; reflexivity].
Qed.

#[using="Type"] Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; first [apply Z.eq_dec| apply N.eq_dec]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nodup_range_len : forall (l : list Z) (N : nat), List.NoDup l -> Forall (fun k => 0 <= k < Z.of_nat N) l -> (length l <= N)%nat.
Proof.
  intros l N ND HF. rewrite <- (length_seq N 0), <- (length_map Z.of_nat). apply NoDup_incl_length; [exact ND|].
  intros k Hk. pose proof (proj1 (Forall_forall _ _) HF k Hk) as R. cbn beta in R.
  apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_len_bound : forall R L st X m, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> Z.of_nat (length (qr_tmp R)) < 2^32.
Proof.
  intros R L st X m ALO WF (_ & _ & _ & _ & _ & _ & CP & _). (pose proof CP as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ NDB BS _ _; nd_post).
  assert (LEN : (length (qr_bslots R) <= Z.to_nat 458752)%nat).
  { apply nodup_range_len; [exact NDB|]. apply Forall_forall. intros k Hk. (nd_pre (proj1 (BS k) Hk) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
    (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ KR G1 G2 (_ & G3 & _) _; nd_post). unfold xb_alloc, aslot_addr in G1, G2. rewrite Cb, Kb, size_of_class_24 in *.
    unfold K_FREEARR_OFF in G3. rewrite Z2Nat.id by (clear; lia). clear -KR G1 G2 G3. lia. }
  unfold qr_bslots in LEN. rewrite length_app, length_map, !length_app, length_map in LEN. clear -LEN. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AREP_reqs : forall AQ AQ' AS AS' ADp AFp L st X m,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L st X m -> (AS L st X m -> AS' L st X m) -> AREP (mkAHoles AQ' AS' ADp AFp) L st X m.
Proof.
  intros AQ AQ' AS AS' ADp AFp L st X m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) HQ HS.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact HQ|]. split; [exact (HS A7)|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma high_fake : forall L iv, alayout_ok L -> ATOP <= fst iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xa7288 \/ 0xa7288 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
  /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
  /\ (snd iv <= 0x1401b1 \/ 0x1401b1 + 1 <= fst iv) /\ (snd iv <= 0x13e098 \/ 0x13e098 + 4 <= fst iv).
Proof.
  intros L iv ALO HI. pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj in *. pose proof atop_range as AR.   (* [comment removed for export] *)
  assert (SF : shad (al_fake L) + shlen 11571200 <= 17594332446720) by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -OF AR; Z.div_mod_to_equations; lia).
  clear -HI OF OD SF AR. repeat split; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DoRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
(* [comment removed for export] *)
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x1804c8 <= a < 0x5d0510) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.     (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

#[using="ADD"] Lemma SHO : forall R, srec_holes_ok (AQdr R 0 0) AD.
Proof. intros R. split; [intros; eapply AQdr_frameD; eassumption| exact ADD]. Qed.

(* [comment removed for export] *)
Variables (L : alayout) (lo TMP HI : Z) (LB : list ablock) (cbs : word) (RNG0 : footprint) (m0 : amem) (st0 : astate).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Let SP : Z := bv_unsigned sp + -112.
Hypothesis ALO : alayout_ok L.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - DOREC_STACK.
Hypothesis SP47 : bv_unsigned sp <= 2^47.
Hypothesis TMPLO : bv_unsigned sp <= TMP.
Hypothesis TMPHI : TMP + 32 <= 2^47.
Hypothesis HHI : TMP + 32 <= HI.
Hypothesis RSTK0 : rng RNG0 lo (bv_unsigned sp - lo).
Hypothesis RTMP0 : rng RNG0 TMP 32.

(* [comment removed for export] *)
Definition dr_frame (junk8 : list byte) : list cell :=
  [CB 8 junk8; C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition st_keep (st : astate) : Prop :=
     a_live st = a_live st0 /\ a_next st = a_next st0 /\ a_qloc st = a_qloc st0 /\ a_qloc_bytes st = a_qloc_bytes st0
  /\ a_qglob st = a_qglob st0 /\ a_qglob_bytes st = a_qglob_bytes st0 /\ a_nres st = a_nres st0 /\ a_ptr_array st = a_ptr_array st0
  /\ a_space_beg st = a_space_beg st0.

(* [comment removed for export] *)
Definition drinv (R : qrconc) (st : astate) (X : aconc) (RNG : footprint) (m : amem) : Prop :=
     arng L RNG st /\ AREP (AHr R (csx st R)) L st X m /\ ablocks L st X LB /\ AF L LB m
  /\ RSEC (inflight R) RNG /\ mem_inv asegs m /\ stk asegs m lo SP /\ fp_le RNG0 RNG
  /\ munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m /\ cpres L HI LB m0 m /\ st_keep st.

#[using="RSTK0 RTMP0"] Lemma drinv_rngs : forall R st X RNG m, drinv R st X RNG m -> rng RNG lo (bv_unsigned sp - lo) /\ rng RNG TMP 32.
Proof. intros R st X RNG m (_ & _ & _ & _ & _ & _ & _ & FLE & _). split; (eapply rng_fp_le; [exact FLE|]); assumption. Qed.

(* [comment removed for export] *)
Definition thdr (T : list (abatch * qbatchc)) (tb : word) : list cell :=
  [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb].

(* [comment removed for export] *)
Definition ms_in (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (B cnt i : Z) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 700312) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 700376) (Z_to_bv 64 701000) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 cnt)
          (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + cnt)) (Z_to_bv 64 (16 + i)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition batch_ok (R : qrconc) (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) : Prop :=
  qr_tmp R = T /\ qr_pendb R = [kb] /\ Z.of_nat (length all) <= Q_BATCH /\ 0 <= kb.

(* [comment removed for export] *)
#[using="ASECc_disj"] Lemma live_vs_inflight : forall st L X m A Bk mb ms n,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb'.
Proof.
  intros st L0 X m A Bk mb ms n HS p mb' ms' n' Lp. destruct (ASECc_disj _ _ _ _ _ HS) as [ND DJ].
  pose proof (live_sec_in' st p _ _ _ Lp) as INl.
  assert (IN1 : In (CSec mb' ms' n') ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; left; apply in_app_iff; left; exact INl).
  assert (IN2 : In (CSec mb ms n) ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; right; left; reflexivity).
  assert (NE : CSec mb' ms' n' <> CSec mb ms n).
  { intros E. rewrite E in INl. apply (List.NoDup_remove_2 _ _ _ ND). apply in_app_iff. left. apply in_app_iff. left. exact INl. }
  destruct (DJ _ _ IN1 IN2 NE) as [D|D]; cbn [sec_mb sec_ms] in D; [left| right]; exact D.
Qed.

#[using="ASECc_disj"] Lemma live_vs_hl : forall st L X m A Bk mb ms n hl,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ Bk) /\ sec_wf1 L (CSec (hl - 24) lms ln))) ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl.
Proof.
  intros st L0 X m A Bk mb ms n hl HS HIN p mb' ms' n' Lp. destruct (ASECc_disj _ _ _ _ _ HS) as [ND DJ].
  pose proof (live_sec_in' st p _ _ _ Lp) as INl.
  assert (IN1 : In (CSec mb' ms' n') ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; left; apply in_app_iff; left; exact INl).
  unfold SEC_UOFF. destruct HIN as [[H1 H2]|(lms & ln & INh & SWh)].
  - destruct (live_vs_inflight st L0 X m A Bk mb ms n HS p mb' ms' n' Lp) as [D|D]; [right; clear -D H1; lia| left; clear -D H2; lia].
  - assert (IN2 : In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)).
    { apply in_app_iff in INh. apply in_app_iff. destruct INh as [H|H]; [left; exact H| right; right; exact H]. }
    destruct (achunk_eq_dec' (CSec mb' ms' n') (CSec (hl - 24) lms ln)) as [E|NE].
    + injection E as -> -> ->. left. clear. lia.
    + (nd_pre SWh 7%nat; intros _ _ _ MSE NB NPR _; nd_post).
      (pose proof (sec_facts ln ltac:(unfold AREQMAX in *; clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSB; nd_post). rewrite <- MSE in MSB.
      destruct (DJ _ _ IN1 IN2 NE) as [D|D]; cbn [sec_mb sec_ms] in D; [right; clear -D; lia| left; clear -D MSB; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="HL SREC ADD AFD ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Lemma dr_inner : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (es : list (achunk * Z)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) (i : Z) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  drinv R st X RNG m -> batch_ok R kb all T -> qr_pend R = es -> es = skipn (Z.to_nat i) all -> es <> [] -> 0 <= i ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  u64arr asegs m (abatch_addr L kb + 24) (map (ehdr L) all) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_drop R []) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_in adorec_after rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (abatch_addr L kb) (Z.of_nat (length all)) (Z.of_nat (length all)) m1)) ->
  implS asegs RNG (aembed ATOP (recycle_chunks st (map fst es) K)) (epostF Q)
        (ms_in adorec_lin rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (abatch_addr L kb) (Z.of_nat (length all)) i m).
Proof.
  intros RT Q es. induction es as [|e es IH]; intros K R st X RNG m kb all T i tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    INV BOK EP ES NE I0 FR TH ARR KONT; [congruence|].
  (pose proof INV as ndP__; nd_pre ndP__ 11%nat; intros ARNG AR BL HF RS MI ST FLE MU0 CP0 SK; nd_post). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  (nd_pre BOK 4%nat; intros ET EB ALLB KB0; nd_post).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR). unfold Q_BATCH in ALLB.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  assert (IL : i < Z.of_nat (length all)).
  { destruct (Z.lt_ge_cases i (Z.of_nat (length all))) as [H|H]; [exact H| exfalso]. rewrite skipn_all2 in ES by lia. discriminate. }
  assert (NTH : nth_error (map (ehdr L) all) (Z.to_nat i) = Some (ehdr L e)).
  { rewrite nth_error_map. replace (nth_error all (Z.to_nat i)) with (nth_error (skipn (Z.to_nat i) all) 0) by (rewrite nth_error_skipn, Nat.add_0_r; reflexivity).
    rewrite <- ES. reflexivity. }
  set (B := abatch_addr L kb) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & _).
  (nd_pre (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) 6%nat; intros nb bb1 bctx bl1 bl2 XBB; nd_post).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  (nd_pre BG 9%nat; intros _ _ BG1 BG2 (BG3a & BG3 & BG3b) BG4 BG5 BG6 BG7; nd_post).
  pose proof (u64arr_read asegs m (B + 24) _ i (ehdr L e) (wa (B + 152 + 8 * i + -128)) ARR NTH I0 ltac:(f_equal; lia)) as RDV.
  assert (RB24 : rng RNG (B + 152 + 8 * i + -128) 8).
  { (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post).
    destruct (RCLS K_BATCH_CLASS (K24)) as (R1 & _). eapply rng_sub; [exact R1| |]; clear -BG1 BG2 BG3 I0 IL ALLB; lia. }
  unfold ms_in, adorec_lin. iprefix.
  step.                                     (* [comment removed for export] *)
  clear RDV RB24.
  zstep.                                    (* [comment removed for export] *)
  step.                                     (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 2%nat CBC CBR. clear CB8 CBR.
  (* [comment removed for export] *)
  assert (POSTK : forall stX X' RNG' m' (W : list (Z * Z)) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    fp_le RNG RNG' -> munch W m m' -> mem_inv asegs m' -> stk asegs m' lo SP ->
    (forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SP) \/ (forall b, In b (x_busy X') -> xb_st b = BBatch -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP) ->
    np_fp L HI LB W -> fake_untouched L W -> (AF L LB m -> AF L LB m') ->
    AREP (AHr (qr_drop R es) (csx stX (qr_drop R es))) L stX X' m' -> arng L RNG' stX ->
    (forall b, In b (x_busy X') -> In b (x_busy X)) -> (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')) ->
    a_live stX = a_live st -> a_next stX = a_next st -> a_qloc stX = a_qloc st -> a_qloc_bytes stX = a_qloc_bytes st ->
    a_qglob stX = a_qglob st -> a_qglob_bytes stX = a_qglob_bytes st -> a_nres stX = a_nres st -> a_ptr_array stX = a_ptr_array st -> a_space_beg stX = a_space_beg st ->
    RSEC (inflight (qr_drop R es)) RNG' ->
    implS asegs RNG' (aembed ATOP (recycle_chunks stX (map fst es) K)) (epostF Q)
          (MS (mkR (Z_to_bv 64 220876) (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 TMP) (Z_to_bv 64 700312) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 700376) (Z_to_bv 64 701000) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 (Z.of_nat (length all)))
                   (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + Z.of_nat (length all))) (Z_to_bv 64 (16 + i)) s10 s11 t3' t4' t5' t6')
              F (ret_pc (Z_to_bv 64 220876)) fc None m' (seg_rom asegs))).
  { intros stX X' RNG' m' W t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    intros FPLE MU MI' ST' WK NP FU HF' AR' ARNG' XS XL L1 L2 L3 L4 L5 L6 L8 L9 L10 RS'. (try pose proof atop_range as ATR).
    replace (ret_pc (Z_to_bv 64 220876)) with (Z_to_bv 64 220876 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof AR' as AR1. (nd_pre AR1 7%nat; intros WF' _ _ _ _ HQ' _; nd_post). cbn [ah_quar AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr] in HQ'.
    (nd_pre (pendb_busy L stX X' (qr_drop R es) m' kb HQ' EB) 6%nat; intros nb' bb1' bctx' bl1' bl2' XBB'; nd_post).
    assert (INB : In (bany BBatch K_BATCH_CLASS kb nb' bb1' bctx') (x_busy X')) by (rewrite XBB'; apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (DJF : disjoint_from W SP 112).
    { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; exact H2| left; clear -HI' CEIL LO SPE; lia]. }
    assert (DJT : disjoint_from W TMP 32).
    { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; clear -H2 TMPLO SPE; lia| left; clear -HI' CEIL LO TMPLO SPE; lia]. }
    assert (DJB : disjoint_from W (B + 24) (8 * Z.of_nat (length (map (ehdr L) all)))).
    { rewrite length_map. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(HB & _ & _)].
      - right. clear -H1 BG5 CEIL LO SPE ALLB. lia.
      - specialize (HB _ INB eq_refl). unfold xb_alloc in HB. cbn [xb_class xb_slot bany] in HB. rewrite size_of_class_24 in HB. fold B in HB.
        clear -HB ALLB. lia. }
    pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'. pose proof (u64arr_frameD _ _ _ _ _ ARR MU DJB) as ARR'.
    assert (INV' : drinv (qr_drop R es) stX X' RNG' m').
    { unfold drinv. split; [exact ARNG'|]. split; [exact AR'|].
      split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
      split; [exact (HF' HF)|]. split; [exact RS'|]. split; [exact MI'|]. split; [exact ST'|].
      split; [intros b j Hb; apply FPLE, FLE, Hb|].
      split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. (nd_pre Hx 3%nat; intros Hx1 Hx2 _; nd_post).
               apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & HZ & HI')]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ HI' CEIL LO SPR SPE; lia]. }
      split; [eapply cpres_trans; [exact CP0| eapply cpres_of_munch; [exact MU| exact NP]]|].
      (nd_pre SK 9%nat; intros K1 K2 K3 K4 K5 K6 K7 K8 K9; nd_post). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
      repeat (split; [assumption|]). exact K9. }
    iprefix.
    zstep. zstep.                           (* [comment removed for export] *)
    setreg 25%Z (Z_to_bv 64 (16 + (i + 1))) ltac:(f_equal; clear; lia).
    setreg 23%Z (Z_to_bv 64 (B + 152 + 8 * (i + 1))) ltac:(f_equal; clear; lia).
    step. if_cases KB; zify_cond KB.        (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (NE' : es <> []).
      { intros ->. apply KB. assert (LEN1 : length (skipn (Z.to_nat i) all) = 1%nat) by (rewrite <- ES; reflexivity). rewrite length_skipn in LEN1. clear -LEN1 IL I0. lia. }
      apply evtF_done.
      eapply (IH K (qr_drop R es) stX X' RNG' m' kb all T (i + 1) tb); try eassumption;
        try lazymatch goal with
        | |- batch_ok _ _ _ _ => unfold batch_ok; rewrite <- ET, <- EB; unfold qr_drop; cbn; repeat split; try reflexivity; assumption
        | |- qr_pend _ = _ => reflexivity
        | |- es = _ => replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by (clear -I0; lia); rewrite <- skipn_skipn, <- ES; reflexivity
        | |- 0 <= _ => clear -I0; lia
        end.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (E0 : es = []).
      { destruct es as [|e2 es2]; [reflexivity| exfalso].
        assert (LEN1 : (2 <= length (skipn (Z.to_nat i) all))%nat) by (rewrite <- ES; cbn; lia). rewrite length_skipn in LEN1. clear -LEN1 IL I0 KB. lia. }
      subst es. cbn [map recycle_chunks].
      apply evtF_done. replace (i + 1) with (Z.of_nat (length all)) by (clear -KB; lia).
      eapply KONT; [exact INV'| exact FR'| exact TH']. }
  (* [comment removed for export] *)
  destruct e as [ch kk]. destruct ch as [c n| mb ms n]; cbn [map fst]; [rewrite recycle_chunks_prim| rewrite recycle_chunks_sec].
  - (* [comment removed for export] *)
    eapply arecyc1; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rw_cells _ _ _ _ => exact CBC
      | |- bv_unsigned _ <= _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear; lia
      | |- _ + 16 <= _ => clear -SP47 CEIL LO SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- rng _ _ 16 => eapply rng_sub; [exact RSTK| clear -CEIL LO SPE; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros stX X' RNG' ms' RET.
    (nd_pre RET 19%nat; intros FPLE t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mfa' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 23%nat; intros MU WM MI' ST' MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC MU1 AU1 XS XL; nd_post).
    rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia).
    pose proof AR as AR1. destruct AR1 as (WF0 & _).
    (nd_pre (pend_head_busy L st X R m c n kk es ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EP) 5%nat; intros b1 ctx l1 l2 XB; nd_post).
    (pose proof WF0 as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC c (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0))) 7%nat; intros _ _ _ _ A5 A6 _; nd_post).
    eapply (POSTK stX X' RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact ST'| | | | | | exact ARNG'| exact XS| exact XL| exact L1| exact L2| exact L3| exact L4| exact L5| exact L6| exact L8| exact L9| exact L10|].
    + (* [comment removed for export] *)
      intros iv Hiv. destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 _ _ mfa' iv ALO WF0 XB A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [E|[SL|LP]].
      * left. subst iv. cbn [fst snd]. clear -CEIL LO SPE. lia.
      * right. split; [| split; [(nd_pre (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) 7%nat; intros _ _ _ _ _ G4 _; nd_post); unfold xb_alloc in G4; cbn [xb_class xb_slot bany] in G4; clear -G4 SL; lia|]].
        -- intros b Hb Sb. pose proof (XS b Hb) as HbX.
           assert (NEQ : c <> xb_class b \/ kk <> xb_slot b).
           { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
             apply (In_X_g X BQuar c kk n b1 ctx l1 l2 XB) in HbX. destruct HbX as [Hl| ->]; [| cbn in Sb; discriminate].
             exact (key_fresh_g L st X BQuar c kk n b1 ctx l1 l2 XB WF0 b Hl (eq_sym EC) (eq_sym EK)). }
           (nd_pre (busy_slot_geo L st X ALO WF0 b (XS b Hb)) 3%nat; intros CLB KBb _; nd_post).
           pose proof (slots_sep_any L st X c kk (xb_class b) (xb_slot b) ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) CLB
                         (proj2 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) KBb NEQ) as D.
           unfold xb_alloc. clear -D SL. lia.
        -- (nd_pre (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) 8%nat; intros _ _ _ _ _ _ G5 _; nd_post).
           unfold xb_alloc in G5. cbn [xb_class xb_slot bany] in G5. clear -G5 SL. lia.
      * right. split; [| exact (conj (proj1 LP) (proj1 (proj2 LP)))]. intros b Hb _. exact (lowpiece_vs_slot L st X c b iv ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) (XS b Hb) LP).
    + (* [comment removed for export] *)
      eapply (np_rec_W L st X LB HI lo SP c kk n b1 ctx l1 l2); [exact ALO| exact WF0| exact BL| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + intros HF0. eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF0| exact MU| exact WM|].
      eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + (* [comment removed for export] *)
      replace (csx stX (qr_drop R es)) with (csx st R); [exact AR'|].
      unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite EP, esecs_cons_prim, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity.
    + unfold inflight, secsT, qr_drop in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP, esecs_cons_prim in RS. eapply RSEC_mono'; [exact FPLE| exact RS].
  - (* [comment removed for export] *)
    pose proof AR as AR1. (nd_pre AR1 8%nat; intros WF0 _ _ _ _ HQ0 HS0 _; nd_post). cbn [ah_quar ah_sec AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr] in HQ0, HS0.
    assert (CSE : csx st R = (sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es).
    { unfold csx, inflight. rewrite EP, esecs_cons_sec, app_assoc. reflexivity. }
    pose proof (ASECc_wf1 _ _ _ _ _ HS0) as WF1. rewrite CSE in WF1. apply Forall_app in WF1. destruct WF1 as [_ WF1]. pose proof (Forall_inv WF1) as SW.
    pose proof (ASECc_nres _ _ _ _ _ HS0) as [NR0 NR1].
    rewrite CSE in AR, HS0.
    assert (RSC : RSEC ((sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es) RNG).
    { apply (proj2 (RSEC_app _ _ _)). split; [apply (proj2 (RSEC_app _ _ _)); split; [exact (RSEC_arng _ _ _ ARNG)|]|];
        unfold inflight in RS; rewrite EP, esecs_cons_sec in RS; apply (proj1 (RSEC_app _ _ _)) in RS; destruct RS as [RS1 RS2]; [exact RS1|].
      exact RS2. }
    eapply (SREC (AQdr R 0 0) AD AF (sec_chunks_of st ++ secsT R) (esecs es) _ (fun st1 => recycle_chunks st1 (map fst es) K) Q L RNG);
      try lazymatch goal with
      | |- srec_holes_ok _ _ => exact (SHO R)
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- RSEC _ _ => exact RSC
      | |- AREP _ _ _ _ _ => exact AR
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- bv_unsigned _ <= 2 ^ 47 => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -SP47 SPE CEIL LO; lia
      | |- 4096 <= bv_unsigned _ => rewrite unsigned_lit by (clear; lia); clear; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros st' RNG' ms' SR. unfold srec_ret in SR.
    (nd_pre SR 18%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' hl ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros STE HLOK HLIN MU MI' STK' AR' FS ARNG' RS'; nd_post).
    rewrite unsigned_lit in MU, STK' by (clear -SPR CEIL LO SPE; lia). subst st'.
    pose proof (fstepS_le _ _ _ _ FS) as FPLE.
    assert (AR'' : AREP (AHr (qr_drop R es) (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es))) L (set_nsec (a_nsec st - 1) st) X m').
    { replace (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es)) with ((sec_chunks_of st ++ secsT R) ++ esecs es).
      2:{ unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st) eq_refl eq_refl eq_refl), app_assoc. reflexivity. }
      unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr. eapply AREP_reqs; [exact AR'| | intros HS1; exact HS1].
      (nd_pre AR' 7%nat; intros _ _ _ _ _ HQ1 _; nd_post). cbn [ah_quar] in HQ1. eapply AQdr_drop_sec; [exact HQ1| exact EP]. }
    pose proof (live_vs_inflight st L X m _ _ mb ms n HS0) as DJ. pose proof (live_vs_hl st L X m _ _ mb ms n hl HS0 HLIN) as HLS.
    (nd_pre HLOK 3%nat; intros HK1 HK2 HK3; nd_post).
    eapply (POSTK (set_nsec (a_nsec st - 1) st) X RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact STK'| | | | | exact AR''| exact ARNG'| intros b Hb; exact Hb| intros b p Hb _; exact Hb
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity|].
    + intros iv Hiv. destruct (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv) as [WK _].
      destruct WK as [WK|(WB & WZ & WC)]; [left; exact WK| right]. split; [intros b Hb _; exact (WB b Hb)| exact (conj WZ WC)].
    + eapply (np_srec_W L st X LB HI lo SP mb ms n (a_nres st) hl); [exact ALO| exact WF0| exact BL| exact SW| exact DJ| exact HK1| exact HK2| exact HK3| exact HLS| exact NR0| exact NR1
        | atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + apply fake_untouched_of. intros iv Hiv.
      exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
    + intros HF0. eapply AFD; [exact HF0| exact MU| |].
      * apply fake_untouched_of. intros iv Hiv.
        exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
      * apply Forall_forall. intros iv Hiv. exact (srec_W_t48 L st X lo SP mb ms n (a_nres st) hl iv ALO SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv).
    + unfold inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. apply (proj1 (RSEC_app _ _ _)) in RS'. destruct RS' as [RS3 RS4].
      apply (proj1 (RSEC_app _ _ _)) in RS3. destruct RS3 as [_ RS3]. apply (proj2 (RSEC_app _ _ _)). split; [exact RS3| exact RS4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms_out (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 : word) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 700312) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 700376) (Z_to_bv 64 701000) xs4 (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition dr_after__stmt : Prop := forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (KK : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (T : list (abatch * qbatchc)) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [kb] -> qr_pend R = [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_unbatch R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (KK st1)) (epostF Q)
           (ms_out adorec_chk rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS KK)) (epostF Q)
        (ms_out adorec_after rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Section Zd1.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 0).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 1).
Variable KK : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 2).
Variable R : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 3).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 4).
Variable X : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 5).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 7).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 8).
Variable T : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 9).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 10).
Variable junk8 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 11).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 12).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 13).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 14).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 15).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 16).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 17).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 18).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 19).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 20).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 21).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 22).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 23).
Variable xs6 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 24).
Variable xs7 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 25).
Variable xs8 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 26).
Variable xs9 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 31).
Let B := abatch_addr L kb.
#[using="HL RSEC_mono' ALO CEIL LO TMPLO HHI RSTK0 RTMP0 B"] Lemma dr_after__body : ltac:(let T := type of (fun (h : dr_after__stmt) => h RT Q KK R st X RNG m kb T tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (Q, (KK, (R, (st, (X, (RNG, (m, (kb, (T, (tb, (junk8, (rax, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (xs6, (xs7, (xs8, (xs9, (t3, (t4, (t5, t6)))))))))))))))))))))))))))))))) as _.
  intros INV ET EB EP FR TH KONT.
  (pose proof INV as ndP__; nd_pre ndP__ 11%nat; intros ARNG AR BL HF RS MI ST FLE MU0 CP0 SK; nd_post). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. (nd_pre AR0 4%nat; intros WF _ INST _; nd_post). pose proof (proj1 INST) as ISB. change (AINSTANCE + 32) with 700344 in ISB.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SB1 SB2 _ SB4; nd_post).
  chg (abatch_addr L kb) B.
  (* [comment removed for export] *)
  (nd_pre (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) 6%nat; intros nb bb1 bctx bl1 bl2 XBB; nd_post).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  (nd_pre BG 9%nat; intros _ _ BG1 BG2 (BG3a & BG3 & BG3b) BG4 BG5 BG6 BG7; nd_post).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; clear; lia).
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (RI8 : rng RNG 700344 8) by (destruct ARNG as (R1 & _); eapply rng_sub; [exact R1| clear; lia| clear; lia]).
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 1%nat CBC CBR. clear CB8 CBR.
  unfold ms_out, adorec_after. iprefix.
  step.                                                    (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear -BG4 BG5 SB4 CEIL; lia); [exfalso; clear -K1 BG1 BG3a; lia|].   (* [comment removed for export] *)
  zstep.                                                   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear -BG4 BG5 SB1 SB2 SB4 CEIL; lia); [exfalso; clear -K2 BG2 BG3 BG3b; lia|].   (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  zstep. zstep. zstep.                                     (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 K_BATCH_CLASS) ltac:(f_equal; replace (B - al_space_beg L) with (24 * 4294967296 + (B - aregion L K_BATCH_CLASS)) by (clear -ER24; lia);
                                          symmetry; unfold K_BATCH_CLASS in *; apply class_of_offset; [clear; lia| change (2^32) with 4294967296; clear -BG1 BG2 BG3; lia]).
  step. step.                                              (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  apply evtF_done.
  eapply acdealloc24; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pendb _ = _ => exact EB
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
  intros stX X' RNG' ms' RET.
  (nd_pre RET 19%nat; intros FPLE t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mfa' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 21%nat; intros MU WM MI' ST' MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC XS XL; nd_post).
  rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia). (try pose proof atop_range as ATR).
  replace (ret_pc (Z_to_bv 64 220932)) with (Z_to_bv 64 220932 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 7%nat; intros _ _ _ _ A5 A6 _; nd_post).
  assert (WK : forall iv, In iv (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') ->
                          (lo <= fst iv /\ snd iv <= SP) \/ (0 <= fst iv /\ snd iv <= ATOP)).
  { intros iv Hiv. destruct (cd_W_cases L SP K_BATCH_CLASS _ _ mfa' iv ALO (K24) A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [->|(P0 & P1 & _)];
      [left; cbn [fst snd]; clear -LO SPE; lia| right; exact (conj P0 P1)]. }
  assert (DJF : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') SP 112).
  { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; exact H2| left; clear -H2 CEIL LO SPE; lia]. }
  assert (DJT : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') TMP 32).
  { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; clear -H2 TMPLO SPE; lia| left; clear -H2 CEIL LO TMPLO SPE; lia]. }
  pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'.
  assert (INV' : drinv (qr_unbatch R) stX X' RNG' m').
  { unfold drinv. split; [exact ARNG'|].
    split. { replace (csx stX (qr_unbatch R)) with (csx st R); [exact AR'|].
             unfold csx, inflight, secsT, qr_unbatch. cbn [qr_tmp qr_pend]. rewrite EP, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity. }
    split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
    split. { eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF| exact MU| exact WM|].
             eapply (cd_W_fake L lo); [exact ALO| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia]. }
    split. { unfold inflight, secsT, qr_unbatch in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP in RS. eapply RSEC_mono'; [exact FPLE| exact RS]. }
    split; [exact MI'|]. split; [exact ST'|]. split; [intros b j Hb; apply FPLE, FLE, Hb|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. (nd_pre Hx 3%nat; intros Hx1 Hx2 _; nd_post).
             apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[HZ H2]]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ H2 CEIL LO SPR SPE; lia]. }
    split. { eapply cpres_trans; [exact CP0|]. eapply cpres_of_munch; [exact MU|].
             eapply (np_cd_W L st X LB HI lo SP); [exact ALO| exact WF| exact BL| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia]. }
    (nd_pre SK 9%nat; intros K1' K2' K3 K4 K5 K6 K7 K8 K9; nd_post). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
    repeat (split; [assumption|]). exact K9. }
  iprefix. apply evtF_done.
  eapply KONT; [exact INV'| exact FR'| exact TH'].
Qed.
End Zd1.
#[using="HL RSEC_mono' ALO CEIL LO TMPLO HHI RSTK0 RTMP0"] Lemma dr_after : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (KK : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (T : list (abatch * qbatchc)) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [kb] -> qr_pend R = [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_unbatch R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (KK st1)) (epostF Q)
           (ms_out adorec_chk rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS KK)) (epostF Q)
        (ms_out adorec_after rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof. exact dr_after__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="rc sp SP"] Lemma map_fst_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

#[using="Type"] Lemma qlast_cons_ne : forall q (qs : list qbatchc), qs <> [] -> qlast L (q :: qs) = qlast L qs.
Proof.
  intros q qs NE. unfold qlast, qaddrs. cbn [map]. destruct qs as [|q' qs']; [congruence|]. cbn [map]. 
  generalize (abatch_addr L (qb_slot q')) (map (fun q0 : qbatchc => abatch_addr L (qb_slot q0)) qs'). clear. intros a l. revert a. induction l; intros; reflexivity.
Qed.

Definition qr_done (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) [] [] [] (qr_qpend R).

#[using="HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Lemma dr_outer : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (T : list (abatch * qbatchc)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (tb : word) junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] -> T <> [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' (tb' : word) rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_out 0x35f0c rax' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (do_recycle st (map fst T) K)) (epostF Q)
        (ms_out adorec_lout rax t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length T))) a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof.
  intros RT Q T. induction T as [|[b q] T IH]; intros K R st X RNG m tb junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6
    INV ET EB EP NE FR TH KONT; [congruence|].
  (pose proof INV as ndP__; nd_pre ndP__ 11%nat; intros ARNG AR BL HF RS MI ST FLE MU0 CP0 SK; nd_post). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. (nd_pre AR0 8%nat; intros WF _ _ _ _ HQ HS _; nd_post). cbn [ah_quar ah_sec AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr] in HQ, HS.
  (* [comment removed for export] *)
  (nd_pre (AQdr_popr R L st X m b q T HQ ET EB EP) 4%nat; intros HQ1 BC SZB NTT; nd_post).
  (nd_pre BC 6%nat; intros CC EC JC CCNT CLEN CRNG; nd_post).
  set (R1 := qr_popr R b q T) in *.
  set (B := abatch_addr L (qb_slot q)) in *.
  set (all := rev (combine (b_chunks b) (qb_ks q))).
  assert (LALL : Z.of_nat (length all) = b_count b) by (subst all; rewrite length_rev, length_combine, CLEN, Nat.min_id; lia).
  assert (MALL : map fst all = rev (b_chunks b)) by (subst all; rewrite map_rev, map_fst_combine by exact CLEN; reflexivity).
  rewrite (qhdrs_rev_combine L _ _ CLEN) in EC. fold all in EC.
  assert (PCS : Permutation (csx st R) (csx st R1)).
  { unfold csx. apply Permutation_app_head. apply Permutation_sym. subst R1. apply inflight_popr; [exact ET| exact EP| exact CLEN]. }
  assert (AR1 : AREP (AHr R1 (csx st R1)) L st X m).
  { unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr. eapply AREP_reqs; [exact AR| exact HQ1| intros HS'; eapply ASECc_perm; [exact PCS| exact HS']]. }
  assert (INV1 : drinv R1 st X RNG m).
  { unfold drinv. split; [exact ARNG|]. split; [exact AR1|]. split; [exact BL|]. split; [exact HF|].
    split; [eapply RSEC_perm'; [| exact RS]; apply Permutation_sym; subst R1; apply inflight_popr; [exact ET| exact EP| exact CLEN]|].
    split; [exact MI|]. split; [exact ST|]. split; [exact FLE|]. split; [exact MU0|]. split; [exact CP0| exact SK]. }
  (* [comment removed for export] *)
  (nd_pre (pendb_busy L st X R1 m (qb_slot q) HQ1 eq_refl) 6%nat; intros nb bb1 bctx bl1 bl2 XBB; nd_post).
  destruct (any_range L st X BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx bl1 bl2 XBB WF) as [_ KQ].
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  (nd_pre BG 9%nat; intros _ _ BG1 BG2 (BG3a & BG3 & BG3b) BG4 BG5 BG6 BG7; nd_post).
  assert (RB : rng RNG B 24).
  { (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _). eapply rng_sub; [exact RR1| |]; clear -BG1 BG2 BG3; unfold K_FREEARR_OFF; lia. }
  (try pose proof atop_range as ATR). unfold Q_BATCH in CRNG.
  pose proof (tmp_len_bound R1 L st X m ALO WF HQ1) as TLEN. subst R1. cbn [qr_tmp qr_popr] in TLEN. set (R1 := qr_popr R b q T) in *.
  (* [comment removed for export] *)
  assert (QF : (T = [] /\ qfirst L (map snd T) = 0) \/ (T <> [] /\ 17594333495296 <= qfirst L (map snd T) /\ qfirst L (map snd T) + 8192 <= ATOP)).   (* [comment removed for export] *)
  { destruct T as [|[b' q'] T']; [left; split; reflexivity| right]. split; [discriminate|].
    pose proof (tmp_head_geo R1 L st X m b' q' T' ALO WF HQ1 eq_refl) as G. (try pose proof atop_range as ATR). unfold qfirst, qaddrs. cbn [map hd]. exact G. }
  (* [comment removed for export] *)
  assert (REST : forall m2 rax2 (a1x : word),
    munch [(TMP, TMP + 32)]%Z m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo SP -> munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m2 ->
    rw_cells asegs m2 SP (dr_frame junk8) ->
    rw_cells asegs m2 TMP [C8 (Z_to_bv 64 (Z.of_nat (S (length T)))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb] ->
    rw_cells asegs m2 B [C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))] ->
    evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (do_recycle st (b :: map fst T) K)) (epostF Q) ms')
         (MS (mkR rax2 (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 700312) (Z_to_bv 64 (Z.of_nat (S (length T)))) a1x a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 700376) (Z_to_bv 64 701000) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35e94) fc None m2 (seg_rom asegs))).
  { intros m2 rax2 a1x MUp WMp MI2 ST2 MU02 FR2 TH2 CC2. unfold dr_frame in FR2.
    zstep.                                                 (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (Z.of_nat (length T))) ltac:(f_equal; clear; lia).
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AR2 : AREP (AHr R1 (csx st R1)) L st X mx);
      [ eapply (AREP_frame_ext _ (HL R1 (csx st R1)) L st X m mx); [exact ALO| exact AR1| exact MUp| exact WMp|];
        constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO TMPLO; lia |];
      assert (HF2 : AF L LB mx);
      [ eapply AFD; [exact HF| exact MUp| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO| cbn [fst]; atop_facts; clear -CEIL LO TMPLO; lia]
        | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO TMPLO; lia] |];
      assert (CP2 : cpres L HI LB m0 mx);
      [ eapply cpres_trans; [exact CP0|]; eapply cpres_of_munch; [exact MUp|]; intros iv [<-|[]]; cbn [fst snd];
        eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO TMPLO; lia| exact HHI] |];
      assert (INV2 : drinv R1 st X RNG mx);
      [ unfold drinv; (nd_pre INV1 6%nat; intros _ _ _ _ RS1 _; nd_post); split; [exact ARNG|]; split; [exact AR2|]; split; [exact BL|]; split; [exact HF2|]; split; [exact RS1|];
        split; [assumption|]; split; [assumption|]; split; [exact FLE|]; split; [assumption|]; split; [exact CP2| exact SK] |];
      assert (EC2 : u64arr asegs mx (B + 24) (map (ehdr L) all));
      [ eapply (u64arr_frameD _ _ _ _ _ EC MUp); rewrite length_map; cbn [disjoint_from fst snd]; split; [left; clear -LALL CRNG BG5 CEIL LO TMPLO; lia| exact I] |]
    end.
    step.                                                  (* [comment removed for export] *)
    rewrite do_recycle_cons, <- MALL.
    step. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear -CRNG; lia).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      assert (E0 : all = []) by (destruct all; [reflexivity| exfalso; cbn [length] in LALL; clear -LALL KC; lia]).
      rewrite E0. cbn [map recycle_chunks].
      apply evtF_done.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) R1 st X RNG _ (qb_slot q) T);
        [exact INV2| reflexivity| reflexivity| subst R1; unfold qr_popr; cbn [qr_pend]; fold all; exact E0| eassumption| eassumption|].
      intros st4 X4 RNG4 m4 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV4 FR4 TH4.
      (pose proof INV4 as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ MI4 ST4 FLE4 MU04 _; nd_post). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4].
    - (* [comment removed for export] *)
      assert (NEA : all <> []) by (intros E0; apply KC; rewrite <- LALL, E0; reflexivity).
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      setreg 23 (Z_to_bv 64 (B + 152 + 8 * 0)) ltac:(f_equal; clear; lia).
      setreg 24 (Z_to_bv 64 (16 + Z.of_nat (length all))) ltac:(f_equal; clear -LALL; lia).
      setreg 25 (Z_to_bv 64 (16 + 0)) ltac:(f_equal; clear; lia).
      rewrite <- LALL.
      apply evtF_done.
      eapply (dr_inner Q all (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 (map fst T) K)) R1 st X RNG _ (qb_slot q) all T 0);
        [exact INV2| | reflexivity| reflexivity| exact NEA| clear; lia| eassumption| eassumption| eassumption|].
      { unfold batch_ok. subst R1. unfold qr_popr. cbn [qr_tmp qr_pendb]. split; [reflexivity|]. split; [reflexivity|]. unfold Q_BATCH. split; [clear -LALL CRNG; lia| clear -KQ; lia]. }
      intros st3 X3 RNG3 m3 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV3 FR3 TH3.
      unfold ms_in.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) (qr_drop R1 []) st3 X3 RNG3 m3 (qb_slot q) T);
        [exact INV3| reflexivity| reflexivity| reflexivity| exact FR3| exact TH3|].
      intros st4 X4 RNG4 m4 junk8'' rax'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' INV4 FR4 TH4.
      (pose proof INV4 as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ MI4 ST4 FLE4 MU04 _; nd_post). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8'');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4]. }
  (* [comment removed for export] *)
  unfold ms_out, adorec_lout. unfold thdr in TH. cbn [length map snd qfirst qaddrs hd] in TH. change (abatch_addr L (qb_slot q)) with B in TH.
  change (Z.of_nat (length ((b, q) :: T))) with (Z.of_nat (S (length T))).
  pose proof (munch_refl [(TMP, TMP + 32)]%Z m) as MUp. pose proof (wmono_refl asegs m) as WMp. unfold dr_frame in FR.
  iprefix.
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct QF as [[-> QF0]|(TNE & QF1 & QF2)]; [exfalso; apply KN; rewrite QF0; reflexivity|].
    rewrite (qlast_cons_ne q (map snd T)) in * by (destruct T; [congruence| discriminate]).
    eapply REST; eassumption.
  - (* [comment removed for export] *)
    destruct QF as [[ET0 QF0]|(TNE & QF1 & QF2)]; [| exfalso; first [rewrite Z.mod_small in KN by (clear -QF1 QF2; lia)| rewrite unsigned_lit in KN by (clear -QF1 QF2; lia)| idtac]; clear -KN QF1; lia].
    step.                                     (* [comment removed for export] *)
    subst T. eapply REST; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma drinv_done : forall R st X RNG m, qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] -> drinv R st X RNG m -> drinv (qr_done R) st X RNG m.
Proof.
  intros R st X RNG m ET EB EP (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK).
  assert (EI : inflight (qr_done R) = inflight R) by (unfold inflight, secsT, qr_done; cbn [qr_tmp qr_pend]; rewrite ET, EP; reflexivity).
  unfold drinv. rewrite (ltac:(unfold csx; rewrite EI; reflexivity) : csx st (qr_done R) = csx st R), EI.
  split; [exact ARNG|]. split; [| exact (conj BL (conj HF (conj RS (conj MI (conj ST (conj FLE (conj MU0 (conj CP0 SK))))))))].
  unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr in AR |- *. eapply AREP_reqs; [exact AR| | intros HS'; exact HS'].
  (nd_pre AR 7%nat; intros _ _ _ _ _ HQ _; nd_post). cbn [ah_quar] in HQ. (nd_pre HQ 9%nat; intros QC MX TC GL TB IA CP NUM NT; nd_post).
  unfold AQdr, qr_done. cbn [qr_loc qr_glob qr_tmp qr_ia qr_pendb qr_pend map]. rewrite ET in NT. cbn [map] in NT.
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact I|]. split; [exact IA|]. split; [| exact (conj NUM NT)].
  eapply qcoupled_rec_perm; [exact CP| | | | | reflexivity].
  - exact (proj1 CP).
  - exact (proj1 (proj2 CP)).
  - unfold qr_entries. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite ET, EP. cbn [map qentries app]. apply Permutation_refl.
  - unfold qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map app]. apply Permutation_refl.
Qed.

Definition adorec__stmt : Prop := forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (R : qrconc) (X : aconc) (T : list (abatch * qbatchc)) (tb : word) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  arng L RNG0 st0 -> AREP (AHr R (csx st0 R)) L st0 X m0 -> ablocks L st0 X LB -> AF L LB m0 -> RSEC (inflight R) RNG0 ->
  qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] ->
  mem_inv asegs m0 -> stk asegs m0 lo (bv_unsigned sp) ->
  rw_cells asegs m0 TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 (tb' : word) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 -> stk asegs m1 lo (bv_unsigned sp) ->
     rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom asegs))) ->
  implS asegs RNG0 (aembed ATOP (do_recycle st0 (map fst T) K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TMP) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 adorec_entry) fc None m0 (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 0).
Variable K : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 2).
Variable R : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 3).
Variable X : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 4).
Variable T : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 5).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 14).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 15).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 16).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 17).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 18).
#[using="HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Lemma adorec__body : ltac:(let T := type of (fun (h : adorec__stmt) => h RT K Q R X T tb t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (K, (Q, (R, (X, (T, (tb, (t0, (t1, (t2, (a0, (a4, (a5, (a6, (a7, (t3, (t4, (t5, t6))))))))))))))))))) as _.
  intros ARNG AR BL HF RS ET EB EP MI ST TH KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. (nd_pre AR0 7%nat; intros WF _ _ _ _ HQ _; nd_post). cbn [ah_quar AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.AHr] in HQ.
  pose proof (tmp_len_bound R L st0 X m0 ALO WF HQ) as TLEN. rewrite ET in TLEN.
  pose proof (munch_refl [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0) as MU0. pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m0) as MUf. pose proof (wmono_refl asegs m0) as WM0.
  unfold adorec_entry. unfold thdr in TH.
  iprefix.
  carve_frame 112%nat ST.
  do 12 step.                                 (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. step.                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (INV : drinv R st0 X RNG0 mx);
    [ unfold drinv; split; [exact ARNG|];
      split; [eapply (AREP_frame_ext _ (HL R (csx st0 R)) L st0 X m0 mx); [exact ALO| exact AR| exact MUf| exact WM0|];
              constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO; lia |];
      split; [exact BL|];
      split; [eapply AFD; [exact HF| exact MUf| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO|]; cbn [fst]; atop_facts; clear -CEIL LO; lia
               | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO; lia] |];
      split; [exact RS|]; split; [assumption|]; split; [rewrite SPE; assumption|]; split; [intros bb j Hb; exact Hb|]; split; [exact MU0|];
      split; [eapply cpres_of_munch; [exact MUf|]; intros iv [<-|[]]; cbn [fst snd]; eapply (np_high L st0 X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| clear -TMPLO HHI; lia] |];
      unfold st_keep; repeat (split; [reflexivity|]); reflexivity |]
  end.
  (* [comment removed for export] *)
  assert (EPI : forall m1 st1 X1 RNG1 junk8' (tb' : word) rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6',
    drinv (qr_done R) st1 X1 RNG1 m1 -> rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr [] tb') ->
    evtF asegs RNG1 (fun ms' => implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms')
         (MS (mkR rax' (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x35f0c) fc None m1 (seg_rom asegs))).
  { intros m1 st1 X1 RNG1 junk8' tb' rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6' INV1 FR1 TH1.
    (pose proof INV1 as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ MI1 ST1 FLE1 _; nd_post). destruct (drinv_rngs _ _ _ _ _ INV1) as [RSTK1 RTMP1].
    unfold dr_frame in FR1.
    do 11 step.                               (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    setreg 2 sp ltac:(rewrite SPE; replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
    step.                                     (* [comment removed for export] *)
    release_frame FR1 ST1 (bv_unsigned sp).
    apply evtF_done. eapply KONT; [exact INV1| exact ST1| exact TH1]. }
  step. if_cases K0; zify_cond K0.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct T as [|bq T']; [| exfalso; cbn [length] in K0, TLEN; first [rewrite Z.mod_small in K0 by (clear -TLEN; lia)| rewrite unsigned_lit in K0 by (clear -TLEN; lia)| idtac]; clear -K0; lia].
    cbn [map do_recycle].
    eapply EPI; [apply drinv_done; [exact ET| exact EB| exact EP| exact INV]| exact FR| exact TH].
  - destruct T as [|bq T']; [exfalso; apply K0; reflexivity|].
    do 8 step.                                (* [comment removed for export] *)
    apply evtF_done.
    eapply (dr_outer Q (bq :: T') K R st0 X RNG0 _ tb); [exact INV| exact ET| exact EB| exact EP| discriminate| exact FR| exact TH|].
    intros st1 X1 RNG1 m1 junk8' tb' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' INV1 FR1 TH1.
    unfold ms_out. iprefix. eapply EPI; [exact INV1| exact FR1| exact TH1].
Qed.
End Zd2.
#[using="HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Theorem adorec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (R : qrconc) (X : aconc) (T : list (abatch * qbatchc)) (tb : word) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  arng L RNG0 st0 -> AREP (AHr R (csx st0 R)) L st0 X m0 -> ablocks L st0 X LB -> AF L LB m0 -> RSEC (inflight R) RNG0 ->
  qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] ->
  mem_inv asegs m0 -> stk asegs m0 lo (bv_unsigned sp) ->
  rw_cells asegs m0 TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 (tb' : word) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 -> stk asegs m1 lo (bv_unsigned sp) ->
     rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom asegs))) ->
  implS asegs RNG0 (aembed ATOP (do_recycle st0 (map fst T) K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TMP) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 adorec_entry) fc None m0 (seg_rom asegs)).
Proof. exact adorec__body. Qed.
End DoRec.
End CANSEC2.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AKitR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARecRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.ARepQD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.RT_stubs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_aensure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apopulate.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_agetfrom.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_arefill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_amaybe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_areturn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agetfrom__A3W.F_acdrain.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arefill__A3W.F_acdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ASecRecycle_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ACdeallocP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecGeo.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition adorec_entry : Z := 0x35e70.
Definition adorec_lout : Z := 0x35ee8.     (* [comment removed for export] *)
Definition adorec_lin : Z := 0x35f28.      (* [comment removed for export] *)
Definition adorec_after : Z := 0x35f40.    (* [comment removed for export] *)
Definition adorec_chk : Z := 0x35f6c.      (* [comment removed for export] *)
End CANSEC1.
Notation DOREC_FRAME := 112 (only parsing).
Notation DOREC_STACK := 1136 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ehdr (L : alayout) (e : achunk * Z) : word := Z_to_bv 64 (qhdr L (fst e) (snd e)).

#[using="Type"] Lemma qhdrs_rev_combine : forall L chs ks, length ks = length chs ->
  map (Z_to_bv 64) (qhdrs L chs ks) = map (ehdr L) (rev (combine chs ks)).
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try reflexivity; try lia.
  rewrite map_app, map_app, IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition esecs (es : list (achunk * Z)) : list achunk := List.filter is_sec (map fst es).
#[using="Type"] Lemma esecs_app : forall a b, esecs (a ++ b) = esecs a ++ esecs b.
Proof. intros. unfold esecs. rewrite map_app. apply List.filter_app. Qed.
#[using="Type"] Lemma esecs_cons_prim : forall c n k es, esecs ((CPrim c n, k) :: es) = esecs es.
Proof. reflexivity. Qed.
#[using="Type"] Lemma esecs_cons_sec : forall mb ms n k es, esecs ((CSec mb ms n, k) :: es) = CSec mb ms n :: esecs es.
Proof. reflexivity. Qed.
#[using="Type"] Lemma esecs_perm : forall a b, Permutation a b -> Permutation (esecs a) (esecs b).
Proof.
  intros a b P. unfold esecs. induction P; cbn; [constructor| | | eapply Permutation_trans; eassumption].
  - destruct (is_sec (fst x)); [apply perm_skip|]; assumption.
  - destruct (is_sec (fst x)), (is_sec (fst y)); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Definition secsT (R : qrconc) : list achunk := esecs (qentries (map fst (qr_tmp R)) (map snd (qr_tmp R))).
Definition inflight (R : qrconc) : list achunk := secsT R ++ esecs (qr_pend R).
(* [comment removed for export] *)
Definition csx (st : astate) (R : qrconc) : list achunk := sec_chunks_of st ++ inflight R.

(* [comment removed for export] *)
Definition qr_popr (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (rev (combine (b_chunks b) (qb_ks q))) (qr_qpend R).

#[using="Type"] Lemma qcoupled_rec_popr : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_popr R b q T).
Proof.
  intros L st X R b q T CP ET EB EP. pose proof (qcoupled_rec_pop L st X R b q T CP ET EB EP) as CP1. (pose proof CP1 as ndP__; nd_pre ndP__ 3%nat; intros LN1 LN2 _; nd_post).
  eapply qcoupled_rec_perm; [exact CP1| exact LN1| exact LN2| | | reflexivity].
  - unfold qr_entries, qr_popr, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pend]. repeat apply Permutation_app_head. apply Permutation_sym. apply Permutation_rev.
  - unfold qr_bslots, qr_popr, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pendb]. apply Permutation_refl.
Qed.

#[using="Type"] Lemma inflight_popr : forall R b q T, qr_tmp R = (b, q) :: T -> qr_pend R = [] -> length (qb_ks q) = length (b_chunks b) ->
  Permutation (inflight (qr_popr R b q T)) (inflight R).
Proof.
  intros R b q T ET EP LEN. unfold inflight, secsT, qr_popr. cbn [qr_tmp qr_pend]. rewrite ET, EP. cbn [map fst snd qentries].
  rewrite esecs_app. replace (esecs []) with (@nil achunk) by reflexivity. rewrite app_nil_r.
  eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply esecs_perm. apply Permutation_sym. apply Permutation_rev.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma do_recycle_cons : forall {RT} st b bs (k : astate -> AM RT),
  do_recycle st (b :: bs) k = recycle_chunks st (rev (b_chunks b)) (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 bs k)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma recycle_chunks_prim : forall {RT} st c n l (k : astate -> AM RT),
  recycle_chunks st (CPrim c n :: l) k = cache_dealloc st c (fun st1 => recycle_chunks st1 l k).
Proof. reflexivity. Qed.
#[using="Type"] Lemma recycle_chunks_sec : forall {RT} st mb ms n l (k : astate -> AM RT),
  recycle_chunks st (CSec mb ms n :: l) k = large_dealloc st mb ms (fun st1 => recycle_chunks st1 l k).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_popr : forall R L st X m b q T,
  AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
     AQdr (qr_popr R b q T) 0 0 L st X m
  /\ abatch_cells L m b q (qfirst L (map snd T))
  /\ Q_BATCH_BYTES <= b_size b /\ qnum_tmp (map fst T).
Proof.
  intros R L st X m b q T (QC & MX & TC & GL & TB & IA & CP & NUM & NT) ET EB EP.
  rewrite ET in TB, NT. cbn [map fst snd] in TB, NT. destruct TB as [BC TB']. pose proof (Forall_inv NT) as NB. pose proof (Forall_inv_tail NT) as NT'. cbn beta in NB.
  split; [| split; [exact BC| split; [exact NB| exact NT']]].
  unfold AQdr, qr_popr. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB'|]. split; [exact IA|].
  split; [exact (qcoupled_rec_popr L st X R b q T CP ET EB EP)|]. split; [exact NUM| exact NT'].
Qed.

#[using="Type"] Lemma AQdr_drop_sec : forall R L st X m mb ms n kk pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CSec mb ms n, kk) :: pend' -> AQdr (qr_drop R pend') 0 0 L st X m.
Proof.
  intros R L st X m mb ms n kk pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [exact (qcoupled_rec_drop_sec L st X R mb ms n kk pend' CP EP)|]. exact (conj NUM NT).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQdr_set_nsec : forall R L st X m v, AQdr R 0 0 L st X m -> AQdr R 0 0 L (set_nsec v st) X m.
Proof.
  intros R L st X m v (QC & MX & TC & GL & TB & IA & CP & NUM & NT). unfold AQdr. cbn.
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  eapply qcoupled_rec_same; [exact CP|]. unfold quar_same. cbn. repeat (split; [reflexivity|]).
  split; intros b Hb; destruct (xb_st b); first [exact I| exact Hb].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_head_geo : forall R L st X m b q T, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T ->
  17594333495296 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= ATOP.
Proof.
  intros R L st X m b q T ALO WF (_ & _ & _ & _ & _ & _ & CP & _) ET.
  (nd_pre (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP ltac:(apply In_qr_bslots; rewrite ET; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
  (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ G4 G5 _; nd_post).
  unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5. unfold abatch_addr. exact (conj G4 G5).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_sec_in' : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof.
  intros st p mb ms n Lp. unfold sec_chunks_of. apply List.filter_In. split; [| reflexivity].
  unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p _ Lp) as P. apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_in; [exact P| left; reflexivity].
Qed.

#[using="Type"] Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; first [apply Z.eq_dec| apply N.eq_dec]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma nodup_range_len : forall (l : list Z) (N : nat), List.NoDup l -> Forall (fun k => 0 <= k < Z.of_nat N) l -> (length l <= N)%nat.
Proof.
  intros l N ND HF. rewrite <- (length_seq N 0), <- (length_map Z.of_nat). apply NoDup_incl_length; [exact ND|].
  intros k Hk. pose proof (proj1 (Forall_forall _ _) HF k Hk) as R. cbn beta in R.
  apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tmp_len_bound : forall R L st X m, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> Z.of_nat (length (qr_tmp R)) < 2^32.
Proof.
  intros R L st X m ALO WF (_ & _ & _ & _ & _ & _ & CP & _). (pose proof CP as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ NDB BS _ _; nd_post).
  assert (LEN : (length (qr_bslots R) <= Z.to_nat 458752)%nat).
  { apply nodup_range_len; [exact NDB|]. apply Forall_forall. intros k Hk. (nd_pre (proj1 (BS k) Hk) 5%nat; intros bb Hb Sb Cb Kb; nd_post).
    (pose proof (busy_slot_geo L st X ALO WF bb Hb) as ndP__; nd_pre ndP__ 6%nat; intros _ KR G1 G2 (_ & G3 & _) _; nd_post). unfold xb_alloc, aslot_addr in G1, G2. rewrite Cb, Kb, size_of_class_24 in *.
    unfold K_FREEARR_OFF in G3. rewrite Z2Nat.id by (clear; lia). clear -KR G1 G2 G3. lia. }
  unfold qr_bslots in LEN. rewrite length_app, length_map, !length_app, length_map in LEN. clear -LEN. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AREP_reqs : forall AQ AQ' AS AS' ADp AFp L st X m,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L st X m -> (AS L st X m -> AS' L st X m) -> AREP (mkAHoles AQ' AS' ADp AFp) L st X m.
Proof.
  intros AQ AQ' AS AS' ADp AFp L st X m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) HQ HS.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact HQ|]. split; [exact (HS A7)|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma high_fake : forall L iv, alayout_ok L -> ATOP <= fst iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xa7668 \/ 0xa7668 + 8 <= fst iv) /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
  /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv) /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
  /\ (snd iv <= 0x1405b1 \/ 0x1405b1 + 1 <= fst iv) /\ (snd iv <= 0x13e498 \/ 0x13e498 + 4 <= fst iv).
Proof.
  intros L iv ALO HI. pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj in *. pose proof atop_range as AR.   (* [comment removed for export] *)
  assert (SF : shad (al_fake L) + shlen 11571200 <= 17594332446720) by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -OF AR; Z.div_mod_to_equations; lia).
  clear -HI OF OD SF AR. repeat split; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DoRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
(* [comment removed for export] *)
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x1808c8 <= a < 0x5d0910) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.     (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

#[using="ADD"] Lemma SHO : forall R, srec_holes_ok (AQdr R 0 0) AD.
Proof. intros R. split; [intros; eapply AQdr_frameD; eassumption| exact ADD]. Qed.

(* [comment removed for export] *)
Variables (L : alayout) (lo TMP HI : Z) (LB : list ablock) (cbs : word) (RNG0 : footprint) (m0 : amem) (st0 : astate).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Let SP : Z := bv_unsigned sp + -112.
Hypothesis ALO : alayout_ok L.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - DOREC_STACK.
Hypothesis SP47 : bv_unsigned sp <= 2^47.
Hypothesis TMPLO : bv_unsigned sp <= TMP.
Hypothesis TMPHI : TMP + 32 <= 2^47.
Hypothesis HHI : TMP + 32 <= HI.
Hypothesis RSTK0 : rng RNG0 lo (bv_unsigned sp - lo).
Hypothesis RTMP0 : rng RNG0 TMP 32.

(* [comment removed for export] *)
Definition dr_frame (junk8 : list byte) : list cell :=
  [CB 8 junk8; C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition st_keep (st : astate) : Prop :=
     a_live st = a_live st0 /\ a_next st = a_next st0 /\ a_qloc st = a_qloc st0 /\ a_qloc_bytes st = a_qloc_bytes st0
  /\ a_qglob st = a_qglob st0 /\ a_qglob_bytes st = a_qglob_bytes st0 /\ a_nres st = a_nres st0 /\ a_ptr_array st = a_ptr_array st0
  /\ a_space_beg st = a_space_beg st0.

(* [comment removed for export] *)
Definition drinv (R : qrconc) (st : astate) (X : aconc) (RNG : footprint) (m : amem) : Prop :=
     arng L RNG st /\ AREP (AHr R (csx st R)) L st X m /\ ablocks L st X LB /\ AF L LB m
  /\ RSEC (inflight R) RNG /\ mem_inv asegs m /\ stk asegs m lo SP /\ fp_le RNG0 RNG
  /\ munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m /\ cpres L HI LB m0 m /\ st_keep st.

#[using="RSTK0 RTMP0"] Lemma drinv_rngs : forall R st X RNG m, drinv R st X RNG m -> rng RNG lo (bv_unsigned sp - lo) /\ rng RNG TMP 32.
Proof. intros R st X RNG m (_ & _ & _ & _ & _ & _ & _ & FLE & _). split; (eapply rng_fp_le; [exact FLE|]); assumption. Qed.

(* [comment removed for export] *)
Definition thdr (T : list (abatch * qbatchc)) (tb : word) : list cell :=
  [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb].

(* [comment removed for export] *)
Definition ms_in (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (B cnt i : Z) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 701336) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 701400) (Z_to_bv 64 702024) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 cnt)
          (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + cnt)) (Z_to_bv 64 (16 + i)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition batch_ok (R : qrconc) (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) : Prop :=
  qr_tmp R = T /\ qr_pendb R = [kb] /\ Z.of_nat (length all) <= Q_BATCH /\ 0 <= kb.

(* [comment removed for export] *)
#[using="ASECc_disj"] Lemma live_vs_inflight : forall st L X m A Bk mb ms n,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb'.
Proof.
  intros st L0 X m A Bk mb ms n HS p mb' ms' n' Lp. destruct (ASECc_disj _ _ _ _ _ HS) as [ND DJ].
  pose proof (live_sec_in' st p _ _ _ Lp) as INl.
  assert (IN1 : In (CSec mb' ms' n') ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; left; apply in_app_iff; left; exact INl).
  assert (IN2 : In (CSec mb ms n) ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; right; left; reflexivity).
  assert (NE : CSec mb' ms' n' <> CSec mb ms n).
  { intros E. rewrite E in INl. apply (List.NoDup_remove_2 _ _ _ ND). apply in_app_iff. left. apply in_app_iff. left. exact INl. }
  destruct (DJ _ _ IN1 IN2 NE) as [D|D]; cbn [sec_mb sec_ms] in D; [left| right]; exact D.
Qed.

#[using="ASECc_disj"] Lemma live_vs_hl : forall st L X m A Bk mb ms n hl,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ Bk) /\ sec_wf1 L (CSec (hl - 24) lms ln))) ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl.
Proof.
  intros st L0 X m A Bk mb ms n hl HS HIN p mb' ms' n' Lp. destruct (ASECc_disj _ _ _ _ _ HS) as [ND DJ].
  pose proof (live_sec_in' st p _ _ _ Lp) as INl.
  assert (IN1 : In (CSec mb' ms' n') ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; left; apply in_app_iff; left; exact INl).
  unfold SEC_UOFF. destruct HIN as [[H1 H2]|(lms & ln & INh & SWh)].
  - destruct (live_vs_inflight st L0 X m A Bk mb ms n HS p mb' ms' n' Lp) as [D|D]; [right; clear -D H1; lia| left; clear -D H2; lia].
  - assert (IN2 : In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)).
    { apply in_app_iff in INh. apply in_app_iff. destruct INh as [H|H]; [left; exact H| right; right; exact H]. }
    destruct (achunk_eq_dec' (CSec mb' ms' n') (CSec (hl - 24) lms ln)) as [E|NE].
    + injection E as -> -> ->. left. clear. lia.
    + (nd_pre SWh 7%nat; intros _ _ _ MSE NB NPR _; nd_post).
      (pose proof (sec_facts ln ltac:(unfold AREQMAX in *; clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSB; nd_post). rewrite <- MSE in MSB.
      destruct (DJ _ _ IN1 IN2 NE) as [D|D]; cbn [sec_mb sec_ms] in D; [right; clear -D; lia| left; clear -D MSB; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="HL SREC ADD AFD ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Lemma dr_inner : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (es : list (achunk * Z)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) (i : Z) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  drinv R st X RNG m -> batch_ok R kb all T -> qr_pend R = es -> es = skipn (Z.to_nat i) all -> es <> [] -> 0 <= i ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  u64arr asegs m (abatch_addr L kb + 24) (map (ehdr L) all) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_drop R []) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_in adorec_after rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (abatch_addr L kb) (Z.of_nat (length all)) (Z.of_nat (length all)) m1)) ->
  implS asegs RNG (aembed ATOP (recycle_chunks st (map fst es) K)) (epostF Q)
        (ms_in adorec_lin rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (abatch_addr L kb) (Z.of_nat (length all)) i m).
Proof.
  intros RT Q es. induction es as [|e es IH]; intros K R st X RNG m kb all T i tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    INV BOK EP ES NE I0 FR TH ARR KONT; [congruence|].
  (pose proof INV as ndP__; nd_pre ndP__ 11%nat; intros ARNG AR BL HF RS MI ST FLE MU0 CP0 SK; nd_post). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  (nd_pre BOK 4%nat; intros ET EB ALLB KB0; nd_post).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR). unfold Q_BATCH in ALLB.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  assert (IL : i < Z.of_nat (length all)).
  { destruct (Z.lt_ge_cases i (Z.of_nat (length all))) as [H|H]; [exact H| exfalso]. rewrite skipn_all2 in ES by lia. discriminate. }
  assert (NTH : nth_error (map (ehdr L) all) (Z.to_nat i) = Some (ehdr L e)).
  { rewrite nth_error_map. replace (nth_error all (Z.to_nat i)) with (nth_error (skipn (Z.to_nat i) all) 0) by (rewrite nth_error_skipn, Nat.add_0_r; reflexivity).
    rewrite <- ES. reflexivity. }
  set (B := abatch_addr L kb) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & _).
  (nd_pre (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) 6%nat; intros nb bb1 bctx bl1 bl2 XBB; nd_post).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  (nd_pre BG 9%nat; intros _ _ BG1 BG2 (BG3a & BG3 & BG3b) BG4 BG5 BG6 BG7; nd_post).
  pose proof (u64arr_read asegs m (B + 24) _ i (ehdr L e) (wa (B + 152 + 8 * i + -128)) ARR NTH I0 ltac:(f_equal; lia)) as RDV.
  assert (RB24 : rng RNG (B + 152 + 8 * i + -128) 8).
  { (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post).
    destruct (RCLS K_BATCH_CLASS (K24)) as (R1 & _). eapply rng_sub; [exact R1| |]; clear -BG1 BG2 BG3 I0 IL ALLB; lia. }
  unfold ms_in, adorec_lin. iprefix.
  step.                                     (* [comment removed for export] *)
  clear RDV RB24.
  zstep.                                    (* [comment removed for export] *)
  step.                                     (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 2%nat CBC CBR. clear CB8 CBR.
  (* [comment removed for export] *)
  assert (POSTK : forall stX X' RNG' m' (W : list (Z * Z)) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    fp_le RNG RNG' -> munch W m m' -> mem_inv asegs m' -> stk asegs m' lo SP ->
    (forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SP) \/ (forall b, In b (x_busy X') -> xb_st b = BBatch -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP) ->
    np_fp L HI LB W -> fake_untouched L W -> (AF L LB m -> AF L LB m') ->
    AREP (AHr (qr_drop R es) (csx stX (qr_drop R es))) L stX X' m' -> arng L RNG' stX ->
    (forall b, In b (x_busy X') -> In b (x_busy X)) -> (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')) ->
    a_live stX = a_live st -> a_next stX = a_next st -> a_qloc stX = a_qloc st -> a_qloc_bytes stX = a_qloc_bytes st ->
    a_qglob stX = a_qglob st -> a_qglob_bytes stX = a_qglob_bytes st -> a_nres stX = a_nres st -> a_ptr_array stX = a_ptr_array st -> a_space_beg stX = a_space_beg st ->
    RSEC (inflight (qr_drop R es)) RNG' ->
    implS asegs RNG' (aembed ATOP (recycle_chunks stX (map fst es) K)) (epostF Q)
          (MS (mkR (Z_to_bv 64 220980) (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 TMP) (Z_to_bv 64 701336) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 701400) (Z_to_bv 64 702024) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 (Z.of_nat (length all)))
                   (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + Z.of_nat (length all))) (Z_to_bv 64 (16 + i)) s10 s11 t3' t4' t5' t6')
              F (ret_pc (Z_to_bv 64 220980)) fc None m' (seg_rom asegs))).
  { intros stX X' RNG' m' W t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    intros FPLE MU MI' ST' WK NP FU HF' AR' ARNG' XS XL L1 L2 L3 L4 L5 L6 L8 L9 L10 RS'. (try pose proof atop_range as ATR).
    replace (ret_pc (Z_to_bv 64 220980)) with (Z_to_bv 64 220980 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof AR' as AR1. (nd_pre AR1 7%nat; intros WF' _ _ _ _ HQ' _; nd_post). cbn [ah_quar AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr] in HQ'.
    (nd_pre (pendb_busy L stX X' (qr_drop R es) m' kb HQ' EB) 6%nat; intros nb' bb1' bctx' bl1' bl2' XBB'; nd_post).
    assert (INB : In (bany BBatch K_BATCH_CLASS kb nb' bb1' bctx') (x_busy X')) by (rewrite XBB'; apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (DJF : disjoint_from W SP 112).
    { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; exact H2| left; clear -HI' CEIL LO SPE; lia]. }
    assert (DJT : disjoint_from W TMP 32).
    { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; clear -H2 TMPLO SPE; lia| left; clear -HI' CEIL LO TMPLO SPE; lia]. }
    assert (DJB : disjoint_from W (B + 24) (8 * Z.of_nat (length (map (ehdr L) all)))).
    { rewrite length_map. apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(HB & _ & _)].
      - right. clear -H1 BG5 CEIL LO SPE ALLB. lia.
      - specialize (HB _ INB eq_refl). unfold xb_alloc in HB. cbn [xb_class xb_slot bany] in HB. rewrite size_of_class_24 in HB. fold B in HB.
        clear -HB ALLB. lia. }
    pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'. pose proof (u64arr_frameD _ _ _ _ _ ARR MU DJB) as ARR'.
    assert (INV' : drinv (qr_drop R es) stX X' RNG' m').
    { unfold drinv. split; [exact ARNG'|]. split; [exact AR'|].
      split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
      split; [exact (HF' HF)|]. split; [exact RS'|]. split; [exact MI'|]. split; [exact ST'|].
      split; [intros b j Hb; apply FPLE, FLE, Hb|].
      split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. (nd_pre Hx 3%nat; intros Hx1 Hx2 _; nd_post).
               apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & HZ & HI')]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ HI' CEIL LO SPR SPE; lia]. }
      split; [eapply cpres_trans; [exact CP0| eapply cpres_of_munch; [exact MU| exact NP]]|].
      (nd_pre SK 9%nat; intros K1 K2 K3 K4 K5 K6 K7 K8 K9; nd_post). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
      repeat (split; [assumption|]). exact K9. }
    iprefix.
    zstep. zstep.                           (* [comment removed for export] *)
    setreg 25%Z (Z_to_bv 64 (16 + (i + 1))) ltac:(f_equal; clear; lia).
    setreg 23%Z (Z_to_bv 64 (B + 152 + 8 * (i + 1))) ltac:(f_equal; clear; lia).
    step. if_cases KB; zify_cond KB.        (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (NE' : es <> []).
      { intros ->. apply KB. assert (LEN1 : length (skipn (Z.to_nat i) all) = 1%nat) by (rewrite <- ES; reflexivity). rewrite length_skipn in LEN1. clear -LEN1 IL I0. lia. }
      apply evtF_done.
      eapply (IH K (qr_drop R es) stX X' RNG' m' kb all T (i + 1) tb); try eassumption;
        try lazymatch goal with
        | |- batch_ok _ _ _ _ => unfold batch_ok; rewrite <- ET, <- EB; unfold qr_drop; cbn; repeat split; try reflexivity; assumption
        | |- qr_pend _ = _ => reflexivity
        | |- es = _ => replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by (clear -I0; lia); rewrite <- skipn_skipn, <- ES; reflexivity
        | |- 0 <= _ => clear -I0; lia
        end.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (E0 : es = []).
      { destruct es as [|e2 es2]; [reflexivity| exfalso].
        assert (LEN1 : (2 <= length (skipn (Z.to_nat i) all))%nat) by (rewrite <- ES; cbn; lia). rewrite length_skipn in LEN1. clear -LEN1 IL I0 KB. lia. }
      subst es. cbn [map recycle_chunks].
      apply evtF_done. replace (i + 1) with (Z.of_nat (length all)) by (clear -KB; lia).
      eapply KONT; [exact INV'| exact FR'| exact TH']. }
  (* [comment removed for export] *)
  destruct e as [ch kk]. destruct ch as [c n| mb ms n]; cbn [map fst]; [rewrite recycle_chunks_prim| rewrite recycle_chunks_sec].
  - (* [comment removed for export] *)
    eapply arecyc1; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rw_cells _ _ _ _ => exact CBC
      | |- bv_unsigned _ <= _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear; lia
      | |- _ + 16 <= _ => clear -SP47 CEIL LO SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- rng _ _ 16 => eapply rng_sub; [exact RSTK| clear -CEIL LO SPE; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros stX X' RNG' ms' RET.
    (nd_pre RET 19%nat; intros FPLE t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mfa' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 23%nat; intros MU WM MI' ST' MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC MU1 AU1 XS XL; nd_post).
    rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia).
    pose proof AR as AR1. destruct AR1 as (WF0 & _).
    (nd_pre (pend_head_busy L st X R m c n kk es ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EP) 5%nat; intros b1 ctx l1 l2 XB; nd_post).
    (pose proof WF0 as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC c (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0))) 7%nat; intros _ _ _ _ A5 A6 _; nd_post).
    eapply (POSTK stX X' RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact ST'| | | | | | exact ARNG'| exact XS| exact XL| exact L1| exact L2| exact L3| exact L4| exact L5| exact L6| exact L8| exact L9| exact L10|].
    + (* [comment removed for export] *)
      intros iv Hiv. destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 _ _ mfa' iv ALO WF0 XB A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [E|[SL|LP]].
      * left. subst iv. cbn [fst snd]. clear -CEIL LO SPE. lia.
      * right. split; [| split; [(nd_pre (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) 7%nat; intros _ _ _ _ _ G4 _; nd_post); unfold xb_alloc in G4; cbn [xb_class xb_slot bany] in G4; clear -G4 SL; lia|]].
        -- intros b Hb Sb. pose proof (XS b Hb) as HbX.
           assert (NEQ : c <> xb_class b \/ kk <> xb_slot b).
           { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
             apply (In_X_g X BQuar c kk n b1 ctx l1 l2 XB) in HbX. destruct HbX as [Hl| ->]; [| cbn in Sb; discriminate].
             exact (key_fresh_g L st X BQuar c kk n b1 ctx l1 l2 XB WF0 b Hl (eq_sym EC) (eq_sym EK)). }
           (nd_pre (busy_slot_geo L st X ALO WF0 b (XS b Hb)) 3%nat; intros CLB KBb _; nd_post).
           pose proof (slots_sep_any L st X c kk (xb_class b) (xb_slot b) ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) CLB
                         (proj2 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) KBb NEQ) as D.
           unfold xb_alloc. clear -D SL. lia.
        -- (nd_pre (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) 8%nat; intros _ _ _ _ _ _ G5 _; nd_post).
           unfold xb_alloc in G5. cbn [xb_class xb_slot bany] in G5. clear -G5 SL. lia.
      * right. split; [| exact (conj (proj1 LP) (proj1 (proj2 LP)))]. intros b Hb _. exact (lowpiece_vs_slot L st X c b iv ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) (XS b Hb) LP).
    + (* [comment removed for export] *)
      eapply (np_rec_W L st X LB HI lo SP c kk n b1 ctx l1 l2); [exact ALO| exact WF0| exact BL| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + intros HF0. eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF0| exact MU| exact WM|].
      eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + (* [comment removed for export] *)
      replace (csx stX (qr_drop R es)) with (csx st R); [exact AR'|].
      unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite EP, esecs_cons_prim, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity.
    + unfold inflight, secsT, qr_drop in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP, esecs_cons_prim in RS. eapply RSEC_mono'; [exact FPLE| exact RS].
  - (* [comment removed for export] *)
    pose proof AR as AR1. (nd_pre AR1 8%nat; intros WF0 _ _ _ _ HQ0 HS0 _; nd_post). cbn [ah_quar ah_sec AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr] in HQ0, HS0.
    assert (CSE : csx st R = (sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es).
    { unfold csx, inflight. rewrite EP, esecs_cons_sec, app_assoc. reflexivity. }
    pose proof (ASECc_wf1 _ _ _ _ _ HS0) as WF1. rewrite CSE in WF1. apply Forall_app in WF1. destruct WF1 as [_ WF1]. pose proof (Forall_inv WF1) as SW.
    pose proof (ASECc_nres _ _ _ _ _ HS0) as [NR0 NR1].
    rewrite CSE in AR, HS0.
    assert (RSC : RSEC ((sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es) RNG).
    { apply (proj2 (RSEC_app _ _ _)). split; [apply (proj2 (RSEC_app _ _ _)); split; [exact (RSEC_arng _ _ _ ARNG)|]|];
        unfold inflight in RS; rewrite EP, esecs_cons_sec in RS; apply (proj1 (RSEC_app _ _ _)) in RS; destruct RS as [RS1 RS2]; [exact RS1|].
      exact RS2. }
    eapply (SREC (AQdr R 0 0) AD AF (sec_chunks_of st ++ secsT R) (esecs es) _ (fun st1 => recycle_chunks st1 (map fst es) K) Q L RNG);
      try lazymatch goal with
      | |- srec_holes_ok _ _ => exact (SHO R)
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- RSEC _ _ => exact RSC
      | |- AREP _ _ _ _ _ => exact AR
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- bv_unsigned _ <= 2 ^ 47 => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -SP47 SPE CEIL LO; lia
      | |- 4096 <= bv_unsigned _ => rewrite unsigned_lit by (clear; lia); clear; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros st' RNG' ms' SR. unfold srec_ret in SR.
    (nd_pre SR 18%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' hl ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 10%nat; intros STE HLOK HLIN MU MI' STK' AR' FS ARNG' RS'; nd_post).
    rewrite unsigned_lit in MU, STK' by (clear -SPR CEIL LO SPE; lia). subst st'.
    pose proof (fstepS_le _ _ _ _ FS) as FPLE.
    assert (AR'' : AREP (AHr (qr_drop R es) (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es))) L (set_nsec (a_nsec st - 1) st) X m').
    { replace (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es)) with ((sec_chunks_of st ++ secsT R) ++ esecs es).
      2:{ unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st) eq_refl eq_refl eq_refl), app_assoc. reflexivity. }
      unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr. eapply AREP_reqs; [exact AR'| | intros HS1; exact HS1].
      (nd_pre AR' 7%nat; intros _ _ _ _ _ HQ1 _; nd_post). cbn [ah_quar] in HQ1. eapply AQdr_drop_sec; [exact HQ1| exact EP]. }
    pose proof (live_vs_inflight st L X m _ _ mb ms n HS0) as DJ. pose proof (live_vs_hl st L X m _ _ mb ms n hl HS0 HLIN) as HLS.
    (nd_pre HLOK 3%nat; intros HK1 HK2 HK3; nd_post).
    eapply (POSTK (set_nsec (a_nsec st - 1) st) X RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact STK'| | | | | exact AR''| exact ARNG'| intros b Hb; exact Hb| intros b p Hb _; exact Hb
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity|].
    + intros iv Hiv. destruct (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv) as [WK _].
      destruct WK as [WK|(WB & WZ & WC)]; [left; exact WK| right]. split; [intros b Hb _; exact (WB b Hb)| exact (conj WZ WC)].
    + eapply (np_srec_W L st X LB HI lo SP mb ms n (a_nres st) hl); [exact ALO| exact WF0| exact BL| exact SW| exact DJ| exact HK1| exact HK2| exact HK3| exact HLS| exact NR0| exact NR1
        | atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + apply fake_untouched_of. intros iv Hiv.
      exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
    + intros HF0. eapply AFD; [exact HF0| exact MU| |].
      * apply fake_untouched_of. intros iv Hiv.
        exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
      * apply Forall_forall. intros iv Hiv. exact (srec_W_t48 L st X lo SP mb ms n (a_nres st) hl iv ALO SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv).
    + unfold inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. apply (proj1 (RSEC_app _ _ _)) in RS'. destruct RS' as [RS3 RS4].
      apply (proj1 (RSEC_app _ _ _)) in RS3. destruct RS3 as [_ RS3]. apply (proj2 (RSEC_app _ _ _)). split; [exact RS3| exact RS4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms_out (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 : word) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 701336) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 701400) (Z_to_bv 64 702024) xs4 (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition dr_after__stmt : Prop := forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (KK : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (T : list (abatch * qbatchc)) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [kb] -> qr_pend R = [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_unbatch R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (KK st1)) (epostF Q)
           (ms_out adorec_chk rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS KK)) (epostF Q)
        (ms_out adorec_after rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Section Zd1.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 0).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 1).
Variable KK : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 2).
Variable R : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 3).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 4).
Variable X : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 5).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 7).
Variable kb : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 8).
Variable T : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 9).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 10).
Variable junk8 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 11).
Variable rax : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 12).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 13).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 14).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 15).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 16).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 17).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 18).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 19).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 20).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 21).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 22).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 23).
Variable xs6 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 24).
Variable xs7 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 25).
Variable xs8 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 26).
Variable xs9 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dr_after__stmt 31).
Let B := abatch_addr L kb.
#[using="HL RSEC_mono' ALO CEIL LO TMPLO HHI RSTK0 RTMP0 B"] Lemma dr_after__body : ltac:(let T := type of (fun (h : dr_after__stmt) => h RT Q KK R st X RNG m kb T tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (Q, (KK, (R, (st, (X, (RNG, (m, (kb, (T, (tb, (junk8, (rax, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (xs6, (xs7, (xs8, (xs9, (t3, (t4, (t5, t6)))))))))))))))))))))))))))))))) as _.
  intros INV ET EB EP FR TH KONT.
  (pose proof INV as ndP__; nd_pre ndP__ 11%nat; intros ARNG AR BL HF RS MI ST FLE MU0 CP0 SK; nd_post). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. (nd_pre AR0 4%nat; intros WF _ INST _; nd_post). pose proof (proj1 INST) as ISB. change (AINSTANCE + 32) with 701368 in ISB.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SB1 SB2 _ SB4; nd_post).
  chg (abatch_addr L kb) B.
  (* [comment removed for export] *)
  (nd_pre (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) 6%nat; intros nb bb1 bctx bl1 bl2 XBB; nd_post).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  (nd_pre BG 9%nat; intros _ _ BG1 BG2 (BG3a & BG3 & BG3b) BG4 BG5 BG6 BG7; nd_post).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; clear; lia).
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (RI8 : rng RNG 701368 8) by (destruct ARNG as (R1 & _); eapply rng_sub; [exact R1| clear; lia| clear; lia]).
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 1%nat CBC CBR. clear CB8 CBR.
  unfold ms_out, adorec_after. iprefix.
  step.                                                    (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear -BG4 BG5 SB4 CEIL; lia); [exfalso; clear -K1 BG1 BG3a; lia|].   (* [comment removed for export] *)
  zstep.                                                   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear -BG4 BG5 SB1 SB2 SB4 CEIL; lia); [exfalso; clear -K2 BG2 BG3 BG3b; lia|].   (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  zstep. zstep. zstep.                                     (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 K_BATCH_CLASS) ltac:(f_equal; replace (B - al_space_beg L) with (24 * 4294967296 + (B - aregion L K_BATCH_CLASS)) by (clear -ER24; lia);
                                          symmetry; unfold K_BATCH_CLASS in *; apply class_of_offset; [clear; lia| change (2^32) with 4294967296; clear -BG1 BG2 BG3; lia]).
  step. step.                                              (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  apply evtF_done.
  eapply acdealloc24; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pendb _ = _ => exact EB
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
  intros stX X' RNG' ms' RET.
  (nd_pre RET 19%nat; intros FPLE t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mfa' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 21%nat; intros MU WM MI' ST' MFB AR' ARNG' CIN L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 GC XS XL; nd_post).
  rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia). (try pose proof atop_range as ATR).
  replace (ret_pc (Z_to_bv 64 221036)) with (Z_to_bv 64 221036 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 7%nat; intros _ _ _ _ A5 A6 _; nd_post).
  assert (WK : forall iv, In iv (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') ->
                          (lo <= fst iv /\ snd iv <= SP) \/ (0 <= fst iv /\ snd iv <= ATOP)).
  { intros iv Hiv. destruct (cd_W_cases L SP K_BATCH_CLASS _ _ mfa' iv ALO (K24) A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [->|(P0 & P1 & _)];
      [left; cbn [fst snd]; clear -LO SPE; lia| right; exact (conj P0 P1)]. }
  assert (DJF : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') SP 112).
  { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; exact H2| left; clear -H2 CEIL LO SPE; lia]. }
  assert (DJT : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') TMP 32).
  { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; clear -H2 TMPLO SPE; lia| left; clear -H2 CEIL LO TMPLO SPE; lia]. }
  pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'.
  assert (INV' : drinv (qr_unbatch R) stX X' RNG' m').
  { unfold drinv. split; [exact ARNG'|].
    split. { replace (csx stX (qr_unbatch R)) with (csx st R); [exact AR'|].
             unfold csx, inflight, secsT, qr_unbatch. cbn [qr_tmp qr_pend]. rewrite EP, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity. }
    split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
    split. { eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF| exact MU| exact WM|].
             eapply (cd_W_fake L lo); [exact ALO| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia]. }
    split. { unfold inflight, secsT, qr_unbatch in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP in RS. eapply RSEC_mono'; [exact FPLE| exact RS]. }
    split; [exact MI'|]. split; [exact ST'|]. split; [intros b j Hb; apply FPLE, FLE, Hb|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. (nd_pre Hx 3%nat; intros Hx1 Hx2 _; nd_post).
             apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[HZ H2]]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ H2 CEIL LO SPR SPE; lia]. }
    split. { eapply cpres_trans; [exact CP0|]. eapply cpres_of_munch; [exact MU|].
             eapply (np_cd_W L st X LB HI lo SP); [exact ALO| exact WF| exact BL| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia]. }
    (nd_pre SK 9%nat; intros K1' K2' K3 K4 K5 K6 K7 K8 K9; nd_post). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
    repeat (split; [assumption|]). exact K9. }
  iprefix. apply evtF_done.
  eapply KONT; [exact INV'| exact FR'| exact TH'].
Qed.
End Zd1.
#[using="HL RSEC_mono' ALO CEIL LO TMPLO HHI RSTK0 RTMP0"] Lemma dr_after : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (KK : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (T : list (abatch * qbatchc)) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [kb] -> qr_pend R = [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_unbatch R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr T tb) ->
     implS asegs RNG1 (aembed ATOP (KK st1)) (epostF Q)
           (ms_out adorec_chk rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS KK)) (epostF Q)
        (ms_out adorec_after rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof. exact dr_after__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="rc sp SP"] Lemma map_fst_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

#[using="Type"] Lemma qlast_cons_ne : forall q (qs : list qbatchc), qs <> [] -> qlast L (q :: qs) = qlast L qs.
Proof.
  intros q qs NE. unfold qlast, qaddrs. cbn [map]. destruct qs as [|q' qs']; [congruence|]. cbn [map]. 
  generalize (abatch_addr L (qb_slot q')) (map (fun q0 : qbatchc => abatch_addr L (qb_slot q0)) qs'). clear. intros a l. revert a. induction l; intros; reflexivity.
Qed.

Definition qr_done (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) [] [] [] (qr_qpend R).

#[using="HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Lemma dr_outer : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (T : list (abatch * qbatchc)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (tb : word) junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] -> T <> [] ->
  rw_cells asegs m SP (dr_frame junk8) -> rw_cells asegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' (tb' : word) rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 ->
     rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_out 0x35f74 rax' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' m1)) ->
  implS asegs RNG (aembed ATOP (do_recycle st (map fst T) K)) (epostF Q)
        (ms_out adorec_lout rax t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length T))) a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof.
  intros RT Q T. induction T as [|[b q] T IH]; intros K R st X RNG m tb junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6
    INV ET EB EP NE FR TH KONT; [congruence|].
  (pose proof INV as ndP__; nd_pre ndP__ 11%nat; intros ARNG AR BL HF RS MI ST FLE MU0 CP0 SK; nd_post). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. (nd_pre AR0 8%nat; intros WF _ _ _ _ HQ HS _; nd_post). cbn [ah_quar ah_sec AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr] in HQ, HS.
  (* [comment removed for export] *)
  (nd_pre (AQdr_popr R L st X m b q T HQ ET EB EP) 4%nat; intros HQ1 BC SZB NTT; nd_post).
  (nd_pre BC 6%nat; intros CC EC JC CCNT CLEN CRNG; nd_post).
  set (R1 := qr_popr R b q T) in *.
  set (B := abatch_addr L (qb_slot q)) in *.
  set (all := rev (combine (b_chunks b) (qb_ks q))).
  assert (LALL : Z.of_nat (length all) = b_count b) by (subst all; rewrite length_rev, length_combine, CLEN, Nat.min_id; lia).
  assert (MALL : map fst all = rev (b_chunks b)) by (subst all; rewrite map_rev, map_fst_combine by exact CLEN; reflexivity).
  rewrite (qhdrs_rev_combine L _ _ CLEN) in EC. fold all in EC.
  assert (PCS : Permutation (csx st R) (csx st R1)).
  { unfold csx. apply Permutation_app_head. apply Permutation_sym. subst R1. apply inflight_popr; [exact ET| exact EP| exact CLEN]. }
  assert (AR1 : AREP (AHr R1 (csx st R1)) L st X m).
  { unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr. eapply AREP_reqs; [exact AR| exact HQ1| intros HS'; eapply ASECc_perm; [exact PCS| exact HS']]. }
  assert (INV1 : drinv R1 st X RNG m).
  { unfold drinv. split; [exact ARNG|]. split; [exact AR1|]. split; [exact BL|]. split; [exact HF|].
    split; [eapply RSEC_perm'; [| exact RS]; apply Permutation_sym; subst R1; apply inflight_popr; [exact ET| exact EP| exact CLEN]|].
    split; [exact MI|]. split; [exact ST|]. split; [exact FLE|]. split; [exact MU0|]. split; [exact CP0| exact SK]. }
  (* [comment removed for export] *)
  (nd_pre (pendb_busy L st X R1 m (qb_slot q) HQ1 eq_refl) 6%nat; intros nb bb1 bctx bl1 bl2 XBB; nd_post).
  destruct (any_range L st X BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx bl1 bl2 XBB WF) as [_ KQ].
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  (nd_pre BG 9%nat; intros _ _ BG1 BG2 (BG3a & BG3 & BG3b) BG4 BG5 BG6 BG7; nd_post).
  assert (RB : rng RNG B 24).
  { (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _). eapply rng_sub; [exact RR1| |]; clear -BG1 BG2 BG3; unfold K_FREEARR_OFF; lia. }
  (try pose proof atop_range as ATR). unfold Q_BATCH in CRNG.
  pose proof (tmp_len_bound R1 L st X m ALO WF HQ1) as TLEN. subst R1. cbn [qr_tmp qr_popr] in TLEN. set (R1 := qr_popr R b q T) in *.
  (* [comment removed for export] *)
  assert (QF : (T = [] /\ qfirst L (map snd T) = 0) \/ (T <> [] /\ 17594333495296 <= qfirst L (map snd T) /\ qfirst L (map snd T) + 8192 <= ATOP)).   (* [comment removed for export] *)
  { destruct T as [|[b' q'] T']; [left; split; reflexivity| right]. split; [discriminate|].
    pose proof (tmp_head_geo R1 L st X m b' q' T' ALO WF HQ1 eq_refl) as G. (try pose proof atop_range as ATR). unfold qfirst, qaddrs. cbn [map hd]. exact G. }
  (* [comment removed for export] *)
  assert (REST : forall m2 rax2 (a1x : word),
    munch [(TMP, TMP + 32)]%Z m m2 -> wmono asegs m m2 -> mem_inv asegs m2 -> stk asegs m2 lo SP -> munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m2 ->
    rw_cells asegs m2 SP (dr_frame junk8) ->
    rw_cells asegs m2 TMP [C8 (Z_to_bv 64 (Z.of_nat (S (length T)))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb] ->
    rw_cells asegs m2 B [C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))] ->
    evtF asegs RNG (fun ms' => implS asegs RNG (aembed ATOP (do_recycle st (b :: map fst T) K)) (epostF Q) ms')
         (MS (mkR rax2 (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 701336) (Z_to_bv 64 (Z.of_nat (S (length T)))) a1x a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 701400) (Z_to_bv 64 702024) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35efc) fc None m2 (seg_rom asegs))).
  { intros m2 rax2 a1x MUp WMp MI2 ST2 MU02 FR2 TH2 CC2. unfold dr_frame in FR2.
    zstep.                                                 (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (Z.of_nat (length T))) ltac:(f_equal; clear; lia).
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AR2 : AREP (AHr R1 (csx st R1)) L st X mx);
      [ eapply (AREP_frame_ext _ (HL R1 (csx st R1)) L st X m mx); [exact ALO| exact AR1| exact MUp| exact WMp|];
        constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO TMPLO; lia |];
      assert (HF2 : AF L LB mx);
      [ eapply AFD; [exact HF| exact MUp| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO| cbn [fst]; atop_facts; clear -CEIL LO TMPLO; lia]
        | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO TMPLO; lia] |];
      assert (CP2 : cpres L HI LB m0 mx);
      [ eapply cpres_trans; [exact CP0|]; eapply cpres_of_munch; [exact MUp|]; intros iv [<-|[]]; cbn [fst snd];
        eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO TMPLO; lia| exact HHI] |];
      assert (INV2 : drinv R1 st X RNG mx);
      [ unfold drinv; (nd_pre INV1 6%nat; intros _ _ _ _ RS1 _; nd_post); split; [exact ARNG|]; split; [exact AR2|]; split; [exact BL|]; split; [exact HF2|]; split; [exact RS1|];
        split; [assumption|]; split; [assumption|]; split; [exact FLE|]; split; [assumption|]; split; [exact CP2| exact SK] |];
      assert (EC2 : u64arr asegs mx (B + 24) (map (ehdr L) all));
      [ eapply (u64arr_frameD _ _ _ _ _ EC MUp); rewrite length_map; cbn [disjoint_from fst snd]; split; [left; clear -LALL CRNG BG5 CEIL LO TMPLO; lia| exact I] |]
    end.
    step.                                                  (* [comment removed for export] *)
    rewrite do_recycle_cons, <- MALL.
    step. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear -CRNG; lia).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      assert (E0 : all = []) by (destruct all; [reflexivity| exfalso; cbn [length] in LALL; clear -LALL KC; lia]).
      rewrite E0. cbn [map recycle_chunks].
      apply evtF_done.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) R1 st X RNG _ (qb_slot q) T);
        [exact INV2| reflexivity| reflexivity| subst R1; unfold qr_popr; cbn [qr_pend]; fold all; exact E0| eassumption| eassumption|].
      intros st4 X4 RNG4 m4 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV4 FR4 TH4.
      (pose proof INV4 as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ MI4 ST4 FLE4 MU04 _; nd_post). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4].
    - (* [comment removed for export] *)
      assert (NEA : all <> []) by (intros E0; apply KC; rewrite <- LALL, E0; reflexivity).
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      setreg 23 (Z_to_bv 64 (B + 152 + 8 * 0)) ltac:(f_equal; clear; lia).
      setreg 24 (Z_to_bv 64 (16 + Z.of_nat (length all))) ltac:(f_equal; clear -LALL; lia).
      setreg 25 (Z_to_bv 64 (16 + 0)) ltac:(f_equal; clear; lia).
      rewrite <- LALL.
      apply evtF_done.
      eapply (dr_inner Q all (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 (map fst T) K)) R1 st X RNG _ (qb_slot q) all T 0);
        [exact INV2| | reflexivity| reflexivity| exact NEA| clear; lia| eassumption| eassumption| eassumption|].
      { unfold batch_ok. subst R1. unfold qr_popr. cbn [qr_tmp qr_pendb]. split; [reflexivity|]. split; [reflexivity|]. unfold Q_BATCH. split; [clear -LALL CRNG; lia| clear -KQ; lia]. }
      intros st3 X3 RNG3 m3 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV3 FR3 TH3.
      unfold ms_in.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) (qr_drop R1 []) st3 X3 RNG3 m3 (qb_slot q) T);
        [exact INV3| reflexivity| reflexivity| reflexivity| exact FR3| exact TH3|].
      intros st4 X4 RNG4 m4 junk8'' rax'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' INV4 FR4 TH4.
      (pose proof INV4 as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ MI4 ST4 FLE4 MU04 _; nd_post). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8'');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4]. }
  (* [comment removed for export] *)
  unfold ms_out, adorec_lout. unfold thdr in TH. cbn [length map snd qfirst qaddrs hd] in TH. change (abatch_addr L (qb_slot q)) with B in TH.
  change (Z.of_nat (length ((b, q) :: T))) with (Z.of_nat (S (length T))).
  pose proof (munch_refl [(TMP, TMP + 32)]%Z m) as MUp. pose proof (wmono_refl asegs m) as WMp. unfold dr_frame in FR.
  iprefix.
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct QF as [[-> QF0]|(TNE & QF1 & QF2)]; [exfalso; apply KN; rewrite QF0; reflexivity|].
    rewrite (qlast_cons_ne q (map snd T)) in * by (destruct T; [congruence| discriminate]).
    eapply REST; eassumption.
  - (* [comment removed for export] *)
    destruct QF as [[ET0 QF0]|(TNE & QF1 & QF2)]; [| exfalso; first [rewrite Z.mod_small in KN by (clear -QF1 QF2; lia)| rewrite unsigned_lit in KN by (clear -QF1 QF2; lia)| idtac]; clear -KN QF1; lia].
    step.                                     (* [comment removed for export] *)
    subst T. eapply REST; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma drinv_done : forall R st X RNG m, qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] -> drinv R st X RNG m -> drinv (qr_done R) st X RNG m.
Proof.
  intros R st X RNG m ET EB EP (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK).
  assert (EI : inflight (qr_done R) = inflight R) by (unfold inflight, secsT, qr_done; cbn [qr_tmp qr_pend]; rewrite ET, EP; reflexivity).
  unfold drinv. rewrite (ltac:(unfold csx; rewrite EI; reflexivity) : csx st (qr_done R) = csx st R), EI.
  split; [exact ARNG|]. split; [| exact (conj BL (conj HF (conj RS (conj MI (conj ST (conj FLE (conj MU0 (conj CP0 SK))))))))].
  unfold AHr, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr in AR |- *. eapply AREP_reqs; [exact AR| | intros HS'; exact HS'].
  (nd_pre AR 7%nat; intros _ _ _ _ _ HQ _; nd_post). cbn [ah_quar] in HQ. (nd_pre HQ 9%nat; intros QC MX TC GL TB IA CP NUM NT; nd_post).
  unfold AQdr, qr_done. cbn [qr_loc qr_glob qr_tmp qr_ia qr_pendb qr_pend map]. rewrite ET in NT. cbn [map] in NT.
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact I|]. split; [exact IA|]. split; [| exact (conj NUM NT)].
  eapply qcoupled_rec_perm; [exact CP| | | | | reflexivity].
  - exact (proj1 CP).
  - exact (proj1 (proj2 CP)).
  - unfold qr_entries. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite ET, EP. cbn [map qentries app]. apply Permutation_refl.
  - unfold qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map app]. apply Permutation_refl.
Qed.

Definition adorec__stmt : Prop := forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (R : qrconc) (X : aconc) (T : list (abatch * qbatchc)) (tb : word) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  arng L RNG0 st0 -> AREP (AHr R (csx st0 R)) L st0 X m0 -> ablocks L st0 X LB -> AF L LB m0 -> RSEC (inflight R) RNG0 ->
  qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] ->
  mem_inv asegs m0 -> stk asegs m0 lo (bv_unsigned sp) ->
  rw_cells asegs m0 TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 (tb' : word) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 -> stk asegs m1 lo (bv_unsigned sp) ->
     rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom asegs))) ->
  implS asegs RNG0 (aembed ATOP (do_recycle st0 (map fst T) K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TMP) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 adorec_entry) fc None m0 (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RT : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 0).
Variable K : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 2).
Variable R : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 3).
Variable X : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 4).
Variable T : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 5).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 6).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 7).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 8).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 14).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 15).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 16).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 17).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'adorec__stmt 18).
#[using="HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Lemma adorec__body : ltac:(let T := type of (fun (h : adorec__stmt) => h RT K Q R X T tb t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RT, (K, (Q, (R, (X, (T, (tb, (t0, (t1, (t2, (a0, (a4, (a5, (a6, (a7, (t3, (t4, (t5, t6))))))))))))))))))) as _.
  intros ARNG AR BL HF RS ET EB EP MI ST TH KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. (nd_pre AR0 7%nat; intros WF _ _ _ _ HQ _; nd_post). cbn [ah_quar AHr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARecyc1P__A3W.ARecyc1P.TwB.AHr] in HQ.
  pose proof (tmp_len_bound R L st0 X m0 ALO WF HQ) as TLEN. rewrite ET in TLEN.
  pose proof (munch_refl [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0) as MU0. pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m0) as MUf. pose proof (wmono_refl asegs m0) as WM0.
  unfold adorec_entry. unfold thdr in TH.
  iprefix.
  carve_frame 112%nat ST.
  do 12 step.                                 (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. step.                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (INV : drinv R st0 X RNG0 mx);
    [ unfold drinv; split; [exact ARNG|];
      split; [eapply (AREP_frame_ext _ (HL R (csx st0 R)) L st0 X m0 mx); [exact ALO| exact AR| exact MUf| exact WM0|];
              constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO; lia |];
      split; [exact BL|];
      split; [eapply AFD; [exact HF| exact MUf| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO|]; cbn [fst]; atop_facts; clear -CEIL LO; lia
               | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO; lia] |];
      split; [exact RS|]; split; [assumption|]; split; [rewrite SPE; assumption|]; split; [intros bb j Hb; exact Hb|]; split; [exact MU0|];
      split; [eapply cpres_of_munch; [exact MUf|]; intros iv [<-|[]]; cbn [fst snd]; eapply (np_high L st0 X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| clear -TMPLO HHI; lia] |];
      unfold st_keep; repeat (split; [reflexivity|]); reflexivity |]
  end.
  (* [comment removed for export] *)
  assert (EPI : forall m1 st1 X1 RNG1 junk8' (tb' : word) rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6',
    drinv (qr_done R) st1 X1 RNG1 m1 -> rw_cells asegs m1 SP (dr_frame junk8') -> rw_cells asegs m1 TMP (thdr [] tb') ->
    evtF asegs RNG1 (fun ms' => implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms')
         (MS (mkR rax' (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x35f74) fc None m1 (seg_rom asegs))).
  { intros m1 st1 X1 RNG1 junk8' tb' rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6' INV1 FR1 TH1.
    (pose proof INV1 as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ MI1 ST1 FLE1 _; nd_post). destruct (drinv_rngs _ _ _ _ _ INV1) as [RSTK1 RTMP1].
    unfold dr_frame in FR1.
    do 11 step.                               (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    setreg 2 sp ltac:(rewrite SPE; replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
    step.                                     (* [comment removed for export] *)
    release_frame FR1 ST1 (bv_unsigned sp).
    apply evtF_done. eapply KONT; [exact INV1| exact ST1| exact TH1]. }
  step. if_cases K0; zify_cond K0.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct T as [|bq T']; [| exfalso; cbn [length] in K0, TLEN; first [rewrite Z.mod_small in K0 by (clear -TLEN; lia)| rewrite unsigned_lit in K0 by (clear -TLEN; lia)| idtac]; clear -K0; lia].
    cbn [map do_recycle].
    eapply EPI; [apply drinv_done; [exact ET| exact EB| exact EP| exact INV]| exact FR| exact TH].
  - destruct T as [|bq T']; [exfalso; apply K0; reflexivity|].
    do 8 step.                                (* [comment removed for export] *)
    apply evtF_done.
    eapply (dr_outer Q (bq :: T') K R st0 X RNG0 _ tb); [exact INV| exact ET| exact EB| exact EP| discriminate| exact FR| exact TH|].
    intros st1 X1 RNG1 m1 junk8' tb' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' INV1 FR1 TH1.
    unfold ms_out. iprefix. eapply EPI; [exact INV1| exact FR1| exact TH1].
Qed.
End Zd2.
#[using="HL SREC ADD AFD ASECc_perm ASECc_wf1 ASECc_disj ASECc_nres RSEC_app RSEC_perm' RSEC_mono' RSEC_arng ALO CEIL LO SP47 TMPLO HHI RSTK0 RTMP0"] Theorem adorec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (R : qrconc) (X : aconc) (T : list (abatch * qbatchc)) (tb : word) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  arng L RNG0 st0 -> AREP (AHr R (csx st0 R)) L st0 X m0 -> ablocks L st0 X LB -> AF L LB m0 -> RSEC (inflight R) RNG0 ->
  qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] ->
  mem_inv asegs m0 -> stk asegs m0 lo (bv_unsigned sp) ->
  rw_cells asegs m0 TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 (tb' : word) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 -> stk asegs m1 lo (bv_unsigned sp) ->
     rw_cells asegs m1 TMP (thdr [] tb') ->
     implS asegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom asegs))) ->
  implS asegs RNG0 (aembed ATOP (do_recycle st0 (map fst T) K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TMP) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 adorec_entry) fc None m0 (seg_rom asegs)).
Proof. exact adorec__body. Qed.
End DoRec.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
End F_adorec.
