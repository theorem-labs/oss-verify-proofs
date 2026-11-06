(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "mslot"; "sptr"; "ameta"; "MUsed"; "am_aidx"; "am_last"; "am_sc"; "am_maplen"; "am_mem"; "slot_start"; "st_metas"; "PGSZ"; "UNIT"; "class_size"; "stride_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "reach_fields"; "tier"; "hosts_ok"; "partial_ok"; "@Corelib.Init.Datatypes"; "prod"; "Some"; "option"; "bool"; "pair"; "list"; "nat"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "eqb"; "add"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "nested_host_classes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "upd_meta"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocLemmasBase MallocWfFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition hosts_ok (s : astate) : Prop := ltac2:(tb__ "0|2|
S7S8S7S8S5S0S1cS6A1S22Vs;R5A2S1bS6S9R4A1A2A3M0S0S5SdR5A1Z0M1A3G0S1S23G1R4A2S23R4SbR5A1A2A2S0S7SeR8A1SfR6R5A2A3S2bS5ScR7A1S29A3F_;F_;F_;F_;F_;Fi';Fam';Fg';Fam;Fg;").

Definition tier (sc : Z) : nat := ltac2:(tb__ "0|1|
S1dS20L_;M0S25Vsc;Z17A2U0G0S25Vsc;Z13A2U1G0S25Vsc;ZfA2U2U3X1dx2X1dx2X1dx2").

Lemma tier_le3 sc : (tier sc <= 3)%nat.
Proof. unfold tier. repeat (destruct (_ =? _)); lia. Qed.

Lemma tier_host_lt (c p : Z) : ltac2:(tb__ "0|0|
S2bS5Vp;S29A3S24Vc;Vp;A2S2cS17Vp;A1S17Vc;A1A2F_;F_;").
Proof.
  unfold nested_host_classes, tier. intros [<-|[<-|[<-|[]]]] Hlt; cbn;
    repeat match goal with |- context [c =? ?k] => destruct (Z.eqb_spec c k); [subst; try lia|] end; cbn; lia.
Qed.

Definition partial_ok (s : astate) : Prop := ltac2:(tb__ "0|0|
S7S8S0S1cS6A1S22Vs;R2A2S1bS6S9R1A1A2A3S24SaR2A1SbR2A1A2S24S28S11S12A2S27S13ScR3A1A1S26SaR3A1Z2A2A2A2F_;F_;Fam;Fg;").

Definition reach_ok (s : astate) : Prop := ltac2:(tb__ "0|0|
S1S18Vs;A1S19Vs;A1A2").

Definition reach_fields (am : ameta) : Z * sptr * Z * Z := ltac2:(tb__ "0|1|
S1eS1aS1aS5S7A2M0S5A2S5S1eG0S5S1eS5S7SdVam;A1SeVam;A1A4SbVam;A1A4ScVam;A1A4").

Lemma reach_ok_nometas s : ltac2:(tb__ "0|1|
S0S1fS1aS7S6A2M0A1S10Vs;A1S21G0A1A3S15Vs;A1F_;").
Proof.
  intros E. split.
  - intros g am g' am' i' M. unfold MT, mlookup in M. rewrite E in M. discriminate.
  - intros g am M. unfold MT, mlookup in M. rewrite E in M. discriminate.
Qed.

Lemma class_size_nonneg sc : 0 <= class_size sc.
Proof.
  unfold class_size, znth.
  assert (H : Forall (fun x => 0 <= x) size_classes) by (unfold size_classes; repeat constructor; lia).
  destruct (nth_in_or_default (Z.to_nat sc) size_classes 0) as [Hin | E].
  - pose proof (proj1 (Forall_forall _ _) H _ Hin) as X. cbn beta in X. unfold UNIT. nia.
  - rewrite E. unfold UNIT. lia.
Qed.

Lemma reach_ok_mono s s' : ltac2:(tb__ "0|2|
S7S8S0S1cS6A1M0S22Vs';R2A2S1bS6S9R1A1A2M1A3S3S8S8S1S0G0S22Vs;R4A2G1A3S1S0S1aS1aS1aS5S7A2S5A2S5A2S16R3A1S16R1A1A3S23SaR1A1SaR3A1A2A2A2Lam;A2F_;Fam';Fg;S15Vs;A1S15Vs';A1F_;F_;").
Proof.
  intros H [HH HP]. split.
  - intros g am' g' bm' i' M' Hml M2' Hi' Hmem.
    destruct (H g am' M') as (am & M & F & _). destruct (H g' bm' M2') as (bm & M2 & F2 & _).
    unfold reach_fields in F, F2. injection F as E1 E2 E3 E4. injection F2 as F1' F2' F3' F4'.

    rewrite F4'. apply (HH g am g' bm i' M); [congruence | exact M2 | rewrite <- F3'; exact Hi' |].
    rewrite <- E2, Hmem. unfold slot_start, stride_of. rewrite F1', F2', F3', F4'. reflexivity.
  - intros g am' M' Hlt. destruct (H g am' M') as (am & M & F & LE).
    unfold reach_fields in F. injection F as E1 E2 E3 E4. rewrite E4.
    assert (Hlt0 : am_aidx am < am_last am) by lia.
    pose proof (HP g am M Hlt0) as X. pose proof (class_size_nonneg (am_sc am)). nia.
Qed.

Lemma reach_ok_same_used s s' : ltac2:(tb__ "0|2|
S7S8S4S0S1cS6A1M0S22Vs';R2A2S1bS6S9R1A1A2M1A3S0G0S22Vs;R2A2G1A3A2Fam;Fg;S15Vs;A1S15Vs';A1F_;F_;").
Proof.
  intros H. apply reach_ok_mono. intros g am' M'. exists am'. split; [apply H; exact M'|]. split; [reflexivity | lia].
Qed.

Lemma reach_ok_upd s g am am' : ltac2:(tb__ "0|0|
S0S1cS6A1S22Vs;Vg;A2S1bS6S9Vam;A1A2A3S0S1aS1aS1aS5S7A2S5A2S5A2S16Vam';A1S16Vam;A1A3S23SaVam;A1SaVam';A1A2S15Vs;A1S15S2aVg;S9Vam';A1Vs;A3A1F_;F_;F_;F_;").
Proof.
  intros M F LE. apply reach_ok_mono. intros q bm M'.
  destruct (sptr_eq_dec q g) as [->|NE].
  - rewrite MT_upd_same in M'. injection M' as <-. exists am. auto.
  - rewrite (MT_upd_other g _ s q NE) in M'. exists bm. split; [exact M'|]. split; [reflexivity|lia].
Qed.

Lemma reach_ok_unuse s g x : ltac2:(tb__ "0|0|
S8S2S0S6Vx;S9R1A1A3A1Fam;S15Vs;A1S15S2aVg;Vx;Vs;A3A1F_;F_;").
Proof.
  intros Hx. apply reach_ok_mono. intros q bm M'.
  destruct (sptr_eq_dec q g) as [->|NE].
  - rewrite MT_upd_same in M'. injection M' as E. exfalso. exact (Hx bm E).
  - rewrite (MT_upd_other g _ s q NE) in M'. exists bm. split; [exact M'|]. split; [reflexivity|lia].
Qed.

Lemma reach_ok_install s m am_new : ltac2:(tb__ "0|5|
S8S2S0S1cS6A1M0S22Vs;Vm;A2S1bS6S9R1A1A2A3A1Fam;S23Z0M1S14Vam_new;A1A2S7S8S5S0G0S22Vs;R3A2S1bS6S9R2A1A2A3M2S0S5SdR3A1G1A3S1S23G1R3A2S23R3SbVam_new;A1M3A2A2S2S0S7SeR5A1SfVam_new;R4A2A3A1F_;F_;F_;Fi;Fam;Fg;S0S5SdVam_new;A1G1A3S7S8S5G2S1S23G1R2A2S23R2SbR3A1A2A2S0S7SeVam_new;A1SfR4R3A2A3S2bS5ScR5A1S29A3F_;F_;F_;Fi';Fam';Fg';F_;S24SaVam_new;A1M4G3A2S24S28S11S12A2S27S13ScVam_new;A1A1S26G4Z2A2A2A2F_;S15Vs;A1S15S2aVm;S9Vam_new;A1Vs;A3A1F_;F_;F_;F_;F_;F_;").
Proof.
  intros Hm Hst Hnonest Hhost Hpart [HH HP]. split.
  - intros g am g' am' i' M Hml M' Hi' Emem.
    destruct (sptr_eq_dec g m) as [->|NE]; destruct (sptr_eq_dec g' m) as [->|NE'].
    + rewrite MT_upd_same in M, M'. injection M as <-. injection M' as <-. exfalso.
      unfold slot_start in Emem. destruct (am_mem am_new) as [r o]. cbn [padd] in Emem. injection Emem as E.
      assert (0 <= stride_of am_new * i') by nia. unfold UNIT in E. lia.
    + rewrite MT_upd_same in M. injection M as <-. rewrite (MT_upd_other m _ s g' NE') in M'.
      exact (Hhost Hml g' am' i' M' Hi' Emem).
    + rewrite MT_upd_same in M'. injection M' as <-. rewrite (MT_upd_other m _ s g NE) in M.
      exfalso. exact (Hnonest g am i' M Hml Hi' Emem).
    + rewrite (MT_upd_other m _ s g NE) in M. rewrite (MT_upd_other m _ s g' NE') in M'. exact (HH g am g' am' i' M Hml M' Hi' Emem).
  - intros g am M Hlt. destruct (sptr_eq_dec g m) as [->|NE].
    + rewrite MT_upd_same in M. injection M as <-. exact (Hpart Hlt).
    + rewrite (MT_upd_other m _ s g NE) in M. exact (HP g am M Hlt).
Qed.

Lemma reach_ok_same_metas s s' : ltac2:(tb__ "0|0|
S0S1fS1aS7S6A2A1S10Vs';A1S10Vs;A1A3S15Vs;A1S15Vs';A1F_;F_;").
Proof. intros E. apply reach_ok_same_used. intros g am. unfold MT, mlookup. rewrite E. tauto. Qed.
