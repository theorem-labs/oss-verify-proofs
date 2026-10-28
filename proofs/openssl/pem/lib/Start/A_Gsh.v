(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanDescs AsanRehash AsanRegModel AsanGshModel AsanRegRun A_RegConsts A_PlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition A_NG : nat := 12200.
(* [comment removed for export] *)
Definition A_scan : option (list RGM.desc) := RGN.scan A_SEGS A_NG (RGM.c_tab A_RGC).
Definition A_GTAB : list RGM.desc := GSM.olist A_scan.
Definition A_gtab_chk : bool := GSM.gtab_chkf A_NG (RGM.c_tab A_RGC) (RGM.c_tabend A_RGC) (RGM.l_ilo A_RGL) A_scan.
(* [comment removed for export] *)
Lemma A_gtab_ok : A_gtab_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma A_scan_eq : RGN.scan A_SEGS A_NG (RGM.c_tab A_RGC) = A_scan.
Proof. exact (eq_refl (RGN.scan A_SEGS A_NG (RGM.c_tab A_RGC))). Qed.

Lemma A_GTAB_facts : RGN.scan A_SEGS (length A_GTAB) (RGM.c_tab A_RGC) = Some A_GTAB
  /\ RGM.c_tab A_RGC + 64 * Z.of_nat (length A_GTAB) = RGM.c_tabend A_RGC
  /\ GSM.sortedb (RGM.l_ilo A_RGL) A_GTAB = true.
Proof.
  destruct (GSM.gtab_chkf_spec _ _ _ _ _ A_gtab_ok) as (H0 & H1 & H2 & H3). fold A_GTAB in H0, H1, H2, H3.
  split; [|split; [exact H2 | exact H3]]. rewrite H1, A_scan_eq. exact H0.
Qed.
Definition A_GTAB_scan := proj1 A_GTAB_facts.
Definition A_GTAB_len := proj1 (proj2 A_GTAB_facts).
Definition A_GTAB_sorted := proj2 (proj2 A_GTAB_facts).

(* [comment removed for export] *)
Definition A_HULLS : list (Z * Z) := [(0x80001220, 0x80006bc8); (0x80006bcc, 0x8000b284); (0x8000b2b4, 0x80012174); (0x80012180, 0x800156cc); (0x8001577c, 0x8001b1a0); (0x8009dd8c, 0x800a193c); (0x800a196c, 0x800a312c); (0x800a314c, 0x800a7428); (0x800a7440, 0x800aa664); (0x800aa678, 0x800ad4e8); (0x8016be38, 0x8016c6b8)].

(* [comment removed for export] *)
#[global] Instance A_BLOBS : BlobEnv := fun k =>
  if Nat.leb K_GSH0 k then match nth_error A_HULLS (k - K_GSH0) with
                           | Some (lo, hi) => map (fun z => Z_to_bv 8 z) (GSM.gsh_list A_RGL A_GTAB lo hi)
                           | None => []
                           end
  else [].

Lemma A_BLOBS_hull : forall j lo hi, nth_error A_HULLS j = Some (lo, hi) ->
  A_BLOBS (K_GSH0 + j)%nat = map (fun z => Z_to_bv 8 z) (GSM.gsh_list A_RGL A_GTAB lo hi).
Proof.
  intros j lo hi H. unfold A_BLOBS. rewrite (proj2 (Nat.leb_le _ _) (Nat.le_add_r K_GSH0 j)).
  replace (K_GSH0 + j - K_GSH0)%nat with j by lia. rewrite H. reflexivity.
Qed.
