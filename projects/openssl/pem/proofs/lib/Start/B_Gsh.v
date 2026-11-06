(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanDescs AsanRehash AsanRegModel AsanGshModel AsanRegRun B_RegConsts B_PlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition B_NG : nat := 11827.
(* [comment removed for export] *)
Definition B_scan : option (list RGM.desc) := RGN.scan B_SEGS B_NG (RGM.c_tab B_RGC).
Definition B_GTAB : list RGM.desc := GSM.olist B_scan.
Definition B_gtab_chk : bool := GSM.gtab_chkf B_NG (RGM.c_tab B_RGC) (RGM.c_tabend B_RGC) (RGM.l_ilo B_RGL) B_scan.
(* [comment removed for export] *)
Lemma B_gtab_ok : B_gtab_chk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma B_scan_eq : RGN.scan B_SEGS B_NG (RGM.c_tab B_RGC) = B_scan.
Proof. exact (eq_refl (RGN.scan B_SEGS B_NG (RGM.c_tab B_RGC))). Qed.

Lemma B_GTAB_facts : RGN.scan B_SEGS (length B_GTAB) (RGM.c_tab B_RGC) = Some B_GTAB
  /\ RGM.c_tab B_RGC + 64 * Z.of_nat (length B_GTAB) = RGM.c_tabend B_RGC
  /\ GSM.sortedb (RGM.l_ilo B_RGL) B_GTAB = true.
Proof.
  destruct (GSM.gtab_chkf_spec _ _ _ _ _ B_gtab_ok) as (H0 & H1 & H2 & H3). fold B_GTAB in H0, H1, H2, H3.
  split; [|split; [exact H2 | exact H3]]. rewrite H1, B_scan_eq. exact H0.
Qed.
Definition B_GTAB_scan := proj1 B_GTAB_facts.
Definition B_GTAB_len := proj1 (proj2 B_GTAB_facts).
Definition B_GTAB_sorted := proj2 (proj2 B_GTAB_facts).

(* [comment removed for export] *)
Definition B_HULLS : list (Z * Z) := [(0x800012b4, 0x80006b2c); (0x80006b34, 0x8000adf8); (0x8000ae28, 0x80011eac); (0x80011eb0, 0x800149a0); (0x80014a50, 0x8001a408); (0x800a4e6c, 0x800aa200); (0x800aa220, 0x800abd04); (0x800abd3c, 0x800ae4c8); (0x800ae4e0, 0x800b16b4); (0x800b16c8, 0x800b4590); (0x80172338, 0x80172bb8)].

(* [comment removed for export] *)
#[global] Instance B_BLOBS : BlobEnv := fun k =>
  if Nat.leb K_GSH0 k then match nth_error B_HULLS (k - K_GSH0) with
                           | Some (lo, hi) => map (fun z => Z_to_bv 8 z) (GSM.gsh_list B_RGL B_GTAB lo hi)
                           | None => []
                           end
  else [].

Lemma B_BLOBS_hull : forall j lo hi, nth_error B_HULLS j = Some (lo, hi) ->
  B_BLOBS (K_GSH0 + j)%nat = map (fun z => Z_to_bv 8 z) (GSM.gsh_list B_RGL B_GTAB lo hi).
Proof.
  intros j lo hi H. unfold B_BLOBS. rewrite (proj2 (Nat.leb_le _ _) (Nat.le_add_r K_GSH0 j)).
  replace (K_GSH0 + j - K_GSH0)%nat with j by lia. rewrite H. reflexivity.
Qed.
