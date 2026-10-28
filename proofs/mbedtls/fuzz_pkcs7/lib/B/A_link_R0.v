(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_main_target A_link_layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AHeapR AHeapM AFreePost AHeapHIA AW_AMemmoveS AHeapInstX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ro_addr_ltA : forall a : Z, 0 <= a < 0x10000 -> ro_addr asegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite unsigned_lit by lia.
  unfold asegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments. cbn [find_segment].
  repeat match goal with
  | |- context [Z.of_N (seg_base ?s)] => let v := eval vm_compute in (Z.of_N (seg_base s)) in replace (Z.of_N (seg_base s)) with v by (vm_compute; reflexivity)
  | |- context [Z.of_N (seg_size ?s)] => let v := eval vm_compute in (Z.of_N (seg_size s)) in replace (Z.of_N (seg_size s)) with v by (vm_compute; reflexivity)
  | |- context [seg_writable ?s] => let v := eval vm_compute in (seg_writable s) in replace (seg_writable s) with v by (vm_compute; reflexivity)
  end.
  repeat match goal with |- context [if ?c then _ else _] =>
    let b := fresh in destruct c eqn:b; [apply andb_prop in b; destruct b as [?%Z.leb_le ?%Z.leb_le]; first [reflexivity | exfalso; lia] | clear b] end.
  reflexivity.
Qed.

Lemma roimg0 : forall a : Z, ro_addr asegs (wa a) = true -> 0 <= a < 2 ^ 64 -> 0x10000 <= a < 0x65f000.
Proof.
  intros a RO Ha.
  destruct (Z_lt_ge_dec a 0x10000) as [LT|GE]; [rewrite ro_addr_ltA in RO by lia; discriminate|].
  destruct (Z_lt_ge_dec a 0x0f1000) as [LT|GE2]; [lia|]. rewrite ro_addr_geA in RO by lia. discriminate.
Qed.

Lemma primg0 : forall a : Z, rtc_prist a -> 0x10000 <= a < 0x65f000.
Proof.
  intros a H. unfold rtc_prist in H. apply Exists_exists in H. ddestruct H as ([lo hi] & IN & RG). cbn [fst snd] in RG.
  unfold rtc_pristine in IN. cbn [In] in IN.
  repeat (destruct IN as [E|IN]; [inversion E; subst; unfold AGLOB_LO, AGLOB_HI in *; lia|]). destruct IN.
Qed.

Section R0.
  Context {hAR : arun}.
  Variable STKLO : Z.
  Hypothesis STKLO_OK : ACEIL <= STKLO.

  #[using="Type"] Lemma a_layout_ok_R0 : a_layout_ok (R0 STKLO).
  Proof.
    constructor; try reflexivity; try (cbn; lia).
    - exact AL0_img.
    - exact AL0_wf.
    - exact roimg0.
    - exact primg0.
    - intros m H. exact H.
    - (* [comment removed for export] *)
      unfold P_ecp_sinv.ecp_ids_lok. cbn -[Z.add Z.le Z.lt]. unfold RT. cbn [HMFrame.in_rangesZ fst snd].
      repeat split; try lia.
    - (* [comment removed for export] *)
      unfold P_pk_sinv.mc_lok. cbn -[Z.add Z.le Z.lt]. unfold RT. cbn [HMFrame.in_rangesZ fst snd].
      repeat split; try lia.
  Qed.

  Variable B12 : b12_T.
  Variable MOD_DIE : mod_die_T.
  Variable FH : freeH_T STKLO.

  #[using="Type"] Lemma a_hia_ok_R0 : a_hia_ok (R0 STKLO) (artA_i STKLO STKLO_OK B12 MOD_DIE FH).
  Proof.
    constructor.
    - intros h LB LF m H. exact (hm_blocks_nodup_i STKLO h LB LF m H).
    - exact (amemmove_stmt_i STKLO STKLO_OK B12 MOD_DIE FH).
    - (* [comment removed for export] *)
      intros h LB LF m g H G. exact (ssmap_i STKLO h LB LF m g H G).
    - (* [comment removed for export] *)
      intros h LB LB' LF m H PM. exact (hmperm_i STKLO h LB LB' LF m H PM).
  Qed.
End R0.
