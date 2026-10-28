(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore CxPlan CxPlanSound HBPlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition HAT : atable :=
  {| img_lo := 0x10000; img_hi := 0xbfb000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x194ffc; rw_lo := 0x569000; rw_len := 0x692000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x1d0470; x_imemcpy := 0x1d03f4; x_memset := 0x56123c; x_memcpy := 0x560e08; x_memiszero := 0x1d09a0;
     x_istrncpy := 0x1d089c; x_sealed := 0x1410c; x_popfree := 0x19b7c4;
     x_sniff := 0; sniff_tab := 2 ^ 64; sniff_cell := 0;
     x_envscan := 0x554f94; x_envscan_k := 0x554fa0; x_pnscan := 0x555058; x_pnscan_k := 0x555064;
     stops_more := [0x1d1b68; 0x55b4a8];
     zone_lo := 0x7fff7000; lowsh_hi := 0x8fff7000; highsh_lo := 0x2008fff7000; zone_hi := 0x10007fff8000 |}.

Lemma hat_img_lo : img_lo HAT = HA_IMG_LO. Proof. reflexivity. Qed.
Lemma hat_img_hi : img_hi HAT = HA_IMG_HI. Proof. reflexivity. Qed.
Lemma hat_entry : a_entry HAT = HA_ENTRY. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hat_segs_wx : wx_segs_nowrap HASEGS.
Proof. exact ha_wx. Qed.

Lemma hat_in_hull : forall a : word,
  CXS.in_hull HAT (bv_unsigned a) = false -> find_segment HASEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply ha_outside_hull. unfold CXS.in_hull in H. cbn [img_lo img_hi HAT] in H.
  unfold HA_IMG_LO, HA_IMG_HI. apply Bool.andb_false_iff in H. destruct H as [H|H].
  - apply Z.leb_gt in H. lia.
  - apply Z.ltb_ge in H. lia.
Qed.

Lemma hat_res_len : CXS.res_len_ok HASEGS HAT.
Proof. unfold CXS.res_len_ok. rewrite ha_res_len. reflexivity. Qed.

Lemma hat_res_hull : Forall (fun iv => img_lo HAT <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi HAT)
                            (segments_reserved HASEGS).
Proof. exact ha_res_hull. Qed.

Lemma hat_hull_ok : CXS.hull_ok HAT.
Proof. unfold CXS.hull_ok. cbn [img_lo img_hi HAT]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma hat_shadow_ok : CXS.shadow_ok HAT.
Proof. unfold CXS.shadow_ok. cbn [shadow_off HAT]. lia. Qed.

Lemma hat_zone_ok : CXS.zone_ok HAT.
Proof.
  unfold CXS.zone_ok. cbn [zone_lo lowsh_hi highsh_lo zone_hi shadow_off img_hi HAT]. unfold TASK, CEIL.
  repeat split; cbv; try reflexivity; try lia; congruence.
Qed.

(* [comment removed for export] *)
Lemma hat_res_cover : forall z, img_lo HAT <= z < img_hi HAT -> CXS.in_ivs z (segments_reserved HASEGS) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi HAT] in Hz. rewrite ha_res_eq. unfold CXS.in_ivs. apply existsb_exists.
  Ltac one_iv := cbn [fst snd]; rewrite !u64_lit by lia; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  destruct (Z_lt_le_dec z 0x194000) as [H1|H1].
  { eexists. split; [left; reflexivity|]. one_iv. }
  destruct (Z_lt_le_dec z 0x569000) as [H2|H2].
  { eexists. split; [right; left; reflexivity|]. one_iv. }
  destruct (Z_lt_le_dec z 0x5e1000) as [H3|H3].
  { eexists. split; [right; right; left; reflexivity|]. one_iv. }
  eexists. split; [right; right; right; left; reflexivity|]. one_iv.
Qed.

Lemma hat_hull_ne : img_lo HAT < img_hi HAT.
Proof. cbn [img_lo img_hi HAT]. lia. Qed.

(* [comment removed for export] *)
Lemma hat_if_ph : ph_addr_z HAT = Z.of_N (ph_addr HAPH) /\ ph_ent_z HAT = Z.of_N (ph_ent HAPH) /\ ph_num_z HAT = Z.of_N (ph_num HAPH).
Proof. rewrite ha_phdrs_eq. cbn. repeat split; reflexivity. Qed.

Lemma hat_if_hull : 0 <= img_lo HAT <= img_hi HAT /\ img_hi HAT <= 2 ^ 32 /\ img_lo HAT mod 4096 = 0 /\ img_hi HAT mod 4096 = 0.
Proof. cbn [img_lo img_hi HAT]. repeat split; cbv; try reflexivity; congruence. Qed.

Lemma hat_if_top : reserved_top (segments_reserved HASEGS) = img_hi HAT.
Proof. vm_compute. reflexivity. Qed.

Lemma hat_if_sizes : CXS.sum_sizes (segments_reserved HASEGS) = img_hi HAT - img_lo HAT.
Proof. rewrite ha_res_eq. cbn [CXS.sum_sizes snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

Lemma hat_if_rw : (0 <= rw_lo HAT /\ 0 <= rw_len HAT /\ rw_lo HAT + rw_len HAT < 2 ^ 64)
                  /\ forall m (x : word), rw_lo HAT <= bv_unsigned x < rw_lo HAT + rw_len HAT -> wview HASEGS m x <> None.
Proof.
  split; [cbn [rw_lo rw_len HAT]; lia|].
  intros m x Hx. apply ha_rw_window. cbn [rw_lo rw_len HAT] in Hx. unfold HA_RW_LO, HA_RW_HI. lia.
Qed.
