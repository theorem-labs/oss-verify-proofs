(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore CxPlan CxPlanSound HUPlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition H0T : atable :=
  {| img_lo := 0x10000; img_hi := 0x354000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0xe1830; rw_lo := 0x2c1000; rw_len := 0x93000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 10;
     x_imemset := 0; x_imemcpy := 0; x_memset := 0x2bc5a4; x_memcpy := 0x2bc024; x_memiszero := 0;
     x_istrncpy := 0; x_sealed := 0; x_popfree := 0;
     x_sniff := 0; sniff_tab := 2 ^ 64; sniff_cell := 0;
     x_envscan := 0; x_envscan_k := 0; x_pnscan := 0; x_pnscan_k := 0;
     stops_more := [0x2b55ac];
     zone_lo := 0x7fff7000; lowsh_hi := 0x8fff7000; highsh_lo := 0x2008fff7000; zone_hi := 0x10007fff8000 |}.

Lemma h0t_img_lo : img_lo H0T = H0_IMG_LO. Proof. reflexivity. Qed.
Lemma h0t_img_hi : img_hi H0T = H0_IMG_HI. Proof. reflexivity. Qed.
Lemma h0t_entry : a_entry H0T = H0_ENTRY. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma h0t_segs_wx : wx_segs_nowrap HSEGS.
Proof. exact h0_wx. Qed.

Lemma h0t_in_hull : forall a : word,
  CXS.in_hull H0T (bv_unsigned a) = false -> find_segment HSEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply h0_outside_hull. unfold CXS.in_hull in H. cbn [img_lo img_hi H0T] in H.
  unfold H0_IMG_LO, H0_IMG_HI. apply Bool.andb_false_iff in H. destruct H as [H|H].
  - apply Z.leb_gt in H. lia.
  - apply Z.ltb_ge in H. lia.
Qed.

Lemma h0t_res_len : CXS.res_len_ok HSEGS H0T.
Proof. unfold CXS.res_len_ok. rewrite h0_res_len. reflexivity. Qed.

Lemma h0t_res_hull : Forall (fun iv => img_lo H0T <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi H0T)
                            (segments_reserved HSEGS).
Proof. exact h0_res_hull. Qed.

Lemma h0t_hull_ok : CXS.hull_ok H0T.
Proof. unfold CXS.hull_ok. cbn [img_lo img_hi H0T]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma h0t_shadow_ok : CXS.shadow_ok H0T.
Proof. unfold CXS.shadow_ok. cbn [shadow_off H0T]. lia. Qed.

Lemma h0t_zone_ok : CXS.zone_ok H0T.
Proof.
  unfold CXS.zone_ok. cbn [zone_lo lowsh_hi highsh_lo zone_hi shadow_off img_hi H0T]. unfold TASK, CEIL.
  repeat split; cbv; try reflexivity; try lia; congruence.
Qed.

(* [comment removed for export] *)
Lemma h0t_res_cover : forall z, img_lo H0T <= z < img_hi H0T -> CXS.in_ivs z (segments_reserved HSEGS) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi H0T] in Hz. rewrite h0_res_eq. unfold CXS.in_ivs. apply existsb_exists.
  Ltac one_iv := cbn [fst snd]; rewrite !u64_lit by lia; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  destruct (Z_lt_le_dec z 0xe1000) as [H1|H1].
  { eexists. split; [left; reflexivity|]. one_iv. }
  destruct (Z_lt_le_dec z 0x2c1000) as [H2|H2].
  { eexists. split; [right; left; reflexivity|]. one_iv. }
  destruct (Z_lt_le_dec z 0x31e000) as [H3|H3].
  { eexists. split; [right; right; left; reflexivity|]. one_iv. }
  eexists. split; [right; right; right; left; reflexivity|]. one_iv.
Qed.

Lemma h0t_hull_ne : img_lo H0T < img_hi H0T.
Proof. cbn [img_lo img_hi H0T]. lia. Qed.

(* [comment removed for export] *)
Lemma h0t_if_ph : ph_addr_z H0T = Z.of_N (ph_addr HPH) /\ ph_ent_z H0T = Z.of_N (ph_ent HPH) /\ ph_num_z H0T = Z.of_N (ph_num HPH).
Proof. rewrite h0_phdrs_eq. cbn. repeat split; reflexivity. Qed.

Lemma h0t_if_hull : 0 <= img_lo H0T <= img_hi H0T /\ img_hi H0T <= 2 ^ 32 /\ img_lo H0T mod 4096 = 0 /\ img_hi H0T mod 4096 = 0.
Proof. cbn [img_lo img_hi H0T]. repeat split; cbv; try reflexivity; congruence. Qed.

Lemma h0t_if_top : reserved_top (segments_reserved HSEGS) = img_hi H0T.
Proof. vm_compute. reflexivity. Qed.

Lemma h0t_if_sizes : CXS.sum_sizes (segments_reserved HSEGS) = img_hi H0T - img_lo H0T.
Proof. rewrite h0_res_eq. cbn [CXS.sum_sizes snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

Lemma h0t_if_rw : (0 <= rw_lo H0T /\ 0 <= rw_len H0T /\ rw_lo H0T + rw_len H0T < 2 ^ 64)
                  /\ forall m (x : word), rw_lo H0T <= bv_unsigned x < rw_lo H0T + rw_len H0T -> wview HSEGS m x <> None.
Proof.
  split; [cbn [rw_lo rw_len H0T]; lia|].
  intros m x Hx. apply h0_rw_window. cbn [rw_lo rw_len H0T] in Hx. unfold H0_RW_LO, H0_RW_HI. lia.
Qed.
