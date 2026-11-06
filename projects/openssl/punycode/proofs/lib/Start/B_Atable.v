(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import B_PlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition B_T : atable :=
  {| img_lo := 0x10000; img_hi := 0xbfd000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x194984; rw_lo := 0x56b000; rw_len := 0x692000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x1cfdf8; x_imemcpy := 0x1cfd7c; x_memset := 0x563738; x_memcpy := 0x563304; x_memiszero := 0x1d0328;
     x_istrncpy := 0x1d0224; x_sealed := 0x140d1; x_popfree := 0x19b14c;
     x_sniff := 0; sniff_tab := 2 ^ 64 (* [comment removed for export] *); sniff_cell := 0;
     x_envscan := 0x557490; x_envscan_k := 0x55749c; x_pnscan := 0x557554; x_pnscan_k := 0x557560;
     stops_more := [0x1d14f0];
     zone_lo := 0x7fff7000; lowsh_hi := 0x8fff7000; highsh_lo := 0x2008fff7000; zone_hi := 0x10007fff8000;
     nolazy := false (* [comment removed for export] *) |}.

Lemma B_t_img_lo : img_lo B_T = B_IMG_LO. Proof. reflexivity. Qed.
Lemma B_t_img_hi : img_hi B_T = B_IMG_HI. Proof. reflexivity. Qed.
Lemma B_t_entry : a_entry B_T = B_ENTRY. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma B_t_segs_wx : wx_segs_nowrap B_SEGS.
Proof. exact B_wx. Qed.

Lemma B_t_in_hull : forall a : word,
  APS.in_hull B_T (bv_unsigned a) = false -> find_segment B_SEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply B_outside_hull. unfold APS.in_hull in H. cbn [img_lo img_hi B_T] in H.
  unfold B_IMG_LO, B_IMG_HI. apply Bool.andb_false_iff in H. destruct H as [H|H].
  - apply Z.leb_gt in H. lia.
  - apply Z.ltb_ge in H. lia.
Qed.

Lemma B_t_res_len : APS.res_len_ok B_SEGS B_T.
Proof. unfold APS.res_len_ok. rewrite B_res_len. reflexivity. Qed.

Lemma B_t_res_hull : Forall (fun iv => img_lo B_T <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi B_T)
                            (segments_reserved B_SEGS).
Proof. exact B_res_hull. Qed.

Lemma B_t_hull_ok : APS.hull_ok B_T.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi B_T]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma B_t_shadow_ok : APS.shadow_ok B_T.
Proof. unfold APS.shadow_ok. cbn [shadow_off B_T]. lia. Qed.

Lemma B_t_zone_ok : APS.zone_ok B_T.
Proof.
  unfold APS.zone_ok. cbn [zone_lo lowsh_hi highsh_lo zone_hi shadow_off img_hi B_T]. unfold TASK, CEIL.
  repeat split; cbv; try reflexivity; try lia; congruence.
Qed.

(* [comment removed for export] *)
Ltac B_one_iv := cbn [fst snd]; rewrite !u64_lit by lia; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Lemma B_t_res_cover : forall z, img_lo B_T <= z < img_hi B_T -> APS.in_ivs z (segments_reserved B_SEGS) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi B_T] in Hz. rewrite B_res_eq. unfold APS.in_ivs. apply existsb_exists.
  destruct (Z_lt_le_dec z 0x194000) as [H1|H1].
  { eexists. split; [left; reflexivity|]. B_one_iv. }
  destruct (Z_lt_le_dec z 0x56b000) as [H2|H2].
  { eexists. split; [right; left; reflexivity|]. B_one_iv. }
  destruct (Z_lt_le_dec z 0x5e3000) as [H3|H3].
  { eexists. split; [right; right; left; reflexivity|]. B_one_iv. }
  eexists. split; [right; right; right; left; reflexivity|]. B_one_iv.
Qed.

Lemma B_t_hull_ne : img_lo B_T < img_hi B_T.
Proof. cbn [img_lo img_hi B_T]. lia. Qed.

(* [comment removed for export] *)
Lemma B_t_if_ph : ph_addr_z B_T = Z.of_N (ph_addr B_PH) /\ ph_ent_z B_T = Z.of_N (ph_ent B_PH) /\ ph_num_z B_T = Z.of_N (ph_num B_PH).
Proof. rewrite B_phdrs_eq. cbn. repeat split; reflexivity. Qed.

Lemma B_t_if_hull : 0 <= img_lo B_T <= img_hi B_T /\ img_hi B_T <= 2 ^ 32 /\ img_lo B_T mod 4096 = 0 /\ img_hi B_T mod 4096 = 0.
Proof. cbn [img_lo img_hi B_T]. repeat split; cbv; try reflexivity; congruence. Qed.

Lemma B_t_if_top : reserved_top (segments_reserved B_SEGS) = img_hi B_T.
Proof. vm_compute. reflexivity. Qed.

Lemma B_t_if_sizes : APS.sum_sizes (segments_reserved B_SEGS) = img_hi B_T - img_lo B_T.
Proof. rewrite B_res_eq. cbn [APS.sum_sizes snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

Lemma B_t_if_rw : (0 <= rw_lo B_T /\ 0 <= rw_len B_T /\ rw_lo B_T + rw_len B_T < 2 ^ 64)
                  /\ forall m (x : word), rw_lo B_T <= bv_unsigned x < rw_lo B_T + rw_len B_T -> wview B_SEGS m x <> None.
Proof.
  split; [cbn [rw_lo rw_len B_T]; lia|].
  intros m x Hx. apply B_rw_window. cbn [rw_lo rw_len B_T] in Hx. unfold B_RW_LO, B_RW_HI. lia.
Qed.
