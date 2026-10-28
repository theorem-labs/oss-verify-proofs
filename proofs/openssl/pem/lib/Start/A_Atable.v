(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import A_PlanImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_T : atable :=
  {| img_lo := 0x10000; img_hi := 0xbc6000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x199a18; rw_lo := 0x52e000; rw_len := 0x698000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x1d4e8c; x_imemcpy := 0x1d4e10; x_memset := 0x526914; x_memcpy := 0x5264e0; x_memiszero := 0x1d53bc;
     x_istrncpy := 0x1d52b8; x_sealed := 0x14026; x_popfree := 0x1a01e0;
     x_sniff := 0; sniff_tab := 2 ^ 64 (* [comment removed for export] *); sniff_cell := 0;
     x_envscan := 0x51a66c; x_envscan_k := 0x51a678; x_pnscan := 0x51a730; x_pnscan_k := 0x51a73c;
     stops_more := [0x1d6584];
     zone_lo := 0x7fff7000; lowsh_hi := 0x8fff7000; highsh_lo := 0x2008fff7000; zone_hi := 0x10007fff8000;
     nolazy := false (* [comment removed for export] *) |}.

Lemma A_t_img_lo : img_lo A_T = A_IMG_LO. Proof. reflexivity. Qed.
Lemma A_t_img_hi : img_hi A_T = A_IMG_HI. Proof. reflexivity. Qed.
Lemma A_t_entry : a_entry A_T = A_ENTRY. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma A_t_segs_wx : wx_segs_nowrap A_SEGS.
Proof. exact A_wx. Qed.

Lemma A_t_in_hull : forall a : word,
  APS.in_hull A_T (bv_unsigned a) = false -> find_segment A_SEGS (bv_unsigned a) 1 = None.
Proof.
  intros a H. apply A_outside_hull. unfold APS.in_hull in H. cbn [img_lo img_hi A_T] in H.
  unfold A_IMG_LO, A_IMG_HI. apply Bool.andb_false_iff in H. destruct H as [H|H].
  - apply Z.leb_gt in H. lia.
  - apply Z.ltb_ge in H. lia.
Qed.

Lemma A_t_res_len : APS.res_len_ok A_SEGS A_T.
Proof. unfold APS.res_len_ok. rewrite A_res_len. reflexivity. Qed.

Lemma A_t_res_hull : Forall (fun iv => img_lo A_T <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A_T)
                            (segments_reserved A_SEGS).
Proof. exact A_res_hull. Qed.

Lemma A_t_hull_ok : APS.hull_ok A_T.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi A_T]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma A_t_shadow_ok : APS.shadow_ok A_T.
Proof. unfold APS.shadow_ok. cbn [shadow_off A_T]. lia. Qed.

Lemma A_t_zone_ok : APS.zone_ok A_T.
Proof.
  unfold APS.zone_ok. cbn [zone_lo lowsh_hi highsh_lo zone_hi shadow_off img_hi A_T]. unfold TASK, CEIL.
  repeat split; cbv; try reflexivity; try lia; congruence.
Qed.

(* [comment removed for export] *)
Ltac A_one_iv := cbn [fst snd]; rewrite !u64_lit by lia; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Lemma A_t_res_cover : forall z, img_lo A_T <= z < img_hi A_T -> APS.in_ivs z (segments_reserved A_SEGS) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi A_T] in Hz. rewrite A_res_eq. unfold APS.in_ivs. apply existsb_exists.
  destruct (Z_lt_le_dec z 0x199000) as [H1|H1].
  { eexists. split; [left; reflexivity|]. A_one_iv. }
  destruct (Z_lt_le_dec z 0x52e000) as [H2|H2].
  { eexists. split; [right; left; reflexivity|]. A_one_iv. }
  destruct (Z_lt_le_dec z 0x5a7000) as [H3|H3].
  { eexists. split; [right; right; left; reflexivity|]. A_one_iv. }
  eexists. split; [right; right; right; left; reflexivity|]. A_one_iv.
Qed.

Lemma A_t_hull_ne : img_lo A_T < img_hi A_T.
Proof. cbn [img_lo img_hi A_T]. lia. Qed.

(* [comment removed for export] *)
Lemma A_t_if_ph : ph_addr_z A_T = Z.of_N (ph_addr A_PH) /\ ph_ent_z A_T = Z.of_N (ph_ent A_PH) /\ ph_num_z A_T = Z.of_N (ph_num A_PH).
Proof. rewrite A_phdrs_eq. cbn. repeat split; reflexivity. Qed.

Lemma A_t_if_hull : 0 <= img_lo A_T <= img_hi A_T /\ img_hi A_T <= 2 ^ 32 /\ img_lo A_T mod 4096 = 0 /\ img_hi A_T mod 4096 = 0.
Proof. cbn [img_lo img_hi A_T]. repeat split; cbv; try reflexivity; congruence. Qed.

Lemma A_t_if_top : reserved_top (segments_reserved A_SEGS) = img_hi A_T.
Proof. vm_compute. reflexivity. Qed.

Lemma A_t_if_sizes : APS.sum_sizes (segments_reserved A_SEGS) = img_hi A_T - img_lo A_T.
Proof. rewrite A_res_eq. cbn [APS.sum_sizes snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

Lemma A_t_if_rw : (0 <= rw_lo A_T /\ 0 <= rw_len A_T /\ rw_lo A_T + rw_len A_T < 2 ^ 64)
                  /\ forall m (x : word), rw_lo A_T <= bv_unsigned x < rw_lo A_T + rw_len A_T -> wview A_SEGS m x <> None.
Proof.
  split; [cbn [rw_lo rw_len A_T]; lia|].
  intros m x Hx. apply A_rw_window. cbn [rw_lo rw_len A_T] in Hx. unfold A_RW_LO, A_RW_HI. lia.
Qed.
