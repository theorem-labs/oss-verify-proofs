(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocBlocksVL RelocImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition canon_strs_VL : list (positive * Z * Z) := [
  (400%positive, 0x10298, 17); (401%positive, 0x102aa, 11); (402%positive, 0x102b6, 11); (403%positive, 0x102c2, 16);
  (404%positive, 0x102d3, 14); (405%positive, 0x102e2, 16); (406%positive, 0x102fd, 36); (407%positive, 0x10322, 14);
  (408%positive, 0x10331, 15); (409%positive, 0x10341, 10); (410%positive, 0x1034c, 14); (411%positive, 0x1035b, 47);
  (412%positive, 0x1038b, 55); (413%positive, 0x103c3, 13); (414%positive, 0x103d1, 14); (415%positive, 0x103e0, 14);
  (416%positive, 0x103ef, 24); (417%positive, 0x1041b, 38); (418%positive, 0x10442, 14); (419%positive, 0x1046c, 15);
  (420%positive, 0x1047c, 11); (421%positive, 0x10488, 21); (422%positive, 0x104cf, 18); (423%positive, 0x104e2, 9);
  (424%positive, 0x104ec, 18); (425%positive, 0x104ff, 83); (426%positive, 0x10553, 15); (427%positive, 0x10563, 30);
  (428%positive, 0x10586, 10); (429%positive, 0x10591, 26); (430%positive, 0x105ac, 10); (431%positive, 0x105b7, 13);
  (432%positive, 0x105c5, 36); (433%positive, 0x105ea, 24); (434%positive, 0x10603, 45); (435%positive, 0x10631, 50);
  (436%positive, 0x10664, 12); (437%positive, 0x10671, 14); (438%positive, 0x10680, 18); (439%positive, 0x10693, 13);
  (440%positive, 0x106a1, 76); (441%positive, 0x10713, 18); (442%positive, 0x10726, 34); (443%positive, 0x10749, 17);
  (444%positive, 0x1075b, 52); (445%positive, 0x10790, 14); (446%positive, 0x1079f, 15); (447%positive, 0x107af, 12);
  (448%positive, 0x107bc, 57); (449%positive, 0x107f6, 16); (450%positive, 0x10807, 12); (451%positive, 0x10814, 14);
  (452%positive, 0x10838, 23); (453%positive, 0x10850, 9); (454%positive, 0x1085a, 21); (455%positive, 0x10870, 22);
  (456%positive, 0x10887, 46); (457%positive, 0x108b6, 17); (458%positive, 0x108f4, 28); (459%positive, 0x10911, 11);
  (460%positive, 0x1091d, 21); (461%positive, 0x10933, 28); (462%positive, 0x10950, 46); (463%positive, 0x1097f, 13);
  (464%positive, 0x10991, 51); (465%positive, 0x109c5, 11); (466%positive, 0x109d5, 36); (467%positive, 0x10a28, 7);
  (468%positive, 0x10a41, 16); (469%positive, 0x10a52, 21); (470%positive, 0x10a68, 19); (471%positive, 0x10a7c, 13);
  (4000%positive, 0x102e7, 9); (4001%positive, 0x103fc, 18); (4002%positive, 0x10445, 19); (4003%positive, 0x10459, 3);
  (4004%positive, 0x1045d, 0); (4005%positive, 0x1045e, 1); (4006%positive, 0x10492, 16); (4007%positive, 0x104a3, 31);
  (4008%positive, 0x10563, 3); (4009%positive, 0x106e4, 3); (4010%positive, 0x106e8, 32); (4011%positive, 0x108b7, 20);
  (4012%positive, 0x108cc, 22); (4013%positive, 0x1097c, 3); (4014%positive, 0x109b4, 3); (4015%positive, 0x109eb, 31);
  (4016%positive, 0x10a13, 16); (4017%positive, 0x10a6d, 9); (4018%positive, 0x10a77, 6)].

Definition lceVL_1e3b0_8 : ccell := mkCell 5035%positive 0x1e3b0 8%nat (CV_rl 5013%positive 0x1f420).   (* [comment removed for export] *)
Definition lceVL_1f420_4 : ccell := mkCell 5013%positive 0x1f420 4%nat (CV_lit 3).   (* [comment removed for export] *)
Definition lceVL_1e3e0_8 : ccell := mkCell 5027%positive 0x1e3e0 8%nat (CV_rl 5031%positive 0x2f848).   (* [comment removed for export] *)
Definition lceVL_1f430_8 : ccell := mkCell 5028%positive 0x1f430 8%nat (CV_rl 1036%positive 0x15b3c).   (* [comment removed for export] *)
Definition lceVL_1f438_8 : ccell := mkCell 5028%positive 0x1f438 8%nat (CV_rl 1035%positive 0x15b38).   (* [comment removed for export] *)
Definition lceVL_2f848_8 : ccell := mkCell 5031%positive 0x2f848 8%nat (CV_bytes [0; 0; 0; 0; 0; 0; 0; 0]).   (* [comment removed for export] *)
Definition lceVL_10a80_132 : ccell := mkCell 5018%positive 0x10a80 132%nat (CV_bytes [0; 0; 0; 0; 1; 0; 0; 0; 3; 0; 0; 0; 7; 0; 0; 0; 15; 0; 0; 0; 31; 0; 0; 0; 63; 0; 0; 0; 127; 0; 0; 0; 255; 0; 0; 0; 255; 1; 0; 0; 255; 3; 0; 0; 255; 7; 0; 0; 255; 15; 0; 0; 255; 31; 0; 0; 255; 63; 0; 0; 255; 127; 0; 0; 255; 255; 0; 0; 255; 255; 1; 0; 255; 255; 3; 0; 255; 255; 7; 0; 255; 255; 15; 0; 255; 255; 31; 0; 255; 255; 63; 0; 255; 255; 127; 0; 255; 255; 255; 0; 255; 255; 255; 1; 255; 255; 255; 3; 255; 255; 255; 7; 255; 255; 255; 15; 255; 255; 255; 31; 255; 255; 255; 63; 255; 255; 255; 127; 255; 255; 255; 255]).   (* [comment removed for export] *)

Definition canon_cells_VL : list ccell := [lceVL_1e3b0_8; lceVL_1f420_4; lceVL_1e3e0_8; lceVL_1f430_8; lceVL_1f438_8; lceVL_2f848_8; lceVL_10a80_132].

Definition canon_spans_VL : list (bool * positive * Z * Z) := [(true, 5035%positive, 0x1e3b0, 8); (true, 5013%positive, 0x1f420, 4); (true, 5027%positive, 0x1e3e0, 8); (true, 5028%positive, 0x1f430, 8); (true, 5028%positive, 0x1f438, 8); (true, 5031%positive, 0x2f848, 8); (false, 5018%positive, 0x10a80, 132); (true, 5013%positive, 0x1f428, 8)].

Class RelocImgVL (RL : Reloc) := {
  rl_strs_vl_ok : strs_check canon_strs_VL = true;
  rl_cells_vl_ok : cells_check canon_cells_VL = true;
  rl_spans_vl_ok : RelocLept.spans_check canon_spans_VL = true }.

Section Facts.
Context {RL : Reloc} {RIF : RelocImgVL RL}.
Lemma limgVL_1e3b0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1e3b0 + dA_1e3b0)) 8%nat = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)).
Proof.
  pose proof (cell_fact canon_cells_VL rl_cells_vl_ok 0%nat lceVL_1e3b0_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceVL_1e3b0_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgVL_1f420_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f420 + dA_1f3f8)) 4%nat = Some (Z_to_le_bytes 4 3).
Proof. exact (cell_fact canon_cells_VL rl_cells_vl_ok 1%nat lceVL_1f420_4 eq_refl). Qed.
Lemma limgVL_1e3e0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1e3e0 + dA_1e3b8)) 8%nat = Some (Z_to_le_bytes 8 (0x2f848 + dA_2f848)).
Proof.
  pose proof (cell_fact canon_cells_VL rl_cells_vl_ok 2%nat lceVL_1e3e0_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceVL_1e3e0_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgVL_1f430_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f430 + dA_1f430)) 8%nat = Some (Z_to_le_bytes 8 (0x15b3c + dF_15b3c)).
Proof.
  pose proof (cell_fact canon_cells_VL rl_cells_vl_ok 3%nat lceVL_1f430_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceVL_1f430_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgVL_1f438_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f438 + dA_1f430)) 8%nat = Some (Z_to_le_bytes 8 (0x15b38 + dF_15b38)).
Proof.
  pose proof (cell_fact canon_cells_VL rl_cells_vl_ok 4%nat lceVL_1f438_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceVL_1f438_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgVL_2f848_8 : exists T, rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x2f848 + dA_2f848)) 8%nat = Some T.
Proof. eexists. exact (cell_fact canon_cells_VL rl_cells_vl_ok 5%nat lceVL_2f848_8 eq_refl). Qed.
Lemma limgVL_10a80_132 : exists T, rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x10a80 + dA_10a80)) 132%nat = Some T.
Proof. eexists. exact (cell_fact canon_cells_VL rl_cells_vl_ok 6%nat lceVL_10a80_132 eq_refl). Qed.
Lemma lspanVL_1e3b0 : rl_rw_lo <= 0x1e3b0 + dA_1e3b0 /\ 0x1e3b0 + dA_1e3b0 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 0%nat _ eq_refl). Qed.
Lemma lspanVL_1f420 : rl_rw_lo <= 0x1f420 + dA_1f3f8 /\ 0x1f420 + dA_1f3f8 + 4 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 1%nat _ eq_refl). Qed.
Lemma lspanVL_1e3e0 : rl_rw_lo <= 0x1e3e0 + dA_1e3b8 /\ 0x1e3e0 + dA_1e3b8 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 2%nat _ eq_refl). Qed.
Lemma lspanVL_1f430 : rl_rw_lo <= 0x1f430 + dA_1f430 /\ 0x1f430 + dA_1f430 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 3%nat _ eq_refl). Qed.
Lemma lspanVL_1f438 : rl_rw_lo <= 0x1f438 + dA_1f430 /\ 0x1f438 + dA_1f430 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 4%nat _ eq_refl). Qed.
Lemma lspanVL_2f848 : rl_rw_lo <= 0x2f848 + dA_2f848 /\ 0x2f848 + dA_2f848 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 5%nat _ eq_refl). Qed.
Lemma lspanVL_10a80 : rl_img_lo <= 0x10a80 + dA_10a80 /\ 0x10a80 + dA_10a80 + 132 <= rl_rw_lo.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 6%nat _ eq_refl). Qed.
Lemma lspanVL_1f428 : rl_rw_lo <= 0x1f428 + dA_1f3f8 /\ 0x1f428 + dA_1f3f8 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_VL rl_spans_vl_ok 7%nat _ eq_refl). Qed.
End Facts.

(* [comment removed for export] *)
Ltac rl_lay_VL :=
  rl_lay;
  (let h := fresh "Hspan" in pose proof lspanVL_1e3b0 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_1f420 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_1e3e0 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_1f430 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_1f438 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_2f848 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_10a80 as h);
  (let h := fresh "Hspan" in pose proof lspanVL_1f428 as h).

(* [comment removed for export] *)
Ltac rl_str_far_VL a :=
  lazymatch a with
  | (?c + @rl_delta ?RL ?b)%Z =>
      let h := fresh "Hfar" in pose proof (@str_far_fact RL canon_strs_VL rl_strs_vl_ok b c (@eq_refl bool true)) as h
  end.
Ltac rl_str_tac_VL :=
  lazymatch goal with
  | |- _ (?c + @rl_delta ?RL ?b) ?k => exact (@str_fact RL canon_strs_VL rl_strs_vl_ok b c k (@eq_refl bool true))
  end.
Ltac rl_limg_VL :=
  lazymatch goal with
  | |- context [rdn _ _ (Z_to_bv 64 (0x1e3b0 + _)) 8%nat] => exact limgVL_1e3b0_8
  | |- context [rdn _ _ (rl _ 0x1e3b0) 8%nat] => exact limgVL_1e3b0_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f420 + _)) 4%nat] => exact limgVL_1f420_4
  | |- context [rdn _ _ (rl _ 0x1f420) 4%nat] => exact limgVL_1f420_4
  | |- context [rdn _ _ (Z_to_bv 64 (0x1e3e0 + _)) 8%nat] => exact limgVL_1e3e0_8
  | |- context [rdn _ _ (rl _ 0x1e3e0) 8%nat] => exact limgVL_1e3e0_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f430 + _)) 8%nat] => exact limgVL_1f430_8
  | |- context [rdn _ _ (rl _ 0x1f430) 8%nat] => exact limgVL_1f430_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f438 + _)) 8%nat] => exact limgVL_1f438_8
  | |- context [rdn _ _ (rl _ 0x1f438) 8%nat] => exact limgVL_1f438_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x2f848 + _)) 8%nat] => exact limgVL_2f848_8
  | |- context [rdn _ _ (rl _ 0x2f848) 8%nat] => exact limgVL_2f848_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x10a80 + _)) 132%nat] => exact limgVL_10a80_132
  | |- context [rdn _ _ (rl _ 0x10a80) 132%nat] => exact limgVL_10a80_132
  | _ => fail "rl_limg_VL: no family cell fact for this read"
  end.
