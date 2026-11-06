(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocBlocksOL RelocImg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import RelocLept.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition canon_strs_OL : list (positive * Z * Z) := [
  (300%positive, 0x10298, 17); (301%positive, 0x102aa, 11); (302%positive, 0x102b6, 16); (303%positive, 0x102c7, 14);
  (304%positive, 0x102d6, 16); (305%positive, 0x102f1, 36); (306%positive, 0x10316, 14); (307%positive, 0x10325, 15);
  (308%positive, 0x10335, 10); (309%positive, 0x10340, 14); (310%positive, 0x1034f, 47); (311%positive, 0x1037f, 55);
  (312%positive, 0x103b7, 13); (313%positive, 0x103c5, 14); (314%positive, 0x103d4, 14); (315%positive, 0x103e3, 24);
  (316%positive, 0x1040f, 38); (317%positive, 0x10436, 14); (318%positive, 0x10460, 15); (319%positive, 0x10470, 11);
  (320%positive, 0x1047c, 21); (321%positive, 0x104c3, 9); (322%positive, 0x104cd, 18); (323%positive, 0x104e0, 83);
  (324%positive, 0x10534, 15); (325%positive, 0x10544, 30); (326%positive, 0x10567, 10); (327%positive, 0x10572, 26);
  (328%positive, 0x1058d, 10); (329%positive, 0x10598, 13); (330%positive, 0x105a6, 36); (331%positive, 0x105cb, 24);
  (332%positive, 0x105e4, 45); (333%positive, 0x10612, 50); (334%positive, 0x10645, 14); (335%positive, 0x10654, 18);
  (336%positive, 0x10667, 13); (337%positive, 0x10675, 76); (338%positive, 0x106e7, 18); (339%positive, 0x106fa, 34);
  (340%positive, 0x1071d, 17); (341%positive, 0x1072f, 52); (342%positive, 0x10764, 15); (343%positive, 0x10774, 12);
  (344%positive, 0x10781, 57); (345%positive, 0x107bb, 16); (346%positive, 0x107cc, 12); (347%positive, 0x107ee, 23);
  (348%positive, 0x10806, 9); (349%positive, 0x10810, 21); (350%positive, 0x10826, 22); (351%positive, 0x1083d, 46);
  (352%positive, 0x1086c, 17); (353%positive, 0x108aa, 28); (354%positive, 0x108c7, 11); (355%positive, 0x108d3, 21);
  (356%positive, 0x108e9, 28); (357%positive, 0x10906, 46); (358%positive, 0x10935, 13); (359%positive, 0x10947, 51);
  (360%positive, 0x1097f, 36); (361%positive, 0x109d2, 7); (362%positive, 0x109eb, 16); (363%positive, 0x109fc, 21);
  (364%positive, 0x10a12, 19); (365%positive, 0x10a26, 13); (4000%positive, 0x102e7, 9); (4001%positive, 0x103fc, 18);
  (4002%positive, 0x10445, 19); (4003%positive, 0x10459, 3); (4004%positive, 0x1045d, 0); (4005%positive, 0x1045e, 1);
  (4006%positive, 0x10492, 16); (4007%positive, 0x104a3, 31); (4008%positive, 0x10563, 3); (4009%positive, 0x106e4, 3);
  (4010%positive, 0x106e8, 32); (4011%positive, 0x108b7, 20); (4012%positive, 0x108cc, 22); (4013%positive, 0x1097c, 3);
  (4014%positive, 0x109b4, 3); (4015%positive, 0x109eb, 31); (4016%positive, 0x10a13, 16); (4017%positive, 0x10a6d, 9);
  (4018%positive, 0x10a77, 6)].

Definition lceOL_1e3b0_8 : ccell := mkCell 5026%positive 0x1e3b0 8%nat (CV_rl 5013%positive 0x1f420).   (* [comment removed for export] *)
Definition lceOL_1f420_4 : ccell := mkCell 5013%positive 0x1f420 4%nat (CV_lit 3).   (* [comment removed for export] *)
Definition lceOL_1e3e0_8 : ccell := mkCell 5027%positive 0x1e3e0 8%nat (CV_rl 5031%positive 0x2f848).   (* [comment removed for export] *)
Definition lceOL_1f430_8 : ccell := mkCell 5028%positive 0x1f430 8%nat (CV_rl 1036%positive 0x15b3c).   (* [comment removed for export] *)
Definition lceOL_1f438_8 : ccell := mkCell 5028%positive 0x1f438 8%nat (CV_rl 1035%positive 0x15b38).   (* [comment removed for export] *)
Definition lceOL_2f848_8 : ccell := mkCell 5031%positive 0x2f848 8%nat (CV_bytes [0; 0; 0; 0; 0; 0; 0; 0]).   (* [comment removed for export] *)
Definition lceOL_10a80_132 : ccell := mkCell 5018%positive 0x10a80 132%nat (CV_bytes [0; 0; 0; 0; 1; 0; 0; 0; 3; 0; 0; 0; 7; 0; 0; 0; 15; 0; 0; 0; 31; 0; 0; 0; 63; 0; 0; 0; 127; 0; 0; 0; 255; 0; 0; 0; 255; 1; 0; 0; 255; 3; 0; 0; 255; 7; 0; 0; 255; 15; 0; 0; 255; 31; 0; 0; 255; 63; 0; 0; 255; 127; 0; 0; 255; 255; 0; 0; 255; 255; 1; 0; 255; 255; 3; 0; 255; 255; 7; 0; 255; 255; 15; 0; 255; 255; 31; 0; 255; 255; 63; 0; 255; 255; 127; 0; 255; 255; 255; 0; 255; 255; 255; 1; 255; 255; 255; 3; 255; 255; 255; 7; 255; 255; 255; 15; 255; 255; 255; 31; 255; 255; 255; 63; 255; 255; 255; 127; 255; 255; 255; 255]).   (* [comment removed for export] *)

Definition canon_cells_OL : list ccell := [lceOL_1e3b0_8; lceOL_1f420_4; lceOL_1e3e0_8; lceOL_1f430_8; lceOL_1f438_8; lceOL_2f848_8; lceOL_10a80_132].

Definition canon_spans_OL : list (bool * positive * Z * Z) := [(true, 5026%positive, 0x1e3b0, 8); (true, 5013%positive, 0x1f420, 4); (true, 5027%positive, 0x1e3e0, 8); (true, 5028%positive, 0x1f430, 8); (true, 5028%positive, 0x1f438, 8); (true, 5031%positive, 0x2f848, 8); (false, 5018%positive, 0x10a80, 132); (true, 5013%positive, 0x1f428, 8)].

Class RelocImgOL (RL : Reloc) := {
  rl_strs_ol_ok : strs_check canon_strs_OL = true;
  rl_cells_ol_ok : cells_check canon_cells_OL = true;
  rl_spans_ol_ok : RelocLept.spans_check canon_spans_OL = true }.

Section Facts.
Context {RL : Reloc} {RIF : RelocImgOL RL}.
Lemma limgOL_1e3b0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1e3b0 + dA_1e3a0)) 8%nat = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)).
Proof.
  pose proof (cell_fact canon_cells_OL rl_cells_ol_ok 0%nat lceOL_1e3b0_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceOL_1e3b0_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgOL_1f420_4 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f420 + dA_1f3f8)) 4%nat = Some (Z_to_le_bytes 4 3).
Proof. exact (cell_fact canon_cells_OL rl_cells_ol_ok 1%nat lceOL_1f420_4 eq_refl). Qed.
Lemma limgOL_1e3e0_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1e3e0 + dA_1e3b8)) 8%nat = Some (Z_to_le_bytes 8 (0x2f848 + dA_2f848)).
Proof.
  pose proof (cell_fact canon_cells_OL rl_cells_ol_ok 2%nat lceOL_1e3e0_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceOL_1e3e0_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgOL_1f430_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f430 + dA_1f430)) 8%nat = Some (Z_to_le_bytes 8 (0x15b3c + dF_15b3c)).
Proof.
  pose proof (cell_fact canon_cells_OL rl_cells_ol_ok 3%nat lceOL_1f430_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceOL_1f430_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgOL_1f438_8 : rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x1f438 + dA_1f430)) 8%nat = Some (Z_to_le_bytes 8 (0x15b38 + dF_15b38)).
Proof.
  pose proof (cell_fact canon_cells_OL rl_cells_ol_ok 4%nat lceOL_1f438_8 eq_refl) as H.
  cbn [cell_bytes ce_val ce_n ce_blk ce_addr lceOL_1f438_8] in H. rewrite rl_cell_val in H by lia. exact H.
Qed.
Lemma limgOL_2f848_8 : exists T, rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x2f848 + dA_2f848)) 8%nat = Some T.
Proof. eexists. exact (cell_fact canon_cells_OL rl_cells_ol_ok 5%nat lceOL_2f848_8 eq_refl). Qed.
Lemma limgOL_10a80_132 : exists T, rdn rl_segs (fun _ => None) (Z_to_bv 64 (0x10a80 + dA_10a80)) 132%nat = Some T.
Proof. eexists. exact (cell_fact canon_cells_OL rl_cells_ol_ok 6%nat lceOL_10a80_132 eq_refl). Qed.
Lemma lspanOL_1e3b0 : rl_rw_lo <= 0x1e3b0 + dA_1e3a0 /\ 0x1e3b0 + dA_1e3a0 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 0%nat _ eq_refl). Qed.
Lemma lspanOL_1f420 : rl_rw_lo <= 0x1f420 + dA_1f3f8 /\ 0x1f420 + dA_1f3f8 + 4 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 1%nat _ eq_refl). Qed.
Lemma lspanOL_1e3e0 : rl_rw_lo <= 0x1e3e0 + dA_1e3b8 /\ 0x1e3e0 + dA_1e3b8 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 2%nat _ eq_refl). Qed.
Lemma lspanOL_1f430 : rl_rw_lo <= 0x1f430 + dA_1f430 /\ 0x1f430 + dA_1f430 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 3%nat _ eq_refl). Qed.
Lemma lspanOL_1f438 : rl_rw_lo <= 0x1f438 + dA_1f430 /\ 0x1f438 + dA_1f430 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 4%nat _ eq_refl). Qed.
Lemma lspanOL_2f848 : rl_rw_lo <= 0x2f848 + dA_2f848 /\ 0x2f848 + dA_2f848 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 5%nat _ eq_refl). Qed.
Lemma lspanOL_10a80 : rl_img_lo <= 0x10a80 + dA_10a80 /\ 0x10a80 + dA_10a80 + 132 <= rl_rw_lo.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 6%nat _ eq_refl). Qed.
Lemma lspanOL_1f428 : rl_rw_lo <= 0x1f428 + dA_1f3f8 /\ 0x1f428 + dA_1f3f8 + 8 <= rl_img_hi.
Proof. exact (RelocLept.span_fact canon_spans_OL rl_spans_ol_ok 7%nat _ eq_refl). Qed.
End Facts.

(* [comment removed for export] *)
Ltac rl_lay_OL :=
  rl_lay;
  (let h := fresh "Hspan" in pose proof lspanOL_1e3b0 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f420 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1e3e0 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f430 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f438 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_2f848 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_10a80 as h);
  (let h := fresh "Hspan" in pose proof lspanOL_1f428 as h).

(* [comment removed for export] *)
Ltac rl_str_far_OL a :=
  lazymatch a with
  | (?c + @rl_delta ?RL ?b)%Z =>
      let h := fresh "Hfar" in pose proof (@str_far_fact RL canon_strs_OL rl_strs_ol_ok b c (@eq_refl bool true)) as h
  end.
Ltac rl_str_tac_OL :=
  lazymatch goal with
  | |- _ (?c + @rl_delta ?RL ?b) ?k => exact (@str_fact RL canon_strs_OL rl_strs_ol_ok b c k (@eq_refl bool true))
  end.
Ltac rl_limg_OL :=
  lazymatch goal with
  | |- context [rdn _ _ (Z_to_bv 64 (0x1e3b0 + _)) 8%nat] => exact limgOL_1e3b0_8
  | |- context [rdn _ _ (rl _ 0x1e3b0) 8%nat] => exact limgOL_1e3b0_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f420 + _)) 4%nat] => exact limgOL_1f420_4
  | |- context [rdn _ _ (rl _ 0x1f420) 4%nat] => exact limgOL_1f420_4
  | |- context [rdn _ _ (Z_to_bv 64 (0x1e3e0 + _)) 8%nat] => exact limgOL_1e3e0_8
  | |- context [rdn _ _ (rl _ 0x1e3e0) 8%nat] => exact limgOL_1e3e0_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f430 + _)) 8%nat] => exact limgOL_1f430_8
  | |- context [rdn _ _ (rl _ 0x1f430) 8%nat] => exact limgOL_1f430_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x1f438 + _)) 8%nat] => exact limgOL_1f438_8
  | |- context [rdn _ _ (rl _ 0x1f438) 8%nat] => exact limgOL_1f438_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x2f848 + _)) 8%nat] => exact limgOL_2f848_8
  | |- context [rdn _ _ (rl _ 0x2f848) 8%nat] => exact limgOL_2f848_8
  | |- context [rdn _ _ (Z_to_bv 64 (0x10a80 + _)) 132%nat] => exact limgOL_10a80_132
  | |- context [rdn _ _ (rl _ 0x10a80) 132%nat] => exact limgOL_10a80_132
  | _ => fail "rl_limg_OL: no family cell fact for this read"
  end.
