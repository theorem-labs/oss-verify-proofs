(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanImgScan.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition IMG_RGS : list region :=
  [ RGz (lconst 0x10000) 0x2e000 RO TEmpty;
    RGz (lconst 0xda000) 0x6000 RO TEmpty;
    RGz (lconst 0xe0000) 0x250 RI TEmpty;
    RGz (lconst 0xe2fc0) 0x86900 RZ TEmpty;
    RGz (lconst 0x1758c0) 0x3000 RZ TEmpty;
    RGz (lconst 0x1b78c0) 0x1000 RZ TEmpty;
    RGz (lconst 0x1c78c0) 0x401000 RZ TEmpty;
    RGz (lconst 0x6078c0) 0x1400 RZ TEmpty;
    RGz (lconst 0x608cc0) 0x10010 RZ TEmpty;
    RGz (lconst 0x618cd0) 0x23330 RZ TEmpty;
    RGz (lconst 0xe0250) 0x188 RO TEmpty;
    RGz (lconst 0xe03d8) 0x2720 RI TEmpty;
    RGz (lconst 0xe2af8) 0x8 RO TEmpty;
    RGz (lconst 0xe2b00) 0x4c0 RI TEmpty ].

(* [comment removed for export] *)
Lemma u64 : forall x, 0 <= x < 0x800000000000 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x H. apply u_small64. unfold two64. lia. Qed.

Ltac leb_true := symmetry; apply Z.leb_le; lia.
Ltac leb_false := symmetry; apply Z.leb_gt; lia.

Lemma find_seg0 : forall x, 0x10000 <= x < 0x3e000 -> find_segment ASEGS x 1 = Some AsanUbsan_segment_000.
Proof.
  intros x H. unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments.
  cbn [find_segment seg_base seg_size AsanUbsan_segment_000]. cbn [Z.of_N].
  replace (65536 <=? x) with true by leb_true. replace (x + 1 <=? 65536 + 188416) with true by leb_true. reflexivity.
Qed.
Lemma find_seg2 : forall x, 0xda000 <= x < 0xe0000 -> find_segment ASEGS x 1 = Some AsanUbsan_segment_002.
Proof.
  intros x H. unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments.
  cbn [find_segment seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002].
  cbn [Z.of_N].
  replace (x + 1 <=? 65536 + 188416) with false by leb_false. replace (x + 1 <=? 253952 + 638976) with false by leb_false.
  replace (892928 <=? x) with true by leb_true. replace (x + 1 <=? 892928 + 24576) with true by leb_true.
  rewrite !andb_false_r. reflexivity.
Qed.
Lemma find_seg3 : forall x, 0xe0000 <= x < 0x63c000 -> find_segment ASEGS x 1 = Some AsanUbsan_segment_003.
Proof.
  intros x H. unfold AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments.
  cbn [find_segment seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002
       AsanUbsan_segment_003].
  cbn [Z.of_N].
  replace (x + 1 <=? 65536 + 188416) with false by leb_false. replace (x + 1 <=? 253952 + 638976) with false by leb_false.
  replace (x + 1 <=? 892928 + 24576) with false by leb_false.
  replace (917504 <=? x) with true by leb_true. replace (x + 1 <=? 917504 + 5619712) with true by leb_true.
  rewrite !andb_false_r. reflexivity.
Qed.

Lemma len_c0 : Z.to_N (Uint63.to_Z (PrimString.length c0) / 2) = 0x2e000%N. Proof. vm_compute. reflexivity. Qed.
Lemma len_c2 : Z.to_N (Uint63.to_Z (PrimString.length c2) / 2) = 0x6000%N. Proof. vm_compute. reflexivity. Qed.
Lemma len_c3 : Z.to_N (Uint63.to_Z (PrimString.length c3) / 2) = 0x55c000%N. Proof. vm_compute. reflexivity. Qed.
Lemma rd_seg0 : seg_readable AsanUbsan_segment_000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rd_seg2 : seg_readable AsanUbsan_segment_002 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rd_seg3 : seg_readable AsanUbsan_segment_003 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_seg2 : seg_writable AsanUbsan_segment_002 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wr_seg3 : seg_writable AsanUbsan_segment_003 = true. Proof. vm_compute. reflexivity. Qed.

Lemma one_chunk : forall c off n, Z.to_N (Uint63.to_Z (PrimString.length c) / 2) = n -> (off < n)%N ->
  segment_byte_at [c] off = hex_byte_at c off.
Proof. intros c off n Hl Ho. cbn [segment_byte_at]. rewrite Hl. replace (off <? n)%N with true by (symmetry; apply N.ltb_lt; exact Ho). reflexivity. Qed.

Lemma seg_rom_of : forall x seg c n, find_segment ASEGS x 1 = Some seg -> seg_readable seg = true -> seg_bytes seg = [c] ->
  Z.to_N (Uint63.to_Z (PrimString.length c) / 2) = n -> (Z.to_N (x - Z.of_N (seg_base seg)) < n)%N -> 0 <= x < 0x800000000000 ->
  seg_rom ASEGS (Z_to_bv 64 x) = hex_byte_at c (Z.to_N (x - Z.of_N (seg_base seg))).
Proof.
  intros x seg c n Hf Hr Hb Hl Ho Hx. unfold seg_rom, memory_read. rewrite u64 by exact Hx. change (Z.of_N 1) with 1. rewrite Hf, Hr, Hb.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite (one_chunk c _ n Hl Ho).
  destruct (hex_byte_at c (Z.to_N (x - Z.of_N (seg_base seg)))); reflexivity.
Qed.

Lemma wview_of : forall m x seg c n, m (Z_to_bv 64 x) = None -> find_segment ASEGS x 1 = Some seg -> seg_writable seg = true ->
  seg_bytes seg = [c] -> Z.to_N (Uint63.to_Z (PrimString.length c) / 2) = n -> (Z.to_N (x - Z.of_N (seg_base seg)) < n)%N ->
  0 <= x < 0x800000000000 -> wview ASEGS m (Z_to_bv 64 x) = hex_byte_at c (Z.to_N (x - Z.of_N (seg_base seg))).
Proof.
  intros m x seg c n Hm Hf Hw Hb Hl Ho Hx. unfold wview. rewrite Hm, u64 by exact Hx. rewrite Hf, Hw, Hb.
  exact (one_chunk c _ n Hl Ho).
Qed.

(* [comment removed for export] *)
Lemma rom0 : forall x, 0x10000 <= x < 0x3e000 -> seg_rom ASEGS (Z_to_bv 64 x) = hex_byte_at c0 (Z.to_N (x - 0x10000)).
Proof. intros x H. exact (seg_rom_of x _ c0 0x2e000 (find_seg0 x H) rd_seg0 eq_refl len_c0 ltac:(cbn [seg_base AsanUbsan_segment_000 Z.of_N]; lia) ltac:(lia)). Qed.
Lemma rom2 : forall x, 0xda000 <= x < 0xe0000 -> seg_rom ASEGS (Z_to_bv 64 x) = hex_byte_at c2 (Z.to_N (x - 0xda000)).
Proof. intros x H. exact (seg_rom_of x _ c2 0x6000 (find_seg2 x H) rd_seg2 eq_refl len_c2 ltac:(cbn [seg_base AsanUbsan_segment_002 Z.of_N]; lia) ltac:(lia)). Qed.
Lemma rom3 : forall x, 0xe0000 <= x < 0x63c000 -> seg_rom ASEGS (Z_to_bv 64 x) = hex_byte_at c3 (Z.to_N (x - 0xe0000)).
Proof. intros x H. exact (seg_rom_of x _ c3 0x55c000 (find_seg3 x H) rd_seg3 eq_refl len_c3 ltac:(cbn [seg_base AsanUbsan_segment_003 Z.of_N]; lia) ltac:(lia)). Qed.
Lemma wv2 : forall m x, m (Z_to_bv 64 x) = None -> 0xda000 <= x < 0xe0000 -> wview ASEGS m (Z_to_bv 64 x) = hex_byte_at c2 (Z.to_N (x - 0xda000)).
Proof. intros m x Hm H. exact (wview_of m x _ c2 0x6000 Hm (find_seg2 x H) wr_seg2 eq_refl len_c2 ltac:(cbn [seg_base AsanUbsan_segment_002 Z.of_N]; lia) ltac:(lia)). Qed.
Lemma wv3 : forall m x, m (Z_to_bv 64 x) = None -> 0xe0000 <= x < 0x63c000 -> wview ASEGS m (Z_to_bv 64 x) = hex_byte_at c3 (Z.to_N (x - 0xe0000)).
Proof. intros m x Hm H. exact (wview_of m x _ c3 0x55c000 Hm (find_seg3 x H) wr_seg3 eq_refl len_c3 ltac:(cbn [seg_base AsanUbsan_segment_003 Z.of_N]; lia) ltac:(lia)). Qed.

(* [comment removed for export] *)
Lemma scf_0 : scank c0 0x0 0x2e000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_0 : scan byte_ok c0 64 0x0 0x2e000 = true. Proof. exact (scan_of_scank c0 0x0 0x2e000 eq_refl scf_0). Qed.
Lemma scf_1 : scank c2 0x0 0x6000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_1 : scan byte_ok c2 64 0x0 0x6000 = true. Proof. exact (scan_of_scank c2 0x0 0x6000 eq_refl scf_1). Qed.
Lemma scf_2 : scank c3 0x0 0x250 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_2 : scan byte_ok c3 64 0x0 0x250 = true. Proof. exact (scan_of_scank c3 0x0 0x250 eq_refl scf_2). Qed.
Lemma scf_3 : scanz c3 0x2fc0 0x86900 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_3 : scan byte_z c3 64 0x2fc0 0x86900 = true. Proof. exact (scan_of_scanz c3 0x2fc0 0x86900 eq_refl scf_3). Qed.
Lemma scf_4 : scanz c3 0x958c0 0x3000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_4 : scan byte_z c3 64 0x958c0 0x3000 = true. Proof. exact (scan_of_scanz c3 0x958c0 0x3000 eq_refl scf_4). Qed.
Lemma scf_5 : scanz c3 0xd78c0 0x1000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_5 : scan byte_z c3 64 0xd78c0 0x1000 = true. Proof. exact (scan_of_scanz c3 0xd78c0 0x1000 eq_refl scf_5). Qed.
Lemma scf_6 : scanz c3 0xe78c0 0x401000 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_6 : scan byte_z c3 64 0xe78c0 0x401000 = true. Proof. exact (scan_of_scanz c3 0xe78c0 0x401000 eq_refl scf_6). Qed.
Lemma scf_7 : scanz c3 0x5278c0 0x1400 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_7 : scan byte_z c3 64 0x5278c0 0x1400 = true. Proof. exact (scan_of_scanz c3 0x5278c0 0x1400 eq_refl scf_7). Qed.
Lemma scf_8 : scanz c3 0x528cc0 0x10010 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_8 : scan byte_z c3 64 0x528cc0 0x10010 = true. Proof. exact (scan_of_scanz c3 0x528cc0 0x10010 eq_refl scf_8). Qed.
Lemma scf_9 : scanz c3 0x538cd0 0x23330 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_9 : scan byte_z c3 64 0x538cd0 0x23330 = true. Proof. exact (scan_of_scanz c3 0x538cd0 0x23330 eq_refl scf_9). Qed.
Lemma scf_10 : scank c3 0x250 0x188 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_10 : scan byte_ok c3 64 0x250 0x188 = true. Proof. exact (scan_of_scank c3 0x250 0x188 eq_refl scf_10). Qed.
Lemma scf_11 : scank c3 0x3d8 0x2720 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_11 : scan byte_ok c3 64 0x3d8 0x2720 = true. Proof. exact (scan_of_scank c3 0x3d8 0x2720 eq_refl scf_11). Qed.
Lemma scf_12 : scank c3 0x2af8 0x8 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_12 : scan byte_ok c3 64 0x2af8 0x8 = true. Proof. exact (scan_of_scank c3 0x2af8 0x8 eq_refl scf_12). Qed.
Lemma scf_13 : scank c3 0x2b00 0x4c0 = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sc_13 : scan byte_ok c3 64 0x2b00 0x4c0 = true. Proof. exact (scan_of_scank c3 0x2b00 0x4c0 eq_refl scf_13). Qed.

(* [comment removed for export] *)
Lemma scan_at : forall f c lo n base x, scan f c 64 lo n = true -> base + Z.of_N lo <= x < base + Z.of_N lo + Z.of_N n ->
  f c (Z.to_N (x - base)) = true.
Proof.
  intros f c lo n base x Hs Hx. pose proof (scan_sound f c 64 lo n Hs (Z.to_N (x - base) - lo)%N ltac:(lia)) as H.
  replace (lo + (Z.to_N (x - base) - lo))%N with (Z.to_N (x - base)) in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Section Img.
Variable E : valu.
Variable m : word -> option byte.
Hypothesis Hm : forall x, 0x10000 <= x < 0x63c000 -> m (Z_to_bv 64 x) = None.

#[using="Hm"] Lemma rg_ok_ro : forall A n, 0x10000 <= A -> A + n <= 0x3e000 -> 0 < n ->
  (forall x, A <= x < A + n -> byte_ok c0 (Z.to_N (x - 0x10000)) = true) -> rg_ok ASEGS E m (RGz (lconst A) n RO TEmpty).
Proof. LiaFast.lf_pins (fun (Hm : LiaFast.U) => LiaFast.u0).
  intros A n H1 H2 H3 Hs. unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite lden_lconst, u64 by lia.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. split; [apply Hm; lia|]. rewrite rom0 by lia. destruct (byte_ok_some c0 _ (Hs (A + i) ltac:(lia))) as [b Hb]. rewrite Hb. discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Hm"] Lemma rg_ok_ro2 : forall A n, 0xda000 <= A -> A + n <= 0xe0000 -> 0 < n ->
  (forall x, A <= x < A + n -> byte_ok c2 (Z.to_N (x - 0xda000)) = true) -> rg_ok ASEGS E m (RGz (lconst A) n RO TEmpty).
Proof. LiaFast.lf_pins (fun (Hm : LiaFast.U) => LiaFast.u0).
  intros A n H1 H2 H3 Hs. unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite lden_lconst, u64 by lia.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. split; [apply Hm; lia|]. rewrite rom2 by lia. destruct (byte_ok_some c2 _ (Hs (A + i) ltac:(lia))) as [b Hb]. rewrite Hb. discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.
#[using="Hm"] Lemma rg_ok_ro3 : forall A n, 0xe0000 <= A -> A + n <= 0x63c000 -> 0 < n ->
  (forall x, A <= x < A + n -> byte_ok c3 (Z.to_N (x - 0xe0000)) = true) -> rg_ok ASEGS E m (RGz (lconst A) n RO TEmpty).
Proof. LiaFast.lf_pins (fun (Hm : LiaFast.U) => LiaFast.u0).
  intros A n H1 H2 H3 Hs. unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite lden_lconst, u64 by lia.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. split; [apply Hm; lia|]. rewrite rom3 by lia. destruct (byte_ok_some c3 _ (Hs (A + i) ltac:(lia))) as [b Hb]. rewrite Hb. discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Hm"] Lemma rg_ok_ri : forall A n, 0xda000 <= A -> A + n <= 0x63c000 -> 0 < n ->
  (forall x, A <= x < A + n -> x < 0xe0000 -> byte_ok c2 (Z.to_N (x - 0xda000)) = true) ->
  (forall x, A <= x < A + n -> 0xe0000 <= x -> byte_ok c3 (Z.to_N (x - 0xe0000)) = true) ->
  rg_ok ASEGS E m (RGz (lconst A) n RI TEmpty).
Proof. LiaFast.lf_pins (fun (Hm : LiaFast.U) => LiaFast.u0).
  intros A n H1 H2 H3 Hs2 Hs3. unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite lden_lconst, u64 by lia.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. pose proof (Hm (A + i) ltac:(lia)) as Hmi. unfold rd1. rewrite Hmi. split; [|intros _; reflexivity].
    destruct (Z_lt_ge_dec (A + i) 0xe0000) as [Hl|Hg].
    + rewrite rom2, (wv2 m) by (try exact Hmi; lia). destruct (byte_ok_some c2 _ (Hs2 (A + i) ltac:(lia) Hl)) as [b Hb]. rewrite Hb. split; discriminate.
    + rewrite rom3, (wv3 m) by (try exact Hmi; lia). destruct (byte_ok_some c3 _ (Hs3 (A + i) ltac:(lia) ltac:(lia))) as [b Hb]. rewrite Hb. split; discriminate.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Hm"] Lemma rg_ok_rz : forall A n, 0xe0000 <= A -> A + n <= 0x63c000 -> 0 < n ->
  (forall x, A <= x < A + n -> byte_z c3 (Z.to_N (x - 0xe0000)) = true) -> rg_ok ASEGS E m (RGz (lconst A) n RZ TEmpty).
Proof. LiaFast.lf_pins (fun (Hm : LiaFast.U) => LiaFast.u0).
  intros A n H1 H2 H3 Hs. unfold rg_ok. rewrite rsz_RGz by (unfold two64; lia). cbn [RGz rg_base rg_kind rg_cont]. rewrite lden_lconst, u64 by lia.
  split; [lia|]. split; [unfold two64; lia|]. split.
  - intros i Hi. pose proof (Hm (A + i) ltac:(lia)) as Hmi. pose proof (byte_z_zero c3 _ (Hs (A + i) ltac:(lia))) as Hz.
    unfold rd1. rewrite Hmi. rewrite rom3, (wv3 m) by (try exact Hmi; lia). rewrite Hz. split; [split; discriminate | intros _; reflexivity].
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Hm"] Theorem img_rgs_ok : Forall (rg_ok ASEGS E m) IMG_RGS.
Proof. LiaFast.lf_pins (fun (Hm : LiaFast.U) => LiaFast.u0).
  unfold IMG_RGS.
  repeat (apply Forall_cons); [ | | | | | | | | | | | | | | constructor].
  - apply rg_ok_ro; try lia. intros x Hx. exact (scan_at byte_ok c0 0x0 0x2e000 0x10000 x sc_0 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_ro2; try lia. intros x Hx. exact (scan_at byte_ok c2 0x0 0x6000 0xda000 x sc_1 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_ri; [lia | lia | lia | intros x Hx Hx'; lia |].
    intros x Hx Hx'. exact (scan_at byte_ok c3 0x0 0x250 0xe0000 x sc_2 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0x2fc0 0x86900 0xe0000 x sc_3 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0x958c0 0x3000 0xe0000 x sc_4 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0xd78c0 0x1000 0xe0000 x sc_5 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0xe78c0 0x401000 0xe0000 x sc_6 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0x5278c0 0x1400 0xe0000 x sc_7 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0x528cc0 0x10010 0xe0000 x sc_8 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_rz; try lia. intros x Hx. exact (scan_at byte_z c3 0x538cd0 0x23330 0xe0000 x sc_9 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_ro3; try lia. intros x Hx. exact (scan_at byte_ok c3 0x250 0x188 0xe0000 x sc_10 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_ri; [lia | lia | lia | intros x Hx Hx'; lia |].
    intros x Hx Hx'. exact (scan_at byte_ok c3 0x3d8 0x2720 0xe0000 x sc_11 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_ro3; try lia. intros x Hx. exact (scan_at byte_ok c3 0x2af8 0x8 0xe0000 x sc_12 ltac:(cbn [Z.of_N]; lia)).
  - apply rg_ok_ri; [lia | lia | lia | intros x Hx Hx'; lia |].
    intros x Hx Hx'. exact (scan_at byte_ok c3 0x2b00 0x4c0 0xe0000 x sc_13 ltac:(cbn [Z.of_N]; lia)).
Qed.
End Img.
(* [comment removed for export] *)
