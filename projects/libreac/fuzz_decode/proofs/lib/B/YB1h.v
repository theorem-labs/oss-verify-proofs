(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YB1h.v (origin/ossv/recipes c8557374ad2e), with its module paths changed and its image constants (segments_reserved, their sum, segment 2/3 sizes, rw window) recomputed from fuzz_decode's asan-ubsan image (sha256 5d05689fd5b1...) by provenance/startup-gen/B/gen_ab1hk.py (sha256 0f51cb9cdb18) through provenance/startup-gen/B/dec_ab1hk_drive.py; every fetched word checked equal. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.libreac.fuzz_decode.images Require Import AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK1a YK00 YK04 YK07 YP02. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0c. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YK09 YA01 YA0c YA0e YA0f YA02.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB12.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import APC. Import APG.
Open Scope Z_scope.
Definition TSEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition TPH : PhdrInfo := AsanUbsan.M.phdrs.
Lemma tsegs_tfasegs : TSEGS = tfibsegs.
Proof. reflexivity. Qed.
Lemma tfib_wx : wx_segs_nowrap TSEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.
Lemma find_segment1_none_outside : forall segs lo hi x,
segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
- exact (IH lo hi x Hl Hx).
- symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.
Lemma tfib_segs_in_hull : segs_in_hull_b TSEGS (img_lo TFIB) (img_hi TFIB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_in_hull : forall a : word,
APSG.in_hull TFIB (bv_unsigned a) = false -> find_segment TSEGS (bv_unsigned a) 1 = None.
Proof.
intros a H. apply (find_segment1_none_outside TSEGS (img_lo TFIB) (img_hi TFIB)); [exact tfib_segs_in_hull|].
unfold APSG.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.
Lemma tfib_res_len : APSG.res_len_ok TSEGS TFIB.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_res_lenP : APSXG.res_len_okP TSEGS TFIB.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_res_eq : segments_reserved TSEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x68000);
(Z_to_bv 64 0x98000, Z_to_bv 64 0x2000); (Z_to_bv 64 0x9a000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_res_hull : Forall (fun iv => img_lo TFIB <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi TFIB) (segments_reserved TSEGS).
Proof.
rewrite tfib_res_eq. cbn [img_lo img_hi TFIB].
repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.
Lemma tfib_hull_ok : APSG.hull_ok TFIB.
Proof. unfold APSG.hull_ok. cbn [img_lo img_hi TFIB]. unfold KHI. repeat split; reflexivity || lia. Qed.
Lemma tfib_hull_okP : APSXG.hull_okP TFIB.
Proof. unfold APSXG.hull_okP. cbn [img_lo img_hi TFIB]. unfold KHI. repeat split; reflexivity || lia. Qed.
Lemma tfib_shadow_ok : APSG.shadow_ok TFIB.
Proof. unfold APSG.shadow_ok. cbn [shadow_off TFIB]. lia. Qed.
Lemma tfib_res_sizes : APSG.sum_sizes (segments_reserved TSEGS) = 0x5e6000.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_res_top : reserved_top (segments_reserved TSEGS) = img_hi TFIB.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_res_cover : res_cover_check TSEGS TFIB = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_segs_wr : APSXG.segs_wr_ok TSEGS.
Proof.
intros seg Hin Hw. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; first [reflexivity | discriminate Hw].
Qed.
Lemma tfib_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5619712 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5619712%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_segs_eq : TSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.
Lemma tfib_rw_window : forall m (x : word),
0x98000 <= bv_unsigned x < 0x5f6000 -> wview TSEGS m x <> None.
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment TSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite tfib_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
AsanUbsan_segment_000 AsanUbsan_segment_001
AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 8192); [exact tfib_hex2 | rewrite tfib_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5619712); [exact tfib_hex3 | rewrite tfib_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x9a000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
[rewrite tfib_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
[rewrite tfib_segs_eq; cbn; tauto | cbn; lia].
Qed.
Theorem tfib_img_facts : img_facts TSEGS TFIB TPH.
Proof.
constructor.
- cbn. repeat split; reflexivity.
- cbn [img_lo img_hi TFIB]. repeat split; try reflexivity; lia.
- exact tfib_res_top.
- exact tfib_res_hull.
- rewrite tfib_res_sizes. reflexivity.
- split; [cbn [rw_lo rw_len TFIB]; lia|]. cbn [rw_lo rw_len TFIB]. intros m x Hx. apply tfib_rw_window. lia.
- cbn [shadow_off TFIB]. lia.
Qed.
Section b. Context {fx : YK11.FPState}.
Lemma tfibmusl_fetch : forall (p : word) (w : bv 32),
clookup tfibmusl_tbl (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word TSEGS p = Some w.
Proof.
intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
rewrite tsegs_tfasegs. apply tfibmusl_tbl_ok. exact H.
Qed.
#[local] Ltac ftac := apply tfibmusl_fetch; vm_compute; reflexivity.
Lemma tfib_Xenv : 0 <= x_envscan TFIB /\ x_envscan TFIB + 12 < 2 ^ 64 /\ x_envscan_k TFIB = x_envscan TFIB + 12.
Proof. cbn. lia. Qed.
Lemma tfib_Fe1 : fetch_word TSEGS (Z_to_bv 64 (x_envscan TFIB)) = Some (0x0004b503%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Fe2 : fetch_word TSEGS (Z_to_bv 64 (x_envscan TFIB + 4)) = Some (0x00848493%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Fe3 : fetch_word TSEGS (Z_to_bv 64 (x_envscan TFIB + 8)) = Some (0xfe051ce3%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Ee : is_ecall (0x0004b503%bv : bv 32) = false /\ is_ecall (0x00848493%bv : bv 32) = false /\ is_ecall (0xfe051ce3%bv : bv 32) = false.
Proof. repeat split; reflexivity. Qed.
Lemma tfib_De1 : decode_any (0x0004b503%bv : bv 32) = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_De2 : decode_any (0x00848493%bv : bv 32) = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_De3 : decode_any (0xfe051ce3%bv : bv 32) = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_Xpn : 8 <= x_pnscan TFIB /\ x_pnscan TFIB + 12 < 2 ^ 64 /\ x_pnscan_k TFIB = x_pnscan TFIB + 12.
Proof. cbn. lia. Qed.
Lemma tfib_Fp0 : fetch_word TSEGS (Z_to_bv 64 (x_pnscan TFIB - 8)) = Some (0x00b53023%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Fp1 : fetch_word TSEGS (Z_to_bv 64 (x_pnscan TFIB - 4)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Fp2 : fetch_word TSEGS (Z_to_bv 64 (x_pnscan TFIB)) = Some (0xfff5c683%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Fp3 : fetch_word TSEGS (Z_to_bv 64 (x_pnscan TFIB + 4)) = Some (0xfec68ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Fp4 : fetch_word TSEGS (Z_to_bv 64 (x_pnscan TFIB + 8)) = Some (0xfe069ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma tfib_Ep : is_ecall (0x00b53023%bv : bv 32) = false /\ is_ecall (0x00158593%bv : bv 32) = false /\ is_ecall (0xfff5c683%bv : bv 32) = false
/\ is_ecall (0xfec68ae3%bv : bv 32) = false /\ is_ecall (0xfe069ae3%bv : bv 32) = false.
Proof. repeat split; reflexivity. Qed.
Lemma tfib_Dp0 : decode_any (0x00b53023%bv : bv 32) = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_Dp1 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_Dp2 : decode_any (0xfff5c683%bv : bv 32) = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_Dp3 : decode_any (0xfec68ae3%bv : bv 32) = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma tfib_Dp4 : decode_any (0xfe069ae3%bv : bv 32) = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl_bv. Qed.
End b.
