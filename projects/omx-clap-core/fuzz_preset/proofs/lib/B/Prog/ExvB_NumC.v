(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only through EXB's exv_rm keep and EXV_PRE's entry memnorm (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece C: EXN_C of lib/B/Prog/ExvB_NumCut.v, from the cut CS (exv_pc 0x84c,
   B 0x83d78: the scan stopped at j) to the cut CR (exv_pc 0x8d4, B 0x83e00: strtod returned).
   The code walked (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, lines
   533-566; every pc is exv_pc of a DERIVED offset, B address - B_entry_ex_value 0x8352c):
     0x84c  addi s4,s3,24 / srli / add s9 / lbu / bnez -> 0xd04   ASan check of in->scratch (q + 24); the slow arm
                                                                  0xd04 (B 0x84230, `jal errpath_load8`) is NOT
                                                                  reached: the granule of q + 24 is at shadow 0
                                                                  (EXB's range_addressable of [q, q + 40))
     0x860  ld a0,24(s3) / sub a2,s6,a1 / jal __asan_memcpy       memcpy (scr, x0 + i1, j - i1) (YGcallMxmn's
                                                                  aj_intrin_at_xm at EXV_HYP's eh_memcpy)
     0x86c  ld a0,144(s1) / lbu / bnez -> 0xd0c                   ASan check of in (q); arm 0xd0c (B 0x84238,
                                                                  errpath_load8) NOT reached, as above
     0x878  ld a0,0(s3) / ld a1,24(s3) / sub / add                a0 = scr + (j - i1)
     0x890  beq (scr != 0),(scr + n == 0) -> 0xb50                UBSan pointer-overflow check (B 0x83dbc): NOT
                                                                  taken, 0 < scr + n
     0x8a4  beqz -> 0xb50                                         UBSan (B 0x83dd0): NOT taken, scr + n does not
                                                                  wrap below scr (n >= 0, scr + n < 2 ^ 64)
     0x8a8  beqz a1 -> 0xb50                                      UBSan non-NULL (B 0x83dd4): NOT taken, decided in
                                                                  the run from the fact 4096 <= scr (atom 32)
     0x8ac  srli / add s9 / lb / bnez -> 0xbf8                    ASan check of the NUL byte scr + n (1 byte): the
                                                                  partial-granule arm 0xbf8 (B 0x84124) returns to
                                                                  0x8bc or reaches errpath_store1 (B 0x8412c); the
                                                                  run decides it from the scratch's range_addressable
     0x8bc  sb zero,0(a0)                                         the NUL: the scratch holds txt ++ [0]
     0x8c0  lbu (s11) / bnez -> 0xd14                             ASan check of q + 24 again; arm 0xd14 (B 0x84240,
                                                                  errpath_load8) NOT reached
     0x8c8  ld a0,0(s4) / mv a1,s7 / jal strtod                   strtod (scr, f + 32) (YStrtodRowX's row through
                                                                  ExvB_Stmt's exv_strtod)
   Symbolic runs over the whole-range table B_prog_tbl (YCbqG's SRr_run_tok_AJx / SRr_run_to_tok_AJx, the template
   lib/B/Prog/ex_ws_x.v): CS -> the memcpy entry; 0x86c -> 0x8ac, split by SRr_sym_branch at the two UBSan branches
   0x890 and 0x8a4 (each taken arm refuted from the run's values: exnc_U_A, exnc_U_br2); 0x8ac -> the strtod entry.
   The ASan checks are decided inside the runs from shadow entries: [q, q + 40) from EXB's range_addressable,
   [scr + n, scr + n + 1) from EXB's scratch range_addressable, so no errpath_* arm is reached.
   After strtod the walk is at the callee's float state fx' (the row's post); EXB is re-established by the segment's
   EXN_keepM (MK) at fx' (exnc_exb_fx; its memnorm keep from strtod's aj_memnorm), the spills by EXN_keep_spill (KS), and CR is handed to EXN_D (HD).
   strtod_site_x's facts: the scratch off the image band (blk_img_x + exnc_img_cover), the frame above it
   (exnc_frame_top, from eh_fpos / eh_fflx), the GOT guard's rom view (exnc_got: a const cell of B by eh_got_const,
   kept by alx_const_cells, equal to the rom bytes by strtod_row.strtod_got_B), aj_memnorm (EXB's exv_rm keep at EXV_PRE's entry memnorm,
   carried: the table-engine runs by exnc_mn_frame from their frame_of, whose only window is the NUL byte, inside the
   scratch block; __asan_memcpy by aj_intrin_at_xm's keep).
   Rule 24: proves no function (kind: segment lemma).
   Section hypotheses: HYP (EXV_HYP), HD (EXN_D), MK (EXN_keepM), KS (EXN_keep_spill), as ExvB_NumCut.v states them.
   exnc_shx / exnc_denot_shx / exnc_geom (ExvB_Close.v's exvc_shx / exvc_denot_shx / exvc_geom), exnc_stk_lo /
   exnc_exb_fx (ExvB_Loop_kitP.v's kp_stk_lo / exv_exb_fx) are restated here: those two files do not build on the
   rebind base.
   Numerals: 0x86c, 0x8ac (DERIVED: offsets from ex_value's entry, the starts of the two inner runs; CS and CR are
   ExvB_NumCut's EXN_CS / EXN_CR); 8, 24, 40, 136, 144, 152, 160, 304 (LENGTH: struct ex field offsets and size, the s1
   spill slots and the write zone's top, the realigned frame's bound of B's code); 128, 16384, 1048576, 1064960, 127
   (DERIVED: the class-1 fs_frame_bytes, fs_flags_off 1, 2 ^ kStackSizeLog, the flag-to-frame distance of YG0f's
   fake-stack offsets and its slope in pos); 16384 (DERIVED: STK_RT_STRTOD = 4 * ESTACK); 4096 (DERIVED: ESTACK, the
   low-page bound); 256, 2 ^ 3, 2 ^ 5, 2 ^ 30, 2 ^ 32, 2 ^ 46, 2 ^ 47, 2 ^ 47 - 8, 2 ^ 47 - 40, 2 ^ 62, 2 ^ 63, 2 ^ 64,
   3 * 2 ^ 20 (LENGTH: the byte modulus, alignments, strtod's text bound, address-space and stack bounds, EXV_PRE's
   text bound); 18446744073709551615 and -1 (WORD: 2 ^ 64 - 1, the engine's negation form); 0, 1, 45 (WORD: the NUL
   byte, the compare constants, ASCII '-'); register numbers (WORD) and atom numbers 32 / 33 (DERIVED: the engine's
   numbering); 0 .. 3 (DERIVED: indices of rsegs' segments). No ADDRESS: every pc is an exv_pc / B_prog_sigma term and
   the segment bounds are computed from rsegs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YStrtodRowX YK0o YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import strtod_c ExvB_Stmt ExvB_NumPure ExvB_NumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Num_eng ExvB_Open_sh ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_row.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ======== the pcs of the piece (DERIVED offsets of ex_value's entry) ======== *)
Definition EXNC_P2 : Z := exv_pc 0x86c.   (* B 0x83d98, __asan_memcpy's return site *)
Definition EXNC_P3 : Z := exv_pc 0x8ac.   (* B 0x83dd8, a0 = scr + (j - i1) *)

(* ======== pure: the text strtod reads ======== *)
Lemma exnc_numch_all : forallb (fun b => Bool.eqb (PjGrammar.numch b) (FmtFp_facts3.is_numch b)) exn_bytes256 = true.
Proof. vm_compute. reflexivity. Qed.

(* the scan's class and musl's class agree on every byte (256 cases, as ExvB_NumPure's three tests) *)
Lemma exnc_numch_is : forall b, 0 <= b < 256 -> PjGrammar.numch b = FmtFp_facts3.is_numch b.
Proof.
intros b Hb. pose proof (exn_forallb_bytes256 _ exnc_numch_all b Hb) as H. cbv beta in H.
apply Bool.eqb_prop in H. exact H.
Qed.

Lemma exnc_skipn_S : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof. induction x as [|h t IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.

(* every byte of x[i1, j) is a number character: the sign '-' is one, the rest is EXN_span's *)
Lemma exnc_numch_txt : forall (x : list Z) i1 c j, nth i1 x 0 = c -> (i1 < j <= length x)%nat ->
  Forall (fun z => PjGrammar.numch z = true) (exn_sub x (i1 + exn_sg c) j) ->
  Forall (fun z => PjGrammar.numch z = true) (exn_sub x i1 j).
Proof.
intros x i1 c j Hc Hj H. unfold exn_sg in H. destruct (Z.eqb_spec c 45) as [E|E].
- unfold exn_sub in *. rewrite (exnc_skipn_S x i1) by lia.
  replace (j - i1)%nat with (S (j - S i1)) by lia. cbn [firstn]. constructor.
  + rewrite Hc, E. reflexivity.
  + replace (i1 + 1)%nat with (S i1) in H by lia. exact H.
- rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma exnc_sub_len : forall (x : list Z) i1 j, (i1 <= j <= length x)%nat ->
  length (exn_sub x i1 j) = (j - i1)%nat.
Proof. intros x i1 j H. unfold exn_sub. rewrite length_firstn, length_skipn, Nat.min_l by lia. reflexivity. Qed.

Lemma exnc_sub_bytes : forall (x : list Z) i1 j, Forall (fun z => 0 <= z < 256) x ->
  Forall (fun z => 0 <= z < 256) (exn_sub x i1 j).
Proof.
intros x i1 j H. unfold exn_sub.
pose proof (firstn_skipn i1 x) as E1. rewrite <- E1 in H. apply Forall_app in H as [_ H2].
pose proof (firstn_skipn (j - i1) (skipn i1 x)) as E2. rewrite <- E2 in H2. apply Forall_app in H2 as [H3 _].
exact H3.
Qed.

Lemma exnc_garr8_bytes : forall m p l, garr8 rsegs m p l -> Forall (fun z => 0 <= z < 256) l.
Proof.
intros m p l G. rewrite Forall_forall. intros z Hz. destruct (In_nth l z 0 Hz) as (n & Hn & <-).
exact (proj2 (G n Hn)).
Qed.

(* ExvB_Stmt's text class at strtod: musl's characters, under 2 ^ 30 bytes *)
Lemma exnc_txt_ok : forall (x : list Z) i1 c j, Forall (fun z => 0 <= z < 256) x -> nth i1 x 0 = c ->
  (i1 < j <= length x)%nat -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  Forall (fun z => PjGrammar.numch z = true) (exn_sub x (i1 + exn_sg c) j) ->
  exv_txt_ok (exn_sub x i1 j).
Proof.
intros x i1 c j HB Hc Hj Hl HS. split.
- pose proof (exnc_numch_txt x i1 c j Hc Hj HS) as HN. pose proof (exnc_sub_bytes x i1 j HB) as HB'.
  rewrite Forall_forall in HN, HB' |- *. intros z Hz. rewrite <- (exnc_numch_is z (HB' z Hz)). exact (HN z Hz).
- rewrite exnc_sub_len by lia. lia.
Qed.

(* the image hull [IMG_LO_B, IMG_TOP_B) is covered by the four generated segments of B, without a gap (FuzzStrdupB.v's
   sd_img_cover; the segment bounds are computed from rsegs, no number typed) *)
Ltac exnc_zl_all :=
  repeat first
  [ match goal with |- context [Z.of_N (seg_base ?x)] =>
      let v := eval vm_compute in (Z.of_N (seg_base x)) in lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_N (seg_base x)) with v in * end
  | match goal with |- context [Z.of_N (seg_size ?x)] =>
      let v := eval vm_compute in (Z.of_N (seg_size x)) in lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_N (seg_size x)) with v in * end
  | match goal with H : context [Z.of_N (seg_base ?x)] |- _ =>
      let v := eval vm_compute in (Z.of_N (seg_base x)) in lazymatch v with Zpos _ => idtac | Z0 => idtac end;
      change (Z.of_N (seg_base x)) with v in * end ].
Lemma exnc_img_cover : forall a, IMG_LO_B <= a < IMG_TOP_B -> in_img rsegs a.
Proof.
intros a Ha. unfold IMG_LO_B, IMG_TOP_B in Ha.
assert (Hb : forall k, (k < 4)%nat -> In (nth k rsegs AsanUbsan.AsanUbsan_segment_000) rsegs)
  by (intros k Hk; apply nth_In; vm_compute; lia).
destruct (Z_lt_le_dec a (Z.of_N (seg_base (nth 1 rsegs AsanUbsan.AsanUbsan_segment_000)))) as [h1|h1];
[exists (nth 0 rsegs AsanUbsan.AsanUbsan_segment_000)
| destruct (Z_lt_le_dec a (Z.of_N (seg_base (nth 2 rsegs AsanUbsan.AsanUbsan_segment_000)))) as [h2|h2];
  [exists (nth 1 rsegs AsanUbsan.AsanUbsan_segment_000)
  | destruct (Z_lt_le_dec a (Z.of_N (seg_base (nth 3 rsegs AsanUbsan.AsanUbsan_segment_000)))) as [h3|h3];
    [exists (nth 2 rsegs AsanUbsan.AsanUbsan_segment_000) | exists (nth 3 rsegs AsanUbsan.AsanUbsan_segment_000)]]];
(split; [apply Hb; lia|]); exnc_zl_all; lia.
Qed.

(* ======== bytes and the engine's arithmetic (no state) ======== *)
Lemma exnc_mb_move : forall (H H' : word -> bool) (m m' : word -> option byte) a b v,
  aview rsegs H' m' a = aview rsegs H m b -> mbyte rsegs (mrestrict H m) b = Some v ->
  mbyte rsegs (mrestrict H' m') a = Some v.
Proof.
intros H H' m m' a b v HA V. unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte rsegs (mrestrict H' m') a) as [b'|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* the scratch after the copy and the NUL store: x[i1, i1 + n) ++ [0] *)
Lemma exnc_garr8_build : forall H m m' x0 (x : list Z) i1 n scr,
  garr8 rsegs (mrestrict H m) x0 x -> (i1 + n <= length x)%nat ->
  (forall j, (j < n)%nat -> aview rsegs H m' (scr + Z.of_nat j) = aview rsegs H m (x0 + Z.of_nat (i1 + j))) ->
  val_mem rsegs (mrestrict H m') (scr + Z.of_nat n) 1 0 ->
  garr8 rsegs (mrestrict H m') scr (firstn n (skipn i1 x) ++ [0]).
Proof.
intros H m m' x0 x i1 n scr G Hn HA HZ j Hj.
rewrite length_app, length_firstn, length_skipn, Nat.min_l in Hj by lia. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j n) as [Hjn|Hjn].
- rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
  rewrite nth_firstn, nth_skipn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hjn).
  destruct (G (i1 + j)%nat ltac:(lia)) as [V R]. split; [|exact R].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
  exact (exnc_mb_move H H m m' _ _ _ (HA j Hjn) V).
- assert (j = n) by lia. subst j.
  rewrite app_nth2 by (rewrite length_firstn, length_skipn; lia).
  rewrite length_firstn, length_skipn, Nat.min_l, Nat.sub_diag by lia. cbn [nth]. split; [exact HZ | lia].
Qed.

Lemma exnc_sub_canon : forall u v, 0 <= u <= v -> v < 2 ^ 64 ->
  zcanon (zcanon (u * zcanon (-1)) + v) = v - u.
Proof.
intros u v Huv Hv. unfold zcanon, M64. rewrite Z.add_mod_idemp_l by lia.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (u * (2 ^ 64 - 1) + v) with ((v - u) + u * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* a2 at the memcpy call: s6 - a1 = j - i1 *)
Lemma exnc_U_sub : forall E u v, ew E 11 = Z_to_bv 64 u -> ew E 22 = Z_to_bv 64 v -> 0 <= u <= v -> v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit (-1))) (SOff 22 0)) = Z_to_bv 64 (v - u).
Proof.
intros E u v Hu Hv Huv Hv64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd, (U_atom E 11 u Hu), (U_atom E 22 v Hv), U_SLit by lia. cbn [zalu_raw zmd_raw].
apply exnc_sub_canon; lia.
Qed.

Lemma exnc_garr8_aview : forall H m p l j, garr8 rsegs (mrestrict H m) p l -> (j < length l)%nat ->
  aview rsegs H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j G Hj. unfold aview. rewrite (garr8_mbyte rsegs _ p l j G Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (G j Hj)).
Qed.

(* the shadow address of q + c in the shape the symbolic run matches (`srli / add s9`), restated from ExvClose's
   exvc_shx / exvc_denot_shx (lib/B/Prog/ExvB_Close.v does not build on the rebind base) *)
Definition exnc_shx (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0).
Definition EXNC_SB : sv := SOff 25 0.

Lemma exnc_denot_shx : forall E c v sb, ew E 19 = Z_to_bv 64 v -> ew E 25 = Z_to_bv 64 sb ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (exnc_shx c) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E c v sb Hn Hm Hv Hc Hvc Hsb. unfold exnc_shx.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ex_value's stack need at every nesting covers its realigned frame (304 bytes) and strtod's window (ExvLoop's
   kp_stk_lo, restated: lib/B/Prog/ExvB_Loop_kitP.v does not build on the rebind base) *)
Lemma exnc_stk_lo : forall n : nat, 16688 <= STK_ex_value n.
Proof.
intros n. unfold STK_ex_value.
assert (Hf : @pi_frame prh_img_B F_ex_value = 304) by reflexivity.
assert (Hz : zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; @STK_ex_string prh_img_B; @STK_ex_word prh_img_B;
  @STK_ex_ws prh_img_B] = 16384) by (vm_compute; reflexivity).
rewrite Hf, Hz. pose proof (Nat2Z.is_nonneg n) as Hn. rewrite Nat2Z.inj_succ. nia.
Qed.

(* ======== the symbolic states (closed terms; vm_compute runs the table engine over them) ======== *)
(* seg 1 at CS: s3 (atom 19) = q, s9 (atom 25) = the shadow base, atom 32 = in->scratch read at q + 24 *)
Definition exnc_r1 : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition exnc_f1 : list (nat * afact) :=
  [(19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition ss_exnc1 : sstate := mkSS (exv_pc EXN_CS) sr_atoms [exnc_r1] None (mkFacts exnc_f1 [] []).
(* in's 40 bytes are addressable: the 8-byte checks of q + 24 and q *)
Definition exnc_SHq : list shent := [mkSHE 19 0 40].
Definition EXNC_KL1 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26]%bv.

(* seg 2 at B 0x83d98 (memcpy's return): 144(s1) holds shadow (q), in->p (atom 33) and in->scratch (atom 32) *)
Definition exnc_r2s : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (exnc_shx 0))].
Definition exnc_r2q : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 32 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition exnc_f2 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (22%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 4096 (2 ^ 47) 0)].
Definition ss_exnc2 : sstate := mkSS EXNC_P2 sr_atoms [exnc_r2s; exnc_r2q] None (mkFacts exnc_f2 [] []).

Lemma exnc_kl_cs : forall x, In x EXNC_KL1 -> acallee_saved (bv_unsigned x).
Proof.
intros x Hx. unfold EXNC_KL1 in Hx. unfold acallee_saved.
repeat (destruct Hx as [<-|Hx]; [match goal with |- context [bv_unsigned ?b] =>
  let v := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with v end; lia|]).
destruct Hx.
Qed.
Lemma exnc_pres : forall r r', aregs_preserved r r' -> forall x : bv 5, acallee_saved (bv_unsigned x) -> YK11.getr r' x = YK11.getr r x.
Proof. intros r r' H x Hx. rewrite <- (Z_to_bv_bv_unsigned 5 x). exact (H _ Hx). Qed.
Lemma exnc_pres_kl : forall r r', aregs_preserved r r' -> forall x, In x EXNC_KL1 -> YK11.getr r' x = YK11.getr r x.
Proof. intros r r' H x Hx. exact (exnc_pres r r' H x (exnc_kl_cs x Hx)). Qed.
Lemma exnc_cs20 : acallee_saved (bv_unsigned (20%bv : bv 5)).
Proof. unfold acallee_saved. change (bv_unsigned (20%bv : bv 5)) with 20. lia. Qed.
Lemma exnc_cs27 : acallee_saved (bv_unsigned (27%bv : bv 5)).
Proof. unfold acallee_saved. change (bv_unsigned (27%bv : bv 5)) with 27. lia. Qed.

(* seg 3 at B 0x83dd8: a0 (atom 10) = scr + n, the NUL byte; s4 = q + 24, s11 = shadow (q + 24); q + 24 holds scr *)
Definition exnc_r3b : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].
Definition exnc_r3q : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition exnc_f3 : list (nat * afact) :=
  [(10%nat, mkAF 4096 (2 ^ 47 - 8) 0); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition exnc_regs3 : list sv := sr_set (sr_set sr_atoms 20%bv (SOff 19 24)) 27%bv (exnc_shx 24).
Definition ss_exnc3 : sstate := mkSS EXNC_P3 exnc_regs3 [exnc_r3b; exnc_r3q] None (mkFacts exnc_f3 [] []).
(* the NUL byte is addressable (its 1-byte check with the partial-granule arm), and in's 40 bytes *)
Definition exnc_SH3 : list shent := [mkSHE 10 0 1; mkSHE 19 0 40].
Definition EXNC_KLC : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* a fact lia must not case-split on (a disjunction the piece reads in one place only) *)
Definition exnc_hid (P : Prop) : Prop := P.
Ltac exnc_hide H := let T := type of H in change (exnc_hid T) in H.

(* ======== the whole-overlay normal form (YStrtodRowX.aj_memnorm) across the piece's own steps ======== *)
Lemma exnc_task : 2 ^ 47 <= TASK_SIZE.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma exnc_fs_none : forall a, ~ in_img rsegs a -> find_segment rsegs a 1 = None.
Proof.
intros a H. destruct (find_segment rsegs a 1) as [sg|] eqn:F; [|reflexivity].
exfalso. apply H. destruct (find_segment_some_spec rsegs a 1 sg F) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

(* a run of the table engine changes the overlay only in its write windows (frame_of, YP09.v): the form is kept when
   every window byte lies below TASK_SIZE and off every segment *)
Lemma exnc_mn_frame : forall E rs (m m' : word -> option byte),
  YStrtodRowX.aj_memnorm rsegs m -> frame_of E rs m m' ->
  (forall a, in_wrange E rs a -> a < TASK_SIZE /\ find_segment rsegs a 1 = None) ->
  YStrtodRowX.aj_memnorm rsegs m'.
Proof.
intros E rs m m' (Hi & Ht) HF HW. split.
- intros x b Ex. unfold lib.Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [sg|] eqn:F; [|reflexivity].
  assert (Hn : ~ in_wrange E rs (bv_unsigned x))
    by (intros Hw; destruct (HW _ Hw) as [_ Hf]; rewrite Hf in F; discriminate).
  rewrite (HF x Hn) in Ex. pose proof (Hi x b Ex) as R. unfold lib.Lib.Mem.ro_addr in R. rewrite F in R. exact R.
- intros x b Ex. destruct (Z_lt_le_dec (bv_unsigned x) TASK_SIZE) as [Hl|Hl]; [right; exact Hl|].
  assert (Hn : ~ in_wrange E rs (bv_unsigned x)) by (intros Hw; destruct (HW _ Hw) as [Hw' _]; lia).
  rewrite (HF x Hn) in Ex. exact (Ht x b Ex).
Qed.

(* the form after a run (HF its frame_of), the window bytes discharged by tac *)
Ltac exnc_mn_run HF HM HM' tac :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m ?m' =>
  assert (HM' : YStrtodRowX.aj_memnorm rsegs m');
  [ apply (exnc_mn_frame Ex rs m m' HM HF); let a0 := fresh "a" in let r0 := fresh "r" in
    let Hin0 := fresh "Hin" in let Ha0 := fresh "Ha" in intros a0 (r0 & Hin0 & Ha0); vm_compute in Hin0;
    repeat (destruct Hin0 as [<- | Hin0]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha0; tac Ha0 |]);
    destruct Hin0
  | ] end.

(* the awr side condition of a run that writes only the caller-window journal's stack window (ExvClose's exvc_awr form) *)
Ltac exnc_awr U1 U2 :=
lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
cbn [ew ewset Nat.eqb] in Ha; rewrite ?U1, ?U2 in Ha; left; lia | ]);
apply awr_ok_nil.

(* a0 at B 0x83db0: in->scratch + (s6 - in->p) = scr + (j - i1) *)
Definition exnc_A : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SOff 22 0) (SOff 32 0)) (SMd M_MUL (SOff 33 0) (SLit 18446744073709551615)).
Lemma exnc_U_A : forall E u v s, ew E 22 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 s -> ew E 33 = Z_to_bv 64 u ->
  0 <= u <= v -> v < 2 ^ 64 -> 0 <= s -> s + (v - u) < 2 ^ 64 ->
  U E exnc_A = s + (v - u).
Proof.
intros E u v s H22 H32 H33 Huv Hv Hs Hsv. unfold exnc_A.
rewrite !U_SAlu, U_SMd, (U_atom E 22 v H22), (U_atom E 32 s H32), (U_atom E 33 u H33), U_SLit by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. change (18446744073709551615 mod 2 ^ 64) with (2 ^ 64 - 1).
rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
replace (v + s + u * (2 ^ 64 - 1)) with ((s + (v - u)) + u * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* a2 at B 0x83dac: s6 - in->p = n *)
Definition exnc_Bn : sv := SAlu ALU_ADD (SOff 22 0) (SMd M_MUL (SOff 33 0) (SLit (-1))).
Lemma exnc_U_Bn : forall E u v, ew E 22 = Z_to_bv 64 v -> ew E 33 = Z_to_bv 64 u -> 0 <= u <= v -> v < 2 ^ 64 ->
  U E exnc_Bn = v - u.
Proof.
intros E u v H22 H33 Huv Hv. unfold exnc_Bn.
rewrite U_SAlu, U_SMd, (U_atom E 22 v H22), (U_atom E 33 u H33), U_SLit by lia. cbn [zalu_raw zmd_raw].
rewrite Z.add_comm. apply exnc_sub_canon; lia.
Qed.
(* the UBSan test of B 0x83dc0-0x83dd0: ((a0 <u scr) xor (n <s 0)) xor 1, which is 1 when nothing wraps *)
Lemma exnc_U_br2 : forall E u v s, ew E 22 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 s -> ew E 33 = Z_to_bv 64 u ->
  0 <= u <= v -> v < 2 ^ 63 -> 0 <= s -> s + (v - u) < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU exnc_A (SOff 32 0)) (SAlu ALU_SLT exnc_Bn (SLit 0))) (SLit 1)) = 1.
Proof.
intros E u v s H22 H32 H33 Huv Hv Hs Hsv.
rewrite (U_SAlu E ALU_XOR (SAlu ALU_XOR _ _) (SLit 1)).
rewrite (U_SAlu E ALU_XOR (SAlu ALU_SLTU _ _) (SAlu ALU_SLT _ _)).
rewrite (U_SAlu E ALU_SLTU exnc_A (SOff 32 0)), (U_SAlu E ALU_SLT exnc_Bn (SLit 0)).
rewrite (exnc_U_A E u v s H22 H32 H33), (exnc_U_Bn E u v H22 H33), (U_atom E 32 s H32), !U_SLit by lia.
cbn [zalu_raw].
replace (s + (v - u) <? s) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (swrap64_id (v - u)) by (unfold half64; lia).
replace (bv_swrap 64 (zcanon 0)) with 0 by (rewrite zcanon_id by (unfold M64; lia); symmetry; apply swrap64_id; unfold half64; lia).
replace (v - u <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
Qed.

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis HD : EXN_D B ARx SK E pos.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Let LAWS := eh_laws B ARx SK HYP.
#[local] Abbreviation AJ lyc Sc Hpc Wc memc mdc k :=
  (ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
     (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc mdc k).

(* the geometry of a cut (ExvClose's exvc_geom, restated: ExvB_Close.v does not build on the rebind base) *)
Lemma exnc_geom : forall (fx0 : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k,
  EXV_PRE B ARx E -> EXB (fx := fx0) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  2 ^ 46 <= exv_sp E /\ exv_sp E <= e_q E /\ e_q E mod 8 = 0 /\ e_q E + 40 <= exv_sp E + e_d E /\
  exv_sp E + e_d E <= 2 ^ 47 /\ alloc_ceiling <= exv_sp E /\
  exv_s1 E <= exv_sp E - 288 /\ exv_sp E - 320 < exv_s1 E /\ exv_s1 E mod 32 = 0 /\
  (forall a, exv_sp E - exv_STK E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a) /\
  ARx lyc Sc Hpc Wc memc mdc /\ 0 <= exv_STK E /\
  frame_addr lyc 1 pos + 128 <= alloc_ceiling /\ ly_stk_hi lyc <= 2 ^ 47.
Proof.
intros fx0 lyc Sc Hpc Wc regs memc mdc k HP HB.
unfold EXV_PRE in HP. cbv zeta in HP. unfold EXB in HB. cbv zeta in HB.
pose proof alloc_ceiling_val as (AC1 & AC2).
destruct HP as (HFN & PFZ & PCID & P10 & P11 & PCUR & PQ8 & PCH & PSPQ & PQD & PWIN & PSRC &
  PINB & PLEN & PI0 & PDEP & PDEPN & PDL & PWD & PSINB & PSX & PSQ & PV & PLED & PMN).
destruct HB as (HJ & HWIN & HFRG & HFRM & HHP & HAB & HROOM & HLED & HCNT &
  R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & HSAV & HSLOT & HFLAG & HSRC & HINB & HWD & HSINB &
  HQRA & HTREE).
destruct HJ as (JAR & JLY & JSEC & JWLE & JAOS & JFRAMES & JNEV & JK & JOUT & JBLK & JIMG &
  JFRU & JFREED & JPRES & JSTK & JEXTRA & JQT).
pose proof HFN as ((_ & _ & _ & _ & _ & EA & _) & _). destruct EA as (_ & HSTK0 & _).
destruct JSTK as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (Hsp : alloc_ceiling + exv_STK E <= exv_sp E) by (unfold exv_sp in *; lia).
assert (Hs1 : exv_s1 E <= exv_sp E - 288 /\ exv_sp E - 320 < exv_s1 E /\ exv_s1 E mod 32 = 0)
  by (pose proof (exv_s1_le E); lia).
assert (Hfr : frame_addr lyc 1 pos + 128 <= alloc_ceiling).
{ assert (HIN : In (1, pos) (frames Sc)) by (rewrite JFRAMES; left; reflexivity).
  destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc JAR) as (_ & HF).
  rewrite Forall_forall in HF. specialize (HF (1, pos) HIN). cbn [fst snd] in HF.
  assert (HB1 : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity). lia. }
destruct JLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
unfold exv_sp in *.
repeat (split; [lia|]). split; [intros a Ha; apply JPRES; lia|].
split; [exact JAR|]. split; [exact HSTK0|]. split; [exact Hfr | lia].
Qed.

(* EXB moves to a float state that keeps the callee-saved f registers and has rounding mode 0 (ExvLoop's exv_exb_fx,
   restated: ExvB_Loop_kitP.v does not build on the rebind base) *)
Lemma exnc_exb_fx : forall (f1 f2 : YK11.FPState) lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k,
  EXB (fx := f1) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> fregs_kept_x f1 f2 ->
  YK0o.frm_zero (@YK11.fp_csr f2) ->
  EXB (fx := f2) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos.
Proof.
intros f1 f2 lyc Sc Hpc Wc regs memc mdc k HB HK HZ.
unfold EXB in HB |- *. cbv zeta in HB |- *.
destruct HB as (H1 & H2 & H3 & H4 & REST).
split; [exact H1|]. split; [exact H2|]. split; [|split; [exact HZ | exact REST]].
intros r Hr. rewrite (HK r Hr). exact (H3 r Hr).
Qed.

(* the own fake frame lies above the image: its flag is at or above 4096 (eh_fflx), the frame 1064960 + 127 pos
   bytes above its flag (YG0f's class-1 offsets, 0 <= pos by eh_fpos), and no frame byte is in the image *)
Lemma exnc_frame_top : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  IMG_TOP_B <= frame_addr ly 1 pos.
Proof.
intros ly S Hp W mem md HAR Hin.
pose proof (eh_fpos B ARx SK HYP ly S Hp W mem md 1 pos HAR Hin) as Hpos.
destruct (eh_fflx B ARx SK HYP ly S Hp W mem md 1 pos HAR Hin) as (_ & _ & _ & (Hfl & _ & _)).
assert (Hd : frame_addr ly 1 pos = flag_addr ly 1 pos + 1064960 + 127 * pos).
{ unfold frame_addr, flag_addr, fs_frame_off, fs_flag_off, fs_frame_bytes.
  change (fs_flags_off 1) with 16384. change (Z.shiftl 1 kStackSizeLog) with 1048576.
  change (Z.shiftl 64 1) with 128. unfold kFakeFramesOff, kFakeFlagsOff. lia. }
destruct (Z_lt_le_dec (frame_addr ly 1 pos) IMG_TOP_B) as [Hlt|Hge]; [exfalso|exact Hge].
apply (frm_img_x rsegs B ARx LAWS ly S Hp W mem md 1 pos (frame_addr ly 1 pos) HAR Hin).
- change (fs_frame_bytes 1) with 128. lia.
- apply exnc_img_cover. unfold IMG_LO_B, IMG_TOP_B in *. lia.
Qed.

(* the GOT guard reads its rom bytes at any ARx state: it is a const cell of B (eh_got_const) whose value ARx keeps
   (alx_const_cells), and the rom holds the same bytes there (strtod_row.strtod_got_B, computed) *)
Lemma exnc_got : forall lyc Sc Hpc (Wc : world rsegs) memc mdc, ARx lyc Sc Hpc Wc memc mdc ->
  forall a, STRTOD_GOT_GUARD <= a < STRTOD_GOT_GUARD + 8 ->
  aview rsegs (w_H Wc) memc a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom rsegs (Z_to_bv 64 a)).
Proof.
intros lyc Sc Hpc Wc memc mdc HAR a Ha.
pose proof (alx_const_cells _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) as HC. rewrite Forall_forall in HC.
specialize (HC _ (eh_got_const B ARx SK HYP lyc)). unfold cell_holds, z8, c8 in HC. cbn [c_at c_w c_val aeval] in HC.
specialize (HC (Z.to_nat (a - STRTOD_GOT_GUARD)) ltac:(lia)).
replace a with (STRTOD_GOT_GUARD + Z.of_nat (Z.to_nat (a - STRTOD_GOT_GUARD))) by lia.
rewrite HC, (YStrtodRowX.srx_got_b_sound rsegs STRTOD_GOT_GUARD STRTOD_GUARD _ strtod_row.strtod_got_B) by lia.
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma exnc_i1 : 0 <= exv_i1 E <= exv_len E.
Proof.
unfold exv_i1, exv_len, exv_X. destruct (exn_skip_suffix (skipn (Z.to_nat (e_i0 E)) (e_x E))) as (m & Hm & ->).
rewrite length_skipn in *. rewrite length_skipn. lia.
Qed.

(* ======== the sub-piece ======== *)
Lemma exn_C : EXN_C B ARx SK E pos.
Proof.
unfold EXN_C. intros fxc lyc Sc Hpc Wc regs memc mdc k c j HP HCS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as (AC1 & AC2).
unfold EXN_CS_pre, EXN_base in HCS.
destruct HCS as ((HB & SP144 & SP152) & HDISP & HCUR & HFSH & HSPAN & Hj & Hjend & R27 & R22 & R11 & R21 & R23 & SP136).
destruct (exnc_geom fxc lyc Sc Hpc Wc regs memc mdc k HP HB) as
  (Gsp46 & Gspq & Gq8 & Gqd & Gtop & Gac & Gs1a & Gs1b & Gs1c & Gpres & GAR & GSTK & Gfr & Ghi).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (HFN & PFZ & PCID & P10 & P11 & PCUR & PQ8 & PCH & PSPQ & PQD & PWIN & PSRC & PINB & PLEN & PI0 &
  PDEP & PDEPN & PDL & PWD & PSINB & PSX & PSQ & PV & PLED & PMN).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & HWIN & HFRG & HFRM & HHP & HAB & HROOM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 &
  R19 & R3 & R4 & HSAV & HSLOT & HFLAG & HSRC & HINB & HWD & HSINB & HQRA & HTREE).
pose proof HJ as (JAR & JLY & JSEC & JWLE & JAOS & JFRAMES & JNEV & JK & JOUT & JBLK & JIMG & JFRU & JFREED & JPRES &
  JSTK & JEXTRA & JQT).
(* the overlay is normal at CS: EXB's exv_rm keep applied to EXV_PRE's entry memnorm *)
assert (HMN : YStrtodRowX.aj_memnorm rsegs memc) by exact (proj2 HROOM PMN).
pose proof JSTK as (JS16 & JS0 & JSC & JSLO & JSHI & JS47 & JSB & JST & JST2).
pose proof PWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
unfold EXN_cur in HCUR. pose proof HCUR as (CP & CE & CD & CS & CL).
destruct HDISP as (Hi1lt & Hnth & Hdisp & Hws).
pose proof exnc_i1 as Hi1.
assert (Ei1 : Z.of_nat (EXN_i1 E) = exv_i1 E) by (unfold EXN_i1; lia).
(* ex_value's stack need covers its realigned frame (304 bytes) and strtod's window *)
pose proof (exnc_stk_lo (e_n E)) as HSTK. change (STK_ex_value (e_n E)) with (exv_STK E) in HSTK.
(* ---- geometry: s1, the frame, the scratch block, the text ---- *)
assert (Hs1 : exv_sp E - 304 <= exv_s1 E) by (unfold exv_sp in *; lia).
assert (HinF : In (1, pos) (frames Sc)) by (rewrite JFRAMES; left; reflexivity).
pose proof (exnc_frame_top lyc Sc Hpc Wc memc mdc JAR HinF) as Ftop.
destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos JAR HinF) as (F4096 & Fc & Fapp).
change (fs_frame_bytes 1) with 128 in Fc, Fapp.
destruct HSINB as (bs & ms & Hbs & Hbs1 & Hbs2 & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc bs ms JAR Hbs) as (_ & Hbs4096 & Hbsc & Hbsapp & Hbspres & _).
assert (Hrq : ms <= req_size ms) by (unfold req_size; destruct (Z.eqb_spec ms 0); lia).
pose proof (sep_block_frame_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc bs ms 1 pos JAR Hbs HinF) as Hsbf.
unfold zdisjoint in Hsbf. cbn [fst snd] in Hsbf. change (fs_frame_bytes 1) with 128 in Hsbf.
pose proof HWD as (Hscr0 & Hscrc & Hscram & Hscrw & Hscrra & Hscrhv).
pose proof HSRC as (Gx & Hx4096 & Hxc & Hxam & Hxra & Hxhv).
assert (Hscr_img : e_scr E + exv_len E + 1 <= IMG_LO_B \/ IMG_TOP_B <= e_scr E).
{ destruct (Z_lt_le_dec (e_scr E) IMG_TOP_B) as [H1|H1]; [left|right; exact H1].
  destruct (Z_lt_le_dec IMG_LO_B (e_scr E + exv_len E + 1)) as [H2|H2]; [exfalso|exact H2].
  apply (blk_img_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc bs ms (Z.max (e_scr E) IMG_LO_B) JAR Hbs); [lia|].
  apply exnc_img_cover. unfold IMG_LO_B, IMG_TOP_B in *. lia. }
unfold IMG_LO_B, IMG_TOP_B in Ftop, Hscr_img.
assert (Hn : (EXN_i1 E < j <= length (e_x E))%nat) by (unfold exn_sg in Hj; lia).
assert (Hlen : Z.of_nat (length (e_x E)) = exv_len E) by reflexivity.
(* ---- keep the context small for lia: drop what the piece does not read, hide the disjunctions ---- *)
clear HFN PFZ PCID P10 P11 PCUR PCH PSRC PINB PI0 PDEP PDEPN PDL PWD PSINB PV PLED PMN HWIN HFRG HHP HAB HROOM HLED
  HCNT HSAV HSLOT HFLAG HINB HTREE JLY JSEC JWLE JAOS JNEV JK JOUT JBLK JIMG JFRU JFREED JEXTRA JQT JSB JST JST2
  PWIN Hdtop Hdpres JSTK HSRC HWD Gpres GSTK.
exnc_hide HSPAN. exnc_hide Hjend. exnc_hide Hscr_img. exnc_hide Hsbf. exnc_hide PSX. exnc_hide PSQ.
(* ======== seg 1: CS -> the __asan_memcpy entry (the ASan check of q + 24, in->scratch) ======== *)
remember (Ereg regs [w64 (e_scr E)]) as E1 eqn:HE1.
assert (AG1 : env_agree 32 (Ereg regs [w64 (e_scr E)]) E1) by (rewrite <- HE1; apply env_agree_refl).
assert (E1_19 : ew E1 19 = Z_to_bv 64 (e_q E)) by (subst E1; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E1_25 : ew E1 25 = Z_to_bv 64 SHADOW_OFF) by (subst E1; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E1_11 : ew E1 11 = Z_to_bv 64 (e_x0 E + exv_i1 E))
  by (subst E1; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E1_22 : ew E1 22 = Z_to_bv 64 (e_x0 E + Z.of_nat j))
  by (subst E1; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E1_32 : ew E1 32 = Z_to_bv 64 (e_scr E)) by (subst E1; exact (ew_Ereg_extra regs _ 0)).
assert (U1_19 : bv_unsigned (ew E1 19) = e_q E) by (rewrite E1_19; apply unsigned_lit_small; lia).
assert (U1_25 : bv_unsigned (ew E1 25) = SHADOW_OFF) by (rewrite E1_25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U1_32 : bv_unsigned (ew E1 32) = e_scr E) by (rewrite E1_32; apply unsigned_lit_small; lia).
assert (HS1 : st_ok rsegs E1 ss_exnc1
  (restrict (w_H Wc) (YK11.mkst (fx := fxc) regs (Z_to_bv 64 (exv_pc EXN_CS)) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exnc1. apply (exw_st_ok_full (fx := fxc)).
  - rewrite HE1. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exnc_r1. repeat apply Forall_cons; try apply Forall_nil. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U1_19.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E1 _ (e_q E) 24 8 (SOff 32 0) (e_scr E));
      [cbn [sv_denot]; rewrite U1_32, Z.add_0_r; reflexivity | cbn; lia | zside | exact CS].
  - apply pairwise_disjoint_of_extents. unfold exnc_r1. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]]. unfold exnc_f1. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U1_19, U1_25. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia. }
assert (HBx1 : U E1 EXNC_SB = SHADOW_OFF)
  by (unfold EXNC_SB; rewrite (U_atom E1 25 SHADOW_OFF E1_25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK1 : sh_ok rsegs EXNC_SB exnc_SHq E1 (mrestrict (w_H Wc) memc)).
{ unfold exnc_SHq. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc E1 EXNC_SB 19 (e_q E) 40 (e_q E) 0 40 HQRA HBx1);
    [rewrite (U_atom E1 19 (e_q E) E1_19) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
pose (RUN := SRr_run_tok_AJx (fx := fxc) (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low EXW_TBL
  B_prog_tbl_ok B_prog_wx).
pose (RUNTO := SRr_run_to_tok_AJx (fx := fxc) (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low
  EXW_TBL B_prog_tbl_ok B_prog_wx).
unfold cfg_at. change (w64 (exv_pc EXN_CS)) with (Z_to_bv 64 (exv_pc EXN_CS)).
exw_run_to RUNTO HS1 HJ SHOK1 (B_prog_sigma AS___asan_memcpy).
{ exnc_awr U1_19 U1_19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
rename KEPT into K1. rename HG into G1.
exnc_mn_run HF HMN HMN1 ltac:(fun h => exfalso; lia). clear HF HFr.
(* ---- at the __asan_memcpy entry: a0 = scr, a1 = x0 + i1, a2 = j - i1, ra = B 0x83d98, s4 = q + 24,
   s11 = shadow (q + 24) ---- *)
prreg HS1 (10%bv : bv 5) T10. rewrite E1_32 in T10.
prreg HS1 (11%bv : bv 5) T11. rewrite E1_11 in T11.
prreg HS1 (1%bv : bv 5) T1.
prreg HS1 (20%bv : bv 5) T20. rewrite U1_19 in T20.
pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 27%bv HS1) as T27.
lazymatch type of T27 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 27%bv) with (exnc_shx 24) in T27 end.
rewrite (exnc_denot_shx E1 24 (e_q E) SHADOW_OFF E1_19 E1_25) in T27 by (unfold SHADOW_OFF; lia).
cbn [ms_regs restrict] in T27.
pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 12%bv HS1) as T12.
lazymatch type of T12 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 12%bv) with (SAlu ALU_ADD (SMd M_MUL (SOff 11 0) (SLit (-1))) (SOff 22 0)) in T12 end.
rewrite (exnc_U_sub E1 (e_x0 E + exv_i1 E) (e_x0 E + Z.of_nat j) E1_11 E1_22) in T12 by lia.
cbn [ms_regs restrict] in T12.
replace (e_x0 E + Z.of_nat j - (e_x0 E + exv_i1 E)) with (Z.of_nat j - exv_i1 E) in T12 by lia.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ EXNC_KL1 HS1 AG1 ltac:(vm_compute; reflexivity)) as RK1.
cbn [ms_regs restrict] in RK1.
lazymatch type of HS1 with st_ok _ _ _ (restrict _ ?mx) => rename mx into ms1 end.
assert (T1' : YK11.getr (ms_regs ms1) 1 = Z_to_bv 64 EXNC_P2) by (rewrite T1; f_equal; vm_compute; reflexivity).
clear T1.
pmkst HS1.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
  replace p with (B_prog_sigma AS___asan_memcpy) by (vm_compute; reflexivity) end.
assert (Esp1 : spZ (ms_regs ms1) = exv_s1 E)
  by (unfold spZ; rewrite (RK1 2%bv ltac:(cbn; tauto)), R2; apply unsigned_lit_small; lia).
(* ---- the __asan_memcpy call (YGcallMxmn.aj_intrin_at_xm at EXV_HYP's eh_memcpy; its keep carries memnorm) ---- *)
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_intrin_at_xm (fx := fxc) (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low OCpy
    (B_prog_sigma AS___asan_memcpy) (eh_memcpy B ARx SK HYP fxc) Wc (ms_regs ms1) (ms_mem ms1)
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] lyc Sc Hpc _ k (e_scr E) (e_x0 E + exv_i1 E) (Z.of_nat j - exv_i1 E)
    (exv_s1 E - (exv_sp E + e_d E)) _ HJ).
  - exact T10.
  - exact T11.
  - exact T12.
  - lia.
  - lia.
  - lia.
  - rewrite Esp1. lia.
  - unfold exv_sp in *. lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite (RK1 3%bv ltac:(cbn; tauto)). exact R3.
  - rewrite (RK1 4%bv ltac:(cbn; tauto)). exact R4.
  - exact T1'.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + unfold awr_byte. right; left. split.
      * exists (e_scr E, e_scr E + exv_len E + 1). split; [left; reflexivity | cbn [fst snd]; lia].
      * exists bs, ms. split; [exact Hbs | lia].
    + unfold ESTACK. lia.
  - unfold amem_range in *. lia.
  - intros x Hx. rewrite K1 by (first [tauto | unfold shadow_of_addr, SHADOW_OFF; lia]). apply Hscrra. lia.
  - intros _ s Hs.
    assert (Hh : shadow_hull_vis (aview rsegs (w_H Wc) memc) (e_scr E) (Z.of_nat j - exv_i1 E))
      by (apply (exv_hull_sub _ (e_scr E) (exv_len E + 1)); [exact (Hscrhv ltac:(lia)) | lia | lia]).
    rewrite K1 by (first [tauto | unfold shadow_addr, SHADOW_OFF in *; lia]). exact (Hh s Hs).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - rewrite K1 by (first [tauto | lia]).
        replace a with (e_x0 E + Z.of_nat (Z.to_nat (a - e_x0 E))) by lia.
        rewrite (exnc_garr8_aview _ _ _ _ _ Gx) by lia. discriminate.
      - rewrite Esp1. unfold ESTACK. lia. }
    split; [unfold exnc_hid in PSX; lia|]. split; [unfold amem_range in *; lia|].
    split; [intros x Hx; rewrite K1 by (first [tauto | unfold shadow_of_addr, SHADOW_OFF; lia]); apply Hxra; lia|].
    intros _ s Hs.
    assert (Hh : shadow_hull_vis (aview rsegs (w_H Wc) memc) (e_x0 E + exv_i1 E) (Z.of_nat j - exv_i1 E))
      by (apply (exv_hull_sub _ (e_x0 E) (exv_len E)); [exact (Hxhv ltac:(lia)) | lia | lia]).
    rewrite K1 by (first [tauto | unfold shadow_addr, SHADOW_OFF in *; lia]). exact (Hh s Hs). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hr2 & Hcopy & Hfr2 & Hpres2 & HKM2).
assert (HMN2 : YStrtodRowX.aj_memnorm rsegs mem2) by exact (HKM2 HMN1). clear HKM2.
(* ======== seg 2: B 0x83d98 -> B 0x83dd8 (the ASan check of q, a0 = scr + n, three UBSan checks) ======== *)
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_scr E <= a < e_scr E + exv_len E + 1) ->
  ~ (exv_s1 E - 16384 <= a < exv_s1 E) -> aview rsegs (w_H Wc) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha H1 H2. rewrite (Hfr2 a Ha); [apply K1; [exact Ha | tauto] | intros Hb; apply H1; lia |
    intros Hb; apply H2; unfold ESTACK in Hb; lia]. }
assert (GA2 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem2 a)
  by (intros a Ha; apply Hpres2, (apresent_grows _ _ _ a G1), Ha).
assert (RK2 : forall x, In x EXNC_KL1 -> YK11.getr regs2 x = YK11.getr regs x)
  by (intros x Hx; rewrite (exnc_pres_kl _ _ HP2 x Hx); exact (RK1 x Hx)).
assert (Q20 : YK11.getr regs2 20 = Z_to_bv 64 (e_q E + 24)) by (rewrite (exnc_pres _ _ HP2 20%bv exnc_cs20); exact T20).
assert (Q27 : YK11.getr regs2 27 = w64 (shadow_addr (e_q E + 24)))
  by (rewrite (exnc_pres _ _ HP2 27%bv exnc_cs27); exact T27).
clear T10 T11 T12 T20 T27 HS1 SHOK1.
remember (Ereg regs2 [w64 (e_scr E); w64 (e_x0 E + exv_i1 E)]) as E2 eqn:HE2.
assert (AG2 : env_agree 32 (Ereg regs2 [w64 (e_scr E); w64 (e_x0 E + exv_i1 E)]) E2)
  by (rewrite <- HE2; apply env_agree_refl).
assert (E2_9 : ew E2 9 = Z_to_bv 64 (exv_s1 E))
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), (RK2 9%bv ltac:(cbn; tauto)); exact R9).
assert (E2_19 : ew E2 19 = Z_to_bv 64 (e_q E))
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), (RK2 19%bv ltac:(cbn; tauto)); exact R19).
assert (E2_25 : ew E2 25 = Z_to_bv 64 SHADOW_OFF)
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 25 25%bv eq_refl), (RK2 25%bv ltac:(cbn; tauto)); exact R25).
assert (E2_22 : ew E2 22 = Z_to_bv 64 (e_x0 E + Z.of_nat j))
  by (subst E2; rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl), (RK2 22%bv ltac:(cbn; tauto)); exact R22).
assert (E2_32 : ew E2 32 = Z_to_bv 64 (e_scr E)) by (subst E2; exact (ew_Ereg_extra regs2 _ 0)).
assert (E2_33 : ew E2 33 = Z_to_bv 64 (e_x0 E + exv_i1 E)) by (subst E2; exact (ew_Ereg_extra regs2 _ 1)).
assert (U2_9 : bv_unsigned (ew E2 9) = exv_s1 E) by (rewrite E2_9; apply unsigned_lit_small; lia).
assert (U2_19 : bv_unsigned (ew E2 19) = e_q E) by (rewrite E2_19; apply unsigned_lit_small; lia).
assert (U2_25 : bv_unsigned (ew E2 25) = SHADOW_OFF) by (rewrite E2_25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U2_22 : bv_unsigned (ew E2 22) = e_x0 E + Z.of_nat j) by (rewrite E2_22; apply unsigned_lit_small; lia).
assert (U2_32 : bv_unsigned (ew E2 32) = e_scr E) by (rewrite E2_32; apply unsigned_lit_small; lia).
assert (U2_33 : bv_unsigned (ew E2 33) = e_x0 E + exv_i1 E) by (rewrite E2_33; apply unsigned_lit_small; lia).
assert (HS2 : st_ok rsegs E2 ss_exnc2
  (restrict (w_H Wc) (YK11.mkst (fx := fxc) regs2 (Z_to_bv 64 EXNC_P2) mem2 (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exnc2. apply (exw_st_ok_full (fx := fxc)).
  - rewrite HE2. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold exnc_r2s, exnc_r2q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U2_9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E2 _ (exv_s1 E) 144 8 (exnc_shx 0) (shadow_addr (e_q E)));
        [ rewrite (exnc_denot_shx E2 0 (e_q E) SHADOW_OFF E2_19 E2_25) by (unfold SHADOW_OFF; lia);
          unfold shadow_addr; rewrite Z.add_0_r; reflexivity
        | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside |].
      apply (exw_val_kept rsegs (w_H Wc) memc); [|exact SP144]. intros x Hx. apply KA2; lia.
    + rewrite U2_19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs E2 _ (e_q E) 0 8 (SOff 33 0) (e_x0 E + exv_i1 E));
          [ cbn [sv_denot]; rewrite U2_33, Z.add_0_r; reflexivity | cbn; lia | zside |].
        rewrite Z.add_0_r. apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CP].
        intros x Hx. unfold exnc_hid in PSQ. apply KA2; lia.
      * apply (chunk_ok_val rsegs E2 _ (e_q E) 24 8 (SOff 32 0) (e_scr E));
          [ cbn [sv_denot]; rewrite U2_32, Z.add_0_r; reflexivity | cbn; lia | zside |].
        apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS].
        intros x Hx. unfold exnc_hid in PSQ. apply KA2; lia.
  - apply pairwise_disjoint_of_extents. unfold exnc_r2s, exnc_r2q. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2_9, U2_19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]]. unfold exnc_f2. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U2_9, U2_19, U2_25, U2_22, U2_32, U2_33.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia. }
assert (HBx2 : U E2 EXNC_SB = SHADOW_OFF)
  by (unfold EXNC_SB; rewrite (U_atom E2 25 SHADOW_OFF E2_25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK2 : sh_ok rsegs EXNC_SB exnc_SHq E2 (mrestrict (w_H Wc) mem2)).
{ unfold exnc_SHq. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) mem2 E2 EXNC_SB 19 (e_q E) 40 (e_q E) 0 40); [| exact HBx2 |
    rewrite (U_atom E2 19 (e_q E) E2_19) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia].
  apply (exw_ra_kept rsegs (w_H Wc) memc); [|exact HQRA]. intros x Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbsapp.
  apply KA2; unfold shadow_of_addr, SHADOW_OFF; lia. }
exw_run RUN HS2 HJ2 SHOK2.
{ exnc_awr U2_9 U2_19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
rename KEPT into K21. rename HG into G21.
exnc_mn_run HF HMN2 HMN21 ltac:(fun h => exfalso; lia). clear HF HFr.
exw_branch HS2 SHOK2.
{ (* UBSan B 0x83dbc taken: scr + n = 0, but 4096 <= scr *)
  exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U_lit in Hc by lia.
  rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. fold exnc_A in Hc.
  rewrite (exnc_U_A E2 (e_x0 E + exv_i1 E) (e_x0 E + Z.of_nat j) (e_scr E) E2_22 E2_32 E2_33), U_lit in Hc by lia.
  replace (e_scr E + (e_x0 E + Z.of_nat j - (e_x0 E + exv_i1 E)) <? 1) with false in Hc
    by (symmetry; apply Z.ltb_ge; lia).
  rewrite zcanon_id in Hc by (unfold M64; lia). lia. }
clear Hc.
exw_run RUN HS2 HJ2 SHOK2.
{ exnc_awr U2_9 U2_19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
rename KEPT into K22. rename HG into G22.
exnc_mn_run HF HMN21 HMN22 ltac:(fun h => exfalso; lia). clear HF HFr.
exw_branch HS2 SHOK2.
{ (* UBSan B 0x83dd0 taken: scr + n wraps below scr, or n < 0 *)
  exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite U_lit in Hc by lia.
  fold exnc_A exnc_Bn in Hc.
  rewrite (exnc_U_br2 E2 (e_x0 E + exv_i1 E) (e_x0 E + Z.of_nat j) (e_scr E) E2_22 E2_32 E2_33) in Hc by lia. lia. }
clear Hc.
exw_run_to RUNTO HS2 HJ2 SHOK2 EXNC_P3.
{ exnc_awr U2_9 U2_19. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
rename KEPT into K23. rename HG into G23.
exnc_mn_run HF HMN22 HMN23 ltac:(fun h => exfalso; lia). clear HF HFr.
(* ---- at B 0x83dd8: a0 = scr + n; the registers of KLC kept; no byte written since the call ---- *)
pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 10%bv HS2) as T10.
lazymatch type of T10 with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 10%bv) with exnc_A in T10 end.
rewrite denot_lit_U, (exnc_U_A E2 (e_x0 E + exv_i1 E) (e_x0 E + Z.of_nat j) (e_scr E) E2_22 E2_32 E2_33) in T10 by lia.
cbn [ms_regs restrict] in T10.
replace (e_scr E + (e_x0 E + Z.of_nat j - (e_x0 E + exv_i1 E))) with (e_scr E + (Z.of_nat j - exv_i1 E)) in T10 by lia.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs2 _ EXNC_KLC HS2 AG2 ltac:(vm_compute; reflexivity)) as RK23.
cbn [ms_regs restrict] in RK23.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?mx) => rename mx into ms3 end.
assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_scr E <= a < e_scr E + exv_len E + 1) ->
  ~ (exv_s1 E - 16384 <= a < exv_s1 E) -> aview rsegs (w_H Wc) (ms_mem ms3) a = aview rsegs (w_H Wc) memc a)
  by (intros a Ha H1 H2; rewrite K23, K22, K21 by (first [exact Ha | tauto]); exact (KA2 a Ha H1 H2)).
assert (KA3c : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) (ms_mem ms3) a = aview rsegs (w_H Wc) mem2 a)
  by (intros a Ha; rewrite K23, K22, K21 by (first [exact Ha | tauto]); reflexivity).
assert (GA3 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms3) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a G23), (apresent_grows _ _ _ a G22), (apresent_grows _ _ _ a G21), GA2, Ha).
clear K21 K22 K23 G21 G22 G23 SHOK2.
pmkst HS2.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
  replace p with EXNC_P3 by (vm_compute; reflexivity) end.
clear HS2.
(* ======== seg 3: B 0x83dd8 -> the strtod entry (the NUL byte's check and store, the check of q + 24) ======== *)
assert (RK3 : forall x, In x EXNC_KL1 -> YK11.getr (ms_regs ms3) x = YK11.getr regs x).
{ intros x Hx. rewrite (RK23 x); [exact (RK2 x Hx)|]. unfold EXNC_KL1 in Hx. unfold EXNC_KLC.
  cbn [In] in Hx |- *. tauto. }
assert (R3_20 : YK11.getr (ms_regs ms3) 20 = Z_to_bv 64 (e_q E + 24)) by (rewrite (RK23 20%bv ltac:(cbn; tauto)); exact Q20).
assert (R3_27 : YK11.getr (ms_regs ms3) 27 = w64 (shadow_addr (e_q E + 24)))
  by (rewrite (RK23 27%bv ltac:(cbn; tauto)); exact Q27).
remember (Ereg (ms_regs ms3) [w64 (e_scr E)]) as E3 eqn:HE3.
assert (AG3 : env_agree 32 (Ereg (ms_regs ms3) [w64 (e_scr E)]) E3) by (rewrite <- HE3; apply env_agree_refl).
assert (E3_10 : ew E3 10 = Z_to_bv 64 (e_scr E + (Z.of_nat j - exv_i1 E)))
  by (subst E3; rewrite (ew_Ereg_nat (ms_regs ms3) _ 10 10%bv eq_refl); exact T10).
assert (E3_19 : ew E3 19 = Z_to_bv 64 (e_q E))
  by (subst E3; rewrite (ew_Ereg_nat (ms_regs ms3) _ 19 19%bv eq_refl), (RK3 19%bv ltac:(cbn; tauto)); exact R19).
assert (E3_25 : ew E3 25 = Z_to_bv 64 SHADOW_OFF)
  by (subst E3; rewrite (ew_Ereg_nat (ms_regs ms3) _ 25 25%bv eq_refl), (RK3 25%bv ltac:(cbn; tauto)); exact R25).
assert (E3_32 : ew E3 32 = Z_to_bv 64 (e_scr E)) by (subst E3; exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (U3_10 : bv_unsigned (ew E3 10) = e_scr E + (Z.of_nat j - exv_i1 E)) by (rewrite E3_10; apply unsigned_lit_small; lia).
assert (U3_19 : bv_unsigned (ew E3 19) = e_q E) by (rewrite E3_19; apply unsigned_lit_small; lia).
assert (U3_25 : bv_unsigned (ew E3 25) = SHADOW_OFF) by (rewrite E3_25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U3_32 : bv_unsigned (ew E3 32) = e_scr E) by (rewrite E3_32; apply unsigned_lit_small; lia).
assert (HS3 : st_ok rsegs E3 ss_exnc3
  (restrict (w_H Wc) (YK11.mkst (fx := fxc) (ms_regs ms3) (Z_to_bv 64 EXNC_P3) (ms_mem ms3) (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_exnc3. apply (exw_st_ok_full (fx := fxc)).
  - unfold exnc_regs3. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE3; apply regs_ok_Ereg | intros X; discriminate X |]
      | intros X; discriminate X |].
    + cbn [sv_denot]. rewrite U3_19. exact R3_20.
    + rewrite (exnc_denot_shx E3 24 (e_q E) SHADOW_OFF E3_19 E3_25) by (unfold SHADOW_OFF; lia). exact R3_27.
  - vm_compute. reflexivity.
  - unfold exnc_r3b, exnc_r3q. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U3_10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply GA3.
      apply (proj1 (Hbspres (e_scr E + (Z.of_nat j - exv_i1 E) + o) ltac:(lia))).
    + rewrite U3_19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E3 _ (e_q E) 24 8 (SOff 32 0) (e_scr E));
        [ cbn [sv_denot]; rewrite U3_32, Z.add_0_r; reflexivity | cbn; lia | zside |].
      apply (exw_val_kept rsegs (w_H Wc) memc); [|exact CS].
      intros x Hx. unfold exnc_hid in PSQ. apply KA3; lia.
  - apply pairwise_disjoint_of_extents. unfold exnc_r3b, exnc_r3q. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U3_10, U3_19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold exnc_hid in PSQ. repeat split; lia.
  - split; [|split; [exact I | exact I]]. unfold exnc_f3. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U3_10, U3_19, U3_25.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (HBx3 : U E3 EXNC_SB = SHADOW_OFF)
  by (unfold EXNC_SB; rewrite (U_atom E3 25 SHADOW_OFF E3_25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK3 : sh_ok rsegs EXNC_SB exnc_SH3 E3 (mrestrict (w_H Wc) (ms_mem ms3))).
{ unfold exnc_SH3. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbsapp.
  constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H Wc) (ms_mem ms3) E3 EXNC_SB 10 (e_scr E) (exv_len E + 1)
      (e_scr E + (Z.of_nat j - exv_i1 E)) 0 1); [| exact HBx3 |
      rewrite (U_atom E3 10 _ E3_10) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia].
    apply (exw_ra_kept rsegs (w_H Wc) memc); [|exact Hscrra]. intros x Hx.
    apply KA3; unfold shadow_of_addr, SHADOW_OFF; lia.
  - apply (shent_ok_of_range rsegs (w_H Wc) (ms_mem ms3) E3 EXNC_SB 19 (e_q E) 40 (e_q E) 0 40); [| exact HBx3 |
      rewrite (U_atom E3 19 (e_q E) E3_19) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia].
    apply (exw_ra_kept rsegs (w_H Wc) memc); [|exact HQRA]. intros x Hx.
    apply KA3; unfold shadow_of_addr, SHADOW_OFF; lia. }
exw_run_to RUNTO HS3 HJ2 SHOK3 (B_prog_sigma AS_strtod).
{ lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply exw_awr_cons; [|apply exw_awr_cons; [|apply awr_ok_nil]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; cbn [ew ewset Nat.eqb] in Ha;
    rewrite ?U3_10, ?U3_19 in Ha; [|lia].
  unfold awr_byte. right; left. split.
  - exists (e_scr E, e_scr E + exv_len E + 1). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists bs, ms. split; [exact Hbs | lia]. }
(* ---- at the strtod entry: a0 = scr, a1 = s7 = f + 32, ra = B 0x83e00; the NUL at scr + n ---- *)
exw_kept_of HFr (fun a => a = e_scr E + (Z.of_nat j - exv_i1 E))
  ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U3_10 in h).
rename KEPT into K31. rename HG into G31.
(* the NUL store's one byte scr + n: inside the scratch block, so off every segment and below TASK_SIZE *)
pose proof exnc_task as HTS.
exnc_mn_run HF HMN23 HMN4 ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U3_10 in h;
  first [exfalso; lia
        | split; [lia | apply exnc_fs_none; apply (blk_img_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc bs ms _ JAR Hbs); lia]]).
clear HF HFr.
rename HJ2 into HJ4.
lazymatch type of HS3 with st_ok _ ?Ex _ (restrict _ ?mx) => rename mx into ms4;
  assert (AG4 : env_agree 32 (Ereg (ms_regs ms3) [w64 (e_scr E)]) Ex) by (rewrite <- HE3; apply exw_agree2) end.
pose proof (exw_region_nth rsegs _ _ _ 0 _ HS3 eq_refl) as RB. cbn [ms_mem restrict] in RB.
pose proof (exw_field rsegs _ _ 10%nat (e_scr E + (Z.of_nat j - exv_i1 E)) _ _ _ _ _ 0 1 (SLit 0) 0 RB
  ltac:(cbn [ew ewset Nat.eqb]; exact U3_10) ltac:(left; reflexivity) ltac:(cbn [sv_denot]; reflexivity)
  ltac:(cbn; lia) ltac:(zside)) as VNUL.
rewrite Z.add_0_r in VNUL. clear RB.
prreg HS3 (1%bv : bv 5) T1.
prreg HS3 (10%bv : bv 5) T10b. cbn [ew ewset Nat.eqb] in T10b. rewrite E3_32 in T10b.
prreg HS3 (11%bv : bv 5) T11b. cbn [ew ewset Nat.eqb] in T11b.
rewrite HE3, (ew_Ereg_nat (ms_regs ms3) _ 23 23%bv eq_refl), (RK3 23%bv ltac:(cbn; tauto)) in T11b.
prreg HS3 (20%bv : bv 5) T20b. cbn [ew ewset Nat.eqb] in T20b. rewrite U3_19 in T20b.
pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 27%bv HS3) as T27b.
lazymatch type of T27b with _ = sv_denot ?Ex (sr_get (ss_regs ?ssx) _) =>
  change (sr_get (ss_regs ssx) 27%bv) with (exnc_shx 24) in T27b;
  rewrite (exnc_denot_shx Ex 24 (e_q E) SHADOW_OFF ltac:(exw_ew E3_19) ltac:(exw_ew E3_25)) in T27b
    by (unfold SHADOW_OFF; lia) end.
cbn [ms_regs restrict] in T27b.
pose proof (regs_kept_of_st_ok rsegs _ _ _ (ms_regs ms3) _ EXNC_KL1 HS3 AG4 ltac:(vm_compute; reflexivity)) as RK34.
cbn [ms_regs restrict] in RK34.
assert (RK4 : forall x, In x EXNC_KL1 -> YK11.getr (ms_regs ms4) x = YK11.getr regs x)
  by (intros x Hx; rewrite (RK34 x Hx); exact (RK3 x Hx)).
assert (Esp4 : spZ (ms_regs ms4) = exv_s1 E)
  by (unfold spZ; rewrite (RK4 2%bv ltac:(cbn; tauto)), R2; apply unsigned_lit_small; lia).
assert (KA4 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_scr E <= a < e_scr E + exv_len E + 1) ->
  ~ (exv_s1 E - 16384 <= a < exv_s1 E) -> aview rsegs (w_H Wc) (ms_mem ms4) a = aview rsegs (w_H Wc) memc a).
{ intros a Ha H1 H2. rewrite K31 by (first [exact Ha | intros He; apply H1; lia]). exact (KA3 a Ha H1 H2). }
assert (GA4 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms4) a)
  by (intros a Ha; apply (apresent_grows _ _ _ a G31), GA3, Ha).
(* the scratch holds txt ++ [0] *)
assert (G4 : garr8 rsegs (rdW Wc (ms_mem ms4)) (e_scr E) (exn_sub (e_x E) (EXN_i1 E) j ++ [0])).
{ unfold exn_sub. apply (exnc_garr8_build (w_H Wc) memc (ms_mem ms4) (e_x0 E) (e_x E) (EXN_i1 E) (j - EXN_i1 E)%nat
    (e_scr E) Gx ltac:(lia)).
  - intros jj Hjj. rewrite K31 by (first [lia | intros He; lia]). rewrite KA3c by lia.
    rewrite (Hcopy (Z.of_nat jj)) by lia. rewrite K1 by (first [tauto | lia]). f_equal. lia.
  - replace (e_scr E + Z.of_nat (j - EXN_i1 E)) with (e_scr E + (Z.of_nat j - exv_i1 E)) by lia. exact VNUL. }
assert (HTXT : exv_txt_ok (exn_sub (e_x E) (EXN_i1 E) j)).
{ unfold exnc_hid in HSPAN. destruct HSPAN as (_ & _ & _ & HSP).
  exact (exnc_txt_ok (e_x E) (EXN_i1 E) c j (exnc_garr8_bytes _ _ _ Gx) Hnth Hn ltac:(lia) HSP). }
assert (Htl : Z.of_nat (length (exn_sub (e_x E) (EXN_i1 E) j)) = Z.of_nat j - exv_i1 E)
  by (rewrite exnc_sub_len by lia; lia).
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
  replace p with (B_prog_sigma AS_strtod) by (vm_compute; reflexivity) end.
clear HS3 SHOK3.
(* ======== strtod (scr, f + 32): YStrtodRowX's row at B (ExvB_Stmt's exv_strtod) ======== *)
eapply SRr_bind.
{ eapply (exv_strtod B ARx SK HYP fxc prh_pst Wc (ms_regs ms4) (ms_mem ms4) (exv_STK E + e_d E) (exv_sp E + e_d E)
    (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc _ k (e_scr E)
    (frame_addr lyc 1 pos + 32) (exn_sub (e_x E) (EXN_i1 E) j) (exv_s1 E - (exv_sp E + e_d E)) _ HJ4).
  - exact T10b.
  - rewrite T11b. exact R23.
  - rewrite Esp4. lia.
  - unfold exv_sp in *. lia.
  - lia.
  - unfold STK_RT_STRTOD, ESTACK. lia.
  - rewrite (RK4 3%bv ltac:(cbn; tauto)). exact R3.
  - rewrite (RK4 4%bv ltac:(cbn; tauto)). exact R4.
  - exact T1.
  - vm_compute. reflexivity.
  - exact G4.
  - exact HTXT.
  - lia.
  - rewrite Htl. lia.
  - left. rewrite Htl. unfold STK_RT_STRTOD, ESTACK. lia.
  - intros a Ha. left. unfold awr_byte. right; right; right. exists 1, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. lia.
  - left. unfold STK_RT_STRTOD, ESTACK. lia.
  - rewrite Htl. unfold exnc_hid in Hsbf. lia.
  - exact HFRM.
  - unfold YStrtodRowX.strtod_site_x.
    cbn [YStrtodRowX.si_img_lo YStrtodRowX.si_globals_top YStrtodRowX.si_got_guard strtod_row.strtod_img_B].
    unfold STRTOD_IMG_LO, STRTOD_GLOBALS_TOP. rewrite Htl.
    split; [unfold exnc_hid in Hscr_img; lia|]. split; [lia|]. split; [lia|]. split.
    + exact (exnc_got lyc Sc Hpc Wc _ _ (proj1 HJ4)).
    + exact HMN4. }
cbv beta. intros W5 c5 _ (-> & fx5 & regs5 & mem5 & md5 & bits & cn & -> & FZ & FK & FA & SC & Hcn & HJ5 & HP5 & VE &
  Hfr5 & Hgr5 & HMN5).
(* ======== CR (B 0x83e00): the state at strtod's return, handed to EXN_D ======== *)
assert (Eerr : as_errno B = STRTOD_ERRNO) by exact (eh_errno_B B ARx SK HYP).
unfold STRTOD_ERRNO in Eerr.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (exv_s1 E - 16384 <= a < exv_s1 E) ->
  ~ (e_scr E <= a < e_scr E + exv_len E + 1) -> ~ (frame_addr lyc 1 pos + 32 <= a < frame_addr lyc 1 pos + 40) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview rsegs (w_H Wc) mem5 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha H1 H2 H3 H4. rewrite (Hfr5 a Ha); [exact (KA4 a Ha H2 H1) | lia | | exact H4].
  unfold STK_RT_STRTOD, ESTACK. lia. }
assert (GA5 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem5 a) by (intros a Ha; apply Hgr5, GA4, Ha).
assert (RK5 : forall x, In x EXNC_KL1 -> YK11.getr regs5 x = YK11.getr regs x)
  by (intros x Hx; rewrite (exnc_pres_kl _ _ HP5 x Hx); exact (RK4 x Hx)).
assert (R5_20 : YK11.getr regs5 20 = w64 (e_q E + 24)) by (rewrite (exnc_pres _ _ HP5 20%bv exnc_cs20); exact T20b).
assert (R5_27 : YK11.getr regs5 27 = w64 (shadow_addr (e_q E + 24)))
  by (rewrite (exnc_pres _ _ HP5 27%bv exnc_cs27); exact T27b).
assert (KW : forall z, 0 <= z < 2 ^ 64 -> ~ EXN_wz B E pos lyc z -> aview rsegs (w_H Wc) mem5 z = aview rsegs (w_H Wc) memc z).
{ intros z Hz Hnz. unfold EXN_wz in Hnz. apply KALL; [exact Hz | | | |]; intros Hb; apply Hnz.
  - left. unfold STK_RT_STRTOD, ESTACK. lia.
  - right; right; right; right; right; left. lia.
  - right; left. lia.
  - right; right; right; right; right; right. exact Hb. }
assert (KSP : forall o, 0 <= o -> o + 8 <= 160 ->
  forall z, exv_s1 E + o <= z < exv_s1 E + o + 8 -> aview rsegs (w_H Wc) mem5 z = aview rsegs (w_H Wc) memc z).
{ intros o Ho1 Ho2 z Hz. apply KALL; lia. }
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?r _ _) _) _ =>
  replace r with (w64 (exv_pc EXN_CR)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
change (mkCfg (YK11.mkst (fx := fx5) regs5 (w64 (exv_pc EXN_CR)) mem5 (YK11.seg_rom rsegs)) md5)
  with (cfg_at (fx := fx5) rsegs (exv_pc EXN_CR) regs5 mem5 md5).
apply (HD fx5 lyc Sc Hpc Wc regs5 mem5 md5 k c j bits cn HP).
unfold EXN_CR_pre, EXN_base. cbv zeta.
split; [split; [|split]|].
{ (* EXB at the callee's float state, by the segment's EXN_keepM *)
  apply (MK fx5 lyc Sc Hpc Wc regs memc mdc k regs5 mem5 md5 k HP
    (exnc_exb_fx fxc fx5 lyc Sc Hpc Wc regs memc mdc k HB FK FZ) HJ5 KW GA5 ltac:(intros _; exact HMN5)).
  unfold EXN_regs_kept. repeat split; apply RK5; cbn; tauto. }
{ exact (KS Wc memc mem5 144 _ SP144 (KSP 144 ltac:(lia) ltac:(lia))). }
{ exact (KS Wc memc mem5 152 _ SP152 (KSP 152 ltac:(lia) ltac:(lia))). }
split; [exact (conj Hi1lt (conj Hnth (conj Hdisp Hws)))|].
split.
{ unfold EXN_cur. unfold exnc_hid in PSQ. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp.
  split; [|split; [|split; [|split]]];
    (apply (exw_val_kept rsegs (w_H Wc) memc); [intros x Hx; apply KALL; cbn in Hx; lia | assumption]). }
split.
{ unfold EXN_fsh in *. destruct HFSH as [FS4 FS8].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Hbsapp.
  split; [rewrite KALL; [exact FS4 | unfold shadow_addr, SHADOW_OFF in *; lia ..] |
          rewrite KALL; [exact FS8 | unfold shadow_addr, SHADOW_OFF in *; lia ..]]. }
split; [unfold exnc_hid in HSPAN; exact HSPAN|].
split; [exact Hj|].
split; [unfold exnc_hid in Hjend; exact Hjend|].
split.
{ apply (exw_garr8_kept rsegs (w_H Wc) (ms_mem ms4) mem5); [|exact G4].
  intros a Ha. rewrite length_app, Nat2Z.inj_add, Htl in Ha. cbn [length] in Ha.
  unfold exnc_hid in Hsbf, Hscr_img. apply Hfr5; [lia | lia | unfold STK_RT_STRTOD, ESTACK; lia | lia]. }
split; [exact SC|].
split; [exact Hcn|].
split; [exact VE|].
split; [exact FA|].
split; [rewrite (RK5 22%bv ltac:(cbn; tauto)); exact R22|].
split; [rewrite (RK5 21%bv ltac:(cbn; tauto)); exact R21|].
split; [rewrite (RK5 23%bv ltac:(cbn; tauto)); exact R23|].
split; [exact R5_20|].
split; [exact R5_27|].
exact (KS Wc memc mem5 136 _ SP136 (KSP 136 ltac:(lia) ltac:(lia))).
Qed.

End p.

Print Assumptions exn_C.
