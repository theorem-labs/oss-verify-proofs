(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/ATxLine.v, with its module paths and module names changed; 1442 of its 1552 lines of code are new or changed and 914 lines of the source are left out. *)
(* RULE 24: proves no function (kind: segment lemma of tx_string's A' walk: the loop body).
   fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): THE LOOP BODY of
   the tx_string walk (fuzz_preset.c :413-428), one iteration from the loop head (A' 0x85448) back to it or to the
   closing quote's block (A' 0x85580), against the text ttx_string_specX (lib/A/PRH_FnTx.v: the budgeted fpostWbm
   post), in the per-function form over the listing engine (YC80x / YC1fPx over YCbqG's ajournal_x). The function
   theorem and the other segments are lib/A/Prog/ATxString.v, the static image witnesses lib/A/Prog/ATxStrWitA.v; this
   file imports neither, only the #102 image-generic glue lib/A/Prog/TxStr102Glue.v over lib/A/Prog/Tx102Glue.v (the
   text state), instantiated at PI_prog_A, the whole-program instance (PALib is satisfiable only there).
   HOW. The loop body of image B' (lib/B/Prog/BTxStep.v), ported. In segments D1, H1 .. H5, D and E (the loop head to
   the byte's last tx_put call) and in the class block, every A' instruction has a B' twin with the same operation and
   registers, 8 bytes earlier (in the class block 16 bytes earlier); only the pc-relative immediates of the branches
   and calls differ, each one targets its twin's target. So those segments are the B' proofs at the A' seams and
   `change` numerals: the engine reads the listing. F1 and F2 differ. A' has no UBSan
   test of s + i (the B' `li a0, -1; beq s3, a0` to its trap), so F1 is the re-poison of esc[] alone and needs no fact
   on s3. The A' loop test is inverted: `bnez a1` to the loop head, else `j` to the closing block (B': `beqz a1` to the
   closing block, else `j` to the loop head), so F2's two arms swap their branch facts and the `j` runs on the closing
   arm.
   ONE RELATION. Every tx_put call crosses the grow's free, so the loop body runs at ONE relation, WR := wle' SEGS
   RZ_cf. The live state livea is the glue's ts_liveR at WR (its journal from the entry lifted once by the caller,
   ATxString.v), every segment is SRW (SRr' at RZ_cf), the runners are the R forms at WR, and the glue's ts_put_call /
   ts_LH / ts_loop are at RCF = WR. QF is already the primed post (fpostWbm is fpostW_xbR at WR), so QFa is the glue's
   QF. The text's `(length rp_os <= 4)%nat` is the Section-g hypothesis HOS, passed to the glue's ts_put_call.
   CALLS. tx_put's #102 text has no abort arm: every call returns DONE / FAILED / REFUSED and the code does not test
   `failed`, so every call site continues on every outcome; the live state carries the buffer (b, cap), failed f, own
   and the appended prefix ap besides the calls ks and the text add (TxStr102Glue.v ts_live). Every run's memnorm keep
   is YGcallMxmn.v's memnorm_frame_of; every tx_put call's fpre bound raZ < YM05.alloc_ceiling is PRW_StepKit.v's
   pa_slot_lt_ceil_b, at a closed lemma per return slot.
   SEGMENTS. The engine is re-entered at every seam: each segment starts from a FRESH symbolic state built from
   concrete machine-state facts, with S10Env's environment TE regs rg more (atoms 0-31 the ENTRY registers, 32-63 the
   current ones, 64- extras). The seams of one iteration (offsets from tx_string's entry A' 0x852f4, 4 * the listing
   slot):
     340 (0x85448) the loop head: the unpoison of esc[] (the frame's shadow byte 4 := 06), esc[0..3], the class of
                   the byte and hex[c >> 4]'s address. Its shadow store writes inside the shadow band, so this run
                   carries NO inline check and runs under the dummy span (2 ^ 63, 2 ^ 63);
     428 (0x854a0) the hi nibble's inline check (slow block 0x85558, report site 0x8564c);
     444 (0x854b0) the hi digit's load from tx_string.hex;
     448 (0x854b4) esc[4] and the lo nibble's address (aliased to the segment's extra atom);
     460 (0x854c0) the lo nibble's inline check (slow block 0x85564, report site 0x85650);
     476 (0x854d0) the lo digit's load;
     480 (0x854d4) esc[5], the byte's class tests and its first tx_put call (0x854f0 or 0x85500);
     512 (0x854f4) the byte's call after the backslash's (c = 34 or c = 92 only);
     528 (0x85504) the re-poison of esc[] (the frame's shadow byte 4 := f8);
     536 (0x8550c) the inline check of s + i + 1 (slow block 0x85570, report site 0x8557c), the advance, the next
                   byte's load and the loop test (0x85528 `bnez a1` to the loop head; else 0x8552c `j` to the
                   closing quote's block at 652, 0x85580).
   Each hex digit's load sits in a segment of its own: its region's base is the address itself (a0), and the hi and lo
   nibbles coincide whenever c / 16 = c mod 16, so the two regions can never be pairwise disjoint in one state.
   NUMERALS. DERIVED: the seam offsets above, the literal offsets 70464 / 70368 from pa_val (A_OBJ 2) (the listing's
   PAddHi (A_OBJ 2) 0x11340 / 0x112e0: .str.26, tx_string.hex), atom indices, and the `change` forms 16064 / 16148 /
   16164 = TS_PC_A + 428 / 512 / 528 (TS_PC_A = 15636 by vm_compute). WORD: 6 / 8 / 9 / 10 / 13 / 15 / 16 / 32 / 34 /
   48 / 92 / 102 / 110 / 114 / 116 / 117 / 255 (the bytes the body compares, stores or indexes with). LENGTH: 24, 32,
   38, 56, 64, 104, 160, 176, 4096, 2 ^ 31 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47. No ADDRESS literal: code addresses are
   pa_sigma / pa_val of lib/A/PAImg_prog.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Tx102Glue TxStr102Glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
(* the memnorm keep (Required qualified: YGcallMxmn carries its own copies of in_roP / arodata_okP) and the call's
   ceiling bound; PRW_StepKit loads YF0v.v, which sets the zify division flag to false globally: the #[local] reset
   below follows it *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YCbqGwild.
(* the re-hiding relation WR and its step relation (the free / realloc move) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image A': tx_string's entry and the seams of its loop body (DERIVED; see the header) ---- *)
Definition TS_PC_A : Z := 4 * Z.of_nat (A_prog_slot AS_tx_string).   (* = 15636, A' 0x852f4 *)
Definition TS_LH_OFF_A : Z := 340.   (* 0x85448: the loop head *)
Definition TS_H1_OFF_A : Z := 428.   (* 0x854a0: the hi nibble's inline check *)
Definition TS_H2_OFF_A : Z := 444.   (* 0x854b0: the hi digit's load *)
Definition TS_H3_OFF_A : Z := 448.   (* 0x854b4: esc[4] and the lo nibble's address *)
Definition TS_H4_OFF_A : Z := 460.   (* 0x854c0: the lo nibble's inline check *)
Definition TS_H5_OFF_A : Z := 476.   (* 0x854d0: the lo digit's load *)
Definition TS_D_OFF_A : Z := 480.    (* 0x854d4: esc[5] and the class tests *)
Definition TS_E_OFF_A : Z := 512.    (* 0x854f4: the byte's call after the backslash's *)
Definition TS_F1_OFF_A : Z := 528.   (* 0x85504: the re-poison of esc[] *)
Definition TS_F2_OFF_A : Z := 536.   (* 0x8550c: the check of s + i + 1 *)
Definition TS_X_OFF_A : Z := 652.    (* 0x85580: the closing quote's block *)

(* the loop's index arithmetic, stated outside the Sections (where S is the astate binder, not the successor) *)
Lemma ts_len_succ_A : forall (pre post : list Z) cb nb i, length pre = i ->
  (Datatypes.S i < length (pre ++ cb :: nb :: post))%nat.
Proof. intros pre post cb nb i H. rewrite length_app. cbn [length]. lia. Qed.
Lemma ts_measure_A : forall n i, (Datatypes.S i < n)%nat -> (n - Datatypes.S i < n - i)%nat.
Proof. intros n i H. lia. Qed.
Lemma ts_len_snoc_A : forall (pre : list Z) cb i, length pre = i -> length (pre ++ [cb]) = Datatypes.S i.
Proof. intros pre cb i H. rewrite length_app. cbn [length]. lia. Qed.
Lemma ts_zsucc_A : forall s i, s + Z.of_nat i + 1 = s + Z.of_nat (Datatypes.S i).
Proof. intros s i. lia. Qed.

(* the escape letter tx_string puts in esc[1] (fuzz_preset.c :416) *)
Definition ts_letter_A (c : Z) : Z := if c =? 9 then 116 else if c =? 10 then 110 else if c =? 13 then 114 else 117.
Lemma ts_letter_tnr_A : forall c, c = 9 \/ c = 10 \/ c = 13 ->
  110 <= ts_letter_A c <= 116 /\ WriterSpec.esc c = [92; ts_letter_A c].
Proof. intros c [-> | [-> | ->]]; split; try reflexivity; cbn; lia. Qed.
Lemma ts_letter_u_A : forall c, 0 <= c < 32 -> c <> 9 -> c <> 10 -> c <> 13 ->
  ts_letter_A c = 117 /\
  WriterSpec.esc c = [92; ts_letter_A c; 48; 48; WriterSpec.hexd (c / 16); WriterSpec.hexd (c mod 16)].
Proof.
intros c Hc H9 H10 H13. unfold ts_letter_A.
rewrite (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 10)), (proj2 (Z.eqb_neq c 13)) by lia.
split; [reflexivity | exact (s10s_esc_u c Hc H9 H10 H13)].
Qed.
Lemma ts_letter_q_A : forall c, c = 34 \/ c = 92 \/ 32 <= c -> ts_letter_A c = 117.
Proof.
intros c Hc. unfold ts_letter_A.
rewrite (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 10)), (proj2 (Z.eqb_neq c 13)) by lia. reflexivity.
Qed.
Lemma ts_letter_rng_A : forall c, 0 <= ts_letter_A c < 256.
Proof. intros c. unfold ts_letter_A. repeat destruct (_ =? _); lia. Qed.
Lemma ts_garr8_pre_A : forall segs m a (l1 l2 : list Z), garr8 segs m a (l1 ++ l2) -> garr8 segs m a l1.
Proof.
intros segs m a l1 l2 H j Hj. pose proof (H j ltac:(rewrite length_app; lia)) as Hj'.
rewrite app_nth1 in Hj' by exact Hj. exact Hj'.
Qed.
Lemma ts_hexd_range_A : forall j, 0 <= j < 16 -> 48 <= WriterSpec.hexd j <= 102.
Proof. intros j Hj. unfold WriterSpec.hexd. destruct (Z.ltb_spec j 10); lia. Qed.
Ltac tskeep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.

(* ---- the lo nibble's address, as the body computes it (`andi 15`, `add s9`) ---- *)
Lemma ts_nib_lo_A : forall (E : env) (na nh : nat) (c hx : Z),
  bv_unsigned (ew E na) = c -> bv_unsigned (ew E nh) = hx -> 0 <= c < 256 -> 0 <= hx -> hx + 16 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff nh 0) (SAlu ALU_AND (SOff na 0) (SLit 15)))
  = sv_denot E (SLit (hx + c mod 16)).
Proof.
intros E na nh c hx Ha Hh Hc Hh0 Hh1.
assert (H15 : Z.land c 15 = c mod 16)
  by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
pose proof (Z.mod_pos_bound c 16 ltac:(lia)).
apply U_inj. rewrite U_SLit, (YP0m.zcanon_small (hx + c mod 16)) by lia.
rewrite !U_SAlu, !U_SOff, !U_SLit, Ha, Hh, !Z.add_0_r. cbn [zalu_raw].
rewrite (YP0m.zcanon_small 15) by lia. rewrite (YP0m.zcanon_small c) by lia.
rewrite H15. rewrite (YP0m.zcanon_small (c mod 16)) by lia. rewrite (YP0m.zcanon_small hx) by lia.
apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_lit_w64_A : forall (E : env) (z : Z), sv_denot E (SLit z) = w64 z.
Proof. intros E z. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {SK : YI16.sink_head} {RL : PrhRoomLive}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Notation STKS := (@STK_tx_string prh_img_A).
(* S10Env's segment environment, pinned to the A' listing *)
#[local] Notation TEa := (TE (L := A_prog_listing) (PA := PA)).

Definition TS_STR26_A : Z := VAL (A_OBJ 2) + 70464.   (* .str.26, the backslash (A' 0x21340) *)
Definition TS_HEX_A : Z := VAL (A_OBJ 2) + 70368.     (* tx_string.hex, the 16 digits (A' 0x212e0) *)
Definition TS_SPAN_A : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* the glue's image facts at A' *)
Lemma pa_hi_ok_A : @pa_hi _ A_prog_listing PA <= 2 ^ 31.
Proof. vm_compute. discriminate. Qed.
Lemma HSTK_A : 4096 + 176 <= STKS.
Proof. vm_compute. discriminate. Qed.
Lemma HSTKP_A : 0 <= @STK_tx_put prh_img_A /\ @STK_tx_put prh_img_A + 176 <= STKS.
Proof. split; vm_compute; discriminate. Qed.
Lemma pst_img_A : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_A. Qed.
Lemma pst_ro_A : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_A. Qed.
Lemma TS_HEX_range_A : 4096 <= TS_HEX_A /\ TS_HEX_A + 16 <= 2 ^ 31.
Proof. unfold TS_HEX_A. vm_compute. split; discriminate. Qed.
Lemma TS_HEX_hi_A : TS_HEX_A + 16 <= 2 ^ 47 - 8.
Proof. unfold TS_HEX_A. vm_compute. discriminate. Qed.
(* the whole-program instance's image bounds lie in the ASan low memory (Tx102Glue.v s10_src_img's img_box) *)
Lemma img_box_A : 4096 <= @pa_lo _ A_prog_listing PA /\ @pa_hi _ A_prog_listing PA <= kLowMemEnd.
Proof. vm_compute. split; discriminate. Qed.
(* the 16 digits of tx_string.hex, as the image holds them ("0123456789abcdef") *)
Lemma ts_hex_rom_A : forall j, 0 <= j < 16 ->
  option_map (fun bb : byte => bv_unsigned bb) (seg_rom SEGS (Z_to_bv 64 (TS_HEX_A + j))) = Some (WriterSpec.hexd j).
Proof.
intros j Hj.
assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/
             j = 10 \/ j = 11 \/ j = 12 \/ j = 13 \/ j = 14 \/ j = 15) by lia.
unfold TS_HEX_A.
repeat (destruct Hc as [-> | Hc]; [vm_compute; reflexivity|]). subst j. vm_compute. reflexivity.
Qed.
(* fpre's raZ bound at the body's two tx_put return slots (F1: 16164 = TS_PC_A + 528, A' 0x85504, the byte's and
   esc[]'s calls; E: 16148 = TS_PC_A + 512, A' 0x854f4, the backslash's call), each a CLOSED lemma (PRW_StepKit.v
   pa_slot_lt_ceil_b; vm_compute only on the closed slot test, never inside a walk) *)
Lemma ts_ret_ceil_F1_A : bv_unsigned (Z_to_bv 64 (BASE + 16164)) < YM05.alloc_ceiling.
Proof.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA) 16164 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. exact H.
Qed.
Lemma ts_ret_ceil_E_A : bv_unsigned (Z_to_bv 64 (BASE + 16148)) < YM05.alloc_ceiling.
Proof.
pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL) (PI := PA) 16148 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
pose proof (@pa_B_ok _ _ PA) as HB. rewrite unsigned_lit_small by lia. exact H.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* THE ONE RELATION of the loop body: the journal from the entry at WR, every segment at SRW *)
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation SRW := (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRrefl := (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRtrans := (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf).
(* the allocator laws at the cf instance's head (16 fields); discharged at the instance by ATxString.v's tsi_laws
   (YGcallcf.AR_laws_x_xs, the laws at ARcf /\ xs_placed_cf, which is the instance's iface_ARx) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* MARKED STAND-IN: fake frames are 64-aligned. Needed because esc[] (F + 32, up to 6 bytes) is handed to tx_put, whose
   src_rd asks for the shadow hull of [F + 32, F + 38); the frame's own 8 shadow bytes cover that hull only when
   shadow_addr F is 8-aligned, i.e. F mod 64 = 0 (the base gives only F mod 32 = 0). Discharged at the instance by
   ATxString.v's tsi_fal64: Rtt102CKA.ck_frame_al64 (a fake frame of a class >= 0 is 64-aligned: the layout's
   fake-frame base is page-aligned by AR_laws_x's layout law), at the class bound of AR_laws_x's alx_frames_cid *)
Hypothesis FAL64 : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0.
(* ---- the glue's Section hypotheses (Tx102Glue.v / TxStr102Glue.v, MARKED there) ---- *)
(* MARKED STAND-IN: the zero-shadow ranges are granule-aligned; A' witness ATxStrWitA.v tsw_zs_aligned_TfibA *)
Hypothesis zs_aligned : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* MARKED STAND-IN: PER-INSTANCE over the CfImg bounds cf_img_lo / cf_img_top (A': CfImg_A, 0x10000 / 0x600000), the
   shadow byte of every address inside them is visible at every allocator state; discharged at the instance by
   ATxString.v's tsi_isv (AImgShadowVisCf.img_shadow_vis_xs_A) *)
Hypothesis img_shadow_vis_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md ->
  @cf_img_lo ci <= a < @cf_img_top ci ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* the instance's bounds for Tx102Glue's s10_src_img (TxStr102Glue.v ts_src_lit): pa_lo / pa_hi of PI_prog_A inside the
   CfImg bounds (at CfImg_A: 0x10000 / 0x600000 both); A' witness ATxStrWitA.v tsw_img_cf_box_A *)
Hypothesis img_cf_box : @cf_img_lo ci <= @pa_lo _ A_prog_listing PA /\ @pa_hi _ A_prog_listing PA <= @cf_img_top ci.
(* ---- the callee's text (lib/A/PRH_FnTx.v ttx_put_specX, the budgeted tx_put) at the caller's universe closure CTX0;
   at the instance it is ATxString.v tx_string_A_inst's one premise TXPUT_I ---- *)
Variables (CTX0 : list (list Z)).
Hypothesis TXPUT : ttx_put_specX (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
(* no source-ceiling stand-in: the text's src_rd states `p + len <= alloc_ceiling` (no `+ 8`), and TxStr102Glue.v
   ts_src_byte takes that bound from the string's prhtx_bvis granule bound *)
(* MARKED STAND-IN: the program's statics (prh_pst: alloc.c's six and fuzz_preset.c's g_own_ran_out) are not the
   runtime's own statics and not errno, so a runtime call's image clause
   (acall_kept) keeps them; A' witness ATxStrWitA.v tsw_pal_pst_static_TfibA *)
Hypothesis pal_pst_static : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* ---- the backslash literal and tx_string.hex (MARKED STAND-IN: .str.26 at A' 0x21340 is one read-only byte with a
   const-shadow granule; the 16 digits at A' 0x212e0 lie in a zero-shadow range of .rodata); A' witnesses
   ATxStrWitA.v tsw_lit_img_TfibA (its second conjunct) and tsw_hex_img_TfibA ---- *)
Hypothesis ts_lit_img_A : kept_img (PA := PA) B TS_STR26_A 1.
Hypothesis ts_hex_img_A : kept_at (PA := PA) B [] TS_HEX_A 16.

Section g.
(* ---- the entry: ttx_string_specX's binders and premises ---- *)
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (dw t s k b0 len0 cap0 f0 own0 : Z) (bs txt : list Z) (Lam : list (Z * Z))
  (peak cnt fail ran most : Z).
(* the model-run position the text takes at the entry (PRH_FnTx.v's rp_* binders; the glue's Section g Contexts) *)
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat)) (rp_i : nat)
  (rp_H0 : list Z).
(* the run has at most 4 calls: the text's premise `length rp_os <= 4`, which ts_put_call takes *)
Hypothesis HOS : (length rp_os <= 4)%nat.
#[local] Notation sp0 := (spZ regs).
(* the glue's definitions at this entry *)
#[local] Notation TSks := (@TS_ks bs).
#[local] Notation TSadd := (@TS_add bs).
#[local] Notation FP0a := (@FP0 t b0 cap0).
#[local] Notation sp1 := (@TS_sp1 regs).
#[local] Notation QFa := (@QF fx rc prh_img_A RL SK A_prog_listing PA B ARx ly S Hp W regs mem md dw t s k b0 len0 cap0
  f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
#[local] Notation sidea := (@ts_side rc ci prh_img_A RL A_prog_listing PA B ly S Hp W regs mem dw t s k b0 len0 cap0
  f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0).
(* the live state at WR: the glue's ts_liveR, the copy of ts_live over a relation; LHa's live state (ts_LH, at
   RCF = WR in the glue) is this one *)
#[local] Notation livea := (@ts_liveR rc ci prh_img_A RL SK A_prog_listing PA B ARx ly S Hp W regs mem md dw t s k b0
  len0 cap0 f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i rp_H0 WR).
#[local] Notation bregsa := (@ts_bregs regs t).
#[local] Notation lregsa := (@ts_lregs TS_STR26_A TS_HEX_A regs t s).
#[local] Notation spilla := (ts_spill (L := A_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation LHa := (@ts_LH fx rc ci prh_img_A RL SK A_prog_listing PA TS_PC_A TS_LH_OFF_A TS_STR26_A TS_HEX_A
  B ARx ly S Hp W regs mem md dw t s k b0 len0 cap0 f0 own0 bs txt Lam peak cnt fail ran most rp_sm rp_x rp_os rp_i
  rp_H0).

Hypothesis HPRE : afn_pre_x SEGS B ARx STKS ly S Hp W regs mem md ch.
Hypothesis HCL : prh_univ_closure (PI := prh_img_A) B CTX0.
Hypothesis HFWIN : fwin (PA := PA) ly W regs mem dw.
Hypothesis HPLACE : prhtx_place (PA := PA) ly S W regs mem dw t.
Hypothesis HLEN : len0 + Z.of_nat (length TSadd) + 1 <= 2 ^ 28.
Hypothesis HLIVE : blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX.
Hypothesis HMAX : 2 * (len0 + Z.of_nat (length TSadd) + 1) < cf_malloc_max.

(* the premises every tx_put call site of this body carries are given inline there:
   (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX (conj HEVS (conj HROOMW
   (conj HCONS HFRM)))))))))) : ts_pre ch; the text's guarded room and consumer window *)
Hypothesis HEVS : f0 = 0 -> prh_run_at rp_sm rp_x rp_os rp_i (prhtx_evs len0 cap0 TSks).
Hypothesis HROOMW : f0 = 0 ->
  YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 TSks)) (st_depot S).
Hypothesis HCONS : f0 = 0 -> prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 TSks)).
Hypothesis HFRM : frm_zero (@YK11.fp_csr fx).

(* ---- the fake frame's numeric facts, from the allocator laws at any live state ---- *)
Lemma ts_frame_A : forall {lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap},
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap ->
  ARx lyc Sc Hpc Wc memc mdc /\ In (0, pos) (frames Sc) /\
  4096 <= F /\ F + 64 <= YM05.alloc_ceiling /\ in_app F 64 /\ F mod 64 = 0 /\ F mod 32 = 0 /\
  (forall a, F <= a < F + 64 -> apresent (w_H Wc) memc a) /\
  (forall a, shadow_addr F <= a < shadow_addr F + 8 -> apresent (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap (HJ & _ & EF & _).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_frs HJ) as HFRc.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite HFRc; left; reflexivity).
destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as (F32 & _ & Ffr & Fsh).
change (fs_frame_bytes 0) with 64 in Fb2, Fb3, Ffr, Fsh.
pose proof (FAL64 lyc Sc Hpc Wc memc mdc 0 pos HARc Hin) as F64.
rewrite <- EF in Fb1, Fb2, Fb3, F32, Ffr, Fsh, F64.
split; [exact HARc|]. split; [exact Hin|]. split; [exact Fb1|]. split; [exact Fb2|]. split; [exact Fb3|].
split; [exact F64|]. split; [exact F32|].
split; [intros a Ha; exact (proj1 (Ffr a Ha))|].
intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
exact (proj1 (Fsh (a - shadow_addr F) ltac:(change (64 / 8) with 8; lia))).
Qed.

(* ---- tx_string.hex: the 16 digits are addressable (their shadow is zero) and hold the digits ---- *)
Lemma ts_hex_addr_A : forall lyc Sc Hpc Wc memc mdc,
  ARx lyc Sc Hpc Wc memc mdc ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF TS_HEX_A 16 /\
  (forall a, TS_HEX_A <= a < TS_HEX_A + 16 -> in_roP SEGS RLO RHI a /\
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros lyc Sc Hpc Wc memc mdc HAR.
destruct ts_hex_img_A as [(bb & m & Hin & _) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]].
- destruct Hin.
- split.
  + destruct Hzs as (q & m' & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) zs_aligned (q, m') Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
    pose proof (alx_zshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc (q, m') HAR ltac:(right; exact Hin)) as Hz.
    cbn [fst snd] in Hz.
    apply (range_addressable_sub _ SHADOW_OFF q m'); [|lia|lia].
    exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m' Hq8 Hm8 Hz).
  + intros a Ha. destruct (Hro a Ha) as (H1 & H2 & H3). split; [exact H1 | split; [exact H2 | exact H3]].
- split.
  + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hcell & Hv)]).
    * destruct Hzs as (q & m' & Hin & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) zs_aligned (q, m') Hin) as (Hq8 & Hm8). cbn [fst snd] in Hq8, Hm8.
      pose proof (alx_zshadow _ _ _ LAWS lyc Sc Hpc Wc memc mdc (q, m') HAR ltac:(right; exact Hin)) as Hz.
      cbn [fst snd] in Hz. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
      exact (zero_shadow_range (aview SEGS (w_H Wc) memc) SHADOW_OFF q m' Hq8 Hm8 Hz x ltac:(lia)).
    * pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS lyc Sc Hpc Wc memc mdc HAR) _ (Hcell lyc))
        as Hc.
      unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
      specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
      exists v. split; [|unfold saddr_ok; lia].
      unfold shadow_of_addr. unfold shadow_addr in Hc. rewrite Hc. f_equal.
      unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
      rewrite Z.shiftr_0_r, (Z.mod_small v (2 ^ 8)) by lia. apply Z.mod_small. lia.
  + intros a Ha. destruct (Hro a Ha) as (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact H3]].
Qed.
Lemma ts_hex_byte_A : forall lyc Sc Hpc Wc memc mdc j,
  ARx lyc Sc Hpc Wc memc mdc -> arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memc) -> 0 <= j < 16 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (TS_HEX_A + j) 1 (WriterSpec.hexd j) /\ 0 <= WriterSpec.hexd j < 256.
Proof.
intros lyc Sc Hpc Wc memc mdc j HAR HROc Hj.
destruct (ts_hex_addr_A lyc Sc Hpc Wc memc mdc HAR) as (_ & Hro).
destruct (Hro (TS_HEX_A + j) ltac:(lia)) as (H1 & H2 & H3).
pose proof (HROc (TS_HEX_A + j) H1 H2 H3) as E. rewrite (ts_hex_rom_A j Hj) in E.
exact (s10_val1_of_aview (w_H Wc) memc _ _ E).
Qed.

(* ======================================================================================================== *)
(* ---- the closing block's continuation (ATxString.v's ts_at_X_A at the A' seam 652) and the loop's induction
   hypothesis ---- *)
Definition ts_HX_A : Prop := forall lyc Sc Hpc Wc memc mdc kj pos F b cap f own ap rg,
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces bs)) (concat (ts_pieces bs)) ap ->
  spilla Wc memc F -> bregsa rg -> getr rg 26 = w64 (shadow_addr F) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_X_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Definition ts_IH_A (i : nat) : Prop :=
  forall i' W' cf', (length bs - i' < length bs - i)%nat -> LHa i' W' cf' -> SRW W' cf' QFa.

(* ---- the segment shapes of one iteration ---- *)
(* the loop head: esc[0..3] (the run's write window) and the frame's shadow byte 4. The literal byte a run's final
   region holds at an offset, as the walk reads it back *)
Definition ts_lit_at_A (cs : list YP09.chunk) (o : Z) : Z :=
  match find (fun c => YP09.c_off c =? o) cs with
  | Some c => match YP09.c_val c with CVal _ (SLit v) => v | _ => 0 end
  | None => 0
  end.
Definition ss_D1_A (G : facts) : sstate := mkSS (TS_PC_A + TS_LH_OFF_A) cur_atoms
  [ YP09.mkRegion (Some (xr 22)) 0 6 0 4 []; YP09.mkRegion (Some (xr 26)) 4 5 4 5 [] ] None G.
(* esc[] alone (the stores of esc[4] and esc[5]); the write window is the one byte the segment stores, so the bytes
   stored before it are kept across the run *)
Definition ss_ESC_A (pc : Z) (sr : list sv) (wlo whi : Z) (G : facts) : sstate := mkSS pc sr
  [ YP09.mkRegion (Some (xr 22)) 0 6 wlo whi [] ] None G.
(* an inline check with no region of its own (the two nibbles' checks) *)
Definition ss_CK_A (pc : Z) (G : facts) : sstate := mkSS pc cur_atoms [] None G.
(* one read-only byte at a0 (a digit of tx_string.hex) *)
Definition ss_HXL_A (pc : Z) (G : facts) : sstate := mkSS pc cur_atoms
  [ YP09.mkRegion (Some (xr 10)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 64 0))] ] None G.
(* the re-poison of esc[] (the frame's shadow byte 4); on A' the segment is `li a0, -8; sb a0, 4(s10)` alone *)
Definition ss_F1_A (G : facts) : sstate := mkSS (TS_PC_A + TS_F1_OFF_A) cur_atoms
  [ YP09.mkRegion (Some (xr 26)) 4 5 4 5 [] ] None G.
(* the next byte's check and load; s5 = s3 + 1 is pinned *)
Definition ss_F2_A : sstate := mkSS (TS_PC_A + TS_F2_OFF_A) (sr_set cur_atoms 21%bv (SOff (xr 19) 1))
  [ YP09.mkRegion (Some (xr 19)) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 64 0))] ] None
  (mkFacts [(xr 19, mkAF 4096 (2 ^ 47 - 8) 0); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0); (64%nat, mkAF 0 255 0)] [] []).

Lemma ts_D1_entry_A : forall (G : facts) (Wc : world SEGS) memc rg F,
  getr rg 22 = w64 (F + 32) -> getr rg 26 = w64 (shadow_addr F) ->
  4096 <= F -> F + 64 <= YM05.alloc_ceiling -> in_app F 64 ->
  (forall a, F <= a < F + 64 -> apresent (w_H Wc) memc a) ->
  (forall a, shadow_addr F <= a < shadow_addr F + 8 -> apresent (w_H Wc) memc a) ->
  facts_ok (TEa regs rg []) G ->
  st_ok_pi SEGS VAL (TEa regs rg []) (ss_D1_A G)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_LH_OFF_A))) memc (seg_rom SEGS))) /\
  (forall Bx, sh_ok SEGS Bx [] (TEa regs rg []) (mrestrict (w_H Wc) memc)).
Proof.
intros G Wc memc rg F R22 R26 HF0 HFc Happ Hpf Hpsh HG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
set (E := TEa regs rg []).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (X22 : bv_unsigned (ew E (xr 22)) = F + 32).
{ unfold E, xr. rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. rewrite R22. apply unsigned_lit_small. lia. }
assert (X26 : bv_unsigned (ew E (xr 26)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
split; [|intros Bx; unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (ts_rok E _ (xr 22) (F + 32)); [exact X22 | lia | lia | | constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpf. lia.
  + apply (ts_rok E _ (xr 26) (shadow_addr F)); [exact X26 | unfold SHADOW_OFF in *; lia
    | unfold SHADOW_OFF in *; lia | | constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpsh. lia.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !ts_bv_some. rewrite X22, X26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. repeat split; lia.
- exact HG.
Qed.

Lemma ts_ESC_entry_A : forall (pc : Z) (sr : list sv) (more : list word) (wlo whi : Z) (G : facts)
    (Wc : world SEGS) memc rg F,
  regs_ok (TEa regs rg more) sr rg -> getr rg 22 = w64 (F + 32) ->
  4096 <= F -> F + 64 <= YM05.alloc_ceiling -> 0 <= wlo -> whi <= 6 ->
  (forall a, F <= a < F + 64 -> apresent (w_H Wc) memc a) ->
  regions_wf (ss_mem (ss_ESC_A pc sr wlo whi G)) = true ->
  facts_ok (TEa regs rg more) G ->
  st_ok_pi SEGS VAL (TEa regs rg more) (ss_ESC_A pc sr wlo whi G)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  (forall Bx, sh_ok SEGS Bx [] (TEa regs rg more) (mrestrict (w_H Wc) memc)).
Proof.
intros pc sr more wlo whi G Wc memc rg F HRG R22 HF0 HFc Hw0 Hw6 Hpf HWF HG.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
set (E := TEa regs rg more).
assert (X22 : bv_unsigned (ew E (xr 22)) = F + 32).
{ unfold E, xr. rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. rewrite R22. apply unsigned_lit_small. lia. }
split; [|intros Bx; unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg more) with E.
- exact HRG.
- exact HWF.
- repeat apply Forall_cons; try apply Forall_nil.
  apply (ts_rok E _ (xr 22) (F + 32)); [exact X22 | lia | lia | | constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpf. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.

Lemma ts_CK_entry_A : forall (pc : Z) (G : facts) (Wc : world SEGS) memc rg,
  facts_ok (TEa regs rg []) G ->
  st_ok_pi SEGS VAL (TEa regs rg []) (ss_CK_A pc G)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  (forall Bx, sh_ok SEGS Bx [] (TEa regs rg []) (mrestrict (w_H Wc) memc)).
Proof.
intros pc G Wc memc rg HG.
split; [|intros Bx; unfold sh_ok; apply Forall_nil].
apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | exact HG].
Qed.

Lemma ts_HXL_entry_A : forall (pc : Z) (G : facts) (Wc : world SEGS) memc rg a v,
  getr rg 10 = w64 a -> 4096 <= a -> a + 1 <= 2 ^ 47 -> 0 <= v < 256 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a 1 v ->
  facts_ok (TEa regs rg [w64 v]) G ->
  st_ok_pi SEGS VAL (TEa regs rg [w64 v]) (ss_HXL_A pc G)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  (forall Bx, sh_ok SEGS Bx [] (TEa regs rg [w64 v]) (mrestrict (w_H Wc) memc)).
Proof.
intros pc G Wc memc rg a v R10 Ha0 Ha1 Hv V HG.
pose proof alloc_ceiling_lt as Hc47.
set (E := TEa regs rg [w64 v]).
assert (X10 : bv_unsigned (ew E (xr 10)) = a).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (E64 : ew E 64 = w64 v) by exact (te_more_lt regs rg [w64 v] 0 ltac:(lia)).
split; [|intros Bx; unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg [w64 v]) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 10) a); [exact X10 | lia | lia | intros o Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ 0 1 (SOff 64 0) v);
    [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact V.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.

Lemma ts_F1_entry_A : forall (G : facts) (Wc : world SEGS) memc rg F,
  getr rg 26 = w64 (shadow_addr F) -> 0 <= F < 2 ^ 47 ->
  apresent (w_H Wc) memc (shadow_addr F + 4) ->
  facts_ok (TEa regs rg []) G ->
  st_ok_pi SEGS VAL (TEa regs rg []) (ss_F1_A G)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_F1_OFF_A))) memc (seg_rom SEGS))) /\
  (forall Bx, sh_ok SEGS Bx [] (TEa regs rg []) (mrestrict (w_H Wc) memc)).
Proof.
intros G Wc memc rg F R26 HF HP HG.
set (E := TEa regs rg []).
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (X26 : bv_unsigned (ew E (xr 26)) = shadow_addr F).
{ unfold E, xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
split; [|intros Bx; unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 26) (shadow_addr F)); [exact X26 | unfold SHADOW_OFF in *; lia
    | unfold SHADOW_OFF in *; lia | | constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (shadow_addr F + o) with (shadow_addr F + 4) by lia. exact HP.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.

Lemma ts_F2_entry_A : forall (Wc : world SEGS) memc rg p nb,
  getr rg 19 = w64 p -> getr rg 21 = w64 (p + 1) -> getr rg 24 = w64 SHADOW_OFF ->
  4096 <= p <= 2 ^ 47 - 8 -> 0 <= nb < 256 -> val_mem SEGS (mrestrict (w_H Wc) memc) (p + 1) 1 nb ->
  st_ok_pi SEGS VAL (TEa regs rg [w64 nb]) ss_F2_A
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_F2_OFF_A))) memc (seg_rom SEGS))) /\
  sh_ok SEGS (SOff (xr 24) 0) [] (TEa regs rg [w64 nb]) (mrestrict (w_H Wc) memc).
Proof.
intros Wc memc rg p nb R19 R21 R24 Hpb Hnb V.
set (E := TEa regs rg [w64 nb]).
assert (X19 : bv_unsigned (ew E (xr 19)) = p).
{ unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19. apply unsigned_lit_small. lia. }
assert (X24 : bv_unsigned (ew E (xr 24)) = SHADOW_OFF).
{ unfold E, xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E64 : ew E 64 = w64 nb) by exact (te_more_lt regs rg [w64 nb] 0 ltac:(lia)).
assert (X64 : bv_unsigned (ew E 64) = nb) by (rewrite E64; apply unsigned_lit_small; lia).
split; [|unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg [w64 nb]) with E.
- apply YI04.regs_ok_pin; [apply te_regs_ok | intros X; discriminate X |].
  cbn [sv_denot]. unfold E, xr. rewrite (te_cur regs rg _ 19%bv 19) by reflexivity. rewrite R19, R21.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 19) p); [exact X19 | lia | lia | intros o Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ 1 1 (SOff 64 0) nb);
    [cbn [sv_denot]; rewrite E64, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | cbn; lia |].
  exact V.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X19, X24, X64.
  change (2 ^ 0) with 1. repeat split; lia.
Qed.

(* ---- after the byte's last call: the re-poison of esc[] (A' 0x85504 .. 0x8550c, no UBSan test), the check of
   s + i + 1 and the next byte (A' 0x8550c .. 0x8552c), then the loop test at 0x85528: `bnez a1` to the loop head
   (by the induction) when the next byte is not 0, else `j` at 0x8552c to the closing block ---- *)
Lemma ts_F_A : forall i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i ->
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces (pre ++ [cb])))
    (concat (ts_pieces (pre ++ [cb]))) ap ->
  spilla Wc memc F -> lregsa rg F (Z.of_nat i) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_F1_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post HX IH Ebs Hlen HL HSP HLR.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)).
pose proof HSD as (HWIN & HTX & HPOSs & HMNs & HRO & ((Hl & Hlens & H32 & Hfa & Hga) & HBV) & _).
pose proof HBV as (Hs4096 & Hs8 & Hk0 & Hsk & Hamr & Hras & Hhull & Hpres_s).
pose proof HLR as ((R2 & R3 & R4 & R8 & R9 & R20 & R24) & R18 & R19 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HSTK_A as HSTK.
destruct (ts_frame_A HL) as (HARc & Hin & Fb1 & Fb2 & Fb3 & F64 & F32 & Fpr & Fsh).
assert (Hi : (i < length bs)%nat) by (rewrite Ebs, length_app; cbn; lia).
destruct (ts_sp1_range Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
destruct (ts_F1_entry_A (mkFacts [(xr 26, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 3)] [] []) Wc memc rg F R26
  ltac:(lia) ltac:(apply Fsh; unfold shadow_addr, SHADOW_OFF in *; lia)) as [HS SHOK0].
{ split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (X26 : bv_unsigned (ew (TEa regs rg []) (xr 26)) = shadow_addr F).
  { unfold xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
    unfold shadow_addr, SHADOW_OFF in *. lia. }
  rewrite X26. change (2 ^ 3) with 8.
  assert (HF8 : shadow_addr F mod 8 = 0).
  { pose proof F64 as HD. apply Z.mod_divide in HD; [|lia]. destruct HD as [q Hq].
    unfold shadow_addr, SHADOW_OFF. replace F with (q * 8 * 8) by lia. rewrite Z.div_mul by lia.
    rewrite Zplus_mod, Z.mod_mul by lia. reflexivity. }
  repeat split; try lia; try (unfold shadow_addr, SHADOW_OFF in *; lia); try exact HF8; try apply Z.mod_1_r. }
pose proof (SHOK0 (SLit 0)) as SHOK.
assert (HEI : img_env VAL A_LIM (TEa regs rg [])) by apply te_env.
assert (X26 : bv_unsigned (ew (TEa regs rg []) (xr 26)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF in *. lia. }
pose (RUN := @paj_run_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
pose (RUNTO := @paj_run_to_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
pose (BR := YSRrG.paj_branchR (PI := PA) WR).
(* ---- F1: the re-poison `li a0, -8; sb a0, 4(s10)` ---- *)
pose proof HS as HSk1.
paj_run_to_tok_xR RUNTO HS HJ SHOK (2 ^ 63, 2 ^ 63) (TS_PC_A + TS_F2_OFF_A).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 26) (shadow_addr F)); [reflexivity | exact X26 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. rewrite <- EF. lia. }
  apply awr_ok_nil. }
(* the run's memnorm keep: YGcallMxmn.memnorm_frame_of from the run's start st_ok and its full-memory frame *)
assert (KN1 : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk1 HF); exact Hm).
clear HSk1.
pmkst HS.
set (WSH := ss_mem (ss_F1_A (mkFacts [(xr 26, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 3)] [] []))) in *.
assert (Hwr : forall a, in_wrange (TEa regs rg []) WSH a -> a = shadow_addr F + 4).
{ intros a (r & Hr & Ha). cbv [WSH ss_F1_A ss_mem In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X26 in Ha. lia. }
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Kf : forall a, 0 <= a < 2 ^ 64 -> a <> shadow_addr F + 4 ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. apply (ts_keep Wc _ WSH memc (ms_mem ms) (fun x => x = shadow_addr F + 4) HFr Hwr a Ha Hn). }
pose proof (ts_live_runR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos F b _ _ _ _ _ _ (in_wrange (TEa regs rg []) WSH) HL HJ HFr) as HL1.
specialize (HL1 ltac:(intros a HW; rewrite (Hwr a HW); right; exists pos; split; [exact Hin|]; right;
  unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; rewrite <- EF; lia)).
specialize (HL1 ltac:(intros a HW; rewrite (Hwr a HW);
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia)).
specialize (HL1 KN1).
assert (HSP1 : spilla Wc (ms_mem ms) F).
{ apply (ts_spill_keep Wc memc); [|exact HSP]. intros a Ha. apply Kf; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [tskeep HS |]). destruct Hr. }
assert (Z19 : getr (ms_regs ms) 19 = getr rg 19) by (apply KR; cbv; tauto).
assert (Z21 : getr (ms_regs ms) 21 = getr rg 21) by (apply KR; cbv; tauto).
assert (Z24 : getr (ms_regs ms) 24 = getr rg 24) by (apply KR; cbv; tauto).
assert (HLR1 : lregsa (ms_regs ms) F (Z.of_nat i)).
{ unfold ts_lregs, ts_bregs.
  rewrite (KR 2%bv), (KR 3%bv), (KR 4%bv), (KR 8%bv), (KR 9%bv), (KR 18%bv), (KR 19%bv), (KR 20%bv), (KR 21%bv),
    (KR 22%bv), (KR 23%bv), (KR 24%bv), (KR 25%bv), (KR 26%bv), (KR 27%bv) by (cbv; tauto).
  exact HLR. }
clear HF HG HFr.
(* ---- F2: the check of s + i + 1, the advance and the next byte ---- *)
set (nb := nth (Datatypes.S i) (bs ++ [0]) 0).
assert (HiS : (Datatypes.S i < length (bs ++ [0%Z]))%nat).
{ rewrite length_app. cbn [length]. rewrite Nat.add_1_r. exact (proj1 (Nat.succ_lt_mono _ _) Hi). }
destruct (Hga (Datatypes.S i) HiS) as (Vnb & Rnb). fold nb in Vnb, Rnb.
assert (Vnb1 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (s + Z.of_nat i + 1) 1 nb).
{ eapply ts_vm_av; [|rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.add_assoc in Vnb; exact Vnb].
  intros j Hj. apply Kf; [lia|].
  unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, shadow_addr, SHADOW_OFF in *. lia. }
destruct (ts_F2_entry_A Wc (ms_mem ms) (ms_regs ms) (s + Z.of_nat i) nb ltac:(rewrite Z19; exact R19)
  ltac:(rewrite Z21; exact R21) ltac:(rewrite Z24; exact R24) ltac:(lia) Rnb Vnb1) as [HS2 SHOK2].
assert (HEI2 : img_env VAL A_LIM (TEa regs (ms_regs ms) [w64 nb])) by apply te_env.
pose proof HS2 as HSk2.
paj_run_tok_xR RUN HS2 HJ SHOK2 TS_SPAN_A.
{ (* the inline check of s + i + 1 (shadow load at A' 0x85514): addressable by prhtx_bvis at the F1 state *)
  cbn [ms_mem mkst restrict]. rewrite !U_SOff.
  assert (A56 : ew (TEa regs (ms_regs ms) [w64 nb]) (xr 24) = getr (ms_regs ms) 24)
    by (unfold xr; apply (te_cur regs (ms_regs ms) _ 24%bv 24); reflexivity).
  assert (A51 : ew (TEa regs (ms_regs ms) [w64 nb]) 51 = getr (ms_regs ms) 19) by te_close.
  rewrite A56, A51, Z24, R24, Z19, R19. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !YP0m.zcanon_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  pose proof HL1 as (_ & (_ & _ & _ & _ & _ & (_ & HBV1) & _) & _). pose proof HBV1 as (_ & _ & _ & _ & _ & Hras1 & _).
  apply (range_addressable_sub _ SHADOW_OFF s k); [exact Hras1 | lia | lia]. }
{ cbv [ss_F2_A ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KN2 : YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk2 HF); exact Hm).
clear HSk2.
assert (Hm2 : forall x, mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) (ms_mem ms) x).
{ intros x. apply HFr. intros (r & Hri & Hr). cbv [ss_F2_A ss_mem In] in Hri. destruct Hri as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hr. lia. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL1 HJ Hm2 KN2) as HL2.
assert (HSP2 : spilla Wc (ms_mem ms0) F).
{ apply (ts_spill_keep Wc (ms_mem ms)); [|exact HSP1]. intros a Ha. apply aview_eq_of. apply Hm2. }
clear HF HG HFr.
assert (A64 : ew (TEa regs (ms_regs ms) [w64 nb]) 64 = w64 nb)
  by exact (te_more_lt regs (ms_regs ms) [w64 nb] 0 ltac:(lia)).
assert (Enb : nth 0 (post ++ [0]) 0 = nb).
{ unfold nb. symmetry. rewrite Ebs, <- app_assoc, <- app_comm_cons. rewrite <- Hlen.
  rewrite app_nth2 by apply Nat.le_succ_diag_r. rewrite Nat.sub_succ_l, Nat.sub_diag by apply le_n. reflexivity. }
pose proof Hfa as Hfa'. rewrite Ebs in Hfa'. apply Forall_app in Hfa' as [_ Hfa'].
inversion Hfa' as [|cx px _ Hfa'']. clear Hfa'.
YSRrG.psrr_branch_tokR RUN BR HS2 SHOK2 TS_SPAN_A.
- (* taken, nb <> 0: the next byte, straight to the loop head *)
  rewrite branch_ne_U, !ts_U0, U_SLit in Hc. rewrite !ew_ewset_other in Hc by lia.
  rewrite A64 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite YP0m.zcanon_small in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  destruct post as [|nb' post'].
  1: { exfalso. cbn in Enb. lia. }
  cbn [app nth] in Enb. subst nb'.
  pose proof HS2 as HSk3.
  paj_run_to_tok_xR RUNTO HS2 HJ SHOK2 TS_SPAN_A (TS_PC_A + TS_LH_OFF_A).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KN3 : YAkMemnorm.memnorm SEGS (ms_mem ms0) -> YAkMemnorm.memnorm SEGS (ms_mem ms1))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk3 HF); exact Hm).
  clear HSk3.
  assert (Hm3 : forall y, mrestrict (w_H Wc) (ms_mem ms1) y = mrestrict (w_H Wc) (ms_mem ms0) y).
  { intros y. apply HFr. intros (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hri. }
  pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
    WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ Hm3 KN3) as HL3.
  assert (HSP3 : spilla Wc (ms_mem ms1) F).
  { apply (ts_spill_keep Wc (ms_mem ms0)); [|exact HSP2]. intros a Ha. apply aview_eq_of. apply Hm3. }
  clear HF HG HFr.
  assert (KR3 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms1) r = getr (ms_regs ms) r).
  { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [tskeep HS2 |]). destruct Hr. }
  prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (11%bv : bv 5) Q11.
  try rewrite !ew_ewset_other in Q19 by lia. try rewrite !ew_ewset_other in Q21 by lia.
  try rewrite !ew_ewset_other in Q11 by lia.
  pmkst HS2.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] =>
    change (BASE + n) with (BASE + (TS_PC_A + TS_LH_OFF_A)) end.
  apply (IH (Datatypes.S i) Wc); [rewrite Ebs; apply ts_measure_A; exact (ts_len_succ_A pre post' cb nb i Hlen)|].
  exists lyc, Sc, Hpc, (ms_mem ms1). eexists. eexists.
  exists pos, F, b, cap, f, own, ap, (ms_regs ms1), (pre ++ [cb]), nb, post'.
  split; [reflexivity|]. split; [rewrite Ebs, <- app_assoc; reflexivity|].
  split; [exact (ts_len_snoc_A pre cb i Hlen)|].
  split; [exact HL3|]. split; [exact HSP3|]. split.
  + unfold ts_lregs, ts_bregs. rewrite <- !(ts_zsucc_A s i).
    rewrite (KR3 2%bv), (KR3 3%bv), (KR3 4%bv), (KR3 8%bv), (KR3 9%bv), (KR3 18%bv), (KR3 20%bv), (KR3 22%bv),
      (KR3 23%bv), (KR3 24%bv), (KR3 25%bv), (KR3 26%bv), (KR3 27%bv) by (cbv; tauto).
    pose proof HLR1 as ((B2 & B3 & B4 & B8 & B9 & B20 & B24) & B18 & B19 & B21 & B22 & B23 & B25 & B26 & B27).
    rewrite Q19, Q21. cbn [sv_denot]. rewrite !(te_cur regs (ms_regs ms) _ 19%bv 19) by reflexivity.
    rewrite B19. unfold w64. rewrite !unsigned_lit_small by lia.
    repeat split; try assumption; try reflexivity; f_equal; lia.
  + rewrite Q11. cbn [sv_denot]. rewrite A64. try rewrite Z.add_0_r. unfold w64.
    rewrite ?unsigned_lit_small by lia. first [reflexivity | apply Z_to_bv_bv_unsigned].
- (* not taken, nb = 0: cb was the last byte; the `j` at 0x8552c to the closing quote *)
  rewrite branch_ne_U, !ts_U0, U_SLit in Hc. rewrite !ew_ewset_other in Hc by lia.
  rewrite A64 in Hc. unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
  rewrite YP0m.zcanon_small in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  destruct post as [|nb' post'].
  2: { exfalso. cbn [app nth] in Enb. inversion Hfa'' as [|? ? Hn _]. lia. }
  pose proof HS2 as HSk3.
  paj_run_to_tok_xR RUNTO HS2 HJ SHOK2 TS_SPAN_A (TS_PC_A + TS_X_OFF_A).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KN3 : YAkMemnorm.memnorm SEGS (ms_mem ms0) -> YAkMemnorm.memnorm SEGS (ms_mem ms1))
    by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk3 HF); exact Hm).
  clear HSk3.
  assert (Hm3 : forall y, mrestrict (w_H Wc) (ms_mem ms1) y = mrestrict (w_H Wc) (ms_mem ms0) y).
  { intros y. apply HFr. intros (r & Hri & Hr). vm_compute in Hri.
    repeat (destruct Hri as [<- | Hri]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hri. }
  pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
    WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL2 HJ Hm3 KN3) as HL3.
  assert (HSP3 : spilla Wc (ms_mem ms1) F).
  { apply (ts_spill_keep Wc (ms_mem ms0)); [|exact HSP2]. intros a Ha. apply aview_eq_of. apply Hm3. }
  clear HF HG HFr.
  assert (KR3 : forall r : bv 5, In r [2; 3; 4; 8; 9; 20; 24; 26]%bv -> getr (ms_regs ms1) r = getr (ms_regs ms) r).
  { intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [tskeep HS2 |]). destruct Hr. }
  pmkst HS2.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?n)] =>
    change (BASE + n) with (BASE + (TS_PC_A + TS_X_OFF_A)) end.
  pose proof HLR1 as ((B2 & B3 & B4 & B8 & B9 & B20 & B24) & _ & _ & _ & _ & _ & _ & B26 & _).
  eapply (HX lyc Sc Hpc Wc (ms_mem ms1) _ _ pos F b cap f own ap (ms_regs ms1)).
  + rewrite Ebs in HL3 |- *. exact HL3.
  + exact HSP3.
  + unfold ts_bregs. rewrite (KR3 2%bv), (KR3 3%bv), (KR3 4%bv), (KR3 8%bv), (KR3 9%bv), (KR3 20%bv), (KR3 24%bv)
      by (cbv; tauto). repeat split; assumption.
  + rewrite (KR3 26%bv) by (cbv; tauto). exact B26.
Qed.

(* ---- the two nibbles (A' 0x854a0 .. 0x854d4): each digit's inline check and load, and the store of esc[4]. The
   two digits' addresses coincide whenever c / 16 = c mod 16, so each load sits in a segment of its own ---- *)
Lemma ts_mid_A : forall i cb cls lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap rg,
  0 < cb < 256 -> 0 <= cls < 256 ->
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap -> spilla Wc memc F -> lregsa rg F (Z.of_nat i) ->
  getr rg 11 = w64 cb -> getr rg 12 = w64 cls -> getr rg 13 = w64 cb ->
  getr rg 10 = w64 (TS_HEX_A + cb / 16) ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (F + 32) [92; cls; 48; 48] ->
  aview SEGS (w_H Wc) memc (shadow_addr F + 4) = Some 6 ->
  (forall memc' mdc' kj' rg',
     livea lyc Sc Hpc Wc memc' mdc' kj' pos F b cap f own ks add ap -> spilla Wc memc' F -> lregsa rg' F (Z.of_nat i) ->
     getr rg' 11 = w64 cb -> getr rg' 12 = w64 cls ->
     getr rg' 10 = w64 (WriterSpec.hexd (cb mod 16)) ->
     garr8 SEGS (mrestrict (w_H Wc) memc') (F + 32) [92; cls; 48; 48; WriterSpec.hexd (cb / 16)] ->
     aview SEGS (w_H Wc) memc' (shadow_addr F + 4) = Some 6 ->
     SRW Wc (mkCfg (mkst rg' (Z_to_bv 64 (BASE + (TS_PC_A + TS_D_OFF_A))) memc' (seg_rom SEGS)) mdc') QFa) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_H1_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros i cb cls lyc Sc Hpc Wc memc mdc kj pos F b cap f own ks add ap rg Hcb Hcls HL HSP HLR R11 R12 R13 R10 HG4 HSH6 HK.
pose proof HL as (HJ & HSD & EF & HM).
pose proof HSD as (HWIN & HTX & HPOSs & HMNs & HROc & HSTRc).
pose proof HLR as ((R2 & R3 & R4 & R8 & R9 & R20 & R24) & R18 & R19 & R21 & R22 & R23 & R25 & R26 & R27).
destruct (ts_frame_A HL) as (HARc & Hin & Fb1 & Fb2 & Fb3 & F64 & F32 & Fpr & Fsh).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HSTK_A as HSTK.
destruct (ts_sp1_range Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
destruct TS_HEX_range_A as (Hhx0 & Hhx1). pose proof TS_HEX_hi_A as Hhx2.
assert (Hq : 0 <= cb / 16 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hrm : 0 <= cb mod 16 < 16) by (apply Z.mod_pos_bound; lia).
pose (RUN := @paj_run_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
pose (RUNTO := @paj_run_to_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
(* ---- the hi nibble's inline check (A' 0x854a0 .. 0x854b0) ---- *)
destruct (ts_CK_entry_A (TS_PC_A + TS_H1_OFF_A)
  (mkFacts [(xr 10, mkAF 4096 (2 ^ 47 - 8) 0); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []) Wc memc rg) as [HSa SHa].
{ split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (X10 : bv_unsigned (ew (TEa regs rg []) (xr 10)) = TS_HEX_A + cb / 16).
  { unfold xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
  assert (X24 : bv_unsigned (ew (TEa regs rg []) (xr 24)) = SHADOW_OFF).
  { unfold xr. rewrite (te_cur regs rg _ 24%bv 24) by reflexivity. rewrite R24. apply unsigned_lit_small.
    unfold SHADOW_OFF; lia. }
  rewrite X10, X24. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r. }
pose proof (SHa (SOff (xr 24) 0)) as SHOKa.
assert (HEIa : img_env VAL A_LIM (TEa regs rg [])) by apply te_env.
destruct (ts_hex_addr_A lyc Sc Hpc Wc memc mdc HARc) as (Hras & _).
pose proof HSa as HSka.
paj_run_to_tok_xR RUNTO HSa HJ SHOKa TS_SPAN_A (TS_PC_A + TS_H2_OFF_A).
{ cbn [ms_mem mkst restrict]. rewrite !U_SOff.
  assert (A56 : ew (TEa regs rg []) (xr 24) = getr rg 24)
    by (unfold xr; apply (te_cur regs rg _ 24%bv 24); reflexivity).
  assert (A42 : ew (TEa regs rg []) 42 = getr rg 10) by te_close.
  rewrite A56, A42, R24, R10. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !YP0m.zcanon_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  apply (range_addressable_sub _ SHADOW_OFF TS_HEX_A 16); [exact Hras | lia | lia]. }
{ cbv [ss_CK_A ss_mem]. apply awr_ok_nil. }
assert (KNa : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSka HF); exact Hm).
clear HSka.
assert (Hma : forall x, mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x).
{ intros x. apply HFr. intros (r & Hri & Hr). cbv [ss_CK_A ss_mem In] in Hri. destruct Hri. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hma KNa) as HLa.
assert (HSPa : spilla Wc (ms_mem ms) F)
  by (apply (ts_spill_keep Wc memc); [intros a Ha; apply aview_eq_of; apply Hma | exact HSP]).
assert (HG4a : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms)) (F + 32) [92; cls; 48; 48])
  by (eapply ts_garr_av; [intros j Hj; apply aview_eq_of; apply Hma | exact HG4]).
assert (HSH6a : aview SEGS (w_H Wc) (ms_mem ms) (shadow_addr F + 4) = Some 6)
  by (rewrite <- HSH6; apply aview_eq_of; apply Hma).
assert (KRa : forall r : bv 5, In r [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr rg r).
{ intros r Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [tskeep HSa |]). destruct Hr0. }
assert (HLRa : lregsa (ms_regs ms) F (Z.of_nat i)).
{ unfold ts_lregs, ts_bregs.
  rewrite (KRa 2%bv), (KRa 3%bv), (KRa 4%bv), (KRa 8%bv), (KRa 9%bv), (KRa 18%bv), (KRa 19%bv), (KRa 20%bv),
    (KRa 21%bv), (KRa 22%bv), (KRa 23%bv), (KRa 24%bv), (KRa 25%bv), (KRa 26%bv), (KRa 27%bv) by (cbv; tauto).
  exact HLR. }
clear HF HG HFr.
pmkst HSa.
(* ---- the hi digit's load (A' 0x854b0 .. 0x854b4) ---- *)
pose proof HLa as (HJa & HSDa & EFa & HMa).
pose proof HSDa as (_ & _ & _ & _ & HROa & _).
pose proof (ajxR_ar HJa) as HARa.
destruct (ts_hex_byte_A lyc Sc Hpc Wc (ms_mem ms) _ (cb / 16) HARa HROa ltac:(lia)) as (Vhi & Rhi).
destruct (ts_HXL_entry_A (TS_PC_A + TS_H2_OFF_A)
  (mkFacts [(xr 10, mkAF 4096 (2 ^ 47 - 8) 0); (64%nat, mkAF 0 255 0)] [] []) Wc (ms_mem ms) (ms_regs ms)
  (TS_HEX_A + cb / 16) (WriterSpec.hexd (cb / 16)) ltac:(rewrite (KRa 10%bv) by (cbv; tauto); exact R10)
  ltac:(lia) ltac:(lia) Rhi Vhi) as [HSb SHb].
{ split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (X10 : bv_unsigned (ew (TEa regs (ms_regs ms) [w64 (WriterSpec.hexd (cb / 16))]) (xr 10))
    = TS_HEX_A + cb / 16).
  { unfold xr. rewrite (te_cur regs (ms_regs ms) _ 10%bv 10) by reflexivity.
    rewrite (KRa 10%bv) by (cbv; tauto). rewrite R10. apply unsigned_lit_small. lia. }
  assert (X64 : bv_unsigned (ew (TEa regs (ms_regs ms) [w64 (WriterSpec.hexd (cb / 16))]) 64)
    = WriterSpec.hexd (cb / 16)).
  { rewrite (te_more_lt regs (ms_regs ms) [w64 (WriterSpec.hexd (cb / 16))] 0) by lia. cbn [nth].
    apply unsigned_lit_small. lia. }
  rewrite X10, X64. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r. }
pose proof (SHb (SLit 0)) as SHOKb.
assert (HEIb : img_env VAL A_LIM (TEa regs (ms_regs ms) [w64 (WriterSpec.hexd (cb / 16))])) by apply te_env.
pose proof HSb as HSkb.
paj_run_to_tok_xR RUNTO HSb HJ SHOKb (2 ^ 63, 2 ^ 63) (TS_PC_A + TS_H3_OFF_A).
{ cbv [ss_HXL_A ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KNb : YAkMemnorm.memnorm SEGS (ms_mem ms) -> YAkMemnorm.memnorm SEGS (ms_mem ms0))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSkb HF); exact Hm).
clear HSkb.
assert (Hmb : forall x, mrestrict (w_H Wc) (ms_mem ms0) x = mrestrict (w_H Wc) (ms_mem ms) x).
{ intros x. apply HFr. intros (r & Hri & Hr). cbv [ss_HXL_A ss_mem In] in Hri. destruct Hri as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hr. lia. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLa HJ Hmb KNb) as HLb.
assert (HSPb : spilla Wc (ms_mem ms0) F)
  by (apply (ts_spill_keep Wc (ms_mem ms)); [intros a Ha; apply aview_eq_of; apply Hmb | exact HSPa]).
assert (HG4b : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (F + 32) [92; cls; 48; 48])
  by (eapply ts_garr_av; [intros j Hj; apply aview_eq_of; apply Hmb | exact HG4a]).
assert (HSH6b : aview SEGS (w_H Wc) (ms_mem ms0) (shadow_addr F + 4) = Some 6)
  by (rewrite <- HSH6a; apply aview_eq_of; apply Hmb).
assert (KRb : forall r : bv 5, In r [2; 3; 4; 8; 9; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms0) r = getr (ms_regs ms) r).
{ intros r Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [tskeep HSb |]). destruct Hr0. }
assert (HLRb : lregsa (ms_regs ms0) F (Z.of_nat i)).
{ unfold ts_lregs, ts_bregs.
  rewrite (KRb 2%bv), (KRb 3%bv), (KRb 4%bv), (KRb 8%bv), (KRb 9%bv), (KRb 18%bv), (KRb 19%bv), (KRb 20%bv),
    (KRb 21%bv), (KRb 22%bv), (KRb 23%bv), (KRb 24%bv), (KRb 25%bv), (KRb 26%bv), (KRb 27%bv) by (cbv; tauto).
  exact HLRa. }
prreg HSb (14%bv : bv 5) Q14.
assert (R14 : getr (ms_regs ms0) 14 = w64 (WriterSpec.hexd (cb / 16))).
{ rewrite Q14. exact (te_more_lt regs (ms_regs ms) [w64 (WriterSpec.hexd (cb / 16))] 0 ltac:(lia)). }
clear HF HG HFr.
pmkst HSb.
destruct (ts_frame_A HLb) as (_ & _ & _ & _ & _ & _ & _ & Fprb & _).
(* ---- esc[4] and the lo nibble's address, aliased to the segment's extra word (A' 0x854b4 .. 0x854c0) ---- *)
assert (X13c : bv_unsigned (ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) (xr 13)) = cb).
{ unfold xr. rewrite (te_cur regs (ms_regs ms0) _ 13%bv 13) by reflexivity.
  rewrite (KRb 13%bv), (KRa 13%bv) by (cbv; tauto). rewrite R13. apply unsigned_lit_small. lia. }
assert (X14c : bv_unsigned (ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) (xr 14))
  = WriterSpec.hexd (cb / 16)).
{ unfold xr. rewrite (te_cur regs (ms_regs ms0) _ 14%bv 14) by reflexivity. rewrite R14.
  apply unsigned_lit_small. lia. }
assert (X25c : bv_unsigned (ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) (xr 25)) = TS_HEX_A).
{ unfold xr. rewrite (te_cur regs (ms_regs ms0) _ 25%bv 25) by reflexivity.
  rewrite (KRb 25%bv), (KRa 25%bv) by (cbv; tauto). rewrite R25. apply unsigned_lit_small. lia. }
assert (X22c : bv_unsigned (ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) (xr 22)) = F + 32).
{ unfold xr. rewrite (te_cur regs (ms_regs ms0) _ 22%bv 22) by reflexivity.
  rewrite (KRb 22%bv), (KRa 22%bv) by (cbv; tauto). rewrite R22. apply unsigned_lit_small. lia. }
assert (E64c : ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) 64 = w64 (TS_HEX_A + cb mod 16))
  by exact (te_more_lt regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)] 0 ltac:(lia)).
assert (X64c : bv_unsigned (ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) 64)
  = TS_HEX_A + cb mod 16) by (rewrite E64c; apply unsigned_lit_small; lia).
destruct (ts_ESC_entry_A (TS_PC_A + TS_H3_OFF_A) cur_atoms [w64 (TS_HEX_A + cb mod 16)] 4 5
  (mkFacts [(xr 13, mkAF 0 255 0); (xr 14, mkAF 0 255 0); (xr 25, mkAF 4096 (2 ^ 47 - 8) 0);
            (xr 22, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 4096 (2 ^ 47 - 8) 0)] []
     [(SAlu ALU_ADD (SOff (xr 25) 0) (SAlu ALU_AND (SOff (xr 13) 0) (SLit 15)), SOff 64 0)])
  Wc (ms_mem ms0) (ms_regs ms0) F
  (te_regs_ok regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)])
  ltac:(rewrite (KRb 22%bv) by (cbv; tauto); rewrite (KRa 22%bv) by (cbv; tauto); exact R22)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Fprb ltac:(vm_compute; reflexivity)) as [HSc SHc].
{ split.
  - cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite X13c, X14c, X25c, X22c, X64c. change (2 ^ 0) with 1. change (2 ^ 5) with 32.
    repeat split; try lia; try apply Z.mod_1_r.
  - split; [exact I|]. cbn [f_alias alias_ok]. split; [|exact I].
    rewrite (ts_nib_lo_A _ (xr 13) (xr 25) cb TS_HEX_A X13c X25c ltac:(lia) ltac:(lia) ltac:(lia)).
    cbn [sv_denot]. rewrite X64c, Z.add_0_r. reflexivity. }
pose proof (SHc (SLit 0)) as SHOKc.
assert (HEIc : img_env VAL A_LIM (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)])) by apply te_env.
pose proof HSc as HSkc.
paj_run_to_tok_xR RUNTO HSc HJ SHOKc (2 ^ 63, 2 ^ 63) (TS_PC_A + TS_H4_OFF_A).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 22) (F + 32)); [reflexivity | exact X22c | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. rewrite <- EF. lia. }
  apply awr_ok_nil. }
assert (KNc : YAkMemnorm.memnorm SEGS (ms_mem ms0) -> YAkMemnorm.memnorm SEGS (ms_mem ms1))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSkc HF); exact Hm).
clear HSkc.
set (WE4 := ss_mem (ss_ESC_A (TS_PC_A + TS_H3_OFF_A) cur_atoms 4 5
  (mkFacts [(xr 13, mkAF 0 255 0); (xr 14, mkAF 0 255 0); (xr 25, mkAF 4096 (2 ^ 47 - 8) 0);
            (xr 22, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 4096 (2 ^ 47 - 8) 0)] []
     [(SAlu ALU_ADD (SOff (xr 25) 0) (SAlu ALU_AND (SOff (xr 13) 0) (SLit 15)), SOff 64 0)]))) in *.
assert (Hwrc : forall a, in_wrange (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) WE4 a -> a = F + 36).
{ intros a (r & Hr0 & Ha). cbv [WE4 ss_ESC_A ss_mem In] in Hr0. destruct Hr0 as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite ts_bv_some, X22c in Ha. lia. }
assert (Kc : forall a, 0 <= a < 2 ^ 64 -> a <> F + 36 ->
  aview SEGS (w_H Wc) (ms_mem ms1) a = aview SEGS (w_H Wc) (ms_mem ms0) a).
{ intros a Ha Hn. apply (ts_keep Wc _ WE4 (ms_mem ms0) (ms_mem ms1) (fun x => x = F + 36) HFr Hwrc a Ha Hn). }
pose proof (ts_live_runR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR lyc Sc Hpc Wc (ms_mem ms0) (ms_mem ms1) _ _ _ _ pos F b _ _ _ _ _ _
  (in_wrange (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) WE4)
  HLb HJ HFr) as HLc.
specialize (HLc ltac:(intros a HW; rewrite (Hwrc a HW); right; exists pos; split; [exact Hin|]; left;
  unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite <- EF; lia)).
specialize (HLc ltac:(intros a HW; rewrite (Hwrc a HW); split; lia)).
specialize (HLc KNc).
assert (HSPc : spilla Wc (ms_mem ms1) F).
{ apply (ts_spill_keep Wc (ms_mem ms0)); [|exact HSPb]. intros a Ha. apply Kc; lia. }
assert (HG4c : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (F + 32) [92; cls; 48; 48])
  by (eapply ts_garr_av; [intros j Hj; apply Kc; cbn [length] in Hj; lia | exact HG4b]).
assert (HSH6c : aview SEGS (w_H Wc) (ms_mem ms1) (shadow_addr F + 4) = Some 6).
{ rewrite <- HSH6b. apply Kc; unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia. }
(* esc[4], read back from the region the run leaves *)
pose proof (ts_region_nth (L := A_prog_listing) (PA := PA) _ _ _ 0 _ HSc eq_refl) as HR0c.
cbn [ms_mem restrict] in HR0c.
assert (V4 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (F + 32 + 4) 1 (WriterSpec.hexd (cb / 16))).
{ pose proof (ts_field (L := A_prog_listing) (PA := PA) _ _ (xr 22) (F + 32) _ _ _ _ _ 4 1 (SOff (xr 14) 0)
    HR0c X22c ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V.
  change (2 ^ (8 * Z.of_N 1)) with 256 in V. change (N.to_nat 1) with 1%nat in V. rewrite ts_U0 in V.
  assert (X14 : bv_unsigned (ew (TEa regs (ms_regs ms0) [w64 (TS_HEX_A + cb mod 16)]) (xr 14))
    = WriterSpec.hexd (cb / 16)).
  { unfold xr. rewrite (te_cur regs (ms_regs ms0) _ 14%bv 14) by reflexivity. rewrite R14.
    apply unsigned_lit_small. lia. }
  rewrite X14, (Z.mod_small (WriterSpec.hexd (cb / 16)) 256) in V by lia. exact V. }
assert (HG5c : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms1)) (F + 32) [92; cls; 48; 48; WriterSpec.hexd (cb / 16)]).
{ exact (garr8_app1 SEGS _ _ (F + 32) [92; cls; 48; 48] _ HG4c V4 ltac:(lia) (fun _ _ => eq_refl)). }
assert (KRc : forall r : bv 5, In r [2; 3; 4; 8; 9; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr (ms_regs ms0) r).
{ intros r Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [tskeep HSc |]). destruct Hr0. }
assert (HLRc : lregsa (ms_regs ms1) F (Z.of_nat i)).
{ unfold ts_lregs, ts_bregs.
  rewrite (KRc 2%bv), (KRc 3%bv), (KRc 4%bv), (KRc 8%bv), (KRc 9%bv), (KRc 18%bv), (KRc 19%bv), (KRc 20%bv),
    (KRc 21%bv), (KRc 22%bv), (KRc 23%bv), (KRc 24%bv), (KRc 25%bv), (KRc 26%bv), (KRc 27%bv) by (cbv; tauto).
  exact HLRb. }
prreg HSc (10%bv : bv 5) Q10c.
try rewrite !ew_ewset_other in Q10c by lia.
assert (R10c : getr (ms_regs ms1) 10 = w64 (TS_HEX_A + cb mod 16)).
{ rewrite Q10c. cbn [sv_denot]. rewrite E64c. try rewrite Z.add_0_r. unfold w64.
  rewrite ?unsigned_lit_small by lia. first [reflexivity | apply Z_to_bv_bv_unsigned]. }
clear HF HG HFr.
pmkst HSc.
(* ---- the lo nibble's inline check (A' 0x854c0 .. 0x854d0) ---- *)
pose proof HLc as (HJc & HSDc & EFc & HMc).
pose proof HSDc as (_ & _ & _ & _ & HROcc & _).
pose proof (ajxR_ar HJc) as HARcc.
destruct (ts_hex_addr_A lyc Sc Hpc Wc (ms_mem ms1) _ HARcc) as (Hras1 & _).
assert (R24c : getr (ms_regs ms1) 24 = w64 SHADOW_OFF)
  by (rewrite (KRc 24%bv), (KRb 24%bv), (KRa 24%bv) by (cbv; tauto); exact R24).
destruct (ts_CK_entry_A (TS_PC_A + TS_H4_OFF_A)
  (mkFacts [(xr 10, mkAF 4096 (2 ^ 47 - 8) 0); (xr 24, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [])
  Wc (ms_mem ms1) (ms_regs ms1)) as [HSd SHd].
{ split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (X10 : bv_unsigned (ew (TEa regs (ms_regs ms1) []) (xr 10)) = TS_HEX_A + cb mod 16).
  { unfold xr. rewrite (te_cur regs (ms_regs ms1) _ 10%bv 10) by reflexivity. rewrite R10c.
    apply unsigned_lit_small. lia. }
  assert (X24 : bv_unsigned (ew (TEa regs (ms_regs ms1) []) (xr 24)) = SHADOW_OFF).
  { unfold xr. rewrite (te_cur regs (ms_regs ms1) _ 24%bv 24) by reflexivity. rewrite R24c.
    apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  rewrite X10, X24. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r. }
pose proof (SHd (SOff (xr 24) 0)) as SHOKd.
assert (HEId : img_env VAL A_LIM (TEa regs (ms_regs ms1) [])) by apply te_env.
pose proof HSd as HSkd.
paj_run_to_tok_xR RUNTO HSd HJ SHOKd TS_SPAN_A (TS_PC_A + TS_H5_OFF_A).
{ cbn [ms_mem mkst restrict]. rewrite !U_SOff.
  assert (A56 : ew (TEa regs (ms_regs ms1) []) (xr 24) = getr (ms_regs ms1) 24)
    by (unfold xr; apply (te_cur regs (ms_regs ms1) _ 24%bv 24); reflexivity).
  assert (A42 : ew (TEa regs (ms_regs ms1) []) 42 = getr (ms_regs ms1) 10) by te_close.
  rewrite A56, A42, R24c, R10c. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !YP0m.zcanon_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
  apply (range_addressable_sub _ SHADOW_OFF TS_HEX_A 16); [exact Hras1 | lia | lia]. }
{ cbv [ss_CK_A ss_mem]. apply awr_ok_nil. }
assert (KNd : YAkMemnorm.memnorm SEGS (ms_mem ms1) -> YAkMemnorm.memnorm SEGS (ms_mem ms2))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSkd HF); exact Hm).
clear HSkd.
assert (Hmd : forall x, mrestrict (w_H Wc) (ms_mem ms2) x = mrestrict (w_H Wc) (ms_mem ms1) x).
{ intros x. apply HFr. intros (r & Hri & Hr). cbv [ss_CK_A ss_mem In] in Hri. destruct Hri. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLc HJ Hmd KNd) as HLd.
assert (HSPd : spilla Wc (ms_mem ms2) F)
  by (apply (ts_spill_keep Wc (ms_mem ms1)); [intros a Ha; apply aview_eq_of; apply Hmd | exact HSPc]).
assert (HG5d : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms2)) (F + 32) [92; cls; 48; 48; WriterSpec.hexd (cb / 16)])
  by (eapply ts_garr_av; [intros j Hj; apply aview_eq_of; apply Hmd | exact HG5c]).
assert (HSH6d : aview SEGS (w_H Wc) (ms_mem ms2) (shadow_addr F + 4) = Some 6)
  by (rewrite <- HSH6c; apply aview_eq_of; apply Hmd).
assert (KRd : forall r : bv 5, In r [2; 3; 4; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms2) r = getr (ms_regs ms1) r).
{ intros r Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [tskeep HSd |]). destruct Hr0. }
assert (HLRd : lregsa (ms_regs ms2) F (Z.of_nat i)).
{ unfold ts_lregs, ts_bregs.
  rewrite (KRd 2%bv), (KRd 3%bv), (KRd 4%bv), (KRd 8%bv), (KRd 9%bv), (KRd 18%bv), (KRd 19%bv), (KRd 20%bv),
    (KRd 21%bv), (KRd 22%bv), (KRd 23%bv), (KRd 24%bv), (KRd 25%bv), (KRd 26%bv), (KRd 27%bv) by (cbv; tauto).
  exact HLRc. }
clear HF HG HFr.
pmkst HSd.
(* ---- the lo digit's load (A' 0x854d0 .. 0x854d4) ---- *)
pose proof HLd as (HJd & HSDd & EFd & HMd).
pose proof HSDd as (_ & _ & _ & _ & HROd & _).
pose proof (ajxR_ar HJd) as HARd.
destruct (ts_hex_byte_A lyc Sc Hpc Wc (ms_mem ms2) _ (cb mod 16) HARd HROd ltac:(lia)) as (Vlo & Rlo).
destruct (ts_HXL_entry_A (TS_PC_A + TS_H5_OFF_A)
  (mkFacts [(xr 10, mkAF 4096 (2 ^ 47 - 8) 0); (64%nat, mkAF 0 255 0)] [] []) Wc (ms_mem ms2) (ms_regs ms2)
  (TS_HEX_A + cb mod 16) (WriterSpec.hexd (cb mod 16))
  ltac:(rewrite (KRd 10%bv) by (cbv; tauto); exact R10c) ltac:(lia) ltac:(lia) Rlo Vlo) as [HSe SHe].
{ split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (X10 : bv_unsigned (ew (TEa regs (ms_regs ms2) [w64 (WriterSpec.hexd (cb mod 16))]) (xr 10))
    = TS_HEX_A + cb mod 16).
  { unfold xr. rewrite (te_cur regs (ms_regs ms2) _ 10%bv 10) by reflexivity.
    rewrite (KRd 10%bv) by (cbv; tauto). rewrite R10c. apply unsigned_lit_small. lia. }
  assert (X64 : bv_unsigned (ew (TEa regs (ms_regs ms2) [w64 (WriterSpec.hexd (cb mod 16))]) 64)
    = WriterSpec.hexd (cb mod 16)).
  { rewrite (te_more_lt regs (ms_regs ms2) [w64 (WriterSpec.hexd (cb mod 16))] 0) by lia. cbn [nth].
    apply unsigned_lit_small. lia. }
  rewrite X10, X64. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r. }
pose proof (SHe (SLit 0)) as SHOKe.
assert (HEIe : img_env VAL A_LIM (TEa regs (ms_regs ms2) [w64 (WriterSpec.hexd (cb mod 16))])) by apply te_env.
pose proof HSe as HSke.
paj_run_to_tok_xR RUNTO HSe HJ SHOKe (2 ^ 63, 2 ^ 63) (TS_PC_A + TS_D_OFF_A).
{ cbv [ss_HXL_A ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (KNe : YAkMemnorm.memnorm SEGS (ms_mem ms2) -> YAkMemnorm.memnorm SEGS (ms_mem ms3))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSke HF); exact Hm).
clear HSke.
assert (Hme : forall x, mrestrict (w_H Wc) (ms_mem ms3) x = mrestrict (w_H Wc) (ms_mem ms2) x).
{ intros x. apply HFr. intros (r & Hri & Hr). cbv [ss_HXL_A ss_mem In] in Hri. destruct Hri as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hr. lia. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLd HJ Hme KNe) as HLe.
assert (HSPe : spilla Wc (ms_mem ms3) F)
  by (apply (ts_spill_keep Wc (ms_mem ms2)); [intros a Ha; apply aview_eq_of; apply Hme | exact HSPd]).
assert (HG5e : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms3)) (F + 32) [92; cls; 48; 48; WriterSpec.hexd (cb / 16)])
  by (eapply ts_garr_av; [intros j Hj; apply aview_eq_of; apply Hme | exact HG5d]).
assert (HSH6e : aview SEGS (w_H Wc) (ms_mem ms3) (shadow_addr F + 4) = Some 6)
  by (rewrite <- HSH6d; apply aview_eq_of; apply Hme).
assert (KRe : forall r : bv 5, In r [2; 3; 4; 8; 9; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms3) r = getr (ms_regs ms2) r).
{ intros r Hr0. cbv [In] in Hr0. repeat (destruct Hr0 as [<- | Hr0]; [tskeep HSe |]). destruct Hr0. }
assert (HLRe : lregsa (ms_regs ms3) F (Z.of_nat i)).
{ unfold ts_lregs, ts_bregs.
  rewrite (KRe 2%bv), (KRe 3%bv), (KRe 4%bv), (KRe 8%bv), (KRe 9%bv), (KRe 18%bv), (KRe 19%bv), (KRe 20%bv),
    (KRe 21%bv), (KRe 22%bv), (KRe 23%bv), (KRe 24%bv), (KRe 25%bv), (KRe 26%bv), (KRe 27%bv) by (cbv; tauto).
  exact HLRd. }
prreg HSe (10%bv : bv 5) Q10e.
assert (R10e : getr (ms_regs ms3) 10 = w64 (WriterSpec.hexd (cb mod 16))).
{ rewrite Q10e. exact (te_more_lt regs (ms_regs ms2) [w64 (WriterSpec.hexd (cb mod 16))] 0 ltac:(lia)). }
clear HF HG HFr.
pmkst HSe.
apply (HK (ms_mem ms3) _ _ (ms_regs ms3) HLe HSPe HLRe); try assumption.
- rewrite (KRe 11%bv), (KRd 11%bv), (KRc 11%bv), (KRb 11%bv), (KRa 11%bv) by (cbv; tauto). exact R11.
- rewrite (KRe 12%bv), (KRd 12%bv), (KRc 12%bv), (KRb 12%bv), (KRa 12%bv) by (cbv; tauto). exact R12.
Qed.

(* ---- the byte's own call `tx_put(t, s + i, 1)` returning to F1 (A' 0x85500; from the printable arm or E). The call
   returns on every outcome of tx_put's #102 text (DONE / FAILED / REFUSED); the walk continues with the state the
   glue folds ---- *)
Lemma ts_byte_call_A : forall i Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ap pre cb post ks0 add0,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i ->
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  bv_unsigned (ew E 2) = sp0 ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos F b cap f own ks0 add0 ap -> spilla Wc (ms_mem ms) F ->
  lregsa (ms_regs ms) F (Z.of_nat i) ->
  getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 (s + Z.of_nat i) -> getr (ms_regs ms) 12 = w64 1 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (TS_PC_A + TS_F1_OFF_A)) ->
  ks0 ++ [1] = TxModel.plen (ts_pieces (pre ++ [cb])) -> add0 ++ [cb] = concat (ts_pieces (pre ++ [cb])) ->
  ks0 ++ 1 :: ts_rest post = TSks -> TxModel.zsum ks0 = Z.of_nat (length add0) ->
  SRW Wc (mkCfg ms mdc) QFa.
Proof.
intros i Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ap pre cb post ks0 add0 HX IH Ebs Hlen HS Hrv Hpcs HE2 HL HSP
  HLR X10 X11 X12 X1 Eks Eadd Ers Hz.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTK_A as HSTK.
destruct (ts_src_byteR (LAWS := LAWS) WR
  lyc Sc Hpc Wc (ms_mem ms) mdc kj pos F b cap f own ks0 add0 ap pre cb post HL Ebs ltac:(lia))
  as (HSRC & HKEPT & HDISJ & Hcb).
rewrite Hlen in HSRC, HKEPT, HDISJ.
change (TS_PC_A + TS_F1_OFF_A) with 16164 in X1.
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite X1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite X1, unsigned_lit_small by lia; lia).
(* fpre's raZ bound at image A': the return pc is a listing slot (the closed lemma ts_ret_ceil_F1_A) *)
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite X1; exact ts_ret_ceil_F1_A).
refine (ts_put_call (HSTK := HSTK_A) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_A) (pst_ro := pst_ro_A)
  ch Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ks0 add0 ap 1 (s + Z.of_nat i) [cb] (ts_rest post)
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS Hrv Hpcs HE2 HL (proj1 HLR) X10 X11 X12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ Ers HOS _).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 HSPk HP2.
rewrite Eks, Eadd in HL2.
rewrite X1. change (BASE + 16164) with (BASE + (TS_PC_A + TS_F1_OFF_A)).
exact (ts_F_A i W2 ly2 S2 Hp2 mem2 md2 kj2 pos F b2 cap2 f2 own2 (ap ++ prec) regs2 pre cb post HX IH Ebs Hlen HL2
  (HSPk HSP) (ts_lregs_pres _ _ F (Z.of_nat i) HLR HP2)).
Qed.

(* ---- esc[]'s call `tx_put(t, esc, 2 or 6)` returning to F1 (A' 0x85500 via 0x8554c; a byte below 32) ---- *)
Lemma ts_esc_call_A : forall i Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ap pre cb post l,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i ->
  TxModel.spcs cb = [l] -> (0 < length l <= 6)%nat ->
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  bv_unsigned (ew E 2) = sp0 ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos F b cap f own (TxModel.plen (ts_pieces pre)) (concat (ts_pieces pre)) ap ->
  spilla Wc (ms_mem ms) F -> lregsa (ms_regs ms) F (Z.of_nat i) ->
  getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 (F + 32) ->
  getr (ms_regs ms) 12 = w64 (Z.of_nat (length l)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (TS_PC_A + TS_F1_OFF_A)) ->
  aview SEGS (w_H Wc) (ms_mem ms) (shadow_addr F + 4) = Some 6 ->
  garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms)) (F + 32) l ->
  SRW Wc (mkCfg ms mdc) QFa.
Proof.
intros i Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ap pre cb post l HX IH Ebs Hlen Esp Hn HS Hrv Hpcs HE2 HL
  HSP HLR X10 X11 X12 X1 H6 Hga.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTK_A as HSTK.
destruct (ts_frame_A HL) as (HARc & Hin & Fb1 & Fb2 & Fb3 & F64 & F32 & Ffr & Fsh).
destruct (ts_src_escR (LAWS := LAWS) WR lyc Sc Hpc Wc (ms_mem ms) mdc kj pos F b cap f own _ _ ap l HL ltac:(lia) F64 H6
  Hga Hn) as (HSRC & HKEPT & HDISJ).
change (TS_PC_A + TS_F1_OFF_A) with 16164 in X1.
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite X1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite X1, unsigned_lit_small by lia; lia).
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite X1; exact ts_ret_ceil_F1_A).
assert (Ers : TxModel.plen (ts_pieces pre) ++ Z.of_nat (length l) :: ts_rest post = TSks).
{ rewrite <- (ts_ks_split pre (cb :: post) Ebs), ts_rest_cons, Esp. reflexivity. }
refine (ts_put_call (HSTK := HSTK_A) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_A) (pst_ro := pst_ro_A)
  ch Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own _ _ ap (Z.of_nat (length l)) (F + 32) l (ts_rest post)
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS Hrv Hpcs HE2 HL (proj1 HLR) X10 X11 X12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ Ers HOS _).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 HSPk HP2.
assert (Eks : TxModel.plen (ts_pieces pre) ++ [Z.of_nat (length l)] = TxModel.plen (ts_pieces (pre ++ [cb])))
  by (rewrite ts_pieces_snoc, Esp; unfold TxModel.plen; rewrite map_app; reflexivity).
assert (Eadd : concat (ts_pieces pre) ++ l = concat (ts_pieces (pre ++ [cb])))
  by (rewrite ts_pieces_snoc, Esp, concat_app; cbn [concat]; rewrite app_nil_r; reflexivity).
rewrite Eks, Eadd in HL2.
rewrite X1. change (BASE + 16164) with (BASE + (TS_PC_A + TS_F1_OFF_A)).
exact (ts_F_A i W2 ly2 S2 Hp2 mem2 md2 kj2 pos F b2 cap2 f2 own2 (ap ++ prec) regs2 pre cb post HX IH Ebs Hlen HL2
  (HSPk HSP) (ts_lregs_pres _ _ F (Z.of_nat i) HLR HP2)).
Qed.

(* ---- E (A' 0x854f4): after the backslash of a quote or backslash byte, the byte itself ---- *)
Definition ss_E_A : sstate := mkSS (TS_PC_A + TS_E_OFF_A) cur_atoms [] None (mkFacts [] [] []).
Lemma ts_at_E_A : forall i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i -> (cb = 34 \/ cb = 92) ->
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces pre) ++ [1])
    (concat (ts_pieces pre) ++ [92]) ap ->
  spilla Wc memc F -> lregsa rg F (Z.of_nat i) ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_E_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post HX IH Ebs Hlen Hq HL HSP HLR.
pose proof HL as (HJ & _).
pose proof HLR as ((R2 & R3 & R4 & R8 & R9 & R20 & R24) & R18 & R19 & R21 & R22 & R23 & R25 & R26 & R27).
assert (HS : st_ok_pi SEGS VAL (TEa regs rg []) ss_E_A
  (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_E_OFF_A))) memc (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TEa regs rg []) (mrestrict (w_H Wc) memc)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TEa regs rg [])) by apply te_env.
pose (RUN := @paj_run_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
pose proof HS as HSk.
paj_run_tok_xR RUN HS HJ SHOK (0, 0).
{ cbv [ss_E_A ss_mem]. apply awr_ok_nil. }
assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
clear HSk.
assert (Hm : forall x, mrestrict (w_H Wc) (ms_mem ms) x = mrestrict (w_H Wc) memc x).
{ intros x. apply HFr. intros (r & Hr & _). cbv [ss_E_A ss_mem In] in Hr. destruct Hr. }
pose proof (ts_live_sameR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
  WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL HJ Hm KN) as HL1.
assert (HSP1 : spilla Wc (ms_mem ms) F).
{ apply (ts_spill_keep Wc memc); [|exact HSP]. intros a Ha. apply aview_eq_of. apply Hm. }
clear HF HG HFr.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr rg r).
{ intros r Hr. cbv [In] in Hr. repeat (destruct Hr as [<- | Hr]; [tskeep HS |]). destruct Hr. }
assert (HE2 : bv_unsigned (ew (TEa regs rg []) 2) = sp0)
  by (rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
pose proof (s10s_spcs_q cb Hq) as Esp.
apply (ts_byte_call_A i Wc (TEa regs rg []) _ ms _ lyc Sc Hpc _ pos F b cap f own ap pre cb post _ _ HX IH Ebs Hlen HS
  eq_refl
  ltac:(vm_compute; reflexivity) HE2 HL1 HSP1).
- unfold ts_lregs, ts_bregs.
  rewrite (KR 2%bv), (KR 3%bv), (KR 4%bv), (KR 8%bv), (KR 9%bv), (KR 18%bv), (KR 19%bv), (KR 20%bv), (KR 21%bv),
    (KR 22%bv), (KR 23%bv), (KR 24%bv), (KR 25%bv), (KR 26%bv), (KR 27%bv) by (cbv; tauto).
  exact HLR.
- rewrite Q10, (te_cur regs rg _ 20%bv 20) by reflexivity. exact R20.
- rewrite Q11, (te_cur regs rg _ 19%bv 19) by reflexivity. exact R19.
- rewrite Q12. reflexivity.
- rewrite Q1. reflexivity.
- rewrite ts_pieces_snoc, Esp. unfold TxModel.plen. rewrite map_app, <- app_assoc. reflexivity.
- rewrite ts_pieces_snoc, Esp, concat_app, <- app_assoc. reflexivity.
- rewrite <- (ts_ks_split pre (cb :: post) Ebs), ts_rest_cons, Esp, <- app_assoc. reflexivity.
- rewrite TxModel.zsum_app, TxModel.zsum_plen, length_app. cbn [TxModel.zsum length]. lia.
Qed.

(* ---- the backslash's call `tx_put(t, .str.26, 1)` (A' 0x854f0) returning to E, for a quote or backslash byte ---- *)
Lemma ts_bs_call_A : forall i Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ap pre cb post,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i -> (cb = 34 \/ cb = 92) ->
  st_ok SEGS E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_tx_put ->
  bv_unsigned (ew E 2) = sp0 ->
  livea lyc Sc Hpc Wc (ms_mem ms) mdc kj pos F b cap f own (TxModel.plen (ts_pieces pre)) (concat (ts_pieces pre)) ap ->
  spilla Wc (ms_mem ms) F -> lregsa (ms_regs ms) F (Z.of_nat i) ->
  getr (ms_regs ms) 10 = w64 t -> getr (ms_regs ms) 11 = w64 TS_STR26_A -> getr (ms_regs ms) 12 = w64 1 ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (TS_PC_A + TS_E_OFF_A)) ->
  SRW Wc (mkCfg ms mdc) QFa.
Proof.
intros i Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own ap pre cb post HX IH Ebs Hlen Hq HS Hrv Hpcs HE2 HL HSP HLR
  X10 X11 X12 X1.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTK_A as HSTK.
destruct (ts_src_litR (pa_hi_ok := pa_hi_ok_A) (HSTK := HSTK_A) (LAWS := LAWS) (zs_aligned := zs_aligned)
  (img_shadow_vis_x := img_shadow_vis_x) (img_box := img_box_A) (img_cf_box := img_cf_box)
  WR lyc Sc Hpc Wc (ms_mem ms) _ _ pos F b cap f own _ _ ap TS_STR26_A [92] HL ts_lit_img_A
  ltac:(cbn; lia) ltac:(intros j Hj; destruct j as [|j]; [vm_compute; reflexivity | cbn in Hj; lia]))
  as (HSRC & HKEPT & HDISJ).
change (TS_PC_A + TS_E_OFF_A) with 16148 in X1.
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (HRAOK : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite X1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (HRA4 : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite X1, unsigned_lit_small by lia; lia).
assert (HRAC : raZ (ms_regs ms) < YM05.alloc_ceiling) by (unfold raZ; rewrite X1; exact ts_ret_ceil_E_A).
pose proof (s10s_spcs_q cb Hq) as Esp.
assert (Ers : TxModel.plen (ts_pieces pre) ++ 1 :: 1 :: ts_rest post = TSks).
{ rewrite <- (ts_ks_split pre (cb :: post) Ebs), ts_rest_cons, Esp. reflexivity. }
refine (ts_put_call (HSTK := HSTK_A) (LAWS := LAWS) (TXPUT := TXPUT) (HSTKP := HSTKP_A) (pst_ro := pst_ro_A)
  ch Wc E ss ms mdc lyc Sc Hpc kj pos F b cap f own _ _ ap 1 TS_STR26_A [92] (1 :: ts_rest post)
  (conj HPRE (conj HCL (conj HFWIN (conj HPLACE (conj HLEN (conj HLIVE (conj HMAX
    (conj HEVS (conj HROOMW (conj HCONS HFRM))))))))))
  HS Hrv Hpcs HE2 HL (proj1 HLR) X10 X11 X12 HRAOK HRA4 HRAC HSRC eq_refl HKEPT HDISJ Ers HOS _).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 kj2 b2 cap2 f2 own2 prec HL2 HSPk HP2.
rewrite X1. change (BASE + 16148) with (BASE + (TS_PC_A + TS_E_OFF_A)).
exact (ts_at_E_A i W2 ly2 S2 Hp2 mem2 md2 kj2 pos F b2 cap2 f2 own2 (ap ++ prec) regs2 pre cb post HX IH Ebs Hlen Hq
  HL2 (HSPk HSP) (ts_lregs_pres _ _ F (Z.of_nat i) HLR HP2)).
Qed.


(* ---- D (A' 0x854d4): esc[5], the byte's class tests and its 1 or 2 tx_put calls. The lo digit is already loaded
   (ts_mid_A), so this run carries no inline check ---- *)
Definition ss_D_A (lo hi llo lhi : Z) (cs : list acond) : sstate :=
  mkSS (TS_PC_A + TS_D_OFF_A) cur_atoms [ YP09.mkRegion (Some (xr 22)) 0 6 5 6 [] ] None
  (mkFacts [(xr 11, mkAF lo hi 0); (xr 12, mkAF llo lhi 0); (xr 18, mkAF 92 92 0);
            (xr 22, mkAF 4096 (2 ^ 47) 5); (xr 10, mkAF 48 102 0)] cs []).
Lemma ts_D_entry_A : forall (Wc : world SEGS) memc rg F cb lt hd lo hi llo lhi cs,
  getr rg 10 = w64 hd -> getr rg 11 = w64 cb -> getr rg 12 = w64 lt -> getr rg 18 = w64 92 ->
  getr rg 22 = w64 (F + 32) ->
  lo <= cb <= hi -> 0 <= cb < 256 -> llo <= lt <= lhi -> 0 <= lt < 256 -> 48 <= hd <= 102 ->
  (forall E, bv_unsigned (ew E (xr 11)) = cb -> bv_unsigned (ew E (xr 12)) = lt ->
     bv_unsigned (ew E (xr 18)) = 92 -> conds_ok E cs) ->
  4096 <= F -> F + 64 <= 2 ^ 47 -> F mod 64 = 0 -> apresent (w_H Wc) memc (F + 37) ->
  st_ok_pi SEGS VAL (TEa regs rg []) (ss_D_A lo hi llo lhi cs)
    (restrict (w_H Wc) (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_D_OFF_A))) memc (seg_rom SEGS))) /\
  (forall Bx, sh_ok SEGS Bx [] (TEa regs rg []) (mrestrict (w_H Wc) memc)).
Proof.
intros Wc memc rg F cb lt hd lo hi llo lhi cs R10 R11 R12 R18 R22 Hlh Hcb Hll Hlt Hhd Hcs G1 G2 G3 HP.
set (E := TEa regs rg []).
assert (X10 : bv_unsigned (ew E (xr 10)) = hd).
{ unfold E, xr. rewrite (te_cur regs rg _ 10%bv 10) by reflexivity. rewrite R10. apply unsigned_lit_small. lia. }
assert (X11 : bv_unsigned (ew E (xr 11)) = cb).
{ unfold E, xr. rewrite (te_cur regs rg _ 11%bv 11) by reflexivity. rewrite R11. apply unsigned_lit_small. lia. }
assert (X12 : bv_unsigned (ew E (xr 12)) = lt).
{ unfold E, xr. rewrite (te_cur regs rg _ 12%bv 12) by reflexivity. rewrite R12. apply unsigned_lit_small. lia. }
assert (X18 : bv_unsigned (ew E (xr 18)) = 92).
{ unfold E, xr. rewrite (te_cur regs rg _ 18%bv 18) by reflexivity. rewrite R18. apply unsigned_lit_small. lia. }
assert (X22 : bv_unsigned (ew E (xr 22)) = F + 32).
{ unfold E, xr. rewrite (te_cur regs rg _ 22%bv 22) by reflexivity. rewrite R22. apply unsigned_lit_small. lia. }
split; [|intros Bx; unfold sh_ok; apply Forall_nil].
apply ts_st_ok.
all: try change (TEa regs rg []) with E.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 22) (F + 32)); [exact X22 | lia | lia | | constructor].
  intros o Ho. apply (apresent_writable SEGS). replace (F + 32 + o) with (F + 37) by lia. exact HP.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [|exact I]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X10, X11, X12, X18, X22.
    change (2 ^ 5) with 32. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
  + cbn [f_conds]. exact (Hcs E X11 X12 X18).
Qed.

Lemma ts_at_D_A : forall i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i ->
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces pre)) (concat (ts_pieces pre)) ap ->
  spilla Wc memc F -> lregsa rg F (Z.of_nat i) -> getr rg 11 = w64 cb ->
  getr rg 10 = w64 (WriterSpec.hexd (cb mod 16)) -> getr rg 12 = w64 (ts_letter_A cb) ->
  garr8 SEGS (mrestrict (w_H Wc) memc) (F + 32) [92; ts_letter_A cb; 48; 48; WriterSpec.hexd (cb / 16)] ->
  aview SEGS (w_H Wc) memc (shadow_addr F + 4) = Some 6 ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_D_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post HX IH Ebs Hlen HL HSP HLR R11 R10 R12 Hesc H6.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)).
pose proof HSD as (HWIN & HTX & HPOSs & HMNs & HRO & ((Hl & Hlens & H32 & Hfa & Hga) & HBV) & _).
pose proof HLR as ((R2 & R3 & R4 & R8 & R9 & R20 & R24) & R18 & R19 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTK_A as HSTK.
destruct (ts_sp1_range Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
destruct (ts_frame_A HL) as (HARc & Hin & Fb1 & Fb2 & Fb3 & F64 & F32 & Ffr & Fsh).
assert (Hcb : 0 < cb < 256).
{ rewrite Forall_forall in Hfa. apply Hfa. rewrite Ebs. apply in_or_app. right. left. reflexivity. }
pose proof (ts_hexd_range_A (cb mod 16) ltac:(pose proof (Z.mod_pos_bound cb 16 ltac:(lia)); lia)) as Hd.
pose proof (ts_hexd_range_A (cb / 16)
  ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) as Dhi.
pose proof (ts_letter_rng_A cb) as Hlt.
pose (RUN := @paj_run_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
assert (Hcls : cb = 92 \/ cb = 34 \/ (32 <= cb <= 91 /\ cb <> 34) \/ 93 <= cb <= 255 \/
  (cb = 9 \/ cb = 10 \/ cb = 13) \/ (1 <= cb <= 31 /\ cb <> 9 /\ cb <> 10 /\ cb <> 13)) by lia.
destruct Hcls as [C | [C | [C | [C | [C | C]]]]].
1: destruct (ts_D_entry_A Wc memc rg F cb (ts_letter_A cb) (WriterSpec.hexd (cb mod 16)) 92 92 117 117
     [mkAC BC_EQ (SOff (xr 11) 0) (SOff (xr 18) 0)]
     R10 R11 R12 R18 R22 ltac:(lia) ltac:(lia) ltac:(rewrite ts_letter_q_A by lia; lia) Hlt ltac:(lia)
     ltac:(intros E X11 X12 X18; cbn [conds_ok]; split; [|exact I]; unfold acond_ok; cbn [ac_c ac_a ac_b];
           rewrite branch_eq_U, !ts_U0, X11, X18; apply Z.eqb_eq; lia)
     Fb1 ltac:(lia) F64 (Ffr (F + 37) ltac:(lia))) as [HS SH0].
2: destruct (ts_D_entry_A Wc memc rg F cb (ts_letter_A cb) (WriterSpec.hexd (cb mod 16)) 34 34 117 117
     (map (fun v => mkAC BC_EQ (SOff (xr 11) 0) (SLit v)) [34])
     R10 R11 R12 R18 R22 ltac:(lia) ltac:(lia) ltac:(rewrite ts_letter_q_A by lia; lia) Hlt ltac:(lia)
     ltac:(intros E X11 X12 X18; exact (ts_conds_eq E (xr 11) cb [34] X11 ltac:(repeat constructor; lia)))
     Fb1 ltac:(lia) F64 (Ffr (F + 37) ltac:(lia))) as [HS SH0].
3: destruct (ts_D_entry_A Wc memc rg F cb (ts_letter_A cb) (WriterSpec.hexd (cb mod 16)) 32 91 117 117
     (map (fun v => mkAC BC_NE (SOff (xr 11) 0) (SLit v)) [34])
     R10 R11 R12 R18 R22 ltac:(lia) ltac:(lia) ltac:(rewrite ts_letter_q_A by lia; lia) Hlt ltac:(lia)
     ltac:(intros E X11 X12 X18; exact (ts_conds_ne E (xr 11) cb [34] X11 ltac:(repeat constructor; lia)))
     Fb1 ltac:(lia) F64 (Ffr (F + 37) ltac:(lia))) as [HS SH0].
4: destruct (ts_D_entry_A Wc memc rg F cb (ts_letter_A cb) (WriterSpec.hexd (cb mod 16)) 93 255 117 117 []
     R10 R11 R12 R18 R22 ltac:(lia) ltac:(lia) ltac:(rewrite ts_letter_q_A by lia; lia) Hlt ltac:(lia)
     ltac:(intros; exact I) Fb1 ltac:(lia) F64 (Ffr (F + 37) ltac:(lia))) as [HS SH0].
5: destruct (ts_D_entry_A Wc memc rg F cb (ts_letter_A cb) (WriterSpec.hexd (cb mod 16)) 1 31 110 116 []
     R10 R11 R12 R18 R22 ltac:(lia) ltac:(lia) ltac:(exact (proj1 (ts_letter_tnr_A cb C))) Hlt ltac:(lia)
     ltac:(intros; exact I) Fb1 ltac:(lia) F64 (Ffr (F + 37) ltac:(lia))) as [HS SH0].
6: destruct (ts_D_entry_A Wc memc rg F cb (ts_letter_A cb) (WriterSpec.hexd (cb mod 16)) 1 31 117 117
     (map (fun v => mkAC BC_EQ (SOff (xr 12) 0) (SLit v)) [117])
     R10 R11 R12 R18 R22 ltac:(lia) ltac:(lia)
     ltac:(rewrite (proj1 (ts_letter_u_A cb ltac:(lia) (proj1 (proj2 C)) (proj1 (proj2 (proj2 C)))
       (proj2 (proj2 (proj2 C))))); lia) Hlt ltac:(lia)
     ltac:(intros E X11 X12 X18; exact (ts_conds_eq E (xr 12) (ts_letter_A cb) [117] X12
       ltac:(apply Forall_cons; [split; [exact (proj1 (ts_letter_u_A cb ltac:(lia) (proj1 (proj2 C))
         (proj1 (proj2 (proj2 C))) (proj2 (proj2 (proj2 C))))) | lia] | apply Forall_nil])))
     Fb1 ltac:(lia) F64 (Ffr (F + 37) ltac:(lia))) as [HS SH0].
all: pose proof (SH0 (SLit 0)) as SHOK.
all: assert (HEI : img_env VAL A_LIM (TEa regs rg [])) by apply te_env.
all: assert (X22 : bv_unsigned (ew (TEa regs rg []) (xr 22)) = F + 32)
  by (unfold xr; rewrite (te_cur regs rg _ 22%bv 22) by reflexivity; rewrite R22; apply unsigned_lit_small; lia).
all: pose proof HS as HSk.
all: paj_run_tok_xR RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
all: lazymatch goal with
  | |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own');
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 22) (F + 32)); [reflexivity | exact X22 | | apply awr_ok_nil];
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 0, pos; split; [left; reflexivity|];
      left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite <- EF; lia
  | |- _ => idtac
  end.
all: assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
all: clear HSk.
all: prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (1%bv : bv 5) Q1.
all: assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr rg r)
  by (intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [tskeep HS |]); destruct Hr).
all: assert (HE2 : bv_unsigned (ew (TEa regs rg []) 2) = sp0)
  by (rewrite (te_entry regs rg _ 2%bv 2) by reflexivity; reflexivity).
all: lazymatch type of HFr with frame_of _ ?rs0 _ _ =>
  assert (Hwr : forall a, in_wrange (TEa regs rg []) rs0 a -> a = F + 37)
    by (intros a (r & Hr & Ha); cbv [ss_D_A ss_mem In] in Hr; destruct Hr as [<- | []];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; rewrite ts_bv_some, X22 in Ha; lia);
  pose proof (ts_live_runR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
    WR lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos F b _ _ _ _ _ _ (in_wrange (TEa regs rg []) rs0) HL HJ HFr)
    as HL1 end.
all: specialize (HL1 ltac:(intros a HW; rewrite (Hwr a HW); right; exists pos; split; [exact Hin|]; left;
  unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite <- EF; lia)).
all: specialize (HL1 ltac:(intros a HW; rewrite (Hwr a HW); lia)).
all: specialize (HL1 KN).
all: assert (HSP1 : spilla Wc (ms_mem ms) F) by (apply (ts_spill_keep Wc memc); [|exact HSP]; intros a Ha;
  apply (ts_keep Wc _ _ memc (ms_mem ms) (fun x => x = F + 37) HFr Hwr a); lia).
all: assert (H6' : aview SEGS (w_H Wc) (ms_mem ms) (shadow_addr F + 4) = Some 6) by (rewrite <- H6;
  apply (ts_keep Wc _ _ memc (ms_mem ms) (fun x => x = F + 37) HFr Hwr);
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia).
all: assert (HLR1 : lregsa (ms_regs ms) F (Z.of_nat i)) by (unfold ts_lregs, ts_bregs;
  rewrite (KR 2%bv), (KR 3%bv), (KR 4%bv), (KR 8%bv), (KR 9%bv), (KR 18%bv), (KR 19%bv), (KR 20%bv), (KR 21%bv),
    (KR 22%bv), (KR 23%bv), (KR 24%bv), (KR 25%bv), (KR 26%bv), (KR 27%bv) by (cbv; tauto); exact HLR).
all: assert (X10 : getr (ms_regs ms) 10 = w64 t)
  by (rewrite Q10, (te_cur regs rg _ 20%bv 20) by reflexivity; exact R20).
all: lazymatch type of HS with st_ok _ ?E' _ _ =>
  assert (HE2' : bv_unsigned (ew E' 2) = sp0) by (rewrite ?ew_ewset_other by lia; exact HE2);
  assert (X22' : bv_unsigned (ew E' (xr 22)) = F + 32) by (unfold xr; rewrite ?ew_ewset_other by lia; exact X22) end.
5-6: assert (Hesc' : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms)) (F + 32)
       [92; ts_letter_A cb; 48; 48; WriterSpec.hexd (cb / 16); WriterSpec.hexd (cb mod 16)])
  by (pose proof (ts_region_nth_c _ _ _ 0 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
      pose proof (ts_field _ _ (xr 22) (F + 32) _ _ _ _ _ 5 1%N (SOff (xr 10) 0) HR1 X22'
        ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V;
      rewrite ts_U0 in V; rewrite ?ew_ewset_other in V by lia;
      rewrite (te_cur regs rg _ 10%bv 10) in V by reflexivity; rewrite R10 in V; unfold w64 in V;
      rewrite unsigned_lit_small in V by lia; rewrite Z.mod_small in V by (cbn; lia);
      change (N.to_nat 1) with 1%nat in V;
      apply (garr8_app1 SEGS (mrestrict (w_H Wc) memc) _ (F + 32)
        [92; ts_letter_A cb; 48; 48; WriterSpec.hexd (cb / 16)] (WriterSpec.hexd (cb mod 16)) Hesc V ltac:(lia));
      intros a Ha; cbn [length Z.of_nat] in Ha;
      apply (ts_keep_mb (w_H Wc) _ _ memc (ms_mem ms) (fun x => x = F + 37) HFr Hwr a); lia).
1-2: apply (ts_bs_call_A i Wc _ _ ms _ lyc Sc Hpc _ pos F b cap f own ap pre cb post HX IH Ebs Hlen ltac:(lia)
       HS eq_refl ltac:(vm_compute; reflexivity) HE2' HL1 HSP1 HLR1 X10);
     [ rewrite Q11, (te_cur regs rg _ 23%bv 23) by reflexivity; exact R23
     | rewrite Q12; reflexivity
     | rewrite Q1; reflexivity ].
1-2: apply (ts_byte_call_A i Wc _ _ ms _ lyc Sc Hpc _ pos F b cap f own ap pre cb post _ _ HX IH Ebs Hlen
       HS eq_refl ltac:(vm_compute; reflexivity) HE2' HL1 HSP1 HLR1 X10);
     [ rewrite Q11, (te_cur regs rg _ 19%bv 19) by reflexivity; exact R19
     | rewrite Q12; reflexivity
     | rewrite Q1; reflexivity
     | rewrite ts_pieces_snoc, (s10s_spcs_p cb ltac:(lia) ltac:(lia) ltac:(lia)); unfold TxModel.plen;
       rewrite map_app; reflexivity
     | rewrite ts_pieces_snoc, (s10s_spcs_p cb ltac:(lia) ltac:(lia) ltac:(lia)), concat_app; reflexivity
     | rewrite <- (ts_ks_split pre (cb :: post) Ebs), ts_rest_cons,
         (s10s_spcs_p cb ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity
     | exact (TxModel.zsum_plen (ts_pieces pre)) ].
1: apply (ts_esc_call_A i Wc _ _ ms _ lyc Sc Hpc _ pos F b cap f own ap pre cb post [92; ts_letter_A cb] HX IH Ebs
     Hlen
     ltac:(rewrite (s10s_spcs_e cb ltac:(lia)), (proj2 (ts_letter_tnr_A cb C)); reflexivity) ltac:(cbn; lia)
     HS eq_refl ltac:(vm_compute; reflexivity) HE2' HL1 HSP1 HLR1 X10);
   [ rewrite Q11, (te_cur regs rg _ 22%bv 22) by reflexivity; exact R22
   | rewrite Q12; reflexivity
   | rewrite Q1; reflexivity
   | exact H6'
   | exact (ts_garr8_pre_A _ _ _ [92; ts_letter_A cb]
       [48; 48; WriterSpec.hexd (cb / 16); WriterSpec.hexd (cb mod 16)] Hesc') ].
1: destruct C as (C1' & C9 & C10 & C13).
1: apply (ts_esc_call_A i Wc _ _ ms _ lyc Sc Hpc _ pos F b cap f own ap pre cb post
     [92; ts_letter_A cb; 48; 48; WriterSpec.hexd (cb / 16); WriterSpec.hexd (cb mod 16)] HX IH Ebs Hlen
     ltac:(rewrite (s10s_spcs_e cb ltac:(lia)), (proj2 (ts_letter_u_A cb ltac:(lia) C9 C10 C13)); reflexivity)
     ltac:(cbn; lia)
     HS eq_refl ltac:(vm_compute; reflexivity) HE2' HL1 HSP1 HLR1 X10);
   [ rewrite Q11, (te_cur regs rg _ 22%bv 22) by reflexivity; exact R22
   | rewrite Q12; reflexivity
   | rewrite Q1; reflexivity
   | exact H6'
   | exact Hesc' ].
Qed.

(* ---- the loop head (A' 0x85448 .. 0x854a0): the unpoison of esc[] (the frame's shadow byte 4 := 06), esc[0..3]
   ('\\', the letter, '0', '0'), the byte's class and the address of hex[c >> 4]. The shadow byte and esc[0..3] are
   stored in one run, under the dummy span ---- *)
Lemma ts_at_D1_A : forall i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post,
  ts_HX_A -> ts_IH_A i -> bs = pre ++ cb :: post -> length pre = i ->
  livea lyc Sc Hpc Wc memc mdc kj pos F b cap f own (TxModel.plen (ts_pieces pre)) (concat (ts_pieces pre)) ap ->
  spilla Wc memc F -> lregsa rg F (Z.of_nat i) -> getr rg 11 = w64 cb ->
  SRW Wc (mkCfg (mkst rg (Z_to_bv 64 (BASE + (TS_PC_A + TS_LH_OFF_A))) memc (seg_rom SEGS)) mdc) QFa.
Proof.
intros i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post HX IH Ebs Hlen HL HSP HLR R11.
pose proof HL as (HJ & HSD & EF & (HSV & HFL)).
pose proof HSD as (HWIN & HTX & HPOSs & HMNs & HRO & ((Hl & Hlens & H32 & Hfa & Hga) & HBV) & _).
pose proof HLR as ((R2 & R3 & R4 & R8 & R9 & R20 & R24) & R18 & R19 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_lt as Hc47.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTK_A as HSTK. destruct (ts_sp1_range Hal16 ltac:(lia)) as (Hsp1a & Hsp1b).
destruct (ts_frame_A HL) as (HARc & Hin & Fb1 & Fb2 & Fb3 & F64 & F32 & Ffr & Fsh).
destruct TS_HEX_range_A as (Hhx0 & Hhx1). pose proof TS_HEX_hi_A as Hhx2.
assert (Hcb : 0 < cb < 256).
{ rewrite Forall_forall in Hfa. apply Hfa. rewrite Ebs. apply in_or_app. right. left. reflexivity. }
assert (Hsh : SHADOW_OFF <= shadow_addr F < SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (HEI : img_env VAL A_LIM (TEa regs rg [])) by apply te_env.
assert (X11 : bv_unsigned (ew (TEa regs rg []) (xr 11)) = cb)
  by (unfold xr; rewrite (te_cur regs rg _ 11%bv 11) by reflexivity; rewrite R11; apply unsigned_lit_small; lia).
assert (X22 : bv_unsigned (ew (TEa regs rg []) (xr 22)) = F + 32)
  by (unfold xr; rewrite (te_cur regs rg _ 22%bv 22) by reflexivity; rewrite R22; apply unsigned_lit_small; lia).
assert (X25 : bv_unsigned (ew (TEa regs rg []) (xr 25)) = TS_HEX_A)
  by (unfold xr; rewrite (te_cur regs rg _ 25%bv 25) by reflexivity; rewrite R25; apply unsigned_lit_small; lia).
assert (X26 : bv_unsigned (ew (TEa regs rg []) (xr 26)) = shadow_addr F).
{ unfold xr. rewrite (te_cur regs rg _ 26%bv 26) by reflexivity. rewrite R26. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (HF8 : shadow_addr F mod 8 = 0).
{ pose proof F64 as HD. apply Z.mod_divide in HD; [|lia]. destruct HD as [q Hq].
  unfold shadow_addr, SHADOW_OFF. replace F with (q * 8 * 8) by lia. rewrite Z.div_mul by lia.
  rewrite Zplus_mod, Z.mod_mul by lia. reflexivity. }
pose (RUNTO := @paj_run_to_xR fx rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRrefl WRtrans).
assert (HG : forall lo hi cs, lo <= cb <= hi -> conds_ok (TEa regs rg []) cs ->
  facts_ok (TEa regs rg []) (mkFacts [(xr 11, mkAF lo hi 0); (xr 22, mkAF 4096 (2 ^ 47) 5);
    (xr 26, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 3); (xr 25, mkAF TS_HEX_A TS_HEX_A 0)] cs [])).
{ intros lo hi cs Hlh Hcs. split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite X11, X22, X25, X26. change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  repeat split; try lia; try apply Z.mod_1_r. }
destruct (Z.eq_dec cb 9) as [E9|N9];
  [|destruct (Z.eq_dec cb 10) as [E10|N10]; [|destruct (Z.eq_dec cb 13) as [E13|N13]]].
4: destruct (ts_D1_entry_A _ Wc memc rg F R22 R26 Fb1 ltac:(lia) Fb3 Ffr Fsh
     (HG 1 255 (map (fun v => mkAC BC_NE (SOff (xr 11) 0) (SLit v)) [9; 10; 13]) ltac:(lia)
        (ts_conds_ne _ (xr 11) cb [9; 10; 13] X11 ltac:(repeat constructor; lia)))) as [HS SH0].
3: destruct (ts_D1_entry_A _ Wc memc rg F R22 R26 Fb1 ltac:(lia) Fb3 Ffr Fsh
     (HG 13 13 (map (fun v => mkAC BC_EQ (SOff (xr 11) 0) (SLit v)) [13]) ltac:(lia)
        (ts_conds_eq _ (xr 11) cb [13] X11 ltac:(repeat constructor; lia)))) as [HS SH0].
2: destruct (ts_D1_entry_A _ Wc memc rg F R22 R26 Fb1 ltac:(lia) Fb3 Ffr Fsh
     (HG 10 10 (map (fun v => mkAC BC_EQ (SOff (xr 11) 0) (SLit v)) [10]) ltac:(lia)
        (ts_conds_eq _ (xr 11) cb [10] X11 ltac:(repeat constructor; lia)))) as [HS SH0].
1: destruct (ts_D1_entry_A _ Wc memc rg F R22 R26 Fb1 ltac:(lia) Fb3 Ffr Fsh
     (HG 9 9 (map (fun v => mkAC BC_EQ (SOff (xr 11) 0) (SLit v)) [9]) ltac:(lia)
        (ts_conds_eq _ (xr 11) cb [9] X11 ltac:(repeat constructor; lia)))) as [HS SH0].
all: pose proof (SH0 (SLit 0)) as SHOK.
all: pose proof HS as HSk.
all: paj_run_to_tok_xR RUNTO HS HJ SHOK (2 ^ 63, 2 ^ 63) (TS_PC_A + TS_H1_OFF_A).
all: try (lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 22) (F + 32)); [reflexivity | exact X22 | |];
  [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 0, pos;
    split; [left; reflexivity|];
    left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite <- EF; lia
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ (xr 26) (shadow_addr F)); [reflexivity | exact X26 | |];
    [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 0, pos;
      split; [left; reflexivity|];
      right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; rewrite <- EF; lia
    | apply awr_ok_nil ] ]).
all: assert (KN : YAkMemnorm.memnorm SEGS memc -> YAkMemnorm.memnorm SEGS (ms_mem ms))
  by (intros Hm; unshelve eapply (YGcallMxmn.memnorm_frame_of SEGS (w_H Wc) _ _ _ _ _ HSk HF); exact Hm).
all: clear HSk.
all: pmkst HS.
all: prreg HS (10%bv : bv 5) Q10; prreg HS (12%bv : bv 5) Q12; prreg HS (13%bv : bv 5) Q13.
all: assert (X43 : bv_unsigned (ew (TEa regs rg []) 43) = cb) by exact X11.
all: assert (X57 : bv_unsigned (ew (TEa regs rg []) 57) = TS_HEX_A) by exact X25.
all: assert (Hq16 : 0 <= cb / 16 < 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
all: assert (W13 : getr (ms_regs ms) 13 = w64 cb)
  by (rewrite Q13, (ts_alu_w64 ALU_AND _ _ cb 255 X43 ltac:(apply unsigned_lit_small; lia)), ts_zalu_and255 by lia;
      reflexivity).
all: assert (W10 : getr (ms_regs ms) 10 = w64 (TS_HEX_A + cb / 16))
  by (rewrite Q10, (ts_alu_w64 ALU_AND _ _ cb 255 X43 ltac:(apply unsigned_lit_small; lia)), ts_zalu_and255 by lia;
      rewrite (ts_alu_w64 ALU_SRL (w64 cb) (Z_to_bv 64 4) cb 4 ltac:(apply unsigned_lit_small; lia)
        ltac:(apply unsigned_lit_small; lia)), ts_zalu_srl4 by lia;
      rewrite (ts_alu_w64 ALU_ADD (ew (TEa regs rg []) 57) (w64 (cb / 16)) TS_HEX_A (cb / 16) X57
        ltac:(apply unsigned_lit_small; lia)), ts_zalu_add by lia;
      reflexivity).
all: assert (W12 : getr (ms_regs ms) 12 = w64 (ts_letter_A cb))
  by (rewrite Q12; unfold ts_letter_A, w64;
      repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end;
      first [reflexivity | exfalso; lia]).
all: assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr rg r)
  by (intros r Hr; cbv [In] in Hr; repeat (destruct Hr as [<- | Hr]; [tskeep HS |]); destruct Hr).
(* esc[0..3] and the frame's shadow byte 06, read off the regions the run leaves *)
all: assert (Hesc : garr8 SEGS (mrestrict (w_H Wc) (ms_mem ms)) (F + 32) [92; ts_letter_A cb; 48; 48])
  by (pose proof (ts_region_nth _ _ _ 0 _ HS eq_refl) as HR0; cbn [ms_mem restrict] in HR0;
      intros jj Hjj; cbn [length] in Hjj;
      destruct jj as [|[|[|[|jj]]]]; [| | | | lia]; cbn [nth Z.of_nat];
      [ pose proof (ts_field _ _ (xr 22) (F + 32) _ _ _ _ _ 0 1%N (SOff 50 0) HR0 X22
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
        rewrite ts_U0, (te_cur regs rg _ 18%bv 18) in V by reflexivity; rewrite R18 in V
      | lazymatch type of HR0 with YP09.region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
          let Lv := eval vm_compute in (ts_lit_at_A cs 1) in
          pose proof (ts_field _ _ (xr 22) (F + 32) _ _ _ _ _ 1 1%N (SLit Lv) HR0 X22
            ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
          replace (ts_letter_A cb) with Lv by (unfold ts_letter_A;
            repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end;
            first [reflexivity | exfalso; lia])
        end;
        rewrite U_SLit in V
      | pose proof (ts_field _ _ (xr 22) (F + 32) _ _ _ _ _ 2 1%N (SOff 59 0) HR0 X22
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
        rewrite ts_U0, (te_cur regs rg _ 27%bv 27) in V by reflexivity; rewrite R27 in V
      | pose proof (ts_field _ _ (xr 22) (F + 32) _ _ _ _ _ 3 1%N (SOff 59 0) HR0 X22
          ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
        rewrite ts_U0, (te_cur regs rg _ 27%bv 27) in V by reflexivity; rewrite R27 in V ];
      (unfold w64 in V; rewrite ?unsigned_lit_small in V by lia;
       change (N.to_nat 1) with 1%nat in V;
       split; [ rewrite ?YP0m.zcanon_small in V by lia;
                rewrite Z.mod_small in V by (cbn; lia); exact V
              | cbn; lia ])).
all: assert (H6 : aview SEGS (w_H Wc) (ms_mem ms) (shadow_addr F + 4) = Some 6)
  by (pose proof (ts_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
      pose proof (ts_field _ _ (xr 26) (shadow_addr F) _ _ _ _ _ 4 1%N (SLit 6) HR1 X26
        ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as V;
      rewrite U_SLit in V; change (6 mod 2 ^ 64 mod 2 ^ (8 * Z.of_N 1)) with 6 in V;
      change (N.to_nat 1) with 1%nat in V;
      exact (ts_aview_of_vm1 (w_H Wc) (ms_mem ms) _ 6 V ltac:(lia))).
(* the run's writes: esc[0..3] and the frame's shadow byte 4 *)
all: lazymatch type of HFr with frame_of _ ?rs0 _ _ =>
  assert (Hwr : forall a, in_wrange (TEa regs rg []) rs0 a -> (F + 32 <= a < F + 36 \/ a = shadow_addr F + 4))
    by (intros a (r & Hr & Ha); cbv [ss_D1_A ss_mem In] in Hr; destruct Hr as [<- | [<- | []]];
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha;
        [rewrite ts_bv_some, X22 in Ha; left; lia | rewrite ts_bv_some, X26 in Ha; right; lia]);
  pose proof (ts_live_runR (HSTK := HSTK_A) (LAWS := LAWS) (pst_img := pst_img_A) (pal_pst_static := pal_pst_static)
    WR lyc Sc Hpc Wc memc (ms_mem ms) mdc _ kj _ pos F b _ _ _ _ _ _ (in_wrange (TEa regs rg []) rs0) HL HJ HFr)
    as HL1 end.
all: specialize (HL1 ltac:(intros a HW; right; exists pos; split; [exact Hin|]; destruct (Hwr a HW) as [Hc1|Hc1];
  [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite <- EF; lia
  | right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8; rewrite <- EF; lia])).
all: specialize (HL1 ltac:(intros a HW; destruct (Hwr a HW) as [Hc1|Hc1];
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia)).
all: specialize (HL1 KN).
all: assert (HSP1 : spilla Wc (ms_mem ms) F) by (apply (ts_spill_keep Wc memc); [|exact HSP]; intros a Ha;
  apply (ts_keep Wc _ _ memc (ms_mem ms) (fun x => F + 32 <= x < F + 36 \/ x = shadow_addr F + 4) HFr Hwr a);
  unfold in_app, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *; lia).
all: clear HF HG HFr.
all: change (BASE + 16064) with (BASE + (TS_PC_A + TS_H1_OFF_A)).
all: assert (HLR1 : lregsa (ms_regs ms) F (Z.of_nat i)) by (unfold ts_lregs, ts_bregs;
  rewrite (KR 2%bv), (KR 3%bv), (KR 4%bv), (KR 8%bv), (KR 9%bv), (KR 18%bv), (KR 19%bv), (KR 20%bv), (KR 21%bv),
    (KR 22%bv), (KR 23%bv), (KR 24%bv), (KR 25%bv), (KR 26%bv), (KR 27%bv) by (cbv; tauto); exact HLR).
all: apply (ts_mid_A i cb (ts_letter_A cb) lyc Sc Hpc Wc (ms_mem ms) _ _ pos F b cap f own _ _ ap (ms_regs ms)
       ltac:(lia) (ts_letter_rng_A cb) HL1 HSP1 HLR1 ltac:(rewrite (KR 11%bv) by (cbv; tauto); exact R11)
       W12 W13 W10 Hesc H6).
all: intros memc' mdc' kj' rg' HL2 HSP2 HLR2 S11 S12 S10 Hesc5 H6'.
all: exact (ts_at_D_A i Wc lyc Sc Hpc memc' mdc' kj' pos F b cap f own ap rg' pre cb post HX IH Ebs Hlen HL2 HSP2
       HLR2 S11 S10 S12 Hesc5 H6').
Qed.

(* ---- one iteration, and the loop: the walk's measure is the bytes left ---- *)
Lemma ts_iter_A : ts_HX_A -> forall i Wc cf, ts_IH_A i -> LHa i Wc cf -> SRW Wc cf QFa.
Proof.
intros HX i Wc cf IH (lyc & Sc & Hpc & memc & mdc & kj & pos & F & b & cap & f & own & ap & rg & pre & cb & post & -> &
  Ebs & Hlen & HL & HSP & HLR & R11).
exact (ts_at_D1_A i Wc lyc Sc Hpc memc mdc kj pos F b cap f own ap rg pre cb post HX IH Ebs Hlen HL HSP HLR R11).
Qed.

Lemma ts_loop_A : ts_HX_A -> forall i Wc cf, LHa i Wc cf -> SRW Wc cf QFa.
Proof.
intros HX i. remember (length bs - i)%nat as n eqn:En. revert i En.
induction n as [n IHn] using (well_founded_induction lt_wf).
intros i En Wc cf HL. subst n.
apply (ts_iter_A HX i Wc cf); [|exact HL].
intros i' W' cf' Hm HL'. exact (IHn (length bs - i')%nat Hm i' eq_refl W' cf' HL').
Qed.

(* ---- the loop body, in the glue's ts_loop shape: one iteration from the loop head, to the loop head or to the
   closing quote's block ---- *)
Lemma ts_step_A : ts_HX_A -> forall i Wc cf, LHa i Wc cf ->
  SRW Wc cf (fun W' c' => QFa W' c' \/ exists i', (length bs - i' < length bs - i)%nat /\ LHa i' W' c').
Proof.
intros HX i Wc cf HL.
apply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf Wc cf QFa); [exact (ts_loop_A HX i Wc cf HL)|].
intros W' c' _ HQ. left. exact HQ.
Qed.
End g.
End f.
End w.

(* the audit: the standard axioms only *)
Print Assumptions ts_step_A.
