(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 4213 of its 4307 lines of code are new or changed and 684 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Crt102Rewrite.v, with its module paths and module names changed; 497 of its 546 lines of code are new or changed and 4258 lines of the source are left out. *)
(* fuzz_preset, file Crt102Img: the IMAGE FACTS of check_round_trip on the
   harness-fix #102 pins that a walk of tcheck_round_trip_specX (lib/A/PRH_FnCheck.v) reads off the listing, and the
   capacity discharge of its frame-area call. Image A' concretely (PI_prog_A, prh_img_A); image B' from the B listing
   and prh_img_B where those suffice, and PARAMETRIC over {PA : PAImg B_prog_listing} for the values only the B instance
   carries, because lib/B/PAImg_prog.v does not build (its B_prog_range fails at :160 until the image-top record sets
   IMG_TOP_B = 0x601000): those values are the Section b hypotheses HB_base / HB_entry / HB_segs / HB_relro / HB_hi,
   each with its B' value in a comment; every one is discharged by vm_compute at PI_prog_B once that file builds.
   The B' part (item 6 below) is lib/B/Prog/Crt102ImgB.v, moved there byte for byte so that no A-tree file Requires
   lib.B (the shipping pool's shadow audit; the unit owner's 06:40Z ruling). This file no longer Requires lib.B.

   INPUTS OF RECORD (taken by path):
   - pins: A' asan 1be0f53d96cb9d6c (unstripped twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin
     c90d4fa54d43160b).
   - branch base: first commit 3971724b617 (this file is written on 3a2bafc75c92, which re-takes
     the contract texts by path from 00b50c5745fb: lib/A/PRH_FnCheck.v 6f6bc83d7420;
     lib/A/PRH_Base.v 016934fdc1af, lib/A/PRH_Img.v 934516a622e8, lib/B/PRH_ImgB.v 3216eca68342 unchanged).
   - listings of record: lib/A/Listing_prog.v 1ab147923c5d, lib/A/PAImg_prog.v 47eeb54e93be, lib/B/Listing_prog.v
     8bcc2c9e7809, lib/B/PAImg_prog.v 4392ab2c09ba, lib/Reusable/YPsym.v b6f5a85d234d.
   - engine: the allocator engine's whole set by path from commit 459129c18903 (YG0dcf.v f2e11ac13457, YGcallScf.v
     f19b92982613, YG05.v).
   - segment cut: the walk's internal file DESIGN.md; listings of the body
     the walk's internal file crt.A.s (A' entry 0x82870, size 0x748) and the internal file crt.B.s (B' entry
     0x82828, size 0x880); source fuzz_preset.c (sha256
     c7b4007bba7bab3e).
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1, PAU
     the #102 pin set (pau-preset-102).
   - rule 24: no function proved (the proof-index lookup for check_round_trip, proof-index, exit 0): only the
     plain (lib/Prog) and ubsan (lib/U/Prog) proofs,
     concluding in SR, not consumable. Written new.

   WHAT IS HERE.
   0. Image-free checkers: hi_of / lo_of / res_pair read the address an auipc + addi (or auipc + load) pair computes
      off two instruction words; res_cert_add / res_cert_ld derive it from a listing certificate (YP0b pi_check), and
      pa_res_add / pa_res_ld at any PAImg instance against the instance's own instruction words (fetch_word over
      pa_segs, through pa_tbl_ok); str_at checks a string's bytes in the image (seg_rom).
   1. A': CRT_PC_A (4 * the function's slot) with crt_pc_A : BASE + CRT_PC_A = SIGMA AS_check_round_trip, one
      CRT_<cut>_OFF per cut of the internal file DESIGN.md plus four more (C3, Z5, ZS, RET; B' also UB), each with crt_cut_<cut>_A (its
      absolute pc as SIGMA + offset, and the listing entry at it), one CRT_<site>_CALL per jal of the body with
      crt_call_<site>_A (the listing's PCall and its callee), and crt_img_A: the generated prh_img_A's pi_call_rets /
      pi_ret_sites / pi_abort / pi_err_sites of check_round_trip ARE these offsets. crt_frame_A: the prologue's words
      decode to Crt102Glue's CRT_FRAME / CRT_ALIGN / CRT_REQ, and pi_frame = CRT_FRAME + (CRT_ALIGN - 16).
   2. crt102_cap / crt102_smx: the capacity premise of astack_malloc_realizes_cf 3 (YG0dcf.v:271-286, its line 274
      `count_cid cid (frames S) < fs_frames cid`) from the text's frames bound (PRH_FnCheck.v: ck_FRAMES_CAP,
      FR_check_round_trip), and the existential the call rule consumes, CITED from YGcallScf.v:100
      stack_malloc_x_any (proved there; its progress half is stack_malloc_progress_any :55, after cgif YG05.v:70,
      its post half stack_malloc_apath_post :83). The bound: YG05.v:47 count_cid_filter (count_cid is the length of a
      filter of the list), fs_frames 3 by computation.
   3. crt_stk_A / crt_stk_B: the stack allowances the call rules ask of STK_check_round_trip (PRH_Base.v:320),
      with pi_frame as the own frame; crt_sp1_off: the rules' sp offset o at every call (sp = Crt102Glue's CRT_sp1)
      is a multiple of 16 in [- pi_frame, 0].
   4. The two read-only strings rtt's rewrite passes: CRT_MOD_AT_A / CRT_STAMP_A := VAL (A_OBJ 2) + offset, the
      listing entries at every auipc / addi site (five on each image), the resolution of the image's instruction
      words at those sites, and the bytes ("modifiedAt" and "2026-10-25T00:00:00Z", each with its NUL).
   5. The image facts a journal needs, as lib/A/Prog/S1ImgA.v states them (prh_pst quantified, never enumerated),
      pa_hi <= 2 ^ 31, and the prologue's two GOT words (crt_got_A).
   6. B' (now lib/B/Prog/Crt102ImgB.v): the same, read from the internal file crt.B.s, and crt_offs_AB: which intra-function offsets
      agree on A' and B'.

   FINDINGS against the internal file DESIGN.md (the listing is the authority; each one is a lemma below):
   - Z is +0x348 (pj_free's return; prh_img_A's pi_call_rets F_check_round_trip F_pj_free starts with it), not +0x344
     (the jal pj_free itself).
   - The five string sites are auipc/addi pairs at +0x240/+0x244 (STAMP, pj_string), +0x268/+0x26c (MOD_AT, pj_set),
     +0x4c4/+0x4d4 (MOD_AT, the at-search strcmp; not in the slice brief), +0x65c/+0x660 (MOD_AT) and +0x6bc/+0x6c0
     (STAMP). The brief's +0x658 and +0x6b8 are the `ld a0, 0(a0)` before each auipc.
   - B' agrees with A' on E, P, H, M, R1, R2, T and on the calls at +0x6c / +0x190 / +0x1a0 / +0x1c0 only; every later
     offset differs (UBSan adds an alignment check at the start of T and pointer-overflow checks in the loops), and
     B' keeps different registers (crt_regs_A / crt_regs_B: doc s5 / s6, shadow base s10 / s11, F s11 / s3 with the
     frame call's result s3 / s7, -8 s7 / s9).

   NUMERALS. DERIVED: every *_OFF / *_CALL / *_HI / *_LO (4 * the slot inside the function, read off the internal file crt.A.s / the internal file crt.B.s
   and checked against the listing here), CRT_SLOT_B 1111 = (0x82828 - B_prog_base) / 4, the string offsets 0x110c0 /
   0x11380 from pa_val (A_OBJ 2) (the listing's PAddHi payloads), the +4 of a return site, 2048 = fs_frames 3.
   LENGTH: 16 (the ABI's sp alignment in pi_frame's convention), 2 ^ 31. WORD: the listing entries (PW words, register
   numbers, A_HI / A_OBJ indices), the decoded immediates, 0 (NUL), 3 (the frame class). No ADDRESS literal: every
   code address is pa_sigma / pa_val of a listing, B_prog_base, or a prh_img_* field. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YP0m YP02 YP0b YPsym YImgTop YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG05 YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Glue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

(* split a conjunction only (never an equality) *)
Ltac csplit := repeat lazymatch goal with |- _ /\ _ => split end.

(* ======================================================================================================== *)
(* 0. image-free checkers                                                                                     *)

(* the high half: an auipc word at pc (its destination register and the value it writes) *)
Definition hi_of (fetch : Z -> option (bv 32)) (pc : Z) : option (bv 5 * Z) :=
  match fetch pc with
  | Some w =>
      match decode_any w with
      | Some (Auipc rd imm, isz) => if isz =? 4 then Some (rd, auipc_val pc imm) else None
      | _ => None
      end
  | None => None
  end.
(* the low half: an addi or a load word at pc (its base register and its signed immediate) *)
Definition lo_of (fetch : Z -> option (bv 32)) (pc : Z) : option (bv 5 * Z) :=
  match fetch pc with
  | Some w =>
      match decode_any w with
      | Some (OpImm ALU_ADD _ rs imm, isz) => if isz =? 4 then Some (rs, bv_signed imm) else None
      | Some (Load _ _ _ rs imm, isz) => if isz =? 4 then Some (rs, bv_signed imm) else None
      | _ => None
      end
  | None => None
  end.
(* the address the pair computes, when the low half's base is the high half's destination *)
Definition res_pair (fetch : Z -> option (bv 32)) (pc_hi pc_lo : Z) : option Z :=
  match hi_of fetch pc_hi, lo_of fetch pc_lo with
  | Some (rd, hv), Some (rs, lv) => if bv_eqb rd rs then Some (hv + lv) else None
  | _, _ => None
  end.
(* the two word sources: a word table (YP02's ctable, as YP0b's pi_check reads it) and the image's own fetch *)
Definition zf (fetch : Z -> option Z) : Z -> option (bv 32) := fun pc => option_map (Z_to_bv 32) (fetch pc).
Definition tblf (t : ctable) : Z -> option (bv 32) := zf (clookup t).
Definition segf (segs : list Segment) : Z -> option (bv 32) := fun pc => fetch_word segs (Z_to_bv 64 pc).

Lemma hi_of_tbl : forall segs t, table_ok segs t -> forall p r, hi_of (tblf t) p = Some r -> hi_of (segf segs) p = Some r.
Proof.
intros segs t Ht p r H. unfold hi_of, tblf, zf, segf in *. cbv beta in H |- *.
destruct (clookup t p) as [w|] eqn:E; cbn [option_map] in H; [|discriminate H].
rewrite (Ht p w E). exact H.
Qed.
Lemma lo_of_tbl : forall segs t, table_ok segs t -> forall p r, lo_of (tblf t) p = Some r -> lo_of (segf segs) p = Some r.
Proof.
intros segs t Ht p r H. unfold lo_of, tblf, zf, segf in *. cbv beta in H |- *.
destruct (clookup t p) as [w|] eqn:E; cbn [option_map] in H; [|discriminate H].
rewrite (Ht p w E). exact H.
Qed.
Lemma res_pair_tbl : forall segs t, table_ok segs t -> forall p1 p2 x,
  res_pair (tblf t) p1 p2 = Some x -> res_pair (segf segs) p1 p2 = Some x.
Proof.
intros segs t Ht p1 p2 x H. unfold res_pair in *.
destruct (hi_of (tblf t) p1) as [[rd hv]|] eqn:E1; [|cbv beta iota in H; discriminate H].
destruct (lo_of (tblf t) p2) as [[rs lv]|] eqn:E2; [|cbv beta iota in H; discriminate H].
rewrite (hi_of_tbl segs t Ht p1 _ E1), (lo_of_tbl segs t Ht p2 _ E2). exact H.
Qed.

Lemma bv_eqb_trans3 : forall (a b c : bv 5), bv_eqb a b = true -> bv_eqb a c = true -> bv_eqb b c = true.
Proof. intros a b c H1 H2. unfold bv_eqb in *. apply Z.eqb_eq in H1, H2. apply Z.eqb_eq. lia. Qed.

(* the pair's address from a listing certificate: a PHi entry and the PAddHi entry over its register *)
Lemma res_cert_add : forall (fetch : Z -> option Z) (val : nat -> Z) (sigma : asym -> Z) (L : ptable asym)
  k1 k2 (rd rd' : bv 5) j a off,
  pi_check asym fetch val sigma L = true ->
  plookup_list asym L k1 = Some (PHi rd j) -> plookup_list asym L k2 = Some (PAddHi rd' rd j a off) ->
  res_pair (zf fetch) (val A_TEXT + k1) (val A_TEXT + k2) = Some (val a + off).
Proof.
intros fetch val sigma L k1 k2 rd rd' j a off HC H1 H2.
pose proof (pi_check_lookup asym fetch val sigma L k1 _ HC H1) as C1.
pose proof (pi_check_lookup asym fetch val sigma L k2 _ HC H2) as C2.
unfold pi_slot_check in C1, C2. cbv zeta beta iota in C1, C2.
unfold res_pair, hi_of, lo_of, zf. cbv beta.
destruct (fetch (val A_TEXT + k1)) as [w1|]; cbn [option_map]; cbv beta iota in C1 |- *; [|discriminate C1].
destruct (fetch (val A_TEXT + k2)) as [w2|]; cbn [option_map]; cbv beta iota in C2 |- *; [|discriminate C2].
destruct (decode_any (Z_to_bv 32 w1)) as [[i1 s1]|]; cbv beta iota in C1 |- *; [|discriminate C1].
destruct (decode_any (Z_to_bv 32 w2)) as [[i2 s2]|]; cbv beta iota in C2 |- *; [|discriminate C2].
apply andb_prop in C1 as [S1 C1]. apply andb_prop in C2 as [S2 C2].
destruct i1; cbv beta iota in C1; try discriminate C1.
destruct i2; cbv beta iota in C2; try discriminate C2.
destruct op; cbv beta iota in C2; try discriminate C2.
cbv beta iota. rewrite S1, S2. cbv beta iota.
apply andb_prop in C1 as [R1 E1]. apply andb_prop in C2 as [R2 E2]. apply andb_prop in R2 as [_ R2].
rewrite (bv_eqb_trans3 _ _ _ R1 R2). cbv beta iota. apply Z.eqb_eq in E1, E2. f_equal. lia.
Qed.
(* the same for a PLdHi entry (an auipc / load pair; the address is the load's) *)
Lemma res_cert_ld : forall (fetch : Z -> option Z) (val : nat -> Z) (sigma : asym -> Z) (L : ptable asym)
  k1 k2 (rd rd' : bv 5) j a off sz sg,
  pi_check asym fetch val sigma L = true ->
  plookup_list asym L k1 = Some (PHi rd j) -> plookup_list asym L k2 = Some (PLdHi rd' rd j a off sz sg) ->
  res_pair (zf fetch) (val A_TEXT + k1) (val A_TEXT + k2) = Some (val a + off).
Proof.
intros fetch val sigma L k1 k2 rd rd' j a off sz sg HC H1 H2.
pose proof (pi_check_lookup asym fetch val sigma L k1 _ HC H1) as C1.
pose proof (pi_check_lookup asym fetch val sigma L k2 _ HC H2) as C2.
unfold pi_slot_check in C1, C2. cbv zeta beta iota in C1, C2.
unfold res_pair, hi_of, lo_of, zf. cbv beta.
destruct (fetch (val A_TEXT + k1)) as [w1|]; cbn [option_map]; cbv beta iota in C1 |- *; [|discriminate C1].
destruct (fetch (val A_TEXT + k2)) as [w2|]; cbn [option_map]; cbv beta iota in C2 |- *; [|discriminate C2].
destruct (decode_any (Z_to_bv 32 w1)) as [[i1 s1]|]; cbv beta iota in C1 |- *; [|discriminate C1].
destruct (decode_any (Z_to_bv 32 w2)) as [[i2 s2]|]; cbv beta iota in C2 |- *; [|discriminate C2].
apply andb_prop in C1 as [S1 C1]. apply andb_prop in C2 as [S2 C2].
destruct i1; cbv beta iota in C1; try discriminate C1.
destruct i2; cbv beta iota in C2; try discriminate C2.
cbv beta iota. rewrite S1, S2. cbv beta iota.
apply andb_prop in C1 as [R1 E1]. apply andb_prop in C2 as [R2 E2].
apply andb_prop in R2 as [R2 _]. apply andb_prop in R2 as [R2 _]. apply andb_prop in R2 as [_ R2].
rewrite (bv_eqb_trans3 _ _ _ R1 R2). cbv beta iota. apply Z.eqb_eq in E1, E2. f_equal. lia.
Qed.

Section pa. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
(* at any instance, against the instance's own instruction words (fetch_word over pa_segs) *)
Lemma pa_res_add : forall k1 k2 (rd rd' : bv 5) j a off,
  plookup_list asym L k1 = Some (PHi rd j) -> plookup_list asym L k2 = Some (PAddHi rd' rd j a off) ->
  res_pair (segf pa_segs) (pa_val A_TEXT + k1) (pa_val A_TEXT + k2) = Some (pa_val a + off).
Proof.
intros k1 k2 rd rd' j a off H1 H2. apply (res_pair_tbl pa_segs pa_tbl pa_tbl_ok).
exact (res_cert_add (clookup pa_tbl) pa_val pa_sigma L k1 k2 rd rd' j a off pa_cert H1 H2).
Qed.
Lemma pa_res_ld : forall k1 k2 (rd rd' : bv 5) j a off sz sg,
  plookup_list asym L k1 = Some (PHi rd j) -> plookup_list asym L k2 = Some (PLdHi rd' rd j a off sz sg) ->
  res_pair (segf pa_segs) (pa_val A_TEXT + k1) (pa_val A_TEXT + k2) = Some (pa_val a + off).
Proof.
intros k1 k2 rd rd' j a off sz sg H1 H2. apply (res_pair_tbl pa_segs pa_tbl pa_tbl_ok).
exact (res_cert_ld (clookup pa_tbl) pa_val pa_sigma L k1 k2 rd rd' j a off sz sg pa_cert H1 H2).
Qed.
End pa.

(* a byte string at p in the image's read-only view *)
Fixpoint str_at (segs : list Segment) (p : Z) (s : list Z) : bool :=
  match s with
  | [] => true
  | c :: s' =>
      match YK11.seg_rom segs (Z_to_bv 64 p) with
      | Some b => (bv_unsigned b =? c) && str_at segs (p + 1) s'
      | None => false
      end
  end.
Lemma str_at_sound : forall segs s p, str_at segs p s = true -> forall j, (j < length s)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (p + Z.of_nat j))) = Some (nth j s 0).
Proof.
intros segs s. induction s as [|c s IH]; intros p H j Hj; cbn [length] in Hj; [lia|].
cbn [str_at] in H. destruct (YK11.seg_rom segs (Z_to_bv 64 p)) as [b|] eqn:E; cbv beta iota in H; [|discriminate H].
apply andb_prop in H as [Hc Hs]. apply Z.eqb_eq in Hc.
destruct j as [|j].
- replace (p + Z.of_nat 0) with p by lia. rewrite E. cbn [option_map nth]. rewrite Hc. reflexivity.
- cbn [nth]. replace (p + Z.of_nat (Datatypes.S j)) with (p + 1 + Z.of_nat j) by lia. apply IH; [exact Hs | lia].
Qed.

(* an OpImm / a Load word of a listing slot, decoded: (op, rd, rs1, signed imm) / (size, signed, rd, rs1, imm) *)
Definition opimm_at (L : ptable asym) (k : Z) : option (aluop * Z * Z * Z) :=
  match plookup_list asym L k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (OpImm op rd rs imm, isz) =>
          if isz =? 4 then Some (op, bv_unsigned rd, bv_unsigned rs, bv_signed imm) else None
      | _ => None
      end
  | _ => None
  end.
Definition load_at (L : ptable asym) (k : Z) : option (msize * bool * Z * Z * Z) :=
  match plookup_list asym L k with
  | Some (PW w) =>
      match decode_any (Z_to_bv 32 w) with
      | Some (Load sz sg rd rs imm, isz) =>
          if isz =? 4 then Some (sz, sg, bv_unsigned rd, bv_unsigned rs, bv_signed imm) else None
      | _ => None
      end
  | _ => None
  end.

(* ======================================================================================================== *)
(* 2. THE CAPACITY PREMISE of astack_malloc_realizes_cf 3 (YG0dcf.v:271-286, line 274), and the existential the
   frame-area call rule consumes (cited: YGcallScf.v:100 stack_malloc_x_any)                                  *)

Lemma crt_filter_len : forall (f : Z * Z -> bool) (l : list (Z * Z)), (length (List.filter f l) <= length l)%nat.
Proof.
intros f l. induction l as [|x l IH]; cbn [List.filter length]; [apply le_n|].
destruct (f x); cbn [length]; [apply le_n_S; exact IH | apply le_S; exact IH].
Qed.

Lemma crt102_cap : forall S, Z.of_nat (length (frames S)) <= PRH_FnCheck.ck_FRAMES_CAP - PRH_FnCheck.FR_check_round_trip ->
  count_cid 3 (frames S) < fs_frames 3.
Proof.
intros S H. rewrite YG05.count_cid_filter.
pose proof (crt_filter_len (fun cp => fst cp =? 3) (frames S)) as HL.
assert (HF : fs_frames 3 = 2048) by (vm_compute; reflexivity).
assert (HC : PRH_FnCheck.ck_FRAMES_CAP = 64) by reflexivity.
assert (HR : 0 <= PRH_FnCheck.FR_check_round_trip).
{ unfold PRH_FnCheck.FR_check_round_trip, PRH_FnCheck.FR_round_trip_text, PRH_FnCheck.FR_pj_parse. lia. }
rewrite HF. rewrite HC in H. lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma crt102_smx : forall segs (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
  ly S Hp W mem md, ARx ly S Hp W mem md -> count_cid 3 (frames S) < fs_frames 3 ->
  exists pos S', apath (stack_malloc 3 S) [] (PFake 3 pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (3, pos) :: frames S /\ ~ In (3, pos) (frames S).
Proof.
intros segs ARx ly S Hp W mem md HAR Hc.
exact (YGcallScf.stack_malloc_x_any segs ARx ly S Hp W mem md 3 HAR ltac:(lia) Hc).
Qed.
End s.

(* the call rules' stack premise (YGcallSx.v:76 / :152, and every call rule of the engine): `spZ regsT = sp0 + o ->
   o mod 16 = 0 -> o <= 0 -> STK_callee - o <= STK`. At every call of check_round_trip sp is Crt102Glue.CRT_sp1 =
   (sp0 - CRT_FRAME) / CRT_ALIGN * CRT_ALIGN (the fake-frame path; the alloca fallback is unreachable), so for the
   16-aligned entry sp the rule's o is a multiple of 16 in [- (CRT_FRAME + (CRT_ALIGN - 16)), 0]: the own frame of
   crt_stk_A / crt_stk_B is pi_frame (crt_frame_A / crt_frame_B) *)
Lemma crt_sp1_off : forall sp0, sp0 mod 16 = 0 ->
  ((sp0 - Crt102Glue.CRT_FRAME) / Crt102Glue.CRT_ALIGN * Crt102Glue.CRT_ALIGN - sp0) mod 16 = 0 /\
  - (Crt102Glue.CRT_FRAME + (Crt102Glue.CRT_ALIGN - 16)) <=
    (sp0 - Crt102Glue.CRT_FRAME) / Crt102Glue.CRT_ALIGN * Crt102Glue.CRT_ALIGN - sp0 <= 0.
Proof.
intros sp0 H. unfold Crt102Glue.CRT_FRAME, Crt102Glue.CRT_ALIGN.
pose proof (Z.div_mod (sp0 - 224) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp0 - 224) 32 ltac:(lia)) as R.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16. rewrite H, Z.add_0_r in D16.
assert (Hr : (sp0 - 224) mod 32 = 0 \/ (sp0 - 224) mod 32 = 16) by lia.
replace ((sp0 - 224) / 32 * 32 - sp0) with (- 224 - (sp0 - 224) mod 32) by lia.
destruct Hr as [E | E]; rewrite E; split; [reflexivity | lia | reflexivity | lia].
Qed.

(* ======================================================================================================== *)
(* 1. image A': the entry, the cut, the call sites                                                            *)

Definition CRT_PC_A : Z := 4 * Z.of_nat (A_prog_slot AS_check_round_trip).
(* the cut of the internal file DESIGN.md (offsets from the entry; the comment gives A' = BASE + CRT_PC_A + offset) *)
Definition CRT_E_OFF : Z := 0x0.    (* 0x82870: prologue: addi sp,sp,-0xe0; 13 saves; s0 = sp0; andi sp,sp,-0x20; GOT loads; flag test *)
Definition CRT_P_OFF : Z := 0x70.   (* 0x828e0: __asan_stack_malloc_3's return: mv s3, a0 *)
Definition CRT_H_OFF : Z := 0xa0.   (* 0x82910: sd s11,0x70(s1): the frame F spilled; frame header and the 40 shadow bytes *)
Definition CRT_M_OFF : Z := 0x194.  (* 0x82a04: __asan_memset's return: a0 = doc, a1 = 0, a2 = &copy *)
Definition CRT_R1_OFF : Z := 0x1a4. (* 0x82a14: rtt1's return: beqz a0 (arm C1 otherwise) *)
Definition CRT_R2_OFF : Z := 0x1c4. (* 0x82a34: rtt2's return: bnez a0 -> J (arm C2) *)
Definition CRT_T_OFF : Z := 0x1c8.  (* 0x82a38: doc shadow check, doc->type == 6 test (arm C3 otherwise) *)
Definition CRT_U_OFF : Z := 0x1e4.  (* 0x82a54: unpoison of back / v, &doc->n, doc->n *)
Definition CRT_G_OFF : Z := 0x250.  (* 0x82ac0: pj_string's return *)
Definition CRT_C3_OFF : Z := 0x260. (* 0x82ad0: arm C3: s6 = 0, j J *)
Definition CRT_K_OFF : Z := 0x27c.  (* 0x82aec: pj_set's return: s8 = seqz a0 *)
Definition CRT_O1_OFF : Z := 0x280. (* 0x82af0: the flag tests g_own_ran_out / fuzz_alloc_ran_out (arm C4a), beqz s8 -> AB *)
Definition CRT_W_OFF : Z := 0x2b4.  (* 0x82b24: pj_write's return: s8 = saved *)
Definition CRT_N_OFF : Z := 0x2e4.  (* 0x82b54: parse_noting's return: s6 = snez a0 *)
Definition CRT_O2_OFF : Z := 0x2e8. (* 0x82b58: the flag tests after the read-back; beqz -> L0 *)
Definition CRT_FF_OFF : Z := 0x2f8. (* 0x82b68: arm C4c: fuzz_free (saved), s6 = 1 *)
Definition CRT_X_OFF : Z := 0x304.  (* 0x82b74: the shared re-poison of back / v *)
Definition CRT_J_OFF : Z := 0x340.  (* 0x82bb0: the join: a0 = &copy, jal pj_free *)
Definition CRT_Z_OFF : Z := 0x348.  (* 0x82bb8: pj_free's return: poison of copy, the retired magic, beqz s3 *)
Definition CRT_Z5_OFF : Z := 0x380. (* 0x82bf0: __asan_set_shadow_f5's return: the flag store ld a0,0x1f8(s3); sb zero,0(a0) *)
Definition CRT_ZS_OFF : Z := 0x38c. (* 0x82bfc: the stack-path retire (beqz s3 taken): the 40 shadow bytes zeroed *)
Definition CRT_Q_OFF : Z := 0x42c.  (* 0x82c9c: a0 = s6, the 13 restores *)
Definition CRT_RET_OFF : Z := 0x46c. (* 0x82cdc: ret *)
Definition CRT_L0_OFF : Z := 0x470. (* 0x82ce0: bnez s6 -> AB; the at-search set-up *)
Definition CRT_L1_OFF : Z := 0x4e0. (* 0x82d50: the at-search loop head (strcmp (doc->keys[i], MOD_AT)) *)
Definition CRT_L2_OFF : Z := 0x528. (* 0x82d98: back.n test, the member loop set-up *)
Definition CRT_L3_OFF : Z := 0x590. (* 0x82e00: the member loop head (strcmp keys, same kids) *)
Definition CRT_C_OFF : Z := 0x634.  (* 0x82ea4: the final checks (MOD_AT key, type 4, STAMP) *)
Definition CRT_AB_OFF : Z := 0x6f8. (* 0x82f68: the abort tail: jal __asan_handle_no_return; jal abort *)
(* the jal sites of the body (a return site is the site + 4) *)
Definition CRT_SM3_CALL : Z := 0x6c. (* 0x828dc: jal __asan_stack_malloc_3 *)
Definition CRT_MEMSET_CALL : Z := 0x190. (* 0x82a00: jal __asan_memset *)
Definition CRT_RTT1_CALL : Z := 0x1a0. (* 0x82a10: jal round_trip_text *)
Definition CRT_RTT2_CALL : Z := 0x1c0. (* 0x82a30: jal round_trip_text *)
Definition CRT_PJSTR_CALL : Z := 0x24c. (* 0x82abc: jal pj_string *)
Definition CRT_PJSET_CALL : Z := 0x278. (* 0x82ae8: jal pj_set *)
Definition CRT_RO1_CALL : Z := 0x290. (* 0x82b00: jal fuzz_alloc_ran_out *)
Definition CRT_PJW_CALL : Z := 0x2b0. (* 0x82b20: jal pj_write *)
Definition CRT_RO2_CALL : Z := 0x2c4. (* 0x82b34: jal fuzz_alloc_ran_out *)
Definition CRT_STRLEN_CALL : Z := 0x2d0. (* 0x82b40: jal __wrap_strlen *)
Definition CRT_PN_CALL : Z := 0x2e0. (* 0x82b50: jal parse_noting *)
Definition CRT_RO3_CALL : Z := 0x2f0. (* 0x82b60: jal fuzz_alloc_ran_out *)
Definition CRT_FF1_CALL : Z := 0x2fc. (* 0x82b6c: jal fuzz_free *)
Definition CRT_PJF1_CALL : Z := 0x344. (* 0x82bb4: jal pj_free *)
Definition CRT_SSF5_CALL : Z := 0x37c. (* 0x82bec: jal __asan_set_shadow_f5 *)
Definition CRT_CMP1_CALL : Z := 0x4f8. (* 0x82d68: jal __wrap_strcmp *)
Definition CRT_CMP2_CALL : Z := 0x5bc. (* 0x82e2c: jal __wrap_strcmp *)
Definition CRT_SAME_CALL : Z := 0x5f0. (* 0x82e60: jal same *)
Definition CRT_CMP3_CALL : Z := 0x664. (* 0x82ed4: jal __wrap_strcmp *)
Definition CRT_CMP4_CALL : Z := 0x6c4. (* 0x82f34: jal __wrap_strcmp *)
Definition CRT_FF2_CALL : Z := 0x6d0. (* 0x82f40: jal fuzz_free *)
Definition CRT_PJF2_CALL : Z := 0x6d8. (* 0x82f48: jal pj_free *)
Definition CRT_HNR_CALL : Z := 0x6f8. (* 0x82f68: jal __asan_handle_no_return *)
Definition CRT_ABORT_CALL : Z := 0x6fc. (* 0x82f6c: jal abort *)
(* the prologue's two GOT reads: the shadow-base variable's GOT word (auipc a1 / ld a1, 0x758(a1), then
   ld s10, 0(a1) at +0x5c) and the use-after-return flag's GOT word (auipc a2 / ld a2, 0x7ac(a2), then
   lw a2, 0(a2) at +0x58; beqz a2 at +0x64 skips the frame call) *)
Definition CRT_GOT_SHB_HI : Z := 0x48.   Definition CRT_GOT_SHB_LO : Z := 0x54.
Definition CRT_GOT_UAR_HI : Z := 0x4c.   Definition CRT_GOT_UAR_LO : Z := 0x50.
Definition CRT_FLAG_LW : Z := 0x58.      Definition CRT_SHB_LD : Z := 0x5c.
(* the string sites (auipc / addi), A' *)
Definition CRT_STAMP1_HI : Z := 0x240.   Definition CRT_STAMP1_LO : Z := 0x244.
Definition CRT_MODAT1_HI : Z := 0x268.   Definition CRT_MODAT1_LO : Z := 0x26c.
Definition CRT_MODAT2_HI : Z := 0x4c4.   Definition CRT_MODAT2_LO : Z := 0x4d4.
Definition CRT_MODAT3_HI : Z := 0x65c.   Definition CRT_MODAT3_LO : Z := 0x660.
Definition CRT_STAMP2_HI : Z := 0x6bc.   Definition CRT_STAMP2_LO : Z := 0x6c0.
(* the two strings' offsets from pa_val (A_OBJ 2), the listing's PAddHi payloads (the same on B') *)
Definition CRT_MOD_AT_OFF : Z := 0x110c0.
Definition CRT_STAMP_OFF : Z := 0x11380.
(* the two strings with their NUL, as the text spells them (PRH_FnCheck.v ck_MOD_AT / ck_STAMP) *)
Definition CRT_MOD_AT_S : list Z := PRH_FnCheck.ck_MOD_AT ++ [0].
Definition CRT_STAMP_S : list Z := PRH_FnCheck.ck_STAMP ++ [0].
(* the report jal sites (prh_img_A's pi_err_sites), A' *)
Definition CRT_ERR_OFFS : list Z := [0x6f4; 0x70c; 0x710; 0x714; 0x71c; 0x724; 0x72c; 0x734; 0x738; 0x73c; 0x740; 0x744].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := (PI_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Notation FRA := (@pi_frame prh_img_A F_check_round_trip).
#[local] Notation STKC := (@STK_check_round_trip prh_img_A).
#[local] Notation AT o := (BASE + (CRT_PC_A + o)).

Lemma crt_pc_A : BASE + CRT_PC_A = SIGMA AS_check_round_trip.
Proof. vm_compute. reflexivity. Qed.
Lemma crt_cut_pc_A : forall off, BASE + (CRT_PC_A + off) = SIGMA AS_check_round_trip + off.
Proof. intros off. rewrite <- crt_pc_A. lia. Qed.
(* the frame header's pc word (+0xb0 / +0xc4: auipc a2, 0; addi a2, a2, -0xb0) is the listing's A_TEXT + CRT_PC_A *)
Lemma crt_pc_hdr_A : plookup_list asym A_prog_listing (CRT_PC_A + 0xc4) =
  Some (PAddHi (12%bv : bv 5) (12%bv : bv 5) 32 A_TEXT CRT_PC_A).
Proof. vm_compute. reflexivity. Qed.

Lemma crt_cut_E_A : BASE + (CRT_PC_A + CRT_E_OFF) = SIGMA AS_check_round_trip + CRT_E_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_E_OFF) = Some (PW 0xf2010113).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_P_A : BASE + (CRT_PC_A + CRT_P_OFF) = SIGMA AS_check_round_trip + CRT_P_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_P_OFF) = Some (PW 0x50993).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_H_A : BASE + (CRT_PC_A + CRT_H_OFF) = SIGMA AS_check_round_trip + CRT_H_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_H_OFF) = Some (PW 0x7b4b823).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_M_A : BASE + (CRT_PC_A + CRT_M_OFF) = SIGMA AS_check_round_trip + CRT_M_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_M_OFF) = Some (PW 0xa8513).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_R1_A : BASE + (CRT_PC_A + CRT_R1_OFF) = SIGMA AS_check_round_trip + CRT_R1_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_R1_OFF) = Some (PW 0x50663).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_R2_A : BASE + (CRT_PC_A + CRT_R2_OFF) = SIGMA AS_check_round_trip + CRT_R2_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_R2_OFF) = Some (PW 0x16051e63).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_T_A : BASE + (CRT_PC_A + CRT_T_OFF) = SIGMA AS_check_round_trip + CRT_T_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_T_OFF) = Some (PW 0x3ad513).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_U_A : BASE + (CRT_PC_A + CRT_U_OFF) = SIGMA AS_check_round_trip + CRT_U_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_U_OFF) = Some (PW 0x90223).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_G_A : BASE + (CRT_PC_A + CRT_G_OFF) = SIGMA AS_check_round_trip + CRT_G_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_G_OFF) = Some (PW 0x584b423).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_C3_A : BASE + (CRT_PC_A + CRT_C3_OFF) = SIGMA AS_check_round_trip + CRT_C3_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_C3_OFF) = Some (PW 0xb13).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_K_A : BASE + (CRT_PC_A + CRT_K_OFF) = SIGMA AS_check_round_trip + CRT_K_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_K_OFF) = Some (PW 0x153c13).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_O1_A : BASE + (CRT_PC_A + CRT_O1_OFF) = SIGMA AS_check_round_trip + CRT_O1_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_O1_OFF) = Some (PHi (25%bv : bv 5) 35).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_W_A : BASE + (CRT_PC_A + CRT_W_OFF) = SIGMA AS_check_round_trip + CRT_W_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_W_OFF) = Some (PW 0x50c13).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_N_A : BASE + (CRT_PC_A + CRT_N_OFF) = SIGMA AS_check_round_trip + CRT_N_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_N_OFF) = Some (PW 0xa03b33).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_O2_A : BASE + (CRT_PC_A + CRT_O2_OFF) = SIGMA AS_check_round_trip + CRT_O2_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_O2_OFF) = Some (PW 0xa50cc503).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_FF_A : BASE + (CRT_PC_A + CRT_FF_OFF) = SIGMA AS_check_round_trip + CRT_FF_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_FF_OFF) = Some (PW 0xc0513).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_X_A : BASE + (CRT_PC_A + CRT_X_OFF) = SIGMA AS_check_round_trip + CRT_X_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_X_OFF) = Some (PW 0xff800513).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_J_A : BASE + (CRT_PC_A + CRT_J_OFF) = SIGMA AS_check_round_trip + CRT_J_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_J_OFF) = Some (PW 0xa0513).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_Z_A : BASE + (CRT_PC_A + CRT_Z_OFF) = SIGMA AS_check_round_trip + CRT_Z_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_Z_OFF) = Some (PW 0x1790e23).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_Z5_A : BASE + (CRT_PC_A + CRT_Z5_OFF) = SIGMA AS_check_round_trip + CRT_Z5_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_Z5_OFF) = Some (PW 0x1f89b503).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_ZS_A : BASE + (CRT_PC_A + CRT_ZS_OFF) = SIGMA AS_check_round_trip + CRT_ZS_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_ZS_OFF) = Some (PW 0x90223).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_Q_A : BASE + (CRT_PC_A + CRT_Q_OFF) = SIGMA AS_check_round_trip + CRT_Q_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_Q_OFF) = Some (PW 0xb0513).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_RET_A : BASE + (CRT_PC_A + CRT_RET_OFF) = SIGMA AS_check_round_trip + CRT_RET_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_RET_OFF) = Some (PW 0x8067).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_L0_A : BASE + (CRT_PC_A + CRT_L0_OFF) = SIGMA AS_check_round_trip + CRT_L0_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_L0_OFF) = Some (PW 0x280b1463).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_L1_A : BASE + (CRT_PC_A + CRT_L1_OFF) = SIGMA AS_check_round_trip + CRT_L1_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_L1_OFF) = Some (PW 0x484b503).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_L2_A : BASE + (CRT_PC_A + CRT_L2_OFF) = SIGMA AS_check_round_trip + CRT_L2_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_L2_OFF) = Some (PW 0x2c4b023).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_L3_A : BASE + (CRT_PC_A + CRT_L3_OFF) = SIGMA AS_check_round_trip + CRT_L3_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_L3_OFF) = Some (PW 0xac683).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_C_A : BASE + (CRT_PC_A + CRT_C_OFF) = SIGMA AS_check_round_trip + CRT_C_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_C_OFF) = Some (PW 0x384b503).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.
Lemma crt_cut_AB_A : BASE + (CRT_PC_A + CRT_AB_OFF) = SIGMA AS_check_round_trip + CRT_AB_OFF /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_AB_OFF) = Some (PCall AS___asan_handle_no_return (1%bv : bv 5)).
Proof. split; [apply crt_cut_pc_A | vm_compute; reflexivity]. Qed.

Lemma crt_call_SM3_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_SM3_CALL) = Some (PCall AS___asan_stack_malloc_3 (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_MEMSET_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_MEMSET_CALL) = Some (PCall AS___asan_memset (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RTT1_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_RTT1_CALL) = Some (PCall AS_round_trip_text (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RTT2_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_RTT2_CALL) = Some (PCall AS_round_trip_text (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJSTR_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_PJSTR_CALL) = Some (PCall AS_pj_string (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJSET_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_PJSET_CALL) = Some (PCall AS_pj_set (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RO1_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_RO1_CALL) = Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJW_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_PJW_CALL) = Some (PCall AS_pj_write (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RO2_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_RO2_CALL) = Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_STRLEN_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_STRLEN_CALL) = Some (PCall AS___wrap_strlen (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PN_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_PN_CALL) = Some (PCall AS_parse_noting (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_RO3_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_RO3_CALL) = Some (PCall AS_fuzz_alloc_ran_out (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_FF1_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_FF1_CALL) = Some (PCall AS_fuzz_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJF1_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_PJF1_CALL) = Some (PCall AS_pj_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_SSF5_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_SSF5_CALL) = Some (PCall AS___asan_set_shadow_f5 (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP1_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_CMP1_CALL) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP2_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_CMP2_CALL) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_SAME_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_SAME_CALL) = Some (PCall AS_same (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP3_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_CMP3_CALL) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_CMP4_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_CMP4_CALL) = Some (PCall AS___wrap_strcmp (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_FF2_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_FF2_CALL) = Some (PCall AS_fuzz_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_PJF2_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_PJF2_CALL) = Some (PCall AS_pj_free (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_HNR_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_HNR_CALL) = Some (PCall AS___asan_handle_no_return (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Lemma crt_call_ABORT_A : plookup_list asym A_prog_listing (CRT_PC_A + CRT_ABORT_CALL) = Some (PCall AS_abort (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.

(* the generated image table names exactly these return sites, this abort tail and these report sites *)
Lemma crt_img_A :
  @pi_call_rets prh_img_A F_check_round_trip F_round_trip_text = [AT CRT_R1_OFF; AT CRT_R2_OFF] /\
  @pi_call_rets prh_img_A F_check_round_trip F_pj_string = [AT CRT_G_OFF] /\
  @pi_call_rets prh_img_A F_check_round_trip F_pj_set = [AT CRT_K_OFF] /\
  @pi_call_rets prh_img_A F_check_round_trip F_pj_write = [AT CRT_W_OFF] /\
  @pi_call_rets prh_img_A F_check_round_trip F_parse_noting = [AT CRT_N_OFF] /\
  @pi_call_rets prh_img_A F_check_round_trip F_pj_free = [AT CRT_Z_OFF; AT (CRT_PJF2_CALL + 4)] /\
  @pi_call_rets prh_img_A F_check_round_trip F_fuzz_free = [AT (CRT_FF1_CALL + 4); AT (CRT_FF2_CALL + 4)] /\
  @pi_call_rets prh_img_A F_check_round_trip F_fuzz_alloc_ran_out =
    [AT (CRT_RO1_CALL + 4); AT (CRT_RO2_CALL + 4); AT (CRT_RO3_CALL + 4)] /\
  @pi_call_rets prh_img_A F_check_round_trip F_same = [AT (CRT_SAME_CALL + 4)] /\
  @pi_ret_sites prh_img_A F_check_round_trip RT_fuzz_free = [AT (CRT_FF1_CALL + 4); AT (CRT_FF2_CALL + 4)] /\
  @pi_abort prh_img_A F_check_round_trip = AT CRT_AB_OFF /\
  @pi_err_sites prh_img_A F_check_round_trip = map (fun o => AT o) CRT_ERR_OFFS.
Proof. csplit; vm_compute; reflexivity. Qed.

(* the frame: the first word is addi sp, sp, -CRT_FRAME, +0x3c addi s0, sp, CRT_FRAME (s0 = the entry sp), +0x40
   andi sp, sp, -CRT_ALIGN, +0x68 addi a0, zero, CRT_REQ (the frame call's request). pi_frame's convention
   (PRH_Base.v:123-125, PRH_Img.v:4-5): N + (A - 16) for `addi sp, sp, -N` then `andi sp, sp, -A` -- the entry sp is
   16-aligned, so (sp0 - N) rounded down to A drops at most A - 16 bytes. A' has N = 0xe0, A = 0x20: 240. *)
Lemma crt_frame_A :
  opimm_at A_prog_listing CRT_PC_A = Some (ALU_ADD, 2, 2, - Crt102Glue.CRT_FRAME) /\
  opimm_at A_prog_listing (CRT_PC_A + 0x3c) = Some (ALU_ADD, 8, 2, Crt102Glue.CRT_FRAME) /\
  opimm_at A_prog_listing (CRT_PC_A + 0x40) = Some (ALU_AND, 2, 2, - Crt102Glue.CRT_ALIGN) /\
  opimm_at A_prog_listing (CRT_PC_A + 0x68) = Some (ALU_ADD, 10, 0, Crt102Glue.CRT_REQ) /\
  FRA = Crt102Glue.CRT_FRAME + (Crt102Glue.CRT_ALIGN - 16).
Proof. csplit; vm_compute; reflexivity. Qed.
(* the registers the prologue sets (RISC-V numbers): +0x5c the shadow base (s10 = 26), +0x60 doc (s5 = 21), +0x70 the
   frame call's result (s3 = 19), +0x7c F (s11 = 27, from s3), +0xb8 -8 (s7 = 23) *)
Lemma crt_regs_A :
  load_at A_prog_listing (CRT_PC_A + CRT_FLAG_LW) = Some (SZ4, true, 12, 12, 0) /\
  load_at A_prog_listing (CRT_PC_A + CRT_SHB_LD) = Some (SZ8, true, 26, 11, 0) /\
  opimm_at A_prog_listing (CRT_PC_A + 0x60) = Some (ALU_ADD, 21, 10, 0) /\
  opimm_at A_prog_listing (CRT_PC_A + CRT_P_OFF) = Some (ALU_ADD, 19, 10, 0) /\
  opimm_at A_prog_listing (CRT_PC_A + 0x7c) = Some (ALU_ADD, 27, 19, 0) /\
  opimm_at A_prog_listing (CRT_PC_A + 0xb8) = Some (ALU_ADD, 23, 0, -8).
Proof. csplit; vm_compute; reflexivity. Qed.

(* ---- 3. the stack allowances: the frame-area call (an ecall: ESTACK) and each callee, below the own frame ---- *)
Lemma crt_stk_A :
  ESTACK + FRA <= STKC /\ STK_RT_ECALL + FRA <= STKC /\ STK_RT_STR + FRA <= STKC /\
  @STK_round_trip_text prh_img_A + FRA <= STKC /\ @STK_pj_string prh_img_A + FRA <= STKC /\
  @STK_pj_set prh_img_A DOC_D + FRA <= STKC /\ @STK_pj_write prh_img_A DOC_D + FRA <= STKC /\
  @STK_parse_noting prh_img_A + FRA <= STKC /\ @STK_pj_free prh_img_A DOC_D + FRA <= STKC /\
  @STK_fuzz_free prh_img_A + FRA <= STKC /\ @STK_fuzz_alloc_ran_out prh_img_A + FRA <= STKC /\
  @STK_same prh_img_A DOC_D + FRA <= STKC.
Proof. csplit; vm_compute; discriminate. Qed.
Lemma crt_stk_nonneg_A :
  0 <= ESTACK /\ 0 <= STK_RT_ECALL /\ 0 <= STK_RT_STR /\ 0 <= FRA /\
  0 <= @STK_round_trip_text prh_img_A /\ 0 <= @STK_pj_string prh_img_A /\ 0 <= @STK_pj_set prh_img_A DOC_D /\
  0 <= @STK_pj_write prh_img_A DOC_D /\ 0 <= @STK_parse_noting prh_img_A /\ 0 <= @STK_pj_free prh_img_A DOC_D /\
  0 <= @STK_fuzz_free prh_img_A /\ 0 <= @STK_fuzz_alloc_ran_out prh_img_A /\ 0 <= @STK_same prh_img_A DOC_D.
Proof. csplit; vm_compute; discriminate. Qed.

(* ---- 4. the two read-only strings ---- *)
Definition CRT_MOD_AT_A : Z := VAL (A_OBJ 2) + CRT_MOD_AT_OFF.   (* "modifiedAt", 11 bytes with its NUL *)
Definition CRT_STAMP_A : Z := VAL (A_OBJ 2) + CRT_STAMP_OFF.     (* "2026-10-25T00:00:00Z", 21 bytes with its NUL *)
(* the listing's entries at the five sites *)
Lemma crt_str_lst_A :
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_STAMP1_HI) = Some (PHi (10%bv : bv 5) 33) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_STAMP1_LO) = Some (PAddHi (11%bv : bv 5) (10%bv : bv 5) 33 (A_OBJ 2) 0x11380) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_MODAT1_HI) = Some (PHi (10%bv : bv 5) 34) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_MODAT1_LO) = Some (PAddHi (11%bv : bv 5) (10%bv : bv 5) 34 (A_OBJ 2) 0x110c0) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_MODAT2_HI) = Some (PHi (10%bv : bv 5) 36) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_MODAT2_LO) = Some (PAddHi (10%bv : bv 5) (10%bv : bv 5) 36 (A_OBJ 2) 0x110c0) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_MODAT3_HI) = Some (PHi (11%bv : bv 5) 37) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_MODAT3_LO) = Some (PAddHi (11%bv : bv 5) (11%bv : bv 5) 37 (A_OBJ 2) 0x110c0) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_STAMP2_HI) = Some (PHi (11%bv : bv 5) 38) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_STAMP2_LO) = Some (PAddHi (11%bv : bv 5) (11%bv : bv 5) 38 (A_OBJ 2) 0x11380).
Proof. csplit; vm_compute; reflexivity. Qed.
(* the image's instruction words at the five sites resolve to the two addresses (computed on the image's word table
   A_prog_tbl, then carried to fetch_word over the segments by A_prog_tbl_ok) *)
Lemma crt_str_res_tbl_A :
  res_pair (tblf A_prog_tbl) (AT CRT_STAMP1_HI) (AT CRT_STAMP1_LO) = Some CRT_STAMP_A /\
  res_pair (tblf A_prog_tbl) (AT CRT_MODAT1_HI) (AT CRT_MODAT1_LO) = Some CRT_MOD_AT_A /\
  res_pair (tblf A_prog_tbl) (AT CRT_MODAT2_HI) (AT CRT_MODAT2_LO) = Some CRT_MOD_AT_A /\
  res_pair (tblf A_prog_tbl) (AT CRT_MODAT3_HI) (AT CRT_MODAT3_LO) = Some CRT_MOD_AT_A /\
  res_pair (tblf A_prog_tbl) (AT CRT_STAMP2_HI) (AT CRT_STAMP2_LO) = Some CRT_STAMP_A.
Proof. csplit; vm_compute; reflexivity. Qed.
Lemma crt_str_res_A :
  res_pair (segf SEGS) (AT CRT_STAMP1_HI) (AT CRT_STAMP1_LO) = Some CRT_STAMP_A /\
  res_pair (segf SEGS) (AT CRT_MODAT1_HI) (AT CRT_MODAT1_LO) = Some CRT_MOD_AT_A /\
  res_pair (segf SEGS) (AT CRT_MODAT2_HI) (AT CRT_MODAT2_LO) = Some CRT_MOD_AT_A /\
  res_pair (segf SEGS) (AT CRT_MODAT3_HI) (AT CRT_MODAT3_LO) = Some CRT_MOD_AT_A /\
  res_pair (segf SEGS) (AT CRT_STAMP2_HI) (AT CRT_STAMP2_LO) = Some CRT_STAMP_A.
Proof.
destruct crt_str_res_tbl_A as (H1 & H2 & H3 & H4 & H5).
csplit; apply (res_pair_tbl rsegs A_prog_tbl A_prog_tbl_ok); assumption.
Qed.
(* the bytes there *)
Lemma crt_str_rom_b_A :
  str_at SEGS CRT_MOD_AT_A CRT_MOD_AT_S = true /\
  str_at SEGS CRT_STAMP_A CRT_STAMP_S = true.
Proof. split; vm_compute; reflexivity. Qed.
Lemma crt_str_rom_A :
  (forall j, (j < length CRT_MOD_AT_S)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (CRT_MOD_AT_A + Z.of_nat j))) =
     Some (nth j CRT_MOD_AT_S 0)) /\
  (forall j, (j < length CRT_STAMP_S)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (CRT_STAMP_A + Z.of_nat j))) =
     Some (nth j CRT_STAMP_S 0)).
Proof. split; apply str_at_sound; [exact (proj1 crt_str_rom_b_A) | exact (proj2 crt_str_rom_b_A)]. Qed.

(* ---- 5. the image facts a journal needs (S1ImgA's, at PI_prog_A's names) ---- *)
Lemma crt_pst_img_A : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. exact pst_in_img_A. Qed.
Lemma crt_pst_ro_A : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_A. Qed.
Lemma crt_pa_hi_A : @pa_hi _ A_prog_listing PA <= 2 ^ 31.
Proof. change (@pa_hi _ _ PA) with IMG_TOP. unfold IMG_TOP. lia. Qed.
(* the prologue's GOT words: A_OBJ 0 (the shadow base's) and A_OBJ 1 (the use-after-return flag's) *)
Lemma crt_got_A :
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_SHB_HI) = Some (PHi (11%bv : bv 5) 29) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_SHB_LO) =
    Some (PLdHi (11%bv : bv 5) (11%bv : bv 5) 29 (A_OBJ 0) 0x0 SZ8 true) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_UAR_HI) = Some (PHi (12%bv : bv 5) 30) /\
  plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_UAR_LO) =
    Some (PLdHi (12%bv : bv 5) (12%bv : bv 5) 30 (A_OBJ 1) 0x0 SZ8 true) /\
  res_pair (segf SEGS) (AT CRT_GOT_SHB_HI) (AT CRT_GOT_SHB_LO) = Some (VAL (A_OBJ 0)) /\
  res_pair (segf SEGS) (AT CRT_GOT_UAR_HI) (AT CRT_GOT_UAR_LO) = Some (VAL (A_OBJ 1)).
Proof.
assert (H1 : plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_SHB_HI) = Some (PHi (11%bv : bv 5) 29))
  by (vm_compute; reflexivity).
assert (H2 : plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_SHB_LO) =
  Some (PLdHi (11%bv : bv 5) (11%bv : bv 5) 29 (A_OBJ 0) 0x0 SZ8 true)) by (vm_compute; reflexivity).
assert (H3 : plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_UAR_HI) = Some (PHi (12%bv : bv 5) 30))
  by (vm_compute; reflexivity).
assert (H4 : plookup_list asym A_prog_listing (CRT_PC_A + CRT_GOT_UAR_LO) =
  Some (PLdHi (12%bv : bv 5) (12%bv : bv 5) 30 (A_OBJ 1) 0x0 SZ8 true)) by (vm_compute; reflexivity).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split.
- rewrite <- (Z.add_0_r (VAL (A_OBJ 0))). exact (pa_res_ld _ _ _ _ _ _ _ _ _ H1 H2).
- rewrite <- (Z.add_0_r (VAL (A_OBJ 1))). exact (pa_res_ld _ _ _ _ _ _ _ _ _ H3 H4).
Qed.
End a.
