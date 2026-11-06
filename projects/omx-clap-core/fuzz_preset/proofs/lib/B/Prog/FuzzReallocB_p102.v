(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's
   relay_finish, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)),
   after lib/A/W_relay_finish_h.v (a working branch a3987bff22c: its loop rf_loop and its tail rf_tail), in the
   form of the B walks lib/B/W_check_bounded.v (a working branch 7e062bb9b9c) and lib/B/W_gse_loop.v
   (a working branch bb5ed8a0689). *)
(* Modified by Theorem Labs, 2026-10: the room `_x` form (a Theorem Labs lane, RoomRFB): the walk is pb_relay_finish_x,
   stated over any allocator relation ARx with its laws as W_contract_x.v rf_spec_x (Section c below: PST / ARx / hl /
   LAWS / HP0 / BLKN, the callees' and the allocator rules' `_x` twins, PSTR / PSTC), and it threads rf_spec_x's room
   round: the budget rp_RM RP (each round: the free's 1, then gestures_end's charge) and the count premise
   cnt_ok_pk RP rf_pk (rf_pk = 5) to the free (cnt_ok) and to gestures_end (gse_pk = 4); the round's room bound follows
   rf_room's `- cap` threading (the round frees the old g_out block).  The room argument is lib/A/W_relay_finish_h.v's
   (a working branch 9e4f84a8fb9), the ARx form that of lib/B/W_list_free.v / W_source_reset.v
   (a working branch dfa1a225350).
   B's relay_finish sets no frame pointer and calls no __asan_stack_malloc, so A's fake-frame seat, its set_fs step and rp_RPF across the seat do not apply.
   pb_relay_finish keeps its statement, byte-identical, and its Section hypotheses (the same terms in the same order;
   HPLAIN / HWSEG write rf_cells as rf_cells RG GTU GL): it is re-derived from pb_relay_finish_x at ARx := ARi0,
   PST := [], RP := RP_AR (Section cAR); pb_relay_finish_fr / _fr_tfib are unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_relay_finish.v, with its module paths and module names changed; 2648 of its 2780 lines of code are new or changed and 4211 lines of the source are left out. *)
(* Step-2 re-fit for the free / realloc re-hiding move (row AL4 + its HULL row, the table, the internal file OWNERS.tsv),
   written against lib/A/PRH_FnAlloc.v blob 5f50b300eb2c and the keep twins (YGcallRkKeep, YGcfInstReallocKKeep). The text is the
   primed tfuzz_realloc_specX (SRr' segs RZ_cf, post fpostmR at
   wle' segs RZ_cf, the refusal evidence world-free, the hull budget / use). What moved here:
   - the post is the kit's named projection tfrP_Q (PRH_FnAlloc.v), built through tfrP_R and the arm records;
   - AREAL_cf is the _k keep row YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep, and the realloc call is
     YGcallRkKeep.aj_realloc_x_cfR_keep (R := wle' SEGS RZ_cf; room qtight /\ ROOM_cf_k /\ cf_hull_adm; QMm_cf at the
     call memory, its arodata_ok_cf by YGcallcf.arodata_ok_cf_of_journal_P from fpre's arodata_okP);
   - ROUTE STOP + LIFT: every segment before the realloc call (rb_p0 whole, rb_nz up to the call, CHOSEN-FAIL) stays in
     plain SRr; rb_nz lifts ONCE at its entry by YGcfRhLift.ra_rh_of_SRr and switches to the primed relation at the cut
     before the call; rb_refd / rb_succ (after the call) run over R (the _invR runner, paj_branchR, aj_call_xR with
     own's plain text lifted by apost_base_x_R_lift);
   - THE HULL: the text's entry budget gives cf_hull_ok / cf_hull_adm at the call (PresetHullPay), the use at each end
     state comes from A14's secs_call_post of the realloc path (PresetHullBudget.hull_used_of_call_re).
   STAND-IN added: pal_errno_relro (errno_relro_t B, the unit's image binding of B'; owned by the kit), which
   arodata_ok_cf_of_journal_P needs and no other hypothesis of this file gives. *)
(* fuzz_preset, #102 pins, image B' (asan-ubsan, sha256 d663f82d): the walk of fuzz_realloc (merged alloc.c :104-128,
   blob bd2740a; B' 0x85eb4, 139 slots, frame 48), row AL4 of the rewalk's internal file FREE-PIECES-102.md Part 5 (preset-F),
   against the text tfuzz_realloc_specX in the post-implication form with THE OUTCOME conjuncts, on the landed cut
   (lib/A/PRH_FnAlloc.v blob 4d8aeba047e5, lib/A/PRH_Base.v blob ef7c8ca98529, lib/A/PRH_Refute.v blob
   23f7a37f01c9), which carries this row from the P'' universe set re-fit of this file (first landed on the AL
   acceptance base). Ported from the V1 walk of image B (blob a061a8383eb0)
   (commit 459129c18903; image B 3b5e1a09, 0x85a54, 106 slots, frame 32) to the
   whole-program listing of B' (lib/B/Listing_prog.v, PI_prog_B of lib/B/PAImg_prog.v, both from
   commit d42e123915ae: object atoms numbered by name).
   Two parts. PART 1 (the prep, up to the pure engine runs and the statics each arm leaves) names no kit text: every
   program-statics fact is stated over the listing's objects, or for ANY list PST of program statics that holds the
   written objects' bytes. PART 2 (Section w, "THE TEXT STAGE") binds PST := prh_pst once (rb_pst_obj, from B''s
   generated PrhImg) and proves the text; its header says what it uses.
   What part 1 holds:
   - the head word: the .wip's hdr_sv family (.wip:54-170, unchanged; B' reads the head with the same 8 lbu / slli /
     or at +288..+380, V1 +184..+276), and the two head-word facts of the walk (.wip:710-725);
   - the listing facts of the cut: the entry, every slot where a run of the walk stops on a call, a tail call or the
     return, and the return points 252 / 404 / 512 (V1 148 / 300 / 356);
   - the walk's symbolic states over the B' listing: the frame is 48 (V1 32); g_peak is WRITTEN (refused(n) of the
     REFUSED arm, V2 only); g_most is READ (object g_most, value atom 39);
   - the write windows and what a run keeps (.wip:492-587), over the listing's objects;
   - the small facts and helpers of the .wip that name no kit text (.wip:468-477, 589-680);
   - the pure engine runs of every segment of every arm (p = NULL, entry, CHOSEN-FAIL, the unpoison and realloc
     calls, SUCCESS, the four paths of REFUSED's refused(n), its call of own and the shared epilogue), each with the
     runner's static check, the window check of its start state, where and why it stops, its obligations (none), the
     after-call premises of st_ok_pi_after_call, and the statics each arm leaves.
   Numerals in this file: offsets from the entry 28 .. 512 (DERIVED: 4 * slot of the listing, each checked against the
   listing below), the frame 48 (LENGTH: the listing's `addi sp, sp, -48` at the entry), the head 16 and its offsets
   -16 / -8 (LENGTH: alloc.c HEAD; CfParams_preset's cf_head, checked by reflexivity), atom indices 2 / 10 / 11 /
   32-39 / 64 and havoc bases 40 / 60 / 80 (DERIVED: the symbolic engine's numbering, the .wip's convention, plus 39
   for g_most; 64 is a0 after the realloc call, CLOB's fifth entry), region indices 0 .. 9 (DERIVED: positions in the
   walk's region lists), register numbers (WORD), the head word's byte shifts 0-56, 63, 256, 2 ^ 8 / 2 ^ 16 / 2 ^ 32
   (WORD), 2 ^ 29 (DERIVED: a bound on n from the texts' n + cf_head < cf_malloc_max, cf_malloc_max = 2 ^ 28 + 2 ^ 27
   at CfParams_preset, checked by reflexivity), 2 ^ 31 (DERIVED: a bound on SHADOW_OFF), 2 ^ 40 (DERIVED:
   st_ok_pi_after_call's bound on a return offset), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 and SIZE_MAX
   18446744073709551615 (WORD / DERIVED: the engine's spans and machine words), 4096 / 4112 (DERIVED: cgif's lowest
   block, + the head), 8 / 1 (LENGTH: the asan_globals widths of the statics, g_ran_out one byte), 16448 / 16400 /
   4128 (DERIVED: STK_fuzz_realloc / STK_fuzz_malloc / STK_own at prh_img_B, checked by vm_compute), 16384 / 4096
   (DERIVED: ASTACK / ESTACK, by reflexivity). The object numbers appear ONCE, in the name table below. No ADDRESS
   literal: every address is pa_sigma / pa_val of lib/B/PAImg_prog.v, a PrhImg field of lib/B/PRH_ImgB.v or a CfImg
   field of lib/AU/CfImgB.v, computed where it is compared. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0sshcf YGcfRoomPre YG0lawscf YGcallx YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallRx YGcallPx YGcallPcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YGcfHp YGcfRealloc YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfAmx2 YAkMemnorm YSRrMemnorm YGcallMxmn
  YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoom PresetRun PresetReqAt
  PresetRoomPos PresetRoomPosKeep.
(* THE OUTCOME's refusal exclusion at the realloc call: the kit's refutation family (PRH_Refute.prh_refute_at), used
   qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
(* the Step-2 re-fit: the step relation and journal over YA0nH.wle' at preset's zone YGcfRehidePost.RZ_cf, the realloc
   call rule with the memnorm keep over the primed _k row, the hull budget and the call memory's RELRO rows *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YSRrG YGcfRhLift YGcfRehidePost
  YGcallRkKeep YGcfInstReallocKKeep YGcfSecsStep YGcfPath YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the head read (B' 0x85fd4-0x86030): eight lbu of the head bytes recombined by slli / or are the head word
   (.wip:54-170, unchanged) ---- *)
Definition hdr_b (x : nat) (s : Z) : sv := SExt false 8 (SAlu ALU_SRL (SOff x 0) (SLit s)).
Definition hdr_sll (v : sv) (t : Z) : sv := SAlu ALU_SLL v (SLit t).
Definition hdr_half (b3 b2 b1 b0 : sv) : sv :=
  SAlu ALU_OR (SAlu ALU_OR (hdr_sll b3 24) (hdr_sll b2 16)) (SAlu ALU_OR (hdr_sll b1 8) b0).
Definition hdr_sv (x : nat) : sv :=
  SAlu ALU_OR (hdr_sll (hdr_half (hdr_b x 56) (hdr_b x 48) (hdr_b x 40) (hdr_b x 32)) 32)
    (hdr_half (hdr_b x 24) (hdr_b x 16) (hdr_b x 8) (SExt false 8 (SOff x 0))).
Lemma rb_zc : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma rb_land63 : forall s, 0 <= s < 64 -> Z.land s 63 = s.
Proof. intros s Hs. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma hdr_lor_add : forall a b s, 0 <= a -> 0 <= s -> 0 <= b < 2 ^ s -> Z.lor (a * 2 ^ s) b = a * 2 ^ s + b.
Proof.
intros a b s Ha Hs Hb. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
destruct (Z.lt_ge_cases n s) as [Hl|Hl].
- rewrite Z.mul_pow2_bits_low by lia.
  rewrite <- (Z.mod_pow2_bits_low (a * 2 ^ s + b) s n Hl).
  rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia). rewrite Z.mod_small by lia. reflexivity.
- rewrite Z.mul_pow2_bits by lia.
  assert (Hbn : Z.testbit b n = false).
  { destruct (Z.eq_dec b 0) as [->|Hb0]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
    apply (Z.lt_le_trans _ (2 ^ s)); [lia | apply Z.pow_le_mono_r; lia]. }
  rewrite Hbn, Bool.orb_false_r.
  assert (Ht : Z.testbit (a * 2 ^ s + b) n = Z.testbit ((a * 2 ^ s + b) / 2 ^ s) (n - s)).
  { rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia. f_equal; lia. }
  rewrite Ht. rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  rewrite (Z.div_small b) by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma U_hdr_b : forall E x s, 0 <= s < 64 -> U E (hdr_b x s) = (bv_unsigned (ew E x) / 2 ^ s) mod 256.
Proof.
intros E x s Hs. unfold hdr_b. rewrite U_SExt, U_SAlu, U_SLit, U_SOff, Z.add_0_r. cbn [zalu_raw].
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (rb_zc (bv_unsigned (ew E x))) by lia. rewrite (rb_zc s) by lia. rewrite rb_land63 by lia.
rewrite Z.shiftr_div_pow2 by lia.
assert (H0 : 0 <= bv_unsigned (ew E x) / 2 ^ s < 2 ^ 64).
{ split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (bv_unsigned (ew E x))); [apply Z.div_le_upper_bound; nia | lia]. }
rewrite (rb_zc (bv_unsigned (ew E x) / 2 ^ s)) by lia. change (2 ^ Z.of_N 8) with 256.
apply rb_zc. pose proof (Z.mod_pos_bound (bv_unsigned (ew E x) / 2 ^ s) 256 ltac:(lia)). lia.
Qed.
Lemma U_hdr_b0 : forall E x, U E (SExt false 8 (SOff x 0)) = (bv_unsigned (ew E x) / 2 ^ 0) mod 256.
Proof.
intros E x. rewrite U_SExt, U_SOff, Z.add_0_r. change (2 ^ 0) with 1. rewrite Z.div_1_r.
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (rb_zc (bv_unsigned (ew E x))) by lia. change (2 ^ Z.of_N 8) with 256.
apply rb_zc. pose proof (Z.mod_pos_bound (bv_unsigned (ew E x)) 256 ltac:(lia)). lia.
Qed.
Lemma U_hdr_sll : forall E v t c, U E v = c -> 0 <= c -> 0 <= t < 64 -> c * 2 ^ t < 2 ^ 64 ->
  U E (hdr_sll v t) = c * 2 ^ t.
Proof.
intros E v t c Hv Hc Ht Hlt. unfold hdr_sll. rewrite U_SAlu, U_SLit, Hv. cbn [zalu_raw].
rewrite (rb_zc t) by lia. rewrite rb_land63 by lia. rewrite Z.shiftl_mul_pow2 by lia.
apply rb_zc. assert (0 <= c * 2 ^ t) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma U_hdr_or : forall E u v a s b, U E u = a * 2 ^ s -> U E v = b -> 0 <= a -> 0 <= s -> 0 <= b < 2 ^ s ->
  a * 2 ^ s + b < 2 ^ 64 -> U E (SAlu ALU_OR u v) = a * 2 ^ s + b.
Proof.
intros E u v a s b Hu Hv Ha Hs Hb Hlt. rewrite U_SAlu, Hu, Hv. cbn [zalu_raw]. rewrite hdr_lor_add by lia.
apply rb_zc. assert (0 <= a * 2 ^ s) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma rb_dm : forall w k k', 0 <= w -> 0 <= k -> k' = k + 8 ->
  w / 2 ^ k = (w / 2 ^ k) mod 256 + 256 * (w / 2 ^ k').
Proof.
intros w k k' Hw Hk ->. rewrite (Z.div_mod (w / 2 ^ k) 256) at 1 by lia.
rewrite Z.div_div by (try apply Z.pow_nonzero; lia). rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. lia.
Qed.
Lemma hdr_sv_U : forall E x, U E (hdr_sv x) = bv_unsigned (ew E x).
Proof.
intros E x.
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
set (w := bv_unsigned (ew E x)) in *.
assert (BB : forall s, 0 <= (w / 2 ^ s) mod 256 < 256) by (intros s; apply Z.mod_pos_bound; lia).
pose proof (BB 0) as R0. pose proof (BB 8) as R8. pose proof (BB 16) as R16. pose proof (BB 24) as R24.
pose proof (BB 32) as R32. pose proof (BB 40) as R40. pose proof (BB 48) as R48. pose proof (BB 56) as R56.
set (b0 := (w / 2 ^ 0) mod 256) in *. set (b8 := (w / 2 ^ 8) mod 256) in *. set (b16 := (w / 2 ^ 16) mod 256) in *.
set (b24 := (w / 2 ^ 24) mod 256) in *. set (b32 := (w / 2 ^ 32) mod 256) in *. set (b40 := (w / 2 ^ 40) mod 256) in *.
set (b48 := (w / 2 ^ 48) mod 256) in *. set (b56 := (w / 2 ^ 56) mod 256) in *.
assert (HL : U E (hdr_half (hdr_b x 24) (hdr_b x 16) (hdr_b x 8) (SExt false 8 (SOff x 0))) =
  (b24 * 2 ^ 8 + b16) * 2 ^ 16 + (b8 * 2 ^ 8 + b0)).
{ unfold hdr_half. apply U_hdr_or; try lia.
  - replace ((b24 * 2 ^ 8 + b16) * 2 ^ 16) with (b24 * 2 ^ 24 + b16 * 2 ^ 16) by ring.
    apply U_hdr_or; try lia.
    + apply U_hdr_sll; [apply U_hdr_b; lia | lia | lia | lia].
    + apply U_hdr_sll; [apply U_hdr_b; lia | lia | lia | lia].
  - apply U_hdr_or; try lia.
    + apply U_hdr_sll; [apply U_hdr_b; lia | lia | lia | lia].
    + apply U_hdr_b0. }
assert (HH : U E (hdr_half (hdr_b x 56) (hdr_b x 48) (hdr_b x 40) (hdr_b x 32)) =
  (b56 * 2 ^ 8 + b48) * 2 ^ 16 + (b40 * 2 ^ 8 + b32)).
{ unfold hdr_half. apply U_hdr_or; try lia.
  - replace ((b56 * 2 ^ 8 + b48) * 2 ^ 16) with (b56 * 2 ^ 24 + b48 * 2 ^ 16) by ring.
    apply U_hdr_or; try lia.
    + apply U_hdr_sll; [apply U_hdr_b; lia | lia | lia | lia].
    + apply U_hdr_sll; [apply U_hdr_b; lia | lia | lia | lia].
  - apply U_hdr_or; try lia.
    + apply U_hdr_sll; [apply U_hdr_b; lia | lia | lia | lia].
    + apply U_hdr_b; lia. }
unfold hdr_sv. rewrite (U_hdr_or E _ _ ((b56 * 2 ^ 8 + b48) * 2 ^ 16 + (b40 * 2 ^ 8 + b32)) 32
  ((b24 * 2 ^ 8 + b16) * 2 ^ 16 + (b8 * 2 ^ 8 + b0))); [| apply U_hdr_sll; [exact HH | lia | lia | lia] | exact HL | lia | lia | lia | lia].
pose proof (rb_dm w 0 8 ltac:(lia) ltac:(lia) eq_refl) as D0. pose proof (rb_dm w 8 16 ltac:(lia) ltac:(lia) eq_refl) as D8.
pose proof (rb_dm w 16 24 ltac:(lia) ltac:(lia) eq_refl) as D16. pose proof (rb_dm w 24 32 ltac:(lia) ltac:(lia) eq_refl) as D24.
pose proof (rb_dm w 32 40 ltac:(lia) ltac:(lia) eq_refl) as D32. pose proof (rb_dm w 40 48 ltac:(lia) ltac:(lia) eq_refl) as D40.
pose proof (rb_dm w 48 56 ltac:(lia) ltac:(lia) eq_refl) as D48. pose proof (rb_dm w 56 64 ltac:(lia) ltac:(lia) eq_refl) as D56.
assert (Z0 : w / 2 ^ 0 = w) by (change (2 ^ 0) with 1; apply Z.div_1_r).
assert (Z64 : w / 2 ^ 64 = 0) by (apply Z.div_small; lia).
fold b0 b8 b16 b24 b32 b40 b48 b56 in D0, D8, D16, D24, D32, D40, D48, D56.
clearbody b0 b8 b16 b24 b32 b40 b48 b56 w. clear HL HH BB.
rewrite Z0 in D0. rewrite Z64 in D56. clear Z0 Z64.
remember (w / 2 ^ 8) as q8 eqn:Q8. remember (w / 2 ^ 16) as q16 eqn:Q16. remember (w / 2 ^ 24) as q24 eqn:Q24.
remember (w / 2 ^ 32) as q32 eqn:Q32. remember (w / 2 ^ 40) as q40 eqn:Q40. remember (w / 2 ^ 48) as q48 eqn:Q48.
remember (w / 2 ^ 56) as q56 eqn:Q56. clear Q8 Q16 Q24 Q32 Q40 Q48 Q56.
change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *. change (2 ^ 32) with 4294967296 in *.
lia.
Qed.
Lemma hdr_sv_denot : forall E x, sv_denot E (hdr_sv x) = ew E x.
Proof. intros E x. apply bv_eq. exact (hdr_sv_U E x). Qed.
(* the head word as the argument of the re-own (a1 = s2 + 0) and g_live - k (.wip:710-725) *)
Lemma rb_hdr_add0 : forall E x, sv_denot E (SAlu ALU_ADD (hdr_sv x) (SLit 0)) = ew E x.
Proof.
intros E x. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (hdr_sv x) (SLit 0)))) with (U E (SAlu ALU_ADD (hdr_sv x) (SLit 0))).
rewrite U_SAlu, hdr_sv_U, U_SLit. cbn [zalu_raw].
pose proof (bv_unsigned_in_range _ (ew E x)) as Hw. unfold bv_modulus in Hw. change (Z.of_N 64) with 64 in Hw.
rewrite (rb_zc 0) by lia. rewrite Z.add_0_r. apply rb_zc. lia.
Qed.
Lemma rb_sub_denot : forall E live k, ew E 35 = Z_to_bv 64 live -> ew E 37 = Z_to_bv 64 k -> 0 <= k <= live ->
  live < 2 ^ 64 -> sv_denot E (SAlu ALU_SUB (SOff 35 0) (hdr_sv 37)) = Z_to_bv 64 (live - k).
Proof.
intros E live k H35 H37 Hk Hl. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_SUB (SOff 35 0) (hdr_sv 37)))) with (U E (SAlu ALU_SUB (SOff 35 0) (hdr_sv 37))).
rewrite U_SAlu, hdr_sv_U, U_SOff, H35, H37. rewrite !unsigned_lit_small by lia.
rewrite Z.add_0_r, (rb_zc live) by lia. cbn [zalu_raw]. apply rb_zc. lia.
Qed.

(* ---- the listing's objects the walk names, BY NAME. The numbers are the positions of the names in the "objects"
   list of B in tools/preset-listing/pins/pins102.json (commit 5472bf2e7a82), the pin file
   d42e123915ae's listings were emitted with; each address B_prog_obj gives them is the symbol's in the B' symbol
   table (record: the AL4 prep's objects list). Nowhere else in this file is an object
   named by its number. A_OBJ 0 / A_OBJ 12 inside got_regionP / bcell_regionP are the engine's pins (YC1fP PALib). *)
Definition O_g_count : nat := A_OBJ 7.
Definition O_g_fail_at : nat := A_OBJ 8.
Definition O_g_live : nat := A_OBJ 9.
Definition O_g_peak : nat := A_OBJ 10.
Definition O_g_ran_out : nat := A_OBJ 11.
Definition O_g_most : nat := A_OBJ 14.

(* ---- the symbolic states, over the whole-program listing of image B' ----
   p <> 0 (ss_rb): atoms 2 = entry sp, 10 = p, 11 = n, 32 = the shadow offset, 33 = g_count, 34 = g_fail_at,
   35 = g_live, 36 = g_ran_out, 37 = the old block's head word k, 38 = g_peak, 39 = g_most (NEW); regions: the 48-byte
   frame, the shadow-offset GOT slot and cell (read-only), g_count / g_fail_at / g_live (read and written), g_ran_out
   (one byte written), the head word of the old block at p - 16 (read-only), g_peak (read and WRITTEN: refused(n)
   raises it on the REFUSED arm; V1 read-only) and g_most (read-only, NEW: refused(n) reads it); the generated alias
   rows B_alias_hints carry the static accesses of fuzz_realloc (B' 0x8606c's g_live load through s3 among them).
   p = 0 (ss_rb0): the frame only. After the unpoison call the head's 16 bytes are addressable: rb_SH1. *)
Definition rb_pc0 : Z := 4 * Z.of_nat (B_prog_slot AS_fuzz_realloc).
Definition RB_Bx : sv := SOff 32 0.
Definition RB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition rb_st (o x : nat) : YP09.region :=
  YP09.mkRegion (Some o) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff x 0))].
Definition rb_ran : YP09.region :=
  YP09.mkRegion (Some O_g_ran_out) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition rb_head : YP09.region := YP09.mkRegion (Some 10%nat) (-16) (-8) 0 0 [YP09.mkChunk (-16) (CVal 8 (SOff 37 0))].
Definition rb_pk : YP09.region := rb_st O_g_peak 38.
Definition rb_most : YP09.region := YP09.mkRegion (Some O_g_most) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition rb_regions : smem :=
  [stack_region 48; got_regionP; bcell_regionP 32; rb_st O_g_count 33; rb_st O_g_fail_at 34; rb_st O_g_live 35;
   rb_ran; rb_head; rb_pk; rb_most].
Definition rb_obj (o : nat) : afact := mkAF (B_prog_val o) (B_prog_val o) 0.
Definition rb_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4112 (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 29) 0);
    (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (O_g_count, rb_obj O_g_count); (O_g_fail_at, rb_obj O_g_fail_at); (O_g_live, rb_obj O_g_live);
    (O_g_peak, rb_obj O_g_peak); (O_g_ran_out, rb_obj O_g_ran_out); (O_g_most, rb_obj O_g_most)]
    [] B_alias_hints.
Definition ss_rb : sstate := mkSS rb_pc0 sr_atoms rb_regions None rb_facts.
Definition ss_rb0 : sstate :=
  mkSS rb_pc0 sr_atoms [stack_region 48] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 0 0)] [] []).
Definition rb_SH0 : list shent := [].
Definition rb_SH1 : list shent := [mkSHE 10 (-16) 0].

(* ---- the write windows: the frame [sp - 48, sp) and the written statics' bytes (g_count, g_fail_at, g_live,
   g_peak: 8 bytes; g_ran_out: its one byte); every other region of the walk is read-only ---- *)
Definition rb_wobjs : list nat := [O_g_count; O_g_fail_at; O_g_live; O_g_peak; O_g_ran_out].
Definition rb_wd (o : nat) : Z := if Nat.eqb o O_g_ran_out then 1 else 8.
Definition wins_of (rs : smem) : list (option nat * Z * Z) :=
  map (fun r => (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r)) rs.
Definition rb_win_okb (w : option nat * Z * Z) : bool :=
  match w with (b, lo, hi) =>
    (hi <=? lo) ||
    (match b with Some 2%nat => (-48 <=? lo) && (hi <=? 0) | _ => false end) ||
    existsb (fun o => match b with Some j => Nat.eqb j o && (0 <=? lo) && (hi <=? rb_wd o) | None => false end)
      rb_wobjs
  end.
(* a run whose only write window is the frame *)
Definition rb_win0b (w : option nat * Z * Z) : bool :=
  match w with (b, lo, hi) =>
    (hi <=? lo) || (match b with Some 2%nat => (-48 <=? lo) && (hi <=? 0) | _ => false end) end.
Lemma rb_wobjs_img : forall o, In o rb_wobjs -> (A_TEXT <= o < A_LIM)%nat.
Proof.
intros o Ho. unfold rb_wobjs, O_g_count, O_g_fail_at, O_g_live, O_g_peak, O_g_ran_out in Ho.
cbn [In] in Ho. unfold A_OBJ, A_TEXT, A_LIM in *.
destruct Ho as [<- | [<- | [<- | [<- | [<- | []]]]]]; lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := (@PI_prog_B rc).
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
Definition RB_EI (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg rc B_prog_listing PA (Ereg regs (map (Z_to_bv 64) xs)).

(* ---- the listing facts of the cut (offsets from the entry; B' 0x85eb4 + offset) ---- *)
Lemma rb_entry_pc : SIGMA AS_fuzz_realloc = BASE + rb_pc0.
Proof. vm_compute. reflexivity. Qed.
Lemma rb_entry_frame : plookup B_prog_tpi rb_pc0 = Some (PW 0xfd010113).
Proof. vm_compute. reflexivity. Qed.
(* the slots a run of the walk stops at: the shared return-0 epilogue's ret (+108: CHOSEN-FAIL and both REFUSED
   paths end there), the p = NULL tail call of fuzz_malloc (+140), the unpoison call (+248), the realloc call (+400),
   the SUCCESS tail call of own (+436), the REFUSED call of own (+508) and its jump back to the epilogue (+512) *)
Lemma rb_cut_slots :
  plookup B_prog_tpi (rb_pc0 + 108) = Some (PW RET_WORD_r) /\
  plookup B_prog_tpi (rb_pc0 + 140) = Some (PTail AS_fuzz_malloc) /\
  plookup B_prog_tpi (rb_pc0 + 248) = Some (PCall AS___asan_unpoison_memory_region 1%bv) /\
  plookup B_prog_tpi (rb_pc0 + 400) = Some (PCall AS___wrap_realloc 1%bv) /\
  plookup B_prog_tpi (rb_pc0 + 436) = Some (PTail AS_own) /\
  plookup B_prog_tpi (rb_pc0 + 508) = Some (PCall AS_own 1%bv).
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the three return points of the walk's calls: the unpoison call (+252, V1 148), the realloc call (+404, V1 300),
   the REFUSED arm's call of own (+512, V1 356) *)
Lemma rb_ret_ok : forall o, (o = 252 \/ o = 404 \/ o = 512) -> YK0s.ret_ok (Z_to_bv 64 (BASE + (rb_pc0 + o))).
Proof.
intros o Ho. apply ret_ok_codeptr_v;
(destruct Ho as [ -> | [ -> | -> ] ]; first [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity
  | vm_compute; reflexivity]).
Qed.
Lemma rb_ret_hi : forall o, (o = 252 \/ o = 404 \/ o = 512) -> 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (rb_pc0 + o))).
Proof. intros o Ho. destruct Ho as [ -> | [ -> | -> ] ]; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ---- the written objects' bytes, and the windows' soundness over them ---- *)
Definition rb_obj_byte (a : Z) : Prop := Exists (fun o => VAL o <= a < VAL o + rb_wd o) rb_wobjs.
Lemma rb_win_sound : forall E w a, rb_win_okb w = true -> img_env VAL A_LIM E ->
  base_val E (fst (fst w)) + snd (fst w) <= a < base_val E (fst (fst w)) + snd w ->
  (bv_unsigned (ew E 2) - 48 <= a < bv_unsigned (ew E 2)) \/ rb_obj_byte a.
Proof.
intros E [[b lo] hi] a Hw HE Ha. cbn [fst snd] in Ha. unfold rb_win_okb in Hw.
apply orb_true_iff in Hw as [Hw | Hw]; [apply orb_true_iff in Hw as [Hw | Hw] |].
- apply Z.leb_le in Hw. lia.
- destruct b as [[|[|[|b]]]|]; try discriminate Hw.
  apply andb_true_iff in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  left. cbn [base_val] in Ha. lia.
- right. apply existsb_exists in Hw as (o & Hi & Hw).
  destruct b as [j|]; [|discriminate Hw].
  apply andb_true_iff in Hw as [Hw H3]. apply andb_true_iff in Hw as [Hj H2].
  apply Nat.eqb_eq in Hj. apply Z.leb_le in H2. apply Z.leb_le in H3. subst j.
  cbn [base_val] in Ha. rewrite (HE o (rb_wobjs_img o Hi)) in Ha.
  apply Exists_exists. exists o. split; [exact Hi | lia].
Qed.
(* the write premise of a run, for any program-statics list PST holding the written objects' bytes *)
Lemma rb_wr_l : forall (PST : list (Z * Z)) E rs sp0 STK FP bl0 blc ly own a,
  (forall a, rb_obj_byte a -> Exists (in_zr a) PST) ->
  forallb rb_win_okb (wins_of rs) = true -> img_env VAL A_LIM E -> bv_unsigned (ew E 2) = sp0 -> 48 <= STK ->
  in_wrange E rs a -> awr_byte STK sp0 FP bl0 blc ly own a \/ Exists (in_zr a) PST.
Proof.
intros PST E rs sp0 STK FP bl0 blc ly own a HPST Hf HE Hsp HSTK (r & Hin & Hr).
rewrite forallb_forall in Hf.
assert (Hw : rb_win_okb (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) = true).
{ apply Hf. unfold wins_of. apply in_map_iff. exists r. split; [reflexivity | exact Hin]. }
destruct (rb_win_sound E _ a Hw HE Hr) as [H | H]; [left; left; lia | right; exact (HPST a H)].
Qed.
Lemma rb_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* what a run keeps: every byte outside the frame and the written objects *)
Lemma rb_keep_l : forall (Wx : world SEGS) E rs (m m' : word -> option byte) a,
  frame_of E rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> forallb rb_win_okb (wins_of rs) = true ->
  img_env VAL A_LIM E -> 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (ew E 2) - 48 <= a < bv_unsigned (ew E 2)) ->
  ~ rb_obj_byte a -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E rs m m' a HF Hf HE Ha Hn1 Hn2.
apply (rb_aview_of_frame Wx E rs m m' a HF); [| exact Ha].
intros (r & Hin & Hr). rewrite forallb_forall in Hf.
assert (Hw : rb_win_okb (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) = true).
{ apply Hf. unfold wins_of. apply in_map_iff. exists r. split; [reflexivity | exact Hin]. }
destruct (rb_win_sound E _ a Hw HE Hr) as [H | H]; [exact (Hn1 H) | exact (Hn2 H)].
Qed.
Lemma rb_keep0_l : forall (Wx : world SEGS) E rs (m m' : word -> option byte) a,
  frame_of E rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> forallb rb_win0b (wins_of rs) = true ->
  0 <= a < 2 ^ 64 -> ~ (bv_unsigned (ew E 2) - 48 <= a < bv_unsigned (ew E 2)) ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E rs m m' a HF Hf Ha Hn1.
apply (rb_aview_of_frame Wx E rs m m' a HF); [| exact Ha].
intros (r & Hin & Hr). rewrite forallb_forall in Hf.
assert (Hw : rb_win0b (YP09.r_base r, YP09.r_wlo r, YP09.r_whi r) = true).
{ apply Hf. unfold wins_of. apply in_map_iff. exists r. split; [reflexivity | exact Hin]. }
unfold rb_win0b in Hw. apply orb_true_iff in Hw as [Hw | Hw].
- apply Z.leb_le in Hw. lia.
- destruct (YP09.r_base r) as [[|[|[|b]]]|] eqn:Eb; try discriminate Hw.
  apply andb_true_iff in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Hn1. cbn [base_val] in Hr. lia.
Qed.

(* ---- small facts (.wip:468-470, 589-680; none names a kit text) ---- *)
Lemma rb_apres_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma rb_denot0 : forall E x, sv_denot E (SOff x 0) = ew E x.
Proof. intros E x. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma rb_bne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma rb_beq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma rb_wrap : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.
Lemma rb_obj_env : forall E o, img_env VAL A_LIM E -> In o (O_g_most :: rb_wobjs) ->
  bv_unsigned (ew E o) = VAL o.
Proof.
intros E o HE Ho. apply HE. destruct Ho as [<- | Ho]; [|exact (rb_wobjs_img o Ho)].
unfold O_g_most, A_OBJ, A_TEXT, A_LIM. lia.
Qed.
Lemma rb_chunk_val : forall E (m : word -> option byte) rs i r off n e v,
  mem_ok SEGS E m rs -> nth_error rs i = Some r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E m rs i r off n e v (Hwf & Hrs & Hpd) Hi Hc He Hv Hn.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
exact (val_of_chunk_ok SEGS E m _ off n e v (proj1 (Forall_forall _ _) Hcs _ Hc) He Hv Hn).
Qed.
(* two addresses of one byte read: the copy of realloc moves bytes *)
Lemma rb_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) (a a' : Z),
  aview SEGS H' m' a' = aview SEGS H m a -> mbyte SEGS (mrestrict H' m') a' = mbyte SEGS (mrestrict H m) a.
Proof.
intros H H' m m' a a'. unfold aview.
destruct (mbyte SEGS (mrestrict H' m') a') as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
cbn [option_map]; intros E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rb_garr8_keep : forall (m m' : word -> option byte) base l,
  garr8 SEGS m base l ->
  (forall j, (j < length l)%nat -> mbyte SEGS m' (base + Z.of_nat j) = mbyte SEGS m (base + Z.of_nat j)) ->
  garr8 SEGS m' base l.
Proof.
intros m m' base l H K j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. specialize (Hv 0%nat Hkk).
replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) in * by lia.
rewrite (K j Hj). exact Hv.
Qed.
Lemma rb_le1 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof.
intros z Hz. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
(* the new block's bytes on realloc's success: the first min (k, n) are the old bytes, the rest are readable *)
Lemma rb_bytes_success : forall (m0 m3 : word -> option byte) p base (old : list Z) k n,
  garr8 SEGS m0 p old -> Z.of_nat (length old) = k -> 0 <= k -> 0 <= n ->
  (forall i, 0 <= i < Z.min k n -> mbyte SEGS m3 (base + i) = mbyte SEGS m0 (p + i)) ->
  (forall i, 0 <= i < n -> exists b, mbyte SEGS m3 (base + i) = Some b) ->
  exists rest, Z.of_nat (length rest) = n - Z.min k n /\ garr8 SEGS m3 base (firstn (Z.to_nat (Z.min k n)) old ++ rest).
Proof.
intros m0 m3 p base old k n Hg Hl Hk Hn Hcp Hpr.
set (f := fun j : nat => match mbyte SEGS m3 (base + Z.min k n + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end).
exists (map f (seq 0 (Z.to_nat (n - Z.min k n)))).
split; [rewrite length_map, length_seq; lia|].
intros j Hj. rewrite length_app, length_map, length_seq, length_firstn in Hj.
destruct (Nat.lt_ge_cases j (Z.to_nat (Z.min k n))) as [Hlt|Hge].
- rewrite app_nth1 by (rewrite length_firstn; lia).
  assert (E : nth j (firstn (Z.to_nat (Z.min k n)) old) 0 = nth j old 0).
  { rewrite <- (firstn_skipn (Z.to_nat (Z.min k n)) old) at 2. rewrite app_nth1; [reflexivity | rewrite length_firstn; lia]. }
  rewrite E. destruct (Hg j ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. specialize (Hv 0%nat Hkk).
  replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) by lia.
  replace (p + Z.of_nat j + Z.of_nat 0) with (p + Z.of_nat j) in Hv by lia.
  rewrite (Hcp (Z.of_nat j) ltac:(lia)). exact Hv.
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Nat.min (Z.to_nat (Z.min k n)) (length old)) with (Z.to_nat (Z.min k n)) by lia.
  rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. cbn [Nat.add]. unfold f.
  replace (base + Z.min k n + Z.of_nat (j - Z.to_nat (Z.min k n))) with (base + Z.of_nat j) by lia.
  destruct (Hpr (Z.of_nat j) ltac:(lia)) as (b & Hb). rewrite Hb.
  pose proof (bv_unsigned_in_range _ b) as Hbr. unfold bv_modulus in Hbr. change (2 ^ Z.of_N 8) with 256 in Hbr.
  split; [|lia].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
  replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) by lia. rewrite Hb.
  rewrite rb_le1 by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
End d.

(* ---- the pure engine runs of the walk over the B' listing: every segment of every arm. Each is the run the walk's
   paj_run_tok_x makes (YC1fPx: sym_runN_pi_tok over the listing's tables at run_K A_LIM, the span RB_Bspan and the
   shadow entries of that point), with the runner's static check and the window check of its start state (the
   runner lemma YC80x.SRr_run_pi_tok_AJxm's premises sh_static_ok and, through rb_wr_l, its write premise), where it
   stops, why, and its obligations. Branch successors are paj_branch's (add_cond with the condition or its negation);
   the state after a call is st_ok_pi_after_call's (ss_after_call over the kept regions, at the havoc base of the
   .wip: 40 / 60 / 80), with that lemma's computable premises (rb_after_okb). Offsets from the entry. ---- *)
Notation RBR := (shst * ptrun_status asym)%type.
Definition RB_RUN (SH : list shent) (ss : sstate) : RBR :=
  sym_runN_pi_tok B_prog_tpi B_prog_tw (run_K A_LIM RB_Bx SH ss) RB_Bx RB_Bspan SH FUEL ss.
Definition RB_OK (SH : list shent) (ss : sstate) : bool :=
  sh_static_ok (run_K A_LIM RB_Bx SH ss) RB_Bx RB_Bspan SH (ss_facts ss) (ss_mem ss) &&
  forallb rb_win_okb (wins_of (ss_mem ss)).
Definition rb_off (x : RBR) : Z := ss_pc (sh_ss (fst x)) - rb_pc0.
Definition rb_br (x : RBR) (taken : bool) : sstate :=
  match snd x with
  | PTS_stopped (SR_branch c a b) => add_cond (sh_ss (fst x)) (mkAC (if taken then c else neg_bc c) a b)
  | _ => sh_ss (fst x)
  end.
Definition rb_retk (ss : sstate) : Z := match sr_get (ss_regs ss) 1 with SOff _ z => z | _ => 0 end.
Definition rb_after (x : RBR) (idxs : list nat) (k : nat) : sstate :=
  let ss := sh_ss (fst x) in ss_after_call ss (pick (ss_mem ss) idxs) k (rb_retk ss).
Definition rb_after_okb (x : RBR) (idxs : list nat) (k : nat) : bool :=
  let ss := sh_ss (fst x) in let rs := pick (ss_mem ss) idxs in
  match ss_resv ss with None => true | Some _ => false end && (k + 16 <=? A_TEXT)%nat &&
  ss_atoms_p (pband k A_TEXT) ss && regions_wf rs && no_cdata rs && mem_atoms_p (pband k A_TEXT) rs &&
  sv_eqb (sr_get (ss_regs ss) 1) (SOff A_TEXT (rb_retk ss)) && (0 <=? rb_retk ss) && (rb_retk ss <? 2 ^ 40).
(* the regions each call keeps: the unpoison call drops the shadow-base GOT slot and cell (the base is in s2); the
   realloc call drops the old head (realloc frees the block); the REFUSED call of own keeps the frame only *)
Definition rb_keep_u : list nat := [0; 3; 4; 5; 6; 7; 8; 9]%nat.
Definition rb_keep_r : list nat := [0; 1; 2; 3; 4; 6; 7]%nat.
Definition rb_keep_o : list nat := [0]%nat.
(* g_live after disown and refused(n)'s held = g_live + n, saturating (sltu / neg / or) *)
Definition rb_live1 : sv := SAlu ALU_SUB (SOff 35 0) (hdr_sv 37).
Definition rb_held : sv :=
  SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SAlu ALU_ADD rb_live1 (SOff 11 0)) rb_live1))
    (SAlu ALU_ADD rb_live1 (SOff 11 0)).

(* p = NULL: the beqz at +28, then the tail call of fuzz_malloc at +140 *)
Definition rb_x0 : RBR := RB_RUN rb_SH0 ss_rb0.
Definition rb_x0n : RBR := RB_RUN rb_SH0 (rb_br rb_x0 true).
(* p <> NULL: the CHOSEN-FAIL test at +68; CHOSEN-FAIL to the shared epilogue's ret at +108; the main path through
   the decided TOOBIG and UBSan tests to the unpoison call (ret +252); the head checks, head read and g_live -= k to
   the realloc call (ret +404); the NULL test at +404 *)
Definition rb_x1 : RBR := RB_RUN rb_SH0 ss_rb.
Definition rb_xcf : RBR := RB_RUN rb_SH0 (rb_br rb_x1 false).
Definition rb_xm : RBR := RB_RUN rb_SH0 (rb_br rb_x1 true).
Definition rb_su : sstate := rb_after rb_xm rb_keep_u 40.
Definition rb_xu : RBR := RB_RUN rb_SH1 rb_su.
Definition rb_sr : sstate := rb_after rb_xu rb_keep_r 60.
Definition rb_xr : RBR := RB_RUN rb_SH0 rb_sr.
(* SUCCESS: the tail call of own at +436 *)
Definition rb_xs : RBR := RB_RUN rb_SH0 (rb_br rb_xr false).
(* REFUSED: refused(n) stops at its two tests (+468 g_peak >= held, +484 g_most < n); pk = true: the peak is kept,
   false: g_peak := held; mo = true: n > g_most, g_ran_out kept, false: g_ran_out := 1. Each of the four paths reaches
   the call of own (ret +512); after it, the jump at +512 and the shared epilogue's ret at +108 *)
Definition rb_xf : RBR := RB_RUN rb_SH0 (rb_br rb_xr true).
Definition rb_xf_pk (pk : bool) : RBR := RB_RUN rb_SH0 (rb_br rb_xf pk).
Definition rb_xf_own (pk mo : bool) : RBR := RB_RUN rb_SH0 (rb_br (rb_xf_pk pk) mo).
Definition rb_xf_ret (pk mo : bool) : RBR := RB_RUN rb_SH0 (rb_after (rb_xf_own pk mo) rb_keep_o 80).

Lemma rb_run_p0 : RB_OK rb_SH0 ss_rb0 = true /\ rb_off rb_x0 = 28 /\
  snd rb_x0 = PTS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0)) /\ sh_obls (fst rb_x0) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_p0_tail : RB_OK rb_SH0 (rb_br rb_x0 true) = true /\ rb_off rb_x0n = 140 /\
  snd rb_x0n = PTS_call AS_fuzz_malloc /\ sh_obls (fst rb_x0n) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_entry : RB_OK rb_SH0 ss_rb = true /\ rb_off rb_x1 = 68 /\
  snd rb_x1 = PTS_stopped (SR_branch BC_NE (SOff 33 0) (SOff 34 0)) /\ sh_obls (fst rb_x1) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_chosen_fail : RB_OK rb_SH0 (rb_br rb_x1 false) = true /\ rb_off rb_xcf = 108 /\
  snd rb_xcf = PTS_stopped (SR_jalr (SOff 1 0)) /\ sh_obls (fst rb_xcf) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_unpoison : RB_OK rb_SH0 (rb_br rb_x1 true) = true /\ rb_off rb_xm = 252 /\
  snd rb_xm = PTS_call AS___asan_unpoison_memory_region /\ sh_obls (fst rb_xm) = [] /\
  rb_after_okb rb_xm rb_keep_u 40 = true /\ rb_retk (sh_ss (fst rb_xm)) = rb_pc0 + 252.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_realloc : RB_OK rb_SH1 rb_su = true /\ rb_off rb_xu = 404 /\
  snd rb_xu = PTS_call AS___wrap_realloc /\ sh_obls (fst rb_xu) = [] /\
  rb_after_okb rb_xu rb_keep_r 60 = true /\ rb_retk (sh_ss (fst rb_xu)) = rb_pc0 + 404.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_null_test : RB_OK rb_SH0 rb_sr = true /\ rb_off rb_xr = 404 /\
  snd rb_xr = PTS_stopped (SR_branch BC_EQ (SOff 64 0) (SLit 0)) /\ sh_obls (fst rb_xr) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_success : RB_OK rb_SH0 (rb_br rb_xr false) = true /\ rb_off rb_xs = 436 /\
  snd rb_xs = PTS_call AS_own /\ sh_obls (fst rb_xs) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_refused_peak : RB_OK rb_SH0 (rb_br rb_xr true) = true /\ rb_off rb_xf = 468 /\
  snd rb_xf = PTS_stopped (SR_branch BC_GEU (SOff 38 0) rb_held) /\ sh_obls (fst rb_xf) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_run_refused_most : forall pk, RB_OK rb_SH0 (rb_br rb_xf pk) = true /\ rb_off (rb_xf_pk pk) = 484 /\
  snd (rb_xf_pk pk) = PTS_stopped (SR_branch BC_LTU (SOff 39 0) (SOff 11 0)) /\ sh_obls (fst (rb_xf_pk pk)) = [].
Proof. intros []; vm_compute; repeat split; reflexivity. Qed.
Lemma rb_run_refused_own : forall pk mo, RB_OK rb_SH0 (rb_br (rb_xf_pk pk) mo) = true /\
  rb_off (rb_xf_own pk mo) = 512 /\ snd (rb_xf_own pk mo) = PTS_call AS_own /\ sh_obls (fst (rb_xf_own pk mo)) = [] /\
  rb_after_okb (rb_xf_own pk mo) rb_keep_o 80 = true /\ rb_retk (sh_ss (fst (rb_xf_own pk mo))) = rb_pc0 + 512.
Proof. intros [] []; vm_compute; repeat split; reflexivity. Qed.
Lemma rb_run_refused_ret : forall pk mo, RB_OK rb_SH0 (rb_after (rb_xf_own pk mo) rb_keep_o 80) = true /\
  rb_off (rb_xf_ret pk mo) = 108 /\ snd (rb_xf_ret pk mo) = PTS_stopped (SR_jalr (SOff 1 0)) /\
  sh_obls (fst (rb_xf_ret pk mo)) = [].
Proof. intros [] []; vm_compute; repeat split; reflexivity. Qed.

(* ---- the statics each arm leaves in the symbolic state at its last stop (what the text stage reads with
   rb_chunk_val): g_count + 1 everywhere; CHOSEN-FAIL g_fail_at := SIZE_MAX; after disown g_live = live - k;
   REFUSED g_peak := held unless the peak is kept, g_ran_out := 1 unless n > g_most ---- *)
Definition rb_rg (o : nat) (w : N) (wr : bool) (v : sv) : YP09.region :=
  YP09.mkRegion (Some o) 0 (Z.of_N w) 0 (if wr then Z.of_N w else 0) [YP09.mkChunk 0 (CVal w v)].
Lemma rb_statics_chosen_fail :
  nth_error (ss_mem (sh_ss (fst rb_xcf))) 3 = Some (rb_rg O_g_count 8 true (SOff 33 1)) /\
  nth_error (ss_mem (sh_ss (fst rb_xcf))) 4 = Some (rb_rg O_g_fail_at 8 true (SLit 18446744073709551615)) /\
  nth_error (ss_mem (sh_ss (fst rb_xcf))) 5 = Some (rb_rg O_g_live 8 true (SOff 35 0)) /\
  nth_error (ss_mem (sh_ss (fst rb_xcf))) 6 = Some (rb_rg O_g_ran_out 1 true (SOff 36 0)) /\
  nth_error (ss_mem (sh_ss (fst rb_xcf))) 8 = Some (rb_rg O_g_peak 8 true (SOff 38 0)) /\
  nth_error (ss_mem (sh_ss (fst rb_xcf))) 9 = Some (rb_rg O_g_most 8 false (SOff 39 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_statics_success :
  nth_error (ss_mem (sh_ss (fst rb_xs))) 1 = Some (rb_rg O_g_count 8 true (SOff 33 1)) /\
  nth_error (ss_mem (sh_ss (fst rb_xs))) 2 = Some (rb_rg O_g_fail_at 8 true (SOff 34 0)) /\
  nth_error (ss_mem (sh_ss (fst rb_xs))) 3 = Some (rb_rg O_g_live 8 true rb_live1) /\
  nth_error (ss_mem (sh_ss (fst rb_xs))) 4 = Some (rb_rg O_g_ran_out 1 true (SOff 36 0)) /\
  nth_error (ss_mem (sh_ss (fst rb_xs))) 5 = Some (rb_rg O_g_peak 8 true (SOff 38 0)) /\
  nth_error (ss_mem (sh_ss (fst rb_xs))) 6 = Some (rb_rg O_g_most 8 false (SOff 39 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rb_statics_refused : forall pk mo,
  nth_error (ss_mem (sh_ss (fst (rb_xf_own pk mo)))) 1 = Some (rb_rg O_g_count 8 true (SOff 33 1)) /\
  nth_error (ss_mem (sh_ss (fst (rb_xf_own pk mo)))) 2 = Some (rb_rg O_g_fail_at 8 true (SOff 34 0)) /\
  nth_error (ss_mem (sh_ss (fst (rb_xf_own pk mo)))) 3 = Some (rb_rg O_g_live 8 true rb_live1) /\
  nth_error (ss_mem (sh_ss (fst (rb_xf_own pk mo)))) 4 =
    Some (rb_rg O_g_ran_out 1 true (if mo then SOff 36 0 else SLit 1)) /\
  nth_error (ss_mem (sh_ss (fst (rb_xf_own pk mo)))) 5 =
    Some (rb_rg O_g_peak 8 true (if pk then SOff 38 0 else rb_held)) /\
  nth_error (ss_mem (sh_ss (fst (rb_xf_own pk mo)))) 6 = Some (rb_rg O_g_most 8 false (SOff 39 0)).
Proof. intros [] []; vm_compute; repeat split; reflexivity. Qed.

(* ==== THE TEXT STAGE ====
   the kit's text tfuzz_realloc_specX in the post-implication form with THE OUTCOME conjuncts (the kit's cut 7cdbb61b5fa0,
   lib/A/PRH_FnAlloc.v blob 4d8aeba047e5 :412-516, the FAMILY and THE OUTCOME blocks of its header; callee texts
   tfuzz_malloc_specX :270 and town_specX :568, prh_alloc_post :220; PRH_Base.v blob ef7c8ca98529; PRH_Refute.v blob
   23f7a37f01c9; S1Ledger.v blob 8cf15eeb6311) at image B''s PrhImg prh_img_B
   (lib/B/PRH_ImgB.v), preset's CfParams_preset, the room instance prh_room_live_a8 and the allocator relation ARcfx
   (the cf layer's ARcf pa_segs B with xs_placed_cf; YGcallcf.v), proved with the prep part above.
   The ledger is read only through PRH_Base's named projections (Section ledger_proj, prh_ledger_most / _own
   included) and S1Ledger's lemmas; the statics' record prh_glob is BUILT in one place (rb_glob_mk: S1Ledger has no
   constructor for a g_peak raised to a value other than Z.max peak live', which the REFUSED arm needs). g_most and
   g_own_ran_out are fields of prh_glob: a run or a call that writes neither keeps them (rb_om_kept), and every glob
   the walk builds takes them from the entry ledger (prh_ledger_most / prh_ledger_own). The m-form: memnorm rides
   through every run by the _inv runner (YSRrMemnorm's carrier), through the unpoison call by
   YGcallMxmn.aj_unpoison_x_m, through the realloc call by the realloc leaf's last conjunct (YGcallRx.realloc_leaf_x),
   and through the two callee texts by their fpostm.
   THE POSITION (the FAMILY block): no position at entry; each arm of the post transfers ANY position whose next
   events are that arm's own E, by exactly length E. The walk reuses the kit's one-event steps over the realloc
   leaf's outcome (PresetRoomPosKeep blob dc3f6bee1e0e: room_pos_keep_realloc for SUCCESS, E = [HRe (k + cf_head)
   (n + cf_head)]; room_pos_keep_realloc_null for REFUSED, E = []) and PRH_Base.prh_run_at_one (rb_pos_one); E = []
   at CHOSEN-FAIL keeps the state (rb_pos_nil); p = NULL is fuzz_malloc's post-form text (MALLOC) verbatim.
   THE OUTCOME (PRH_Base.v, THE OUTCOME UNDER THE RUN HYPOTHESIS): at a consumer allocation (prh_cons_from) whose next
   event is the call's granted one, with cnt <> fail, res <> 0 and the advance by that event. p = NULL: fuzz_malloc's
   own outcome conjunct (MALLOC), read BY NAME (rb_conj_pick, a copy of the kit's ec_conj_pick), so no conjunct the kit
   adds to fuzz_malloc's post can shift the others. p <> NULL: CHOSEN-FAIL has cnt = fail; SUCCESS has res >= 4112 and
   the advance it already proves; REFUSED is excluded at the realloc call itself (PRH_Refute.prh_refute_at: the
   realloc leaf's NULL witness mt_refused at the call's allocator state S is PRH_Refute's machine-level refusal
   prh_granted_null S, impossible at a consumer HRe of the run at S).
   THE LIVE PREMISE is per call, guarded by cnt <> fail (the cut's text): rb_p0 passes it to MALLOC as it is; rb_nz
   uses it after the CHOSEN-FAIL test, where cnt <> fail holds.
   The kit's fpre ends in frm_zero (fp_csr fx) (FRM0-ENTRY). fx is the Section's float state, the same at every call
   of the walk, so each callee's fpre (MALLOC, OWN) takes that conjunct from the entry's. *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
(* image B''s CfImg record, generated from the B' unstripped twin c90d4fa5 (lib/AU/CfImgB.v, AL base) *)
#[local] Existing Instance CfImg_B.
#[local] Notation PA := (@PI_prog_B rc).
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).

(* image numbers, computed from the generated instances (never typed) *)
Ltac rb_lits :=
  repeat match goal with
  | |- context [@pa_val ?r B_prog_listing ?P ?j] =>
    let v := eval vm_compute in (@pa_val r B_prog_listing P j) in
    lazymatch v with Zpos _ => idtac | Z0 => idtac end; change (@pa_val r B_prog_listing P j) with v
  | |- context [B_prog_val ?j] =>
    let v := eval vm_compute in (B_prog_val j) in
    lazymatch v with Zpos _ => idtac | Z0 => idtac end; change (B_prog_val j) with v
  | |- context [rb_wd ?o] => let v := eval vm_compute in (rb_wd o) in change (rb_wd o) with v
  end;
  cbv [pi_g_live pi_g_peak pi_g_count pi_g_fail pi_g_ran_out pi_g_most pi_g_own_ran_out
       pi_gz_live pi_gz_peak pi_gz_count pi_gz_fail pi_gz_ran_out pi_gz_most pi_gz_own_ran_out prh_img_B];
  try change (Z.of_nat 8) with 8; try change (Z.of_nat 1) with 1.

Lemma rb_STK_v : STK_fuzz_realloc = 16448.
Proof. vm_compute. reflexivity. Qed.
Lemma rb_stk_malloc : STK_fuzz_malloc = 16400.
Proof. vm_compute. reflexivity. Qed.
Lemma rb_stk_own : STK_own = 4128.
Proof. vm_compute. reflexivity. Qed.
Lemma rb_cf_head : cf_head = 16.
Proof. reflexivity. Qed.
Lemma rb_cf_max : cf_malloc_max = 2 ^ 28 + 2 ^ 27.
Proof. reflexivity. Qed.
(* the realloc call's return site is the generated pi_ret_realloc (B' 0x86048) *)
Lemma rb_ret_site : BASE + (rb_pc0 + 404) = pi_ret_realloc.
Proof. vm_compute. reflexivity. Qed.
(* the written statics are the generated PrhImg cells *)
Lemma rb_vals : VAL O_g_count = pi_g_count /\ VAL O_g_fail_at = pi_g_fail /\ VAL O_g_live = pi_g_live /\
  VAL O_g_peak = pi_g_peak /\ VAL O_g_ran_out = pi_g_ran_out /\ VAL O_g_most = pi_g_most.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- the PST bridge: every byte of the walk's six static objects (the five it writes and g_most, which it reads) is
   a byte of B''s prh_pst ---- *)
Lemma rb_pst_obj : forall o a, In o (O_g_most :: rb_wobjs) -> VAL o <= a < VAL o + rb_wd o -> Exists (in_zr a) PST.
Proof.
intros o a Ho Ha. unfold rb_wobjs in Ho. cbn [In] in Ho.
destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; revert Ha; rb_lits; intros Ha; unfold prh_pst; rb_lits;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Qed.
Lemma rb_obj_pst : forall a, rb_obj_byte a -> Exists (in_zr a) PST.
Proof.
intros a Ha. unfold rb_obj_byte in Ha. apply Exists_exists in Ha as (o & Ho & Hb).
exact (rb_pst_obj o a (or_intror Ho) Hb).
Qed.
(* the same, with the width a region of the walk reads, checked by computation *)
Lemma rb_pst_objw : forall o w a, existsb (Nat.eqb o) (O_g_most :: rb_wobjs) && (w <=? rb_wd o) = true ->
  VAL o <= a < VAL o + w -> Exists (in_zr a) PST.
Proof.
intros o w a Hb Ha. apply andb_true_iff in Hb as [Hb Hw]. apply Z.leb_le in Hw.
apply existsb_exists in Hb as (o' & Ho' & Hoo). apply Nat.eqb_eq in Hoo. subst o'.
apply (rb_pst_obj o a Ho'). lia.
Qed.
(* the statics are image bytes in low memory, below the shadow offset (2 ^ 31 bounds it: SHADOW_OFF's value) *)
Lemma rb_pst_low : forall a, Exists (in_zr a) PST -> 4096 <= a < SHADOW_OFF /\ SHADOW_OFF < 2 ^ 31.
Proof.
intros a Ha. unfold prh_pst in Ha. revert Ha; rb_lits; intros Ha.
repeat (apply Exists_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; unfold SHADOW_OFF; lia|]).
inversion Ha.
Qed.
(* g_most's and g_own_ran_out's bytes: no byte a run of the walk writes (neither the frame nor a written static) *)
Definition rb_far : list (Z * Z) := [(pi_g_most, Z.of_nat pi_gz_most); (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out)].
Lemma rb_far_obj : forall a, Exists (in_zr a) rb_far -> ~ rb_obj_byte a /\ Exists (in_zr a) PST.
Proof.
intros a Ha. unfold rb_far in Ha. split.
- intros Hb. unfold rb_obj_byte, rb_wobjs in Hb. revert Ha Hb; rb_lits; intros Ha Hb.
  apply Exists_cons in Ha as [Ha|Ha]; [|apply Exists_cons in Ha as [Ha|Ha]; [|inversion Ha]];
  unfold in_zr in Ha; cbn [fst snd] in Ha;
  repeat (apply Exists_cons in Hb as [Hb|Hb];
    [revert Hb; rb_lits; intros Hb; lia|]); inversion Hb.
- unfold prh_pst. revert Ha; rb_lits; intros Ha.
  apply Exists_cons in Ha as [Ha|Ha]; [|apply Exists_cons in Ha as [Ha|Ha]; [|inversion Ha]];
  unfold in_zr in Ha; cbn [fst snd] in Ha;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ].
Qed.

(* ---- prh_most / prh_own (PRH_Base :499-502): the value of g_most read off the entry ledger, and both cells kept by
   whatever writes neither ---- *)
Lemma rb_most_val : forall (W : world SEGS) mem most, prh_most (PA := PA) W mem most ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_most pi_gz_most most /\ 0 <= most < 2 ^ 64.
Proof. intros W mem most H. exact H. Qed.
Lemma rb_om_kept : forall (W W' : world SEGS) m m' most own,
  (forall a, Exists (in_zr a) rb_far -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  prh_most (PA := PA) W m most -> prh_own (PA := PA) W m own ->
  prh_most (PA := PA) W' m' most /\ prh_own (PA := PA) W' m' own.
Proof.
intros W W' m m' most own K [Hv Hr] [Hv' Hr']. split; split; [| exact Hr | | exact Hr'].
- apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ Hv). intros j Hj. apply (prh_mbyte_of_aview (PA := PA)). apply K.
  unfold rb_far. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply (prh_val_mem_keep (PA := PA) _ _ _ _ _ Hv'). intros j Hj. apply (prh_mbyte_of_aview (PA := PA)). apply K.
  unfold rb_far. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* rb_om_kept's premise from a run's keep K (rb_keep's form, or rb_keep0's without the static exception) *)
Ltac rb_far_by K :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hnb := fresh "Hnb" in let Hps := fresh "Hps" in intros a Ha;
  destruct (rb_far_obj a Ha) as [Hnb Hps]; pose proof (rb_pst_low a Hps);
  first [ apply K; [lia | unfold SHADOW_OFF in *; lia | exact Hnb] | apply K; [lia | unfold SHADOW_OFF in *; lia] ].

(* ---- prh_glob (PRH_Base :507-511): BUILT in this one place. The REFUSED arm needs g_peak raised to
   Z.max peak (Z.min SIZE_MAXZ (lsum - k + n)) while g_live is lsum - k; S1Ledger's prh_glob_final_le keeps the
   entry's g_peak and prh_glob_final sets it to Z.max peak live', neither of which is that value ---- *)
Lemma rb_glob_mk : forall (W : world SEGS) mem live peak cnt fail ran most own,
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_live pi_gz_live live ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_peak pi_gz_peak peak ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_count pi_gz_count cnt ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_fail pi_gz_fail fail ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_ran_out pi_gz_ran_out ran ->
  prh_most (PA := PA) W mem most -> prh_own (PA := PA) W mem own ->
  0 <= live <= peak -> peak < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 -> (ran = 0 \/ ran = 1) ->
  prh_glob (PA := PA) W mem live peak cnt fail ran most own.
Proof. intros. unfold prh_glob. repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. Qed.

(* ---- the write premise and the keeps of a run (the prep's rb_wr_l / rb_keep_l / rb_keep0_l at PST := prh_pst) ---- *)
Ltac rb_wr Uspx :=
  lazymatch goal with |- forall a, in_wrange ?Ex _ a -> _ =>
  let HEx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  refine (rb_wr_l PST Ex _ _ _ _ _ _ _ _ a rb_obj_pst _ HEx Uspx _ Ha);
  [vm_compute; reflexivity | rewrite ?rb_STK_v, ?rb_stk_own, ?rb_stk_malloc; lia] end.
Ltac rb_keep K Uspx :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
  let HEx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (ew Ex 2) - 48 <= a < bv_unsigned (ew Ex 2)) ->
     ~ rb_obj_byte a -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
    by (let a := fresh "a" in let H1 := fresh "H1" in let H2 := fresh "H2" in let H3 := fresh "H3" in
        intros a H1 H2 H3;
        exact (rb_keep_l Wx Ex rsx mA mB a HFr ltac:(vm_compute; reflexivity) HEx H1 H2 H3));
  rewrite Uspx in K; clear HFr end.
Ltac rb_keep0 K Uspx :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?mA) (mrestrict (w_H ?Wx) ?mB) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (ew Ex 2) - 48 <= a < bv_unsigned (ew Ex 2)) ->
     aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
    by (let a := fresh "a" in let H1 := fresh "H1" in let H2 := fresh "H2" in
        intros a H1 H2; exact (rb_keep0_l Wx Ex rsx mA mB a HFr ltac:(vm_compute; reflexivity) H1 H2));
  rewrite Uspx in K; clear HFr end.
(* name a machine state of a stopped state *)
Ltac rb_gen t x :=
  first [ is_var t; rename t into x
        | let Eg := fresh "Eg" in remember t as x eqn:Eg in *; clear Eg ].
(* the top-level conjuncts of a hypothesis (a syntactic `_ /\ _` only), then the goal BY ITS TYPE: a copy of the kit's
   ec_conj_split / ec_conj_pick (lib/AU/Prog/Ent102CallB.v :169-175; FuzzStrdup.v's sd_conj_pick is the
   same copy).
   fuzz_malloc's post is read through it, so a conjunct the kit adds to that post cannot shift the others. *)
Ltac rb_conj_split H :=
  lazymatch type of H with
  | _ /\ _ =>
    let H1 := fresh "Rc" in let H2 := fresh "Rc" in destruct H as [H1 H2]; rb_conj_split H1; rb_conj_split H2
  | _ => idtac
  end.
Ltac rb_conj_pick H := rb_conj_split H; assumption.
(* a static region kept by a call: its base is the object's address; KP keeps every PST byte *)
Ltac rb_objH Ha :=
  cbn [base_val YP09.r_base] in Ha;
  lazymatch type of Ha with context [bv_unsigned (ew ?Ex ?x)] =>
  let HEx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
  rewrite (HEx x) in Ha by (cbv; lia) end.
Ltac rb_pstH Ha :=
  rb_objH Ha;
  lazymatch type of Ha with context [@pa_val ?r ?L ?P ?x] =>
  first [ apply (rb_pst_objw x 8); [vm_compute; reflexivity | lia]
        | apply (rb_pst_objw x 1); [vm_compute; reflexivity | lia] ] end.
Ltac rb_stk Ha KP := apply (prh_mbyte_of_aview (PA := PA)); apply KP; rb_pstH Ha.
Ltac rb_stw Ha := intros _; apply pst_writable_B; rb_pstH Ha.
(* a static's value read off a stopped state's region chunk: its base is the object's address v *)
Ltac rb_objv H v :=
  cbn [base_val YP09.r_base N.to_nat Pos.to_nat] in H;
  lazymatch type of H with context [bv_unsigned (ew ?Ex ?x)] =>
    let HEx := lazymatch goal with Hh : img_env _ _ Ex |- _ => Hh end in
    rewrite (HEx x) in H by (cbv; lia);
    replace (VAL x) with v in H by (vm_compute; reflexivity) end;
  rewrite ?Z.add_0_r in H.
(* a register of a stopped call state, its symbolic value computed and not normalized *)
Ltac rb_reg HS r X :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as X;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in X;
    cbn [ms_regs restrict mkst] in X
  end.

(* ---- the position clauses of the post (the FAMILY block), from the kit's steps. E = []: a step that keeps every
   position (same history) gives the arm's transfer by length [] = 0. E = [ev]: a step stated over the model run's
   event at i (PresetRoomPosKeep's nth_error form) gives it by length [ev] = 1, through PRH_Base.prh_run_at_one ---- *)
Lemma rb_pos_nil : forall S S',
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PresetRoomPos.iface_room_pos sm x os i H0 hist S') ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S'.
Proof.
intros S S' K sm x os i H0 hist HP _. exists hist.
replace (i + length (@nil PresetReqAt.hev))%nat with i by (simpl; lia). exact (K sm x os i H0 hist HP).
Qed.
Lemma rb_pos_one : forall S S' ev,
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     nth_error (PresetRun.hruns sm x os) i = Some ev ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S') ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
    (i : nat) (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [ev] ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [ev])%nat H0 hist' S'.
Proof.
intros S S' ev K sm x os i H0 hist HP Hr. replace (i + length [ev])%nat with (Datatypes.S i) by (simpl; lia).
exact (K sm x os i H0 hist HP (proj1 (PRH_Base.prh_run_at_one sm x os i ev) Hr)).
Qed.

(* ---- the post: the kit's named projection tfrP_Q (PRH_FnAlloc.v; tfrP_Q_check ties it to tfuzz_realloc_specX's Q). The
   copy rb_Q that stood here (row :849 of blob 9e10ac5d2a55, a near-copy of the text's Q) is gone: the arms state tfrP_Q and build it
   through tfrP_Q_of_R and the arm records tfrP_R1 .. tfrP_R4, field by field ---- *)

(* ---- the p = 0 entry (frame 48) ---- *)
Lemma rb_entry0 : forall B (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
  STK ly S Hp (W : world SEGS) regs mem md ch,
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 48 <= STK -> getr regs 10 = w64 0 ->
  st_ok_pi SEGS VAL (RB_EI regs []) ss_rb0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + rb_pc0)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS RB_Bx rb_SH0 (RB_EI regs []) (mrestrict (w_H W) mem).
Proof.
intros B ARx STK ly S Hp W regs mem md ch HPRE H48 H10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := RB_EI regs []).
assert (EL : forall j, (j < A_TEXT)%nat -> ew E j = ew (Ereg regs (map (Z_to_bv 64) [])) j)
by (intros j Hj; unfold E, RB_EI; apply Eimg_low; exact Hj).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_rb0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10. change (bv_unsigned (Z_to_bv 64 0)) with 0. change (2 ^ 4) with 16.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat match goal with |- _ /\ _ => split end; try lia; exact I.
- unfold sh_ok, rb_SH0. apply Forall_nil.
Qed.

Section f.
Variable B : asyms.
(* the allocator relation of the S1 walks (YGcallcf.v): the cf layer's ARcf with the error-buffer extents placed *)
#[local] Notation ARcfx := (fun ly S Hp (W : world SEGS) mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* ---- Section hypotheses: callee texts and named stand-ins only ---- *)
(* callee text: own (the kit's town_specX, the kit's 4b batch d6318e886fd9 PRH_FnAlloc.v blob 95e26ff95e63 :529, unchanged by
   the batch; B' 0x85dbc, the row of own at image B'; owner a Theorem Labs lane) *)
Hypothesis OWN : town_specX (L := B_prog_listing) (PA := PA) B ARcfx SK.
(* callee text: fuzz_malloc (the tfuzz_malloc_specX in the post-implication form with THE OUTCOME conjunct, the 4b
   batch PRH_FnAlloc.v blob 95e26ff95e63 :269; B' 0x85d08, row AL2 of the internal file FREE-PIECES-102.md Part 5; owner
   a Theorem Labs lane), tail-called on p = NULL *)
Hypothesis MALLOC : tfuzz_malloc_specX (L := B_prog_listing) (PA := PA) B ARcfx SK.
(* callee text: __asan_unpoison_memory_region at the second allocator (YGcfHp.v) *)
Hypothesis AUNPOISON : aunpoison_realizes_cf SEGS B.
(* callee text: the realloc wrapper, the cgif layer's primed _k row with the memnorm keep
   (lib/Reusable/YGcfInstReallocKKeep.v, commit 4f9d7e8b76e5; the
   amreal' RZ_cf walk, the re-hiding leaf realloc_leaf_cf_rh_keep, the entry room ROOM_cf_k (RK_realloc + k) and the
   entry headroom cf_hull_adm). YGcallRkKeep.aj_realloc_x_cfR_keep takes it as it
   stands, so no Let lifts it here *)
Hypothesis AREAL_cf : forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep SEGS B Hp (SIGMA AS___wrap_realloc) k.
(* STAND-IN for the unit's image binding of B' (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
(* STAND-IN for the unit's image binding of B' (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* STAND-IN for the unit's image binding of B' (TfibSyms analogue; owned by the kit), proved once by the final instance
   (lib/AU/CfAroPresetB.v errno_relro_preset_AU from TfibSyms): errno is apart from the RELRO range and the class-full
   report's read-only reads, the row YGcallcf.arodata_ok_cf_of_journal_P reads for QMm_cf at the realloc call *)
Hypothesis pal_errno_relro : errno_relro_t B.
(* the unpoison entry of the listing is CfImg_B's (lib/AU/CfImgB.v, generated from the B' twin c90d4fa5) *)
Lemma pal_unpoison : SIGMA AS___asan_unpoison_memory_region = cf_pc_unpoison.
Proof. vm_compute. reflexivity. Qed.

(* the allocator's laws: the cf layer's AR_laws_ok_cf (YG0lawscf.v), at YGcallcf's bridge *)
Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs SEGS B.
Let XSL := ARx_xs_law_xs SEGS B.
Let AUNPOISONx : aunpoison_realizes_x SEGS B ARcfx cf_head cf_pc_unpoison := aunpoison_realizes_cf_xs SEGS B AUNPOISON.
Lemma rb_pst_ok : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Proof. intros a Ha. split; [exact (pst_in_img_B a Ha) | exact (proj1 (pal_pst_ok a Ha))]. Qed.
Let RUN := @paj_run_x_m fx rc SK B_prog_listing PL_prog_B PA B PST ARcfx _ LAWS rb_pst_ok.
(* the same runner carrying the memnorm keep from a fixed memory m0 (the memnorm carrier, YSRrMemnorm.v:40) *)
Let RUNM (m0 : word -> option byte) := @paj_run_x_m_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARcfx _ LAWS
  rb_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
Let BR := @paj_branch fx rc B_prog_listing PA.
Let RET := @paj_ret_at fx rc B_prog_listing PL_prog_B PA.
(* ---- the primed relation of the re-hiding move (ROUTE STOP + LIFT): the segments after the realloc call run over
   R := wle' SEGS RZ_cf, by the runner's _invR form, paj_branchR and aj_call_xR ---- *)
#[local] Notation RR := (wle' SEGS YGcfRehidePost.RZ_cf).
Let RUNMR (m0 : word -> option byte) := @paj_run_x_m_invR fx rc SK B_prog_listing PL_prog_B PA B PST ARcfx _ LAWS
  rb_pst_ok (fun m => YAkMemnorm.memnorm SEGS m0 -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))
  RR (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let BRR := @YSRrG.paj_branchR fx rc B_prog_listing PA RR.
(* own's plain text inside a caller over R: its SRr lifts (YA0nH.SRr_SRrG) and its post apost_base_x lifts to the R
   form (YCbqG.apost_base_x_R_lift), both at wle <= wle' (YA0nH.wle_wle') *)
Lemma rb_callee_lift : forall (Wc : world SEGS) c STK FP regs ly S Hp (W : world SEGS) mem md Q,
  SRr SEGS Wc c (apost_base_x (SK := SK) SEGS B PST ARcfx STK FP regs ly S Hp W mem md Q) ->
  SRrG SEGS RR Wc c (apost_base_xR (SK := SK) SEGS B PST ARcfx RR STK FP regs ly S Hp W mem md Q).
Proof.
intros Wc c STK FP regs ly S Hp W mem md Q H.
apply (SRr_SRrG SEGS RR (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
eapply SRr_mono; [exact H|]. intros W' c' _ HP.
exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARcfx RR (wle_wle' SEGS YGcfRehidePost.RZ_cf)
  STK FP regs ly S Hp W mem md Q W' c' HP).
Qed.
(* a post of the plain segments (rb_p0, CHOSEN-FAIL) as the text's primed post *)
Lemma rb_post_lift : forall STK FP regs ly S Hp (W : world SEGS) mem md Q (W' : world SEGS) c',
  fpostm B ARcfx SK STK FP regs ly S Hp W mem md Q W' c' ->
  fpostmR B ARcfx SK RR STK FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK FP regs ly S Hp W mem md Q W' c' H.
exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARcfx RR (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* the image objects the walk keeps a region for are image bytes: the shadow-offset GOT slot and cell (the image's
   writable segments, computed) and the six statics (S1ImgB through the PST bridge) *)
Ltac rb_bnd := match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end; lia.
Lemma rb_objs_img : forall o a, In o (A_OBJ 0 :: A_OBJ 12 :: O_g_most :: rb_wobjs) ->
  VAL o <= a < VAL o + rb_wd o -> in_img SEGS a.
Proof.
intros o a Ho Ha. destruct Ho as [<- | [<- | Ho]].
- change SEGS with rsegs. unfold in_img. revert Ha; rb_lits; intros Ha.
  first [ eexists; split; [do 2 right; left; reflexivity | rb_bnd] | eexists; split; [do 3 right; left; reflexivity | rb_bnd] ].
- change SEGS with rsegs. unfold in_img. revert Ha; rb_lits; intros Ha.
  first [ eexists; split; [do 2 right; left; reflexivity | rb_bnd] | eexists; split; [do 3 right; left; reflexivity | rb_bnd] ].
- exact (pst_in_img_B a (rb_pst_obj o a Ho Ha)).
Qed.
(* the read-only view rides through a journal whose footprint is closed (the image clause; PST is not read-only), at
   any world relation R (the image clause does not read R) *)
Lemma rb_rod_kept : forall (R : world SEGS -> world SEGS -> Prop)
  STK sp0 FP ly S Hp (W : world SEGS) mem md own lyc Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B PST ARcfx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (B_prog_relro a Hr)].
- intros Hp'. exact (pst_not_ro_B a Hp' Hro).
Qed.
(* the read-only view and fpre's two entry bounds survive any change above / below the entry frame *)
Lemma rb_rod_low : forall (W W' : world SEGS) m m',
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W) m) ->
  (forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' H HA a Hro Hn He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (B_prog_relro a Hr)]).
pose proof (@pa_segs_low _ _ PA a Hi) as Hl. pose proof asan_consts as (C1 & _ & _ & _ & C5).
rewrite HA by lia. exact (H a Hro Hn He).
Qed.

(* ---- the p <> 0 entry: ss_rb (frame 48, g_peak written, g_most read: atom 39) ---- *)
Lemma rb_entry : forall STK ly S Hp (W : world SEGS) regs mem md ch p n k cnt fail live peak ran most,
  afn_pre_x SEGS B ARcfx STK ly S Hp W regs mem md ch -> 48 <= STK ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 29 ->
  In (p - 16, k + 16) (ablocks B ly S) -> 0 <= k ->
  val_mem SEGS (mrestrict (w_H W) mem) (p - 16) 8 k ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_live pi_gz_live live ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_peak pi_gz_peak peak ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_count pi_gz_count cnt ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_fail pi_gz_fail fail ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_ran_out pi_gz_ran_out ran ->
  val_mem SEGS (mrestrict (w_H W) mem) pi_g_most pi_gz_most most ->
  0 <= live <= peak -> peak < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 -> 0 <= fail < 2 ^ 64 -> (ran = 0 \/ ran = 1) ->
  0 <= most < 2 ^ 64 ->
  st_ok_pi SEGS VAL (RB_EI regs [SHADOW_OFF; cnt; fail; live; ran; k; peak; most]) ss_rb
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + rb_pc0)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS RB_Bx rb_SH0 (RB_EI regs [SHADOW_OFF; cnt; fail; live; ran; k; peak; most]) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch p n k cnt fail live peak ran most HPRE H48 H10 H11 Hn Hin Hk Hhd
  Hlive Hpeak Hcnt Hfail Hran Hmost Rlp Rpk Rcnt Rfail Rran Rmost.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (PVR : forall x, 0 <= VAL x < 2 ^ 64) by (intros x; apply pa_val_range).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) HAR Hin) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & _).
assert (Hreq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (pal_got_cell B PAL) as HgcD.
assert (Hbimg : forall a, p - 16 <= a < p - 8 -> ~ in_img SEGS a).
{ intros a Ha. apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md (p - 16) (k + 16) a HAR Hin). rewrite Hreq. lia. }
assert (Himg : forall o, In o (A_OBJ 0 :: A_OBJ 12 :: O_g_most :: rb_wobjs) ->
  p - 8 <= VAL o \/ VAL o + rb_wd o <= p - 16).
{ intros o Ho.
  destruct (Z_le_gt_dec (p - 8) (VAL o)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (VAL o + rb_wd o) (p - 16)) as [H2|H2]; [right; exact H2|].
  exfalso. assert (Hw : 1 <= rb_wd o) by (unfold rb_wd; destruct (Nat.eqb o O_g_ran_out); lia).
  apply (Hbimg (Z.max (p - 16) (VAL o)) ltac:(lia)). apply (rb_objs_img o _ Ho). lia. }
rewrite restrict_mkst_fx.
set (E := RB_EI regs [SHADOW_OFF; cnt; fail; live; ran; k; peak; most]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, RB_EI; apply Eimg_env).
assert (EL : forall j, (j < A_TEXT)%nat ->
  ew E j = ew (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; live; ran; k; peak; most])) j)
by (intros j Hj; unfold E, RB_EI; apply Eimg_low; exact Hj).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cnt) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fail) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 live) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ran) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 k) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 peak) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 most) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (EI : forall x, (A_TEXT <= x < A_LIM)%nat -> ew E x = Z_to_bv 64 (VAL x))
by (intros x Hx; unfold E, RB_EI; apply Eimg_img; exact Hx).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall j v, ew E j = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some j) = v).
{ intros j v Hj Hv. cbn [base_val]. rewrite Hj. apply unsigned_lit_small. exact Hv. }
assert (VBI : forall x, (A_TEXT <= x < A_LIM)%nat -> base_val E (Some x) = VAL x).
{ intros x Hx. apply VB; [apply EI; exact Hx | apply pa_val_range]. }
assert (Hw : forall o w q, existsb (Nat.eqb o) (O_g_most :: rb_wobjs) && (w <=? rb_wd o) = true -> 0 <= q < w ->
  writable_at SEGS (mrestrict (w_H W) mem) (VAL o + q)).
{ intros o w q Hb Hq. apply pst_writable_B. apply (rb_pst_objw o w _ Hb). lia. }
destruct rb_vals as (Vcnt & Vfail & Vlive & Vpeak & Vran & Vmost).
assert (OI : forall o, In o (A_OBJ 0 :: A_OBJ 12 :: O_g_most :: rb_wobjs) -> (A_TEXT <= o < A_LIM)%nat).
{ intros o Ho. cbn [In] in Ho. unfold rb_wobjs, O_g_most, O_g_count, O_g_fail_at, O_g_live, O_g_peak, O_g_ran_out in Ho.
  unfold A_OBJ, A_TEXT, A_LIM in *. cbn [In] in Ho. lia. }
assert (OI0 : (A_TEXT <= A_OBJ 0 < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OI12 : (A_TEXT <= A_OBJ 12 < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OIc : (A_TEXT <= O_g_count < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OIf : (A_TEXT <= O_g_fail_at < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OIl : (A_TEXT <= O_g_live < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OIp : (A_TEXT <= O_g_peak < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OIr : (A_TEXT <= O_g_ran_out < A_LIM)%nat) by (apply OI; cbn; tauto).
assert (OIm : (A_TEXT <= O_g_most < A_LIM)%nat) by (apply OI; cbn; tauto).
split.
- unfold ss_rb. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rb_regions, rb_pk, stack_region, got_regionP, bcell_regionP, rb_st, rb_ran, rb_head, rb_most.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VBI (A_OBJ 0) OI0).
      split; [rb_lits; lia|]. split; [rb_lits; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite (EI (A_OBJ 12) OI12), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (PVR (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VBI (A_OBJ 12) OI12).
      split; [rb_lits; lia|]. split; [rb_lits; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RB_Bx SHADOW_OFF);
      [cbn [sv_denot RB_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VBI O_g_count OIc).
      split; [rb_lits; lia|]. split; [rb_lits; lia|].
      split; [intros o Ho; apply (Hw O_g_count 8); [vm_compute; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL O_g_count) 0 8 (SOff 33 0) cnt);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, Vcnt. exact Hcnt.
    * rewrite (VBI O_g_fail_at OIf).
      split; [rb_lits; lia|]. split; [rb_lits; lia|].
      split; [intros o Ho; apply (Hw O_g_fail_at 8); [vm_compute; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL O_g_fail_at) 0 8 (SOff 34 0) fail);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, Vfail. exact Hfail.
    * rewrite (VBI O_g_live OIl).
      split; [rb_lits; lia|]. split; [rb_lits; lia|].
      split; [intros o Ho; apply (Hw O_g_live 8); [vm_compute; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL O_g_live) 0 8 (SOff 35 0) live);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, Vlive. exact Hlive.
    * rewrite (VBI O_g_ran_out OIr).
      split; [rb_lits; lia|]. split; [rb_lits; lia|].
      split; [intros o Ho; apply (Hw O_g_ran_out 1); [vm_compute; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL O_g_ran_out) 0 1 (SOff 36 0) ran);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; destruct Rran; lia | cbn; lia |].
      rewrite Z.add_0_r, Vran. exact Hran.
    * rewrite (VB 10%nat p E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p (-16) 8 (SOff 37 0) k);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      replace (p + -16) with (p - 16) by lia. exact Hhd.
    * rewrite (VBI O_g_peak OIp).
      split; [rb_lits; lia|]. split; [rb_lits; lia|].
      split; [intros o Ho; apply (Hw O_g_peak 8); [vm_compute; reflexivity | lia]|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL O_g_peak) 0 8 (SOff 38 0) peak);
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, Vpeak. exact Hpeak.
    * rewrite (VBI O_g_most OIm).
      split; [rb_lits; lia|]. split; [rb_lits; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL O_g_most) 0 8 (SOff 39 0) most);
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, Vmost. exact Hmost.
  + apply pairwise_disjoint_of_extents.
    unfold rb_regions, rb_pk, stack_region, got_regionP, bcell_regionP, rb_st, rb_ran, rb_head, rb_most, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat p E10) by lia.
    rewrite (VBI (A_OBJ 0) OI0), (VBI (A_OBJ 12) OI12), (VBI O_g_count OIc), (VBI O_g_fail_at OIf), (VBI O_g_live OIl),
      (VBI O_g_ran_out OIr), (VBI O_g_peak OIp), (VBI O_g_most OIm).
    cbn [base_val]. rewrite Usp.
    pose proof (Himg (A_OBJ 0) ltac:(cbn; tauto)) as I0. pose proof (Himg (A_OBJ 12) ltac:(cbn; tauto)) as I12.
    pose proof (Himg O_g_count ltac:(cbn; tauto)) as I1. pose proof (Himg O_g_fail_at ltac:(cbn; tauto)) as I2.
    pose proof (Himg O_g_live ltac:(cbn; tauto)) as I3. pose proof (Himg O_g_ran_out ltac:(cbn; tauto)) as I4.
    pose proof (Himg O_g_peak ltac:(cbn; tauto)) as I5. pose proof (Himg O_g_most ltac:(cbn; tauto)) as I6.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    assert (Hsc : alloc_ceiling <= spZ regs - 48) by lia.
    revert I0 I12 I1 I2 I3 I4 I5 I6 HgcD. rb_lits. intros I0 I12 I1 I2 I3 I4 I5 I6 HgcD.
    revert I0 I12 I1 I2 I3 I4 I5 I6 HgcD Rsp Hb4096 Hbceil C1 Hsc Hk. clear. intros. repeat split; lia.
  + split; [|split].
    * cbn [rb_facts f_atoms atoms_ok]. unfold afact_ok, rb_obj. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      assert (Hp16 : p mod 16 = 0) by (replace p with ((p - 16) + 1 * 16) by lia; rewrite Z_mod_plus_full; exact Hb16).
      pose proof HEI as HEI'. unfold img_env in HEI'.
      rewrite !HEI' by assumption.
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity; try exact I.
    * exact I.
    * cbn [rb_facts f_alias]. exact (B_alias_hints_ok E HEI).
- unfold sh_ok, rb_SH0. apply Forall_nil.
Qed.

(* ---- refused(n)'s arithmetic (B' +440..+496): held = g_live + n saturating, the unsigned tests ---- *)
Lemma rb_bltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold c_ltu, bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma rb_bgeu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = (y <=? x).
Proof.
intros x y Hx Hy. cbn [branch_taken]. unfold c_ltu, bv_ltu. rewrite !unsigned_lit_small by lia.
rewrite Z.leb_antisym. reflexivity.
Qed.
Lemma rb_lor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) x = 2 ^ 64 - 1.
Proof.
intros x Hx. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
apply Z.bits_inj'. intros j Hj. rewrite Z.lor_spec.
destruct (Z.lt_ge_cases j 64) as [Hl|Hl].
- rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. cbn [orb].
  destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; [lia|].
  apply (Z.lt_le_trans _ (2 ^ 64)); [lia | apply Z.pow_le_mono_r; lia].
Qed.
Lemma rb_held_denot : forall E live k n, ew E 35 = Z_to_bv 64 live -> ew E 37 = Z_to_bv 64 k -> ew E 11 = Z_to_bv 64 n ->
  0 <= k <= live -> live < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  sv_denot E rb_held = Z_to_bv 64 (Z.min SIZE_MAXZ (live - k + n)).
Proof.
intros E live k n H35 H37 H11 Hk Hl Hn. apply bv_eq.
change (bv_unsigned (sv_denot E rb_held)) with (U E rb_held).
assert (UL : U E rb_live1 = live - k).
{ unfold U, rb_live1. rewrite (rb_sub_denot E live k H35 H37 Hk Hl). apply unsigned_lit_small. lia. }
assert (UN : U E (SOff 11 0) = n).
{ rewrite U_SOff, H11, unsigned_lit_small by lia. rewrite Z.add_0_r. apply rb_zc. lia. }
assert (US : U E (SAlu ALU_ADD rb_live1 (SOff 11 0)) = (live - k + n) mod 2 ^ 64).
{ rewrite U_SAlu, UL, UN. cbn [zalu_raw]. reflexivity. }
assert (HS : 0 <= Z.min SIZE_MAXZ (live - k + n) < 2 ^ 64) by (unfold SIZE_MAXZ; lia).
rewrite unsigned_lit_small by exact HS.
unfold rb_held. rewrite U_SAlu, US. rewrite U_SAlu, U_SLit. rewrite U_SAlu, US, UL. cbn [zalu_raw].
unfold zcanon, M64.
destruct (Z_lt_ge_dec (live - k + n) (2 ^ 64)) as [Hlt|Hge].
- rewrite (Z.mod_small (live - k + n)) by lia.
  replace (live - k + n <? live - k) with false by (symmetry; apply Z.ltb_ge; lia).
  match goal with |- context [Z.lor ?a _] => replace a with 0 by reflexivity end.
  rewrite Z.lor_0_l. rewrite Z.mod_small by lia. unfold SIZE_MAXZ. lia.
- replace ((live - k + n) mod 2 ^ 64) with (live - k + n - 2 ^ 64)
    by (apply (Z.mod_unique _ _ 1); lia).
  replace (live - k + n - 2 ^ 64 <? live - k) with true by (symmetry; apply Z.ltb_lt; lia).
  match goal with |- context [Z.lor ?a _] => replace a with (2 ^ 64 - 1) by reflexivity end.
  rewrite rb_lor_ones by lia. rewrite Z.mod_small by lia. unfold SIZE_MAXZ. lia.
Qed.

(* ---- small facts of the p <> 0 arms ---- *)
Lemma rb_ledger_perm : forall ly S Hp (W : world SEGS) mem L1 L2 peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem L1 peak cnt fail ran most own -> Permutation L1 L2 ->
  prh_ledger B ly S Hp W mem L2 peak cnt fail ran most own.
Proof.
intros ly S Hp W mem L1 L2 peak cnt fail ran most own HL Hperm.
apply prh_ledger_iff in HL as [HG (HN & HF & HP)]. apply prh_ledger_iff. split.
- rewrite <- (prh_lsum_perm _ _ Hperm). exact HG.
- split; [apply NoDup_ListNoDup; apply (Permutation_NoDup (Permutation_map fst Hperm)); apply NoDup_ListNoDup; exact HN|].
  split.
  + rewrite Forall_forall in HF |- *. intros x Hx. apply HF. exact (Permutation_in _ (Permutation_sym Hperm) Hx).
  + exact (Permutation_trans HP (Permutation_map _ Hperm)).
Qed.
Lemma rb_pw_disj : forall (bl : list (Z * Z)) x y,
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) bl) -> In x bl -> In y bl -> fst x <> fst y ->
  zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)).
Proof.
intros bl. induction bl as [|z t IH]; intros x y Hpw Hx Hy Hne; [destruct Hx|].
cbn [map YG0f.pairwise] in Hpw. destruct Hpw as [Hf Hpw]. rewrite Forall_forall in Hf.
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. apply Hne. reflexivity.
- apply (Hf (fst y, req_size (snd y))). apply in_map_iff. exists y. split; [reflexivity | exact Hy].
- apply prh_zdisjoint_sym. apply (Hf (fst x, req_size (snd x))). apply in_map_iff. exists x. split; [reflexivity | exact Hx].
- exact (IH x y Hpw Hx Hy Hne).
Qed.
Lemma rb_new_block : forall (bl : list (Z * Z)) x, 0 <= snd x ->
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (bl ++ [x])) -> ~ In x bl.
Proof.
intros bl x Hx Hpw Hin. rewrite map_app in Hpw. cbn [map] in Hpw.
pose proof (prh_pw_last _ _ _ Hpw (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) bl x Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (prh_req_size_pos (snd x) Hx). lia.
Qed.

(* the environment after the realloc call (havoc base 60), as the two continuations read it *)
Definition rb_envR (E : env) (regs : bvmap 5 word) (p n cnt fail live ran k peak most res : Z) : Prop :=
  img_env VAL A_LIM E /\
  ew E 1 = getr regs 1 /\ ew E 2 = getr regs 2 /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\
  ew E 8 = getr regs 8 /\ ew E 10 = Z_to_bv 64 p /\ ew E 11 = Z_to_bv 64 n /\
  ew E 32 = Z_to_bv 64 SHADOW_OFF /\ ew E 33 = Z_to_bv 64 cnt /\ ew E 34 = Z_to_bv 64 fail /\
  ew E 35 = Z_to_bv 64 live /\ ew E 36 = Z_to_bv 64 ran /\ ew E 37 = Z_to_bv 64 k /\ ew E 38 = Z_to_bv 64 peak /\
  ew E 39 = Z_to_bv 64 most /\ ew E 64 = w64 res /\
  env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; live; ran; k; peak; most])) E.

(* the entry's environment facts (registers, atoms, image objects) *)
Ltac rb_envfacts E regs xs HEI EL :=
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold RB_EI; apply Eimg_env);
  assert (EL : forall j, (j < A_TEXT)%nat -> ew E j = ew (Ereg regs (map (Z_to_bv 64) xs)) j)
    by (intros j Hj; subst E; unfold RB_EI; apply Eimg_low; exact Hj).

(* ===== p = NULL: the frame pops and fuzz_malloc (n) is tail-called (B' 0x85f40, +140) ===== *)
Lemma rb_p0 : forall ly S Hp (W : world SEGS) regs mem md ch n Lam peak cnt fail ran most own,
  fpre B ARcfx STK_fuzz_realloc ly S Hp W regs mem md ch -> room_live_cf S -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* the text's hull budget at p = 0 (fuzz_malloc's one event), handed to MALLOC as it is *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (n + cf_head)] ->
  getr regs 10 = w64 0 -> getr regs 11 = w64 n -> 0 <= n -> n + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (cnt <> fail -> blocks_bytes S + (n + cf_head) <= LIVE_MAX) ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_fuzz_realloc) regs mem md)
    (fpostm B ARcfx SK STK_fuzz_realloc [] regs ly S Hp W mem md
      (tfrP_Q B ly S Hp W 0 0 n [] Lam peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md ch n Lam peak cnt fail ran most own
  HPRE HRL HUNIV HSEC H24 HHB H10 H11 Hn0 Hnmax HLED HLIVE.
destruct HPRE as (HAFN & HROD & HSHI & HRAC & HFRM).
pose proof (@pa_segs_low rc B_prog_listing PA) as Hsegs.
pose proof rb_STK_v as WS. pose proof rb_stk_malloc as WM.
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
destruct (rb_entry0 B ARcfx _ ly S Hp W regs mem md ch HAFN ltac:(rewrite WS; lia) H10) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARcfx STK_fuzz_realloc [] ly S Hp W regs mem md ch HAFN) as HJ.
remember (RB_EI regs []) as E eqn:HE.
rb_envfacts E regs (@nil Z) HEI EL.
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [])) E)
  by (split; [intros j Hj; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. rewrite rb_entry_pc. change (w64 (BASE + rb_pc0)) with (Z_to_bv 64 (BASE + rb_pc0)).
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
(* the frame and the saves; beqz a0 at +28 *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM RB_Bspan; [rb_wr Usp |].
clear HF HG. rb_keep0 KA Usp.
psrr_branch_tok RUN BR HS SHOK RB_Bspan.
2: { exfalso. rewrite rb_denot0, E10 in Hc. vm_compute in Hc. discriminate Hc. }
(* mv a0, s0; the restores; the frame popped; the tail jump to fuzz_malloc at +140 *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM RB_Bspan; [rb_wr Usp |].
clear HF HG. rb_keep0 KB Usp.
lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HSx (1%bv : bv 5) R1; prreg HSx (2%bv : bv 5) R2; prreg HSx (3%bv : bv 5) R3;
  prreg HSx (4%bv : bv 5) R4; prreg HSx (8%bv : bv 5) R8; prreg HSx (10%bv : bv 5) R10;
  rename HSx into HSc; rb_gen msc msC
end.
assert (KAB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; rewrite (KB a Ha Hn); exact (KA a Ha Hn)).
assert (KLO : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KAB; lia).
assert (Hspc : spZ (ms_regs msC) = spZ regs)
  by (unfold spZ at 1; rewrite R2; rewrite ?rb_denot0; rewrite E2; reflexivity).
assert (Hrac : raZ (ms_regs msC) = raZ regs) by (unfold raZ at 1; rewrite R1, E1; reflexivity).
eapply SRr_mono.
{ eapply (aj_call_x (SK := SK) SEGS B PST ARcfx LAWS Hsegs W E _ msC STK_fuzz_realloc (spZ regs)
    [] ly S Hp W mem md [] ly S Hp _ _ STK_fuzz_malloc [] 0 (getr regs 2) (getr regs 1) ch _ HSc eq_refl HJ).
  - rewrite R2; rewrite ?rb_denot0; reflexivity.
  - exact E2.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite WM; lia.
  - rewrite WM, WS; lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - rewrite R1, E1. reflexivity.
  - exact Hra.
  - exact Hra4.
  - rewrite Z.add_0_r.
    assert (Hs0 : s0Z (ms_regs msC) = s0Z regs) by (unfold s0Z; rewrite R8, E8; reflexivity).
    rewrite Hs0.
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply KAB; lia.
  - intros HPREc.
    refine (MALLOC ly S Hp W (ms_regs msC) (ms_mem msC) _ ch n Lam peak cnt fail
      ran most own (conj HPREc (conj _ (conj _ (conj _ HFRM)))) HRL HUNIV HSEC H24 HHB _ Hn0 Hnmax _ HLIVE).
    + exact (rb_rod_low W W mem (ms_mem msC) HROD KLO).
    + rewrite Hspc. exact HSHI.
    + rewrite Hrac. exact HRAC.
    + rewrite R10, E11. exact H11.
    + apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W _ Lam peak cnt fail ran most own HLED).
      * intros a Ha. pose proof (rb_pst_low a Ha). apply KLO. unfold SHADOW_OFF in *; lia.
      * intros a k' i Hin Hi.
        destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k' most own HLED Hin) as (Hk' & Hbl & _).
        destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & Hb4 & Hbc & _).
        assert (Hrq : req_size (k' + cf_head) = k' + 16)
          by (unfold req_size; rewrite rb_cf_head; destruct (Z.eqb_spec (k' + 16) 0); lia).
        rewrite Hrq, rb_cf_head in Hbc. rewrite rb_cf_head in Hb4 |- *. apply KLO; lia.
      * intros a k' _ Hbl. exact Hbl.
      * apply Permutation_refl.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & _ & HP2 & HQ2).
(* fuzz_malloc's post BY NAME (rb_conj_pick): its result register, room_live_cf, its hull use, its two position arms,
   THE OUTCOME and prh_alloc_post, each read where tfrP_R takes it; a conjunct the kit adds to that post cannot shift
   the others *)
unfold fQmn in HQ2. destruct HQ2 as ((res & HMP) & Hmn).
unfold fpostm, fpost, apost_base_x, fQmn.
do 7 eexists. split; [exact Hc2|]. split; [exact HJ2|]. split.
{ eapply rb_apres_trans; [| exact HP2].
  eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HSc); [exact HAE | vm_compute; reflexivity]. }
split; [|intros H0; exact (Hmn (HPM H0))].
apply tfrP_Q_of_R with (res := res).
refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
  tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
{ rb_conj_pick HMP. }
{ rb_conj_pick HMP. }
(* THE HULL USE at p = 0: fuzz_malloc's, at the same event list *)
{ rb_conj_pick HMP. }
{ rb_conj_pick HMP. }
{ intros Hr _; revert Hr; rb_conj_pick HMP. }
{ intros _ Hp0; exfalso; exact (Hp0 eq_refl). }
(* THE OUTCOME at p = NULL: realloc (NULL, n) is the tail call fuzz_malloc (n); its event HMal (n + cf_head), its
   result and its S' are fuzz_malloc's, so the conjunct is fuzz_malloc's own outcome conjunct *)
{ intros _; rb_conj_pick HMP. }
{ intros Hp0; exfalso; exact (Hp0 eq_refl). }
left. apply tfrP_A1_of_R. refine {| tfrP1_null := eq_refl; tfrP1_alloc := _ |}. rb_conj_pick HMP.
Qed.

(* ---- the common setup of the two continuations after the realloc call (entry ledger facts, the old block, the heads
   of Lam's other blocks) ---- *)
(* ===== REFUSED: realloc's NULL; refused(n) (4 paths), own (p - 16, k) again (ret +512), return 0 at +108 ===== *)
Lemma rb_refd : forall ly S Hp (W : world SEGS) regs mem md ch p k n old Lam peak cnt
  fail ran most own l1 l2 E2 (W4 : world SEGS) regs4 mem4 md4 ly4 S4 Hp4 k4,
  afn_pre_x SEGS B ARcfx STK_fuzz_realloc ly S Hp W regs mem md ch ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W) mem) ->
  spZ regs + 64 <= ly_stk_hi ly -> YK0o.frm_zero (@YK11.fp_csr fx) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= most < 2 ^ 64 ->
  Lam = l1 ++ (p, k) :: l2 -> p <> 0 -> cnt <> fail -> bytes_at W mem p old -> Z.of_nat (length old) = k ->
  0 <= n < 2 ^ 29 ->
  rb_envR E2 regs p n cnt fail (Ledger.lsum Lam) ran k peak most 0 ->
  st_ok_pi SEGS VAL E2 rb_sr (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + (rb_pc0 + 404))) mem4 (seg_rom SEGS))) ->
  ajournal_xR (SK := SK) SEGS B PST ARcfx RR STK_fuzz_realloc (spZ regs) (ablocks_fp [(p - 16, k + 16)]) ly S Hp W
    mem md [] ly4 S4 Hp4 W4 mem4 md4 k4 ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem4) ->
  prh_most (PA := PA) W4 mem4 most -> prh_own (PA := PA) W4 mem4 own ->
  room_live_cf S4 ->
  (* the hull use of the refused realloc (A14's secs_call_post of its path, in rb_nz) *)
  PresetHullBudget.hull_used S S4 [PresetReqAt.HRe (k + 16) (n + 16)] ->
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PresetRoomPos.iface_room_pos sm x os i H0 hist S4) ->
  Hp4 = remove Z.eq_dec (p - 16) Hp -> ablocks B ly4 S4 = ablocks B ly S ->
  (forall a, p <= a < p + k -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) mem a) ->
  rd32 (aview SEGS (w_H W4) mem4) (as_errno B) 12 ->
  (* the refusal evidence, WORLD-FREE (the kit's primed text; YGcfRealloc.realloc_cf_refused_state in rb_nz) *)
  (blocks S4 = blocks S /\ st_chunks S4 = st_chunks S /\ from_primary (n + 16) = true /\
   YG00cf.exh_mem_cf S4 (chunk_class (n + 16)) = true) ->
  (* THE OUTCOME's exclusion of this arm (PRH_Refute.prh_refute_at at the realloc call, in rb_nz): no position of a
     model run whose next event is this call's consumer HRe holds at the entry state *)
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PRH_Base.prh_run_at sm x os i [PresetReqAt.HRe (k + 16) (n + 16)] -> PRH_Base.prh_cons_from sm x os i 1 -> False) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W4 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + (rb_pc0 + 404))) mem4 (seg_rom SEGS)) md4)
    (fpostmR B ARcfx SK RR STK_fuzz_realloc (ablocks_fp [(p - 16, k + 16)]) regs ly S Hp W mem md
      (tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own l1 l2 E2 W4
  regs4 mem4 md4 ly4 S4 Hp4 k4 HAFN HROD HSHI HFRM HLED Rmost ELam Hp0 Hc0 Hold Hlen Hn HENVR HSb HJ4 HPM HM4 HO4 HRL4
  HHU4 HPOS4 EHp4 Eab4 HOLD4 Herr4 HNP HREF.
unfold SRr'.
assert (Ep0 : (p =? 0) = false) by (apply Z.eqb_neq; exact Hp0).
destruct HENVR as (HEI2 & F1 & F2 & F3 & F4 & F8 & F10 & F11 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39 & F64 & HAE2).
pose proof (@pa_segs_low rc B_prog_listing PA) as Hsegs.
pose proof rb_STK_v as WS. pose proof rb_stk_own as WO.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (pal_env B PAL) as HENV.
set (FP := ablocks_fp [(p - 16, k + 16)]).
(* the entry ledger, through its named projections *)
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HLED) as (Rlp & Rpk & Rcnt & Rfail & Rran).
assert (HinL : In (p, k) Lam) by (rewrite ELam; apply in_or_app; right; left; reflexivity).
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran p k most own HLED HinL) as (Hk0 & Hblk & HinHp & Hp16 & Hhd).
rewrite rb_cf_head in Hblk, HinHp, Hhd.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) HAR Hblk) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & Hpw).
assert (Hreq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
pose proof (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HND.
assert (Hlsum : Ledger.lsum Lam = Ledger.lsum (l1 ++ l2) + k) by (rewrite ELam; apply prh_lsum_split).
assert (Hsz : Forall (fun ak => 0 <= snd ak) Lam) by exact (prh_ledger_sizes B ly S Hp W mem Lam peak cnt fail ran most own HLED).
assert (Hl12 : 0 <= Ledger.lsum (l1 ++ l2)).
{ apply prh_lsum_nonneg. rewrite Forall_forall in Hsz |- *. intros x Hx. apply Hsz. rewrite ELam.
  apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (Hpnot : ~ In p (map fst (l1 ++ l2))) by (rewrite ELam in HND; exact (prh_lam_rest_notin l1 l2 p k HND)).
assert (HLB : prh_lblocks B ly S Hp W mem Lam)
  by exact (proj2 (proj1 (prh_ledger_iff B ly S Hp W mem Lam peak cnt fail ran most own) HLED)).
(* the old block's user bytes: no frame, no static *)
assert (HBK : forall a, p <= a < p + k -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 48 <= a < spZ regs) /\ ~ rb_obj_byte a).
{ intros a Ha. split; [lia|]. split; [lia|].
  intros Hx. apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md (p - 16) (k + 16) a HAR Hblk);
    [rewrite Hreq; lia | exact (pst_in_img_B a (rb_obj_pst a Hx))]. }
(* the heads of Lam's blocks *)
assert (HHB : forall a ka i, In (a, ka) Lam -> 0 <= i < 8 ->
  In (a - 16, ka + 16) (ablocks B ly S) /\ 0 <= ka /\ (a <> p -> ~ inFP FP (a - 16 + i))).
{ intros a ka i Hin Hi.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HLED Hin) as (Hka & Hbl & _ & _ & _).
  rewrite rb_cf_head in Hbl.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & Hb4 & Hbc & _).
  assert (Hrq : req_size (ka + 16) = ka + 16) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
  split; [exact Hbl|]. split; [exact Hka|].
  intros Hne (r & Hr & Hrr). unfold FP, ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []].
  cbn [fst snd] in Hrr. rewrite Hreq in Hrr.
  pose proof (rb_pw_disj (ablocks B ly S) (a - 16, ka + 16) (p - 16, k + 16) Hpw Hbl Hblk ltac:(cbn; lia)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, Hreq in Hd. lia. }
assert (Rcnt1 : 0 <= (cnt + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite F2; reflexivity).
assert (SHOK2 : sh_ok SEGS RB_Bx rb_SH0 E2 (mrestrict (w_H W4) mem4)) by constructor.
assert (Dlive : sv_denot E2 rb_live1 = Z_to_bv 64 (Ledger.lsum (l1 ++ l2))).
{ unfold rb_live1. rewrite (rb_sub_denot E2 (Ledger.lsum Lam) k F35 F37) by lia. f_equal. lia. }
set (held := Z.min SIZE_MAXZ (Ledger.lsum Lam - k + n)).
assert (Rheld : 0 <= held < 2 ^ 64) by (subst held; unfold SIZE_MAXZ; lia).
assert (Dheld : sv_denot E2 rb_held = Z_to_bv 64 held)
  by (subst held; apply (rb_held_denot E2 (Ledger.lsum Lam) k n F35 F37 F11); lia).
unfold cfg_at.
(* ---- the NULL test (beqz a0 at +404): taken, res = 0 ---- *)
paj_run_tok_x_invR (RUNMR mem) HSb HJ4 SHOK2 HPM RB_Bspan; [rb_wr Usp2 |].
clear HF HG. rb_keep K4 Usp2.
YSRrG.psrr_branch_tokR RUN BRR HSb SHOK2 RB_Bspan.
all: rewrite rb_denot0, F64 in Hc; cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite rb_beq in Hc by lia.
2: { exfalso. rewrite Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
(* ---- refused(n): held = g_live + n (saturating); the peak test (bgeu g_peak, held at +468) ---- *)
paj_run_tok_x_invR (RUNMR mem) HSb HJ4 SHOK2 HPM RB_Bspan; [rb_wr Usp2 |].
clear HF HG. rb_keep K5 Usp2.
(* the four paths' common tail: the static stores pk (g_peak kept) / mo (g_ran_out kept), own, the epilogue *)
assert (TAIL : forall pk mo, pk = (held <=? peak) -> mo = (most <? n) -> forall msX mdX,
  st_ok_pi SEGS VAL E2 (rb_br (rb_xf_pk pk) mo) (restrict (w_H W4) msX) ->
  ajournal_xR (SK := SK) SEGS B PST ARcfx RR STK_fuzz_realloc (spZ regs) FP ly S Hp W mem md [] ly4 S4 Hp4 W4 (ms_mem msX)
    mdX k4 ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem msX)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ rb_obj_byte a ->
     aview SEGS (w_H W4) (ms_mem msX) a = aview SEGS (w_H W4) mem4 a) ->
  SRrG SEGS RR W4 (mkCfg msX mdX)
    (fpostmR B ARcfx SK RR STK_fuzz_realloc FP regs ly S Hp W mem md
      (tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own))).
{ intros pk mo Hpk Hmo msX mdX HSX HJX HPMX KX.
  set (peak' := if pk then peak else held).
  set (ran' := if mo then ran else 1).
  assert (Hpeak' : peak' = Z.max peak held) by (subst peak'; rewrite Hpk; destruct (Z.leb_spec held peak); lia).
  assert (Hran' : ran' = (if n <=? most then 1 else ran))
    by (subst ran'; rewrite Hmo; destruct (Z.ltb_spec most n), (Z.leb_spec n most); first [reflexivity | lia]).
  assert (Dpk : sv_denot E2 (if pk then SOff 38 0 else rb_held) = Z_to_bv 64 peak')
    by (subst peak'; destruct pk; [rewrite rb_denot0; exact F38 | exact Dheld]).
  assert (Dmo : sv_denot E2 (if mo then SOff 36 0 else SLit 1) = Z_to_bv 64 ran')
    by (subst ran'; destruct mo; [rewrite rb_denot0; exact F36 | reflexivity]).
  assert (Rpk' : 0 <= peak' < 2 ^ 64) by (rewrite Hpeak'; lia).
  assert (Rran' : ran' = 0 \/ ran' = 1) by (subst ran'; destruct mo; [exact Rran | right; reflexivity]).
  assert (Hlp' : Ledger.lsum (l1 ++ l2) <= peak') by (rewrite Hpeak'; lia).
  assert (SHOKX : sh_ok SEGS RB_Bx rb_SH0 E2 (mrestrict (w_H W4) (ms_mem msX))) by constructor.
  (* g_most and g_own_ran_out at the path's start state: the runs since the realloc call write neither *)
  assert (HMX : prh_most (PA := PA) W4 (ms_mem msX) most /\ prh_own (PA := PA) W4 (ms_mem msX) own)
    by (apply (rb_om_kept W4 W4 mem4 (ms_mem msX) most own); [rb_far_by KX | exact HM4 | exact HO4]).
  clearbody peak' ran'. clear Hpk Hmo.
  destruct pk, mo.

  - (* refused(n)'s stores, a0 = s1 = p - 16, a1 = s2 = k, the call of own at +508 (ret +512) *)
    paj_run_tok_x_invR (RUNMR mem) HSX HJX SHOKX HPMX RB_Bspan; [rb_wr Usp2 |].
    clear HF HG. rb_keep K7 Usp2.
    lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Q1; prreg HSx (2%bv : bv 5) Q2; prreg HSx (3%bv : bv 5) Q3;
      prreg HSx (4%bv : bv 5) Q4; prreg HSx (8%bv : bv 5) Q8; prreg HSx (10%bv : bv 5) Q10;
      rb_reg HSx (11%bv : bv 5) Q11;
      pose proof (st_ok_mem_ok SEGS E2 ssx (restrict (w_H W4) msc) HSx) as HMO;
      cbn [ss_mem restrict ms_mem setpc] in HMO;
      let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
      rename HSx into HSo; rename HJX into HJo; rb_gen msc msO
    end.
    pose proof HJo as (_ & HJly & _ & _ & _ & _ & _ & _ & _ & HJbo & _).
    pose proof HJly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
    set (mO := mrestrict (w_H W4) (ms_mem msO)).
    pose proof (rb_chunk_val E2 mO _ 1 _ 0 8 (SOff 33 1) ((cnt + 1) mod 2 ^ 64) HMO eq_refl
      ltac:(cbn; left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F33, unsigned_lit_small by lia; symmetry; apply rb_wrap)
      Rcnt1 ltac:(cbn; lia)) as Mc'.
    pose proof (rb_chunk_val E2 mO _ 2 _ 0 8 (SOff 34 0) fail HMO eq_refl
      ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F34; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
    pose proof (rb_chunk_val E2 mO _ 3 _ 0 8 rb_live1 (Ledger.lsum (l1 ++ l2)) HMO eq_refl
      ltac:(cbn; left; reflexivity) Dlive ltac:(cbn; lia) ltac:(cbn; lia)) as Ml'.
    lazymatch type of Dmo with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 4 _ 0 1 e ran' HMO eq_refl ltac:(cbn; left; reflexivity) Dmo
        ltac:(cbn; destruct Rran'; lia) ltac:(cbn; lia)) as Mr0 end.
    lazymatch type of Dpk with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 5 _ 0 8 e peak' HMO eq_refl ltac:(cbn; left; reflexivity) Dpk
        ltac:(cbn; lia) ltac:(cbn; lia)) as Mp' end.
    rb_objv Mc' pi_g_count. rb_objv Mf' pi_g_fail. rb_objv Ml' pi_g_live. rb_objv Mr0 pi_g_ran_out.
    rb_objv Mp' pi_g_peak.
    assert (HMO' : prh_most (PA := PA) W4 (ms_mem msO) most /\ prh_own (PA := PA) W4 (ms_mem msO) own)
      by (apply (rb_om_kept W4 W4 (ms_mem msX) (ms_mem msO) most own); [rb_far_by K7 | exact (proj1 HMX) | exact (proj2 HMX)]).
    pose proof (rb_glob_mk W4 (ms_mem msO) _ _ _ _ _ _ _ Ml' Mp' Mc' Mf' Mr0 (proj1 HMO') (proj2 HMO') ltac:(lia) ltac:(lia)
      Rcnt1 ltac:(lia) Rran') as HGo.
    assert (HLEDo : prh_ledger B ly4 S4 Hp4 W4 (ms_mem msO) (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
    { apply (prh_ledger_disown B ly S Hp W mem ly4 S4 Hp4 W4 (ms_mem msO) l1 l2 p k peak cnt fail ran
        peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
      - rewrite <- ELam. exact HLED.
      - exact HGo.
      - intros a ka i Hin Hi. apply (prh_mbyte_of_aview (PA := PA)).
        assert (HinL' : In (a, ka) Lam).
        { rewrite ELam. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
        destruct (HHB a ka i HinL' Hi) as (Hbl & Hka & Hfp).
        assert (Hne : a <> p) by (intros ->; apply Hpnot; apply in_map_iff; exists (p, ka); split; [reflexivity | exact Hin]).
        rewrite rb_cf_head. apply (HJbo (a - 16) (ka + 16) i Hbl); [rewrite Eab4; exact Hbl | | exact (Hfp Hne)].
        unfold req_size. destruct (Z.eqb_spec (ka + 16) 0); lia.
      - intros a ka _ Hbl. rewrite Eab4. exact Hbl.
      - rewrite EHp4, rb_cf_head. reflexivity. }
    assert (Hs0o : s0Z (ms_regs msO) = n) by (unfold s0Z; rewrite Q8, F11; apply unsigned_lit_small; lia).
    assert (Hspo : spZ (ms_regs msO) = spZ regs - 48).
    { unfold spZ at 1. rewrite Q2. rewrite ?rb_denot0. cbn [sv_denot]. rewrite Usp2. rewrite unsigned_lit_small by lia. lia. }
    eapply (SRrG_bind SEGS RR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    { eapply (aj_call_xR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
        (wle'_trans SEGS YGcfRehidePost.RZ_cf) W4 E2 _ msO STK_fuzz_realloc (spZ regs)
        FP ly S Hp W mem md [] ly4 S4 Hp4 _ _ STK_own [(p - 16, p - 16 + 8)] (-48) (getr regs 2)
        (Z_to_bv 64 (BASE + (rb_pc0 + 512))) [] _ HSo eq_refl HJo).
      - rewrite Q2; rewrite ?rb_denot0; reflexivity.
      - exact F2.
      - reflexivity.
      - reflexivity.
      - lia.
      - rewrite WO; lia.
      - rewrite WO, WS; lia.
      - rewrite Q3, F3. exact Hgp.
      - rewrite Q4, F4. exact Htp.
      - exact Q1.
      - apply rb_ret_ok. lia.
      - apply rb_ret_hi. lia.
      - unfold achain. left. split; [left; rewrite Hs0o; lia | reflexivity].
      - intros HPREo. apply rb_callee_lift.
        refine (OWN ly4 S4 Hp4 W4 (ms_regs msO) (ms_mem msO) _ [] (p - 16) k (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64)
          fail ran' most own (conj HPREo (conj _ (conj _ (conj _ HFRM)))) _ _ Hk0 _ Hb16 ltac:(lia) _ _ HLEDo).
        + apply (rb_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo); [|exact HROD].
          apply sink_closed_ablocks_fp. repeat constructor. cbn. lia.
        + rewrite Hspo, Ehi. lia.
        + unfold raZ. rewrite Q1.
          lazymatch goal with |- bv_unsigned (Z_to_bv 64 ?e) < _ => let v := eval vm_compute in e in change e with v end.
          rewrite unsigned_lit_small by lia. lia.
        + rewrite Q10, F10, unsigned_lit_small by lia. unfold w64. f_equal; lia.
        + rewrite Q11. etransitivity; [exact (rb_hdr_add0 E2 37)|]. rewrite F37. reflexivity.
        + rewrite Eab4. exact Hblk.
        + replace (p - 16 + cf_head) with p by (rewrite rb_cf_head; lia). exact Hpnot.
        + lia.
      - intros a Ha. left. apply inFP_cons in Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
        unfold FP, ablocks_fp. cbn [map fst snd]. apply inFP_cons. left. rewrite Hreq. cbn [fst snd] in Ha. lia. }
    cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & HJown & HP5 & HQ5).
    unfold fQmn in HQ5. destruct HQ5 as ((Hrk5 & ES5 & Ely5 & R5a & EHp5 & Eab5 & Herr5 & HLED5) & Hmn5).
    pose proof (fun H0 => Hmn5 (HPMX H0)) as HPM5. clear Hmn5.
    pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres5 & _).
    pose proof HJown as (_ & _ & _ & _ & _ & _ & _ & _ & HJhio & HJbo5 & _).
    assert (KF5 : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem msO) a).
    { intros a Ha. apply HJhio; [lia | rewrite WO; lia]. }
    jafter_call_keep_pi HSo 80%nat regs5 (mrestrict (w_H W5) mem5) HP5 rb_keep_o HSc.
    match type of HSc with ?tq -> _ => assert (HRK : tq); [|specialize (HSc HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
      - rewrite Usp2 in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KF5. lia.
      - intros _. apply (apresent_writable SEGS). rewrite Usp2 in Ha. apply HJpres5. rewrite WS. lia. }
    rewrite <- restrict_mkst_fx in HSc.
    remember (havoc E2 80 (map (getr regs5) CLOB)) as Eo eqn:HE3 in HSc.
    assert (HEIo : img_env VAL A_LIM Eo) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
    assert (OLD3 : forall j, (j < 80)%nat -> ew Eo j = ew E2 j) by (intros j Hj; rewrite HE3; apply YN3v.ew_havoc_old; exact Hj).
    assert (HAE3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; Ledger.lsum Lam; ran; k; peak; most])) Eo)
      by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
    assert (Usp3 : bv_unsigned (ew Eo 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
    assert (SHOK3 : sh_ok SEGS RB_Bx rb_SH0 Eo (mrestrict (w_H W5) mem5)) by constructor.
    clear HE3.
    (* the jump back to the shared epilogue (+512 -> +80), a0 = 0, the restores, ret at +108 *)
    paj_run_tok_x_invR (RUNMR mem) HSc HJ5 SHOK3 HPM5 RB_Bspan; [rb_wr Usp3 |].
    clear HF HG. rb_keep0 K8 Usp3.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Z1; prreg HSx (10%bv : bv 5) Z10;
      apply (SRr_SRrG SEGS RR (wle_wle' SEGS YGcfRehidePost.RZ_cf));
      eapply (RET W5 _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
      unfold fpostmR, fpostR, apost_base_xR, fQmn;
      exists ly5, S5, Hp5, (ms_regs msc), (ms_mem msc); do 2 eexists;
      split; [cbn [ms_regs]; rewrite Z1, OLD3, F1 by lia; rewrite Hra; reflexivity|];
      split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR); exact HJ5|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Eo _ _ regs _ HSx); [exact HAE3 | vm_compute; reflexivity]|];
      rb_gen msc msF
    end.
    split; [|exact HPM5].
    apply tfrP_Q_of_R with (res := 0).
    refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
      tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
    { rewrite Z10; reflexivity. }
    { rewrite ES5; exact HRL4. }
    (* THE HULL USE: the refused realloc's (own keeps the state) *)
    { rewrite ES5, Ep0. exact HHU4. }
    { intros _; rewrite ES5; exact (rb_pos_nil S S4 HPOS4). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    (* THE OUTCOME: p <> 0; this arm is excluded at a consumer HRe (HREF) *)
    { intros H0; exfalso; exact (Hp0 H0). }
    { intros _ qsm qx qos qi qH0 qhist qHP qHr qHc _; exfalso; exact (HREF qsm qx qos qi qH0 qhist qHP qHr qHc). }
    right; right; left. apply tfrP_A3_of_R.
    refine {| tfrP3_nonnull := Hp0; tfrP3_notchosen := Hc0; tfrP3_res0 := eq_refl; tfrP3_hp := _; tfrP3_ablocks := _;
      tfrP3_bytes := _; tfrP3_evidence := _; tfrP3_errno := _; tfrP3_ledger := _ |}.
    { rewrite EHp5, EHp4; exact (prh_hp_reown_perm B ly S Hp W mem Lam p k HLB HinL). }
    { rewrite Eab5, Eab4; reflexivity. }
    { unfold bytes_at. apply (rb_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
      intros j Hj. apply (prh_mbyte_of_aview (PA := PA)).
      assert (Hj' : p <= p + Z.of_nat j < p + k) by lia.
      destruct (HBK (p + Z.of_nat j) Hj') as (B1 & B2 & B3).
      assert (Y : aview SEGS (w_H W5) mem5 (p + Z.of_nat j) = aview SEGS (w_H W4) (ms_mem msO) (p + Z.of_nat j)).
      { replace (p + Z.of_nat j) with ((p - 16) + (16 + Z.of_nat j)) by lia.
        apply (HJbo5 (p - 16) (k + 16) (16 + Z.of_nat j));
          [rewrite Eab4; exact Hblk | rewrite Eab5, Eab4; exact Hblk | rewrite Hreq; lia |].
        intros Hx. apply inFP_cons in Hx as [Hx | Hx]; [cbn [fst snd] in Hx; lia | exact (inFP_nil _ Hx)]. }
      rewrite (K8 _ B1 B2), Y, (K7 _ B1 B2 B3), (KX _ B1 B2 B3). exact (HOLD4 _ Hj'). }
    { rewrite ES5; exact HNP. }
    { intros kk Hkk. specialize (Herr4 kk Hkk).
      set (ae := as_errno B + Z.of_nat kk) in *.
      assert (Hae : 0 <= ae < kLowMemEnd) by (apply Hsegs; apply (proj1 (proj2 HENV)); unfold ae; lia).
      assert (Hnp : ~ rb_obj_byte ae)
        by (intros Hx; destruct (pal_pst_ok _ (rb_obj_pst _ Hx)) as [_ Hne]; apply Hne; unfold ae; lia).
      rewrite (K8 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia)).
      rewrite (Herr5 ae ltac:(unfold ae; lia)).
      rewrite (K7 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp).
      rewrite (KX ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp). exact Herr4. }
    replace (p - 16 + cf_head) with p in HLED5 by (rewrite rb_cf_head; lia).
    replace (Ledger.lsum (l1 ++ l2) + k) with (Ledger.lsum Lam) in HLED5 by lia.
    rewrite (Z.max_l peak' (Ledger.lsum Lam)) in HLED5 by (rewrite Hpeak'; lia).
    rewrite Hpeak', Hran' in HLED5.
    apply (rb_ledger_perm ly5 S5 Hp5 W5 (ms_mem msF) ((p, k) :: l1 ++ l2) Lam); [| rewrite ELam; apply Permutation_middle].
    apply (prh_ledger_kept_aview B ly5 S5 Hp5 W5 mem5 ly5 S5 Hp5 W5 (ms_mem msF) _ _ _ fail _ most own HLED5).
    + intros a Ha. pose proof (rb_pst_low a Ha). apply K8; unfold SHADOW_OFF in *; lia.
    + intros a ka i Hin Hi.
      destruct (prh_ledger_hblock B ly5 S5 Hp5 W5 mem5 _ _ _ _ _ a ka most own HLED5 Hin) as (Hka & Hbl5 & _).
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR5 Hbl5) as (_ & Hb45 & Hbc5 & _).
      assert (Hrq : req_size (ka + cf_head) = ka + 16)
        by (unfold req_size; rewrite rb_cf_head; destruct (Z.eqb_spec (ka + 16) 0); lia).
      rewrite Hrq, rb_cf_head in Hbc5. rewrite rb_cf_head in Hb45 |- *. apply K8; lia.
    + intros a ka _ Hbl. exact Hbl.
    + apply Permutation_refl.

  - (* refused(n)'s stores, a0 = s1 = p - 16, a1 = s2 = k, the call of own at +508 (ret +512) *)
    paj_run_tok_x_invR (RUNMR mem) HSX HJX SHOKX HPMX RB_Bspan; [rb_wr Usp2 |].
    clear HF HG. rb_keep K7 Usp2.
    lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Q1; prreg HSx (2%bv : bv 5) Q2; prreg HSx (3%bv : bv 5) Q3;
      prreg HSx (4%bv : bv 5) Q4; prreg HSx (8%bv : bv 5) Q8; prreg HSx (10%bv : bv 5) Q10;
      rb_reg HSx (11%bv : bv 5) Q11;
      pose proof (st_ok_mem_ok SEGS E2 ssx (restrict (w_H W4) msc) HSx) as HMO;
      cbn [ss_mem restrict ms_mem setpc] in HMO;
      let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
      rename HSx into HSo; rename HJX into HJo; rb_gen msc msO
    end.
    pose proof HJo as (_ & HJly & _ & _ & _ & _ & _ & _ & _ & HJbo & _).
    pose proof HJly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
    set (mO := mrestrict (w_H W4) (ms_mem msO)).
    pose proof (rb_chunk_val E2 mO _ 1 _ 0 8 (SOff 33 1) ((cnt + 1) mod 2 ^ 64) HMO eq_refl
      ltac:(cbn; left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F33, unsigned_lit_small by lia; symmetry; apply rb_wrap)
      Rcnt1 ltac:(cbn; lia)) as Mc'.
    pose proof (rb_chunk_val E2 mO _ 2 _ 0 8 (SOff 34 0) fail HMO eq_refl
      ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F34; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
    pose proof (rb_chunk_val E2 mO _ 3 _ 0 8 rb_live1 (Ledger.lsum (l1 ++ l2)) HMO eq_refl
      ltac:(cbn; left; reflexivity) Dlive ltac:(cbn; lia) ltac:(cbn; lia)) as Ml'.
    lazymatch type of Dmo with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 4 _ 0 1 e ran' HMO eq_refl ltac:(cbn; left; reflexivity) Dmo
        ltac:(cbn; destruct Rran'; lia) ltac:(cbn; lia)) as Mr0 end.
    lazymatch type of Dpk with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 5 _ 0 8 e peak' HMO eq_refl ltac:(cbn; left; reflexivity) Dpk
        ltac:(cbn; lia) ltac:(cbn; lia)) as Mp' end.
    rb_objv Mc' pi_g_count. rb_objv Mf' pi_g_fail. rb_objv Ml' pi_g_live. rb_objv Mr0 pi_g_ran_out.
    rb_objv Mp' pi_g_peak.
    assert (HMO' : prh_most (PA := PA) W4 (ms_mem msO) most /\ prh_own (PA := PA) W4 (ms_mem msO) own)
      by (apply (rb_om_kept W4 W4 (ms_mem msX) (ms_mem msO) most own); [rb_far_by K7 | exact (proj1 HMX) | exact (proj2 HMX)]).
    pose proof (rb_glob_mk W4 (ms_mem msO) _ _ _ _ _ _ _ Ml' Mp' Mc' Mf' Mr0 (proj1 HMO') (proj2 HMO') ltac:(lia) ltac:(lia)
      Rcnt1 ltac:(lia) Rran') as HGo.
    assert (HLEDo : prh_ledger B ly4 S4 Hp4 W4 (ms_mem msO) (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
    { apply (prh_ledger_disown B ly S Hp W mem ly4 S4 Hp4 W4 (ms_mem msO) l1 l2 p k peak cnt fail ran
        peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
      - rewrite <- ELam. exact HLED.
      - exact HGo.
      - intros a ka i Hin Hi. apply (prh_mbyte_of_aview (PA := PA)).
        assert (HinL' : In (a, ka) Lam).
        { rewrite ELam. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
        destruct (HHB a ka i HinL' Hi) as (Hbl & Hka & Hfp).
        assert (Hne : a <> p) by (intros ->; apply Hpnot; apply in_map_iff; exists (p, ka); split; [reflexivity | exact Hin]).
        rewrite rb_cf_head. apply (HJbo (a - 16) (ka + 16) i Hbl); [rewrite Eab4; exact Hbl | | exact (Hfp Hne)].
        unfold req_size. destruct (Z.eqb_spec (ka + 16) 0); lia.
      - intros a ka _ Hbl. rewrite Eab4. exact Hbl.
      - rewrite EHp4, rb_cf_head. reflexivity. }
    assert (Hs0o : s0Z (ms_regs msO) = n) by (unfold s0Z; rewrite Q8, F11; apply unsigned_lit_small; lia).
    assert (Hspo : spZ (ms_regs msO) = spZ regs - 48).
    { unfold spZ at 1. rewrite Q2. rewrite ?rb_denot0. cbn [sv_denot]. rewrite Usp2. rewrite unsigned_lit_small by lia. lia. }
    eapply (SRrG_bind SEGS RR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    { eapply (aj_call_xR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
        (wle'_trans SEGS YGcfRehidePost.RZ_cf) W4 E2 _ msO STK_fuzz_realloc (spZ regs)
        FP ly S Hp W mem md [] ly4 S4 Hp4 _ _ STK_own [(p - 16, p - 16 + 8)] (-48) (getr regs 2)
        (Z_to_bv 64 (BASE + (rb_pc0 + 512))) [] _ HSo eq_refl HJo).
      - rewrite Q2; rewrite ?rb_denot0; reflexivity.
      - exact F2.
      - reflexivity.
      - reflexivity.
      - lia.
      - rewrite WO; lia.
      - rewrite WO, WS; lia.
      - rewrite Q3, F3. exact Hgp.
      - rewrite Q4, F4. exact Htp.
      - exact Q1.
      - apply rb_ret_ok. lia.
      - apply rb_ret_hi. lia.
      - unfold achain. left. split; [left; rewrite Hs0o; lia | reflexivity].
      - intros HPREo. apply rb_callee_lift.
        refine (OWN ly4 S4 Hp4 W4 (ms_regs msO) (ms_mem msO) _ [] (p - 16) k (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64)
          fail ran' most own (conj HPREo (conj _ (conj _ (conj _ HFRM)))) _ _ Hk0 _ Hb16 ltac:(lia) _ _ HLEDo).
        + apply (rb_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo); [|exact HROD].
          apply sink_closed_ablocks_fp. repeat constructor. cbn. lia.
        + rewrite Hspo, Ehi. lia.
        + unfold raZ. rewrite Q1.
          lazymatch goal with |- bv_unsigned (Z_to_bv 64 ?e) < _ => let v := eval vm_compute in e in change e with v end.
          rewrite unsigned_lit_small by lia. lia.
        + rewrite Q10, F10, unsigned_lit_small by lia. unfold w64. f_equal; lia.
        + rewrite Q11. etransitivity; [exact (rb_hdr_add0 E2 37)|]. rewrite F37. reflexivity.
        + rewrite Eab4. exact Hblk.
        + replace (p - 16 + cf_head) with p by (rewrite rb_cf_head; lia). exact Hpnot.
        + lia.
      - intros a Ha. left. apply inFP_cons in Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
        unfold FP, ablocks_fp. cbn [map fst snd]. apply inFP_cons. left. rewrite Hreq. cbn [fst snd] in Ha. lia. }
    cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & HJown & HP5 & HQ5).
    unfold fQmn in HQ5. destruct HQ5 as ((Hrk5 & ES5 & Ely5 & R5a & EHp5 & Eab5 & Herr5 & HLED5) & Hmn5).
    pose proof (fun H0 => Hmn5 (HPMX H0)) as HPM5. clear Hmn5.
    pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres5 & _).
    pose proof HJown as (_ & _ & _ & _ & _ & _ & _ & _ & HJhio & HJbo5 & _).
    assert (KF5 : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem msO) a).
    { intros a Ha. apply HJhio; [lia | rewrite WO; lia]. }
    jafter_call_keep_pi HSo 80%nat regs5 (mrestrict (w_H W5) mem5) HP5 rb_keep_o HSc.
    match type of HSc with ?tq -> _ => assert (HRK : tq); [|specialize (HSc HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
      - rewrite Usp2 in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KF5. lia.
      - intros _. apply (apresent_writable SEGS). rewrite Usp2 in Ha. apply HJpres5. rewrite WS. lia. }
    rewrite <- restrict_mkst_fx in HSc.
    remember (havoc E2 80 (map (getr regs5) CLOB)) as Eo eqn:HE3 in HSc.
    assert (HEIo : img_env VAL A_LIM Eo) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
    assert (OLD3 : forall j, (j < 80)%nat -> ew Eo j = ew E2 j) by (intros j Hj; rewrite HE3; apply YN3v.ew_havoc_old; exact Hj).
    assert (HAE3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; Ledger.lsum Lam; ran; k; peak; most])) Eo)
      by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
    assert (Usp3 : bv_unsigned (ew Eo 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
    assert (SHOK3 : sh_ok SEGS RB_Bx rb_SH0 Eo (mrestrict (w_H W5) mem5)) by constructor.
    clear HE3.
    (* the jump back to the shared epilogue (+512 -> +80), a0 = 0, the restores, ret at +108 *)
    paj_run_tok_x_invR (RUNMR mem) HSc HJ5 SHOK3 HPM5 RB_Bspan; [rb_wr Usp3 |].
    clear HF HG. rb_keep0 K8 Usp3.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Z1; prreg HSx (10%bv : bv 5) Z10;
      apply (SRr_SRrG SEGS RR (wle_wle' SEGS YGcfRehidePost.RZ_cf));
      eapply (RET W5 _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
      unfold fpostmR, fpostR, apost_base_xR, fQmn;
      exists ly5, S5, Hp5, (ms_regs msc), (ms_mem msc); do 2 eexists;
      split; [cbn [ms_regs]; rewrite Z1, OLD3, F1 by lia; rewrite Hra; reflexivity|];
      split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR); exact HJ5|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Eo _ _ regs _ HSx); [exact HAE3 | vm_compute; reflexivity]|];
      rb_gen msc msF
    end.
    split; [|exact HPM5].
    apply tfrP_Q_of_R with (res := 0).
    refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
      tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
    { rewrite Z10; reflexivity. }
    { rewrite ES5; exact HRL4. }
    (* THE HULL USE: the refused realloc's (own keeps the state) *)
    { rewrite ES5, Ep0. exact HHU4. }
    { intros _; rewrite ES5; exact (rb_pos_nil S S4 HPOS4). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    (* THE OUTCOME: p <> 0; this arm is excluded at a consumer HRe (HREF) *)
    { intros H0; exfalso; exact (Hp0 H0). }
    { intros _ qsm qx qos qi qH0 qhist qHP qHr qHc _; exfalso; exact (HREF qsm qx qos qi qH0 qhist qHP qHr qHc). }
    right; right; left. apply tfrP_A3_of_R.
    refine {| tfrP3_nonnull := Hp0; tfrP3_notchosen := Hc0; tfrP3_res0 := eq_refl; tfrP3_hp := _; tfrP3_ablocks := _;
      tfrP3_bytes := _; tfrP3_evidence := _; tfrP3_errno := _; tfrP3_ledger := _ |}.
    { rewrite EHp5, EHp4; exact (prh_hp_reown_perm B ly S Hp W mem Lam p k HLB HinL). }
    { rewrite Eab5, Eab4; reflexivity. }
    { unfold bytes_at. apply (rb_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
      intros j Hj. apply (prh_mbyte_of_aview (PA := PA)).
      assert (Hj' : p <= p + Z.of_nat j < p + k) by lia.
      destruct (HBK (p + Z.of_nat j) Hj') as (B1 & B2 & B3).
      assert (Y : aview SEGS (w_H W5) mem5 (p + Z.of_nat j) = aview SEGS (w_H W4) (ms_mem msO) (p + Z.of_nat j)).
      { replace (p + Z.of_nat j) with ((p - 16) + (16 + Z.of_nat j)) by lia.
        apply (HJbo5 (p - 16) (k + 16) (16 + Z.of_nat j));
          [rewrite Eab4; exact Hblk | rewrite Eab5, Eab4; exact Hblk | rewrite Hreq; lia |].
        intros Hx. apply inFP_cons in Hx as [Hx | Hx]; [cbn [fst snd] in Hx; lia | exact (inFP_nil _ Hx)]. }
      rewrite (K8 _ B1 B2), Y, (K7 _ B1 B2 B3), (KX _ B1 B2 B3). exact (HOLD4 _ Hj'). }
    { rewrite ES5; exact HNP. }
    { intros kk Hkk. specialize (Herr4 kk Hkk).
      set (ae := as_errno B + Z.of_nat kk) in *.
      assert (Hae : 0 <= ae < kLowMemEnd) by (apply Hsegs; apply (proj1 (proj2 HENV)); unfold ae; lia).
      assert (Hnp : ~ rb_obj_byte ae)
        by (intros Hx; destruct (pal_pst_ok _ (rb_obj_pst _ Hx)) as [_ Hne]; apply Hne; unfold ae; lia).
      rewrite (K8 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia)).
      rewrite (Herr5 ae ltac:(unfold ae; lia)).
      rewrite (K7 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp).
      rewrite (KX ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp). exact Herr4. }
    replace (p - 16 + cf_head) with p in HLED5 by (rewrite rb_cf_head; lia).
    replace (Ledger.lsum (l1 ++ l2) + k) with (Ledger.lsum Lam) in HLED5 by lia.
    rewrite (Z.max_l peak' (Ledger.lsum Lam)) in HLED5 by (rewrite Hpeak'; lia).
    rewrite Hpeak', Hran' in HLED5.
    apply (rb_ledger_perm ly5 S5 Hp5 W5 (ms_mem msF) ((p, k) :: l1 ++ l2) Lam); [| rewrite ELam; apply Permutation_middle].
    apply (prh_ledger_kept_aview B ly5 S5 Hp5 W5 mem5 ly5 S5 Hp5 W5 (ms_mem msF) _ _ _ fail _ most own HLED5).
    + intros a Ha. pose proof (rb_pst_low a Ha). apply K8; unfold SHADOW_OFF in *; lia.
    + intros a ka i Hin Hi.
      destruct (prh_ledger_hblock B ly5 S5 Hp5 W5 mem5 _ _ _ _ _ a ka most own HLED5 Hin) as (Hka & Hbl5 & _).
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR5 Hbl5) as (_ & Hb45 & Hbc5 & _).
      assert (Hrq : req_size (ka + cf_head) = ka + 16)
        by (unfold req_size; rewrite rb_cf_head; destruct (Z.eqb_spec (ka + 16) 0); lia).
      rewrite Hrq, rb_cf_head in Hbc5. rewrite rb_cf_head in Hb45 |- *. apply K8; lia.
    + intros a ka _ Hbl. exact Hbl.
    + apply Permutation_refl.

  - (* refused(n)'s stores, a0 = s1 = p - 16, a1 = s2 = k, the call of own at +508 (ret +512) *)
    paj_run_tok_x_invR (RUNMR mem) HSX HJX SHOKX HPMX RB_Bspan; [rb_wr Usp2 |].
    clear HF HG. rb_keep K7 Usp2.
    lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Q1; prreg HSx (2%bv : bv 5) Q2; prreg HSx (3%bv : bv 5) Q3;
      prreg HSx (4%bv : bv 5) Q4; prreg HSx (8%bv : bv 5) Q8; prreg HSx (10%bv : bv 5) Q10;
      rb_reg HSx (11%bv : bv 5) Q11;
      pose proof (st_ok_mem_ok SEGS E2 ssx (restrict (w_H W4) msc) HSx) as HMO;
      cbn [ss_mem restrict ms_mem setpc] in HMO;
      let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
      rename HSx into HSo; rename HJX into HJo; rb_gen msc msO
    end.
    pose proof HJo as (_ & HJly & _ & _ & _ & _ & _ & _ & _ & HJbo & _).
    pose proof HJly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
    set (mO := mrestrict (w_H W4) (ms_mem msO)).
    pose proof (rb_chunk_val E2 mO _ 1 _ 0 8 (SOff 33 1) ((cnt + 1) mod 2 ^ 64) HMO eq_refl
      ltac:(cbn; left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F33, unsigned_lit_small by lia; symmetry; apply rb_wrap)
      Rcnt1 ltac:(cbn; lia)) as Mc'.
    pose proof (rb_chunk_val E2 mO _ 2 _ 0 8 (SOff 34 0) fail HMO eq_refl
      ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F34; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
    pose proof (rb_chunk_val E2 mO _ 3 _ 0 8 rb_live1 (Ledger.lsum (l1 ++ l2)) HMO eq_refl
      ltac:(cbn; left; reflexivity) Dlive ltac:(cbn; lia) ltac:(cbn; lia)) as Ml'.
    lazymatch type of Dmo with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 4 _ 0 1 e ran' HMO eq_refl ltac:(cbn; left; reflexivity) Dmo
        ltac:(cbn; destruct Rran'; lia) ltac:(cbn; lia)) as Mr0 end.
    lazymatch type of Dpk with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 5 _ 0 8 e peak' HMO eq_refl ltac:(cbn; left; reflexivity) Dpk
        ltac:(cbn; lia) ltac:(cbn; lia)) as Mp' end.
    rb_objv Mc' pi_g_count. rb_objv Mf' pi_g_fail. rb_objv Ml' pi_g_live. rb_objv Mr0 pi_g_ran_out.
    rb_objv Mp' pi_g_peak.
    assert (HMO' : prh_most (PA := PA) W4 (ms_mem msO) most /\ prh_own (PA := PA) W4 (ms_mem msO) own)
      by (apply (rb_om_kept W4 W4 (ms_mem msX) (ms_mem msO) most own); [rb_far_by K7 | exact (proj1 HMX) | exact (proj2 HMX)]).
    pose proof (rb_glob_mk W4 (ms_mem msO) _ _ _ _ _ _ _ Ml' Mp' Mc' Mf' Mr0 (proj1 HMO') (proj2 HMO') ltac:(lia) ltac:(lia)
      Rcnt1 ltac:(lia) Rran') as HGo.
    assert (HLEDo : prh_ledger B ly4 S4 Hp4 W4 (ms_mem msO) (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
    { apply (prh_ledger_disown B ly S Hp W mem ly4 S4 Hp4 W4 (ms_mem msO) l1 l2 p k peak cnt fail ran
        peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
      - rewrite <- ELam. exact HLED.
      - exact HGo.
      - intros a ka i Hin Hi. apply (prh_mbyte_of_aview (PA := PA)).
        assert (HinL' : In (a, ka) Lam).
        { rewrite ELam. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
        destruct (HHB a ka i HinL' Hi) as (Hbl & Hka & Hfp).
        assert (Hne : a <> p) by (intros ->; apply Hpnot; apply in_map_iff; exists (p, ka); split; [reflexivity | exact Hin]).
        rewrite rb_cf_head. apply (HJbo (a - 16) (ka + 16) i Hbl); [rewrite Eab4; exact Hbl | | exact (Hfp Hne)].
        unfold req_size. destruct (Z.eqb_spec (ka + 16) 0); lia.
      - intros a ka _ Hbl. rewrite Eab4. exact Hbl.
      - rewrite EHp4, rb_cf_head. reflexivity. }
    assert (Hs0o : s0Z (ms_regs msO) = n) by (unfold s0Z; rewrite Q8, F11; apply unsigned_lit_small; lia).
    assert (Hspo : spZ (ms_regs msO) = spZ regs - 48).
    { unfold spZ at 1. rewrite Q2. rewrite ?rb_denot0. cbn [sv_denot]. rewrite Usp2. rewrite unsigned_lit_small by lia. lia. }
    eapply (SRrG_bind SEGS RR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    { eapply (aj_call_xR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
        (wle'_trans SEGS YGcfRehidePost.RZ_cf) W4 E2 _ msO STK_fuzz_realloc (spZ regs)
        FP ly S Hp W mem md [] ly4 S4 Hp4 _ _ STK_own [(p - 16, p - 16 + 8)] (-48) (getr regs 2)
        (Z_to_bv 64 (BASE + (rb_pc0 + 512))) [] _ HSo eq_refl HJo).
      - rewrite Q2; rewrite ?rb_denot0; reflexivity.
      - exact F2.
      - reflexivity.
      - reflexivity.
      - lia.
      - rewrite WO; lia.
      - rewrite WO, WS; lia.
      - rewrite Q3, F3. exact Hgp.
      - rewrite Q4, F4. exact Htp.
      - exact Q1.
      - apply rb_ret_ok. lia.
      - apply rb_ret_hi. lia.
      - unfold achain. left. split; [left; rewrite Hs0o; lia | reflexivity].
      - intros HPREo. apply rb_callee_lift.
        refine (OWN ly4 S4 Hp4 W4 (ms_regs msO) (ms_mem msO) _ [] (p - 16) k (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64)
          fail ran' most own (conj HPREo (conj _ (conj _ (conj _ HFRM)))) _ _ Hk0 _ Hb16 ltac:(lia) _ _ HLEDo).
        + apply (rb_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo); [|exact HROD].
          apply sink_closed_ablocks_fp. repeat constructor. cbn. lia.
        + rewrite Hspo, Ehi. lia.
        + unfold raZ. rewrite Q1.
          lazymatch goal with |- bv_unsigned (Z_to_bv 64 ?e) < _ => let v := eval vm_compute in e in change e with v end.
          rewrite unsigned_lit_small by lia. lia.
        + rewrite Q10, F10, unsigned_lit_small by lia. unfold w64. f_equal; lia.
        + rewrite Q11. etransitivity; [exact (rb_hdr_add0 E2 37)|]. rewrite F37. reflexivity.
        + rewrite Eab4. exact Hblk.
        + replace (p - 16 + cf_head) with p by (rewrite rb_cf_head; lia). exact Hpnot.
        + lia.
      - intros a Ha. left. apply inFP_cons in Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
        unfold FP, ablocks_fp. cbn [map fst snd]. apply inFP_cons. left. rewrite Hreq. cbn [fst snd] in Ha. lia. }
    cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & HJown & HP5 & HQ5).
    unfold fQmn in HQ5. destruct HQ5 as ((Hrk5 & ES5 & Ely5 & R5a & EHp5 & Eab5 & Herr5 & HLED5) & Hmn5).
    pose proof (fun H0 => Hmn5 (HPMX H0)) as HPM5. clear Hmn5.
    pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres5 & _).
    pose proof HJown as (_ & _ & _ & _ & _ & _ & _ & _ & HJhio & HJbo5 & _).
    assert (KF5 : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem msO) a).
    { intros a Ha. apply HJhio; [lia | rewrite WO; lia]. }
    jafter_call_keep_pi HSo 80%nat regs5 (mrestrict (w_H W5) mem5) HP5 rb_keep_o HSc.
    match type of HSc with ?tq -> _ => assert (HRK : tq); [|specialize (HSc HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
      - rewrite Usp2 in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KF5. lia.
      - intros _. apply (apresent_writable SEGS). rewrite Usp2 in Ha. apply HJpres5. rewrite WS. lia. }
    rewrite <- restrict_mkst_fx in HSc.
    remember (havoc E2 80 (map (getr regs5) CLOB)) as Eo eqn:HE3 in HSc.
    assert (HEIo : img_env VAL A_LIM Eo) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
    assert (OLD3 : forall j, (j < 80)%nat -> ew Eo j = ew E2 j) by (intros j Hj; rewrite HE3; apply YN3v.ew_havoc_old; exact Hj).
    assert (HAE3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; Ledger.lsum Lam; ran; k; peak; most])) Eo)
      by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
    assert (Usp3 : bv_unsigned (ew Eo 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
    assert (SHOK3 : sh_ok SEGS RB_Bx rb_SH0 Eo (mrestrict (w_H W5) mem5)) by constructor.
    clear HE3.
    (* the jump back to the shared epilogue (+512 -> +80), a0 = 0, the restores, ret at +108 *)
    paj_run_tok_x_invR (RUNMR mem) HSc HJ5 SHOK3 HPM5 RB_Bspan; [rb_wr Usp3 |].
    clear HF HG. rb_keep0 K8 Usp3.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Z1; prreg HSx (10%bv : bv 5) Z10;
      apply (SRr_SRrG SEGS RR (wle_wle' SEGS YGcfRehidePost.RZ_cf));
      eapply (RET W5 _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
      unfold fpostmR, fpostR, apost_base_xR, fQmn;
      exists ly5, S5, Hp5, (ms_regs msc), (ms_mem msc); do 2 eexists;
      split; [cbn [ms_regs]; rewrite Z1, OLD3, F1 by lia; rewrite Hra; reflexivity|];
      split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR); exact HJ5|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Eo _ _ regs _ HSx); [exact HAE3 | vm_compute; reflexivity]|];
      rb_gen msc msF
    end.
    split; [|exact HPM5].
    apply tfrP_Q_of_R with (res := 0).
    refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
      tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
    { rewrite Z10; reflexivity. }
    { rewrite ES5; exact HRL4. }
    (* THE HULL USE: the refused realloc's (own keeps the state) *)
    { rewrite ES5, Ep0. exact HHU4. }
    { intros _; rewrite ES5; exact (rb_pos_nil S S4 HPOS4). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    (* THE OUTCOME: p <> 0; this arm is excluded at a consumer HRe (HREF) *)
    { intros H0; exfalso; exact (Hp0 H0). }
    { intros _ qsm qx qos qi qH0 qhist qHP qHr qHc _; exfalso; exact (HREF qsm qx qos qi qH0 qhist qHP qHr qHc). }
    right; right; left. apply tfrP_A3_of_R.
    refine {| tfrP3_nonnull := Hp0; tfrP3_notchosen := Hc0; tfrP3_res0 := eq_refl; tfrP3_hp := _; tfrP3_ablocks := _;
      tfrP3_bytes := _; tfrP3_evidence := _; tfrP3_errno := _; tfrP3_ledger := _ |}.
    { rewrite EHp5, EHp4; exact (prh_hp_reown_perm B ly S Hp W mem Lam p k HLB HinL). }
    { rewrite Eab5, Eab4; reflexivity. }
    { unfold bytes_at. apply (rb_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
      intros j Hj. apply (prh_mbyte_of_aview (PA := PA)).
      assert (Hj' : p <= p + Z.of_nat j < p + k) by lia.
      destruct (HBK (p + Z.of_nat j) Hj') as (B1 & B2 & B3).
      assert (Y : aview SEGS (w_H W5) mem5 (p + Z.of_nat j) = aview SEGS (w_H W4) (ms_mem msO) (p + Z.of_nat j)).
      { replace (p + Z.of_nat j) with ((p - 16) + (16 + Z.of_nat j)) by lia.
        apply (HJbo5 (p - 16) (k + 16) (16 + Z.of_nat j));
          [rewrite Eab4; exact Hblk | rewrite Eab5, Eab4; exact Hblk | rewrite Hreq; lia |].
        intros Hx. apply inFP_cons in Hx as [Hx | Hx]; [cbn [fst snd] in Hx; lia | exact (inFP_nil _ Hx)]. }
      rewrite (K8 _ B1 B2), Y, (K7 _ B1 B2 B3), (KX _ B1 B2 B3). exact (HOLD4 _ Hj'). }
    { rewrite ES5; exact HNP. }
    { intros kk Hkk. specialize (Herr4 kk Hkk).
      set (ae := as_errno B + Z.of_nat kk) in *.
      assert (Hae : 0 <= ae < kLowMemEnd) by (apply Hsegs; apply (proj1 (proj2 HENV)); unfold ae; lia).
      assert (Hnp : ~ rb_obj_byte ae)
        by (intros Hx; destruct (pal_pst_ok _ (rb_obj_pst _ Hx)) as [_ Hne]; apply Hne; unfold ae; lia).
      rewrite (K8 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia)).
      rewrite (Herr5 ae ltac:(unfold ae; lia)).
      rewrite (K7 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp).
      rewrite (KX ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp). exact Herr4. }
    replace (p - 16 + cf_head) with p in HLED5 by (rewrite rb_cf_head; lia).
    replace (Ledger.lsum (l1 ++ l2) + k) with (Ledger.lsum Lam) in HLED5 by lia.
    rewrite (Z.max_l peak' (Ledger.lsum Lam)) in HLED5 by (rewrite Hpeak'; lia).
    rewrite Hpeak', Hran' in HLED5.
    apply (rb_ledger_perm ly5 S5 Hp5 W5 (ms_mem msF) ((p, k) :: l1 ++ l2) Lam); [| rewrite ELam; apply Permutation_middle].
    apply (prh_ledger_kept_aview B ly5 S5 Hp5 W5 mem5 ly5 S5 Hp5 W5 (ms_mem msF) _ _ _ fail _ most own HLED5).
    + intros a Ha. pose proof (rb_pst_low a Ha). apply K8; unfold SHADOW_OFF in *; lia.
    + intros a ka i Hin Hi.
      destruct (prh_ledger_hblock B ly5 S5 Hp5 W5 mem5 _ _ _ _ _ a ka most own HLED5 Hin) as (Hka & Hbl5 & _).
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR5 Hbl5) as (_ & Hb45 & Hbc5 & _).
      assert (Hrq : req_size (ka + cf_head) = ka + 16)
        by (unfold req_size; rewrite rb_cf_head; destruct (Z.eqb_spec (ka + 16) 0); lia).
      rewrite Hrq, rb_cf_head in Hbc5. rewrite rb_cf_head in Hb45 |- *. apply K8; lia.
    + intros a ka _ Hbl. exact Hbl.
    + apply Permutation_refl.

  - (* refused(n)'s stores, a0 = s1 = p - 16, a1 = s2 = k, the call of own at +508 (ret +512) *)
    paj_run_tok_x_invR (RUNMR mem) HSX HJX SHOKX HPMX RB_Bspan; [rb_wr Usp2 |].
    clear HF HG. rb_keep K7 Usp2.
    lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Q1; prreg HSx (2%bv : bv 5) Q2; prreg HSx (3%bv : bv 5) Q3;
      prreg HSx (4%bv : bv 5) Q4; prreg HSx (8%bv : bv 5) Q8; prreg HSx (10%bv : bv 5) Q10;
      rb_reg HSx (11%bv : bv 5) Q11;
      pose proof (st_ok_mem_ok SEGS E2 ssx (restrict (w_H W4) msc) HSx) as HMO;
      cbn [ss_mem restrict ms_mem setpc] in HMO;
      let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
      rename HSx into HSo; rename HJX into HJo; rb_gen msc msO
    end.
    pose proof HJo as (_ & HJly & _ & _ & _ & _ & _ & _ & _ & HJbo & _).
    pose proof HJly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
    set (mO := mrestrict (w_H W4) (ms_mem msO)).
    pose proof (rb_chunk_val E2 mO _ 1 _ 0 8 (SOff 33 1) ((cnt + 1) mod 2 ^ 64) HMO eq_refl
      ltac:(cbn; left; reflexivity)
      ltac:(cbn [sv_denot]; rewrite F33, unsigned_lit_small by lia; symmetry; apply rb_wrap)
      Rcnt1 ltac:(cbn; lia)) as Mc'.
    pose proof (rb_chunk_val E2 mO _ 2 _ 0 8 (SOff 34 0) fail HMO eq_refl
      ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F34; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
    pose proof (rb_chunk_val E2 mO _ 3 _ 0 8 rb_live1 (Ledger.lsum (l1 ++ l2)) HMO eq_refl
      ltac:(cbn; left; reflexivity) Dlive ltac:(cbn; lia) ltac:(cbn; lia)) as Ml'.
    lazymatch type of Dmo with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 4 _ 0 1 e ran' HMO eq_refl ltac:(cbn; left; reflexivity) Dmo
        ltac:(cbn; destruct Rran'; lia) ltac:(cbn; lia)) as Mr0 end.
    lazymatch type of Dpk with sv_denot _ ?e = _ =>
      pose proof (rb_chunk_val E2 mO _ 5 _ 0 8 e peak' HMO eq_refl ltac:(cbn; left; reflexivity) Dpk
        ltac:(cbn; lia) ltac:(cbn; lia)) as Mp' end.
    rb_objv Mc' pi_g_count. rb_objv Mf' pi_g_fail. rb_objv Ml' pi_g_live. rb_objv Mr0 pi_g_ran_out.
    rb_objv Mp' pi_g_peak.
    assert (HMO' : prh_most (PA := PA) W4 (ms_mem msO) most /\ prh_own (PA := PA) W4 (ms_mem msO) own)
      by (apply (rb_om_kept W4 W4 (ms_mem msX) (ms_mem msO) most own); [rb_far_by K7 | exact (proj1 HMX) | exact (proj2 HMX)]).
    pose proof (rb_glob_mk W4 (ms_mem msO) _ _ _ _ _ _ _ Ml' Mp' Mc' Mf' Mr0 (proj1 HMO') (proj2 HMO') ltac:(lia) ltac:(lia)
      Rcnt1 ltac:(lia) Rran') as HGo.
    assert (HLEDo : prh_ledger B ly4 S4 Hp4 W4 (ms_mem msO) (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
    { apply (prh_ledger_disown B ly S Hp W mem ly4 S4 Hp4 W4 (ms_mem msO) l1 l2 p k peak cnt fail ran
        peak' ((cnt + 1) mod 2 ^ 64) fail ran' most own).
      - rewrite <- ELam. exact HLED.
      - exact HGo.
      - intros a ka i Hin Hi. apply (prh_mbyte_of_aview (PA := PA)).
        assert (HinL' : In (a, ka) Lam).
        { rewrite ELam. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
        destruct (HHB a ka i HinL' Hi) as (Hbl & Hka & Hfp).
        assert (Hne : a <> p) by (intros ->; apply Hpnot; apply in_map_iff; exists (p, ka); split; [reflexivity | exact Hin]).
        rewrite rb_cf_head. apply (HJbo (a - 16) (ka + 16) i Hbl); [rewrite Eab4; exact Hbl | | exact (Hfp Hne)].
        unfold req_size. destruct (Z.eqb_spec (ka + 16) 0); lia.
      - intros a ka _ Hbl. rewrite Eab4. exact Hbl.
      - rewrite EHp4, rb_cf_head. reflexivity. }
    assert (Hs0o : s0Z (ms_regs msO) = n) by (unfold s0Z; rewrite Q8, F11; apply unsigned_lit_small; lia).
    assert (Hspo : spZ (ms_regs msO) = spZ regs - 48).
    { unfold spZ at 1. rewrite Q2. rewrite ?rb_denot0. cbn [sv_denot]. rewrite Usp2. rewrite unsigned_lit_small by lia. lia. }
    eapply (SRrG_bind SEGS RR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
    { eapply (aj_call_xR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
        (wle'_trans SEGS YGcfRehidePost.RZ_cf) W4 E2 _ msO STK_fuzz_realloc (spZ regs)
        FP ly S Hp W mem md [] ly4 S4 Hp4 _ _ STK_own [(p - 16, p - 16 + 8)] (-48) (getr regs 2)
        (Z_to_bv 64 (BASE + (rb_pc0 + 512))) [] _ HSo eq_refl HJo).
      - rewrite Q2; rewrite ?rb_denot0; reflexivity.
      - exact F2.
      - reflexivity.
      - reflexivity.
      - lia.
      - rewrite WO; lia.
      - rewrite WO, WS; lia.
      - rewrite Q3, F3. exact Hgp.
      - rewrite Q4, F4. exact Htp.
      - exact Q1.
      - apply rb_ret_ok. lia.
      - apply rb_ret_hi. lia.
      - unfold achain. left. split; [left; rewrite Hs0o; lia | reflexivity].
      - intros HPREo. apply rb_callee_lift.
        refine (OWN ly4 S4 Hp4 W4 (ms_regs msO) (ms_mem msO) _ [] (p - 16) k (l1 ++ l2) peak' ((cnt + 1) mod 2 ^ 64)
          fail ran' most own (conj HPREo (conj _ (conj _ (conj _ HFRM)))) _ _ Hk0 _ Hb16 ltac:(lia) _ _ HLEDo).
        + apply (rb_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo); [|exact HROD].
          apply sink_closed_ablocks_fp. repeat constructor. cbn. lia.
        + rewrite Hspo, Ehi. lia.
        + unfold raZ. rewrite Q1.
          lazymatch goal with |- bv_unsigned (Z_to_bv 64 ?e) < _ => let v := eval vm_compute in e in change e with v end.
          rewrite unsigned_lit_small by lia. lia.
        + rewrite Q10, F10, unsigned_lit_small by lia. unfold w64. f_equal; lia.
        + rewrite Q11. etransitivity; [exact (rb_hdr_add0 E2 37)|]. rewrite F37. reflexivity.
        + rewrite Eab4. exact Hblk.
        + replace (p - 16 + cf_head) with p by (rewrite rb_cf_head; lia). exact Hpnot.
        + lia.
      - intros a Ha. left. apply inFP_cons in Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
        unfold FP, ablocks_fp. cbn [map fst snd]. apply inFP_cons. left. rewrite Hreq. cbn [fst snd] in Ha. lia. }
    cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & HJown & HP5 & HQ5).
    unfold fQmn in HQ5. destruct HQ5 as ((Hrk5 & ES5 & Ely5 & R5a & EHp5 & Eab5 & Herr5 & HLED5) & Hmn5).
    pose proof (fun H0 => Hmn5 (HPMX H0)) as HPM5. clear Hmn5.
    pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres5 & _).
    pose proof HJown as (_ & _ & _ & _ & _ & _ & _ & _ & HJhio & HJbo5 & _).
    assert (KF5 : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W5) mem5 a = aview SEGS (w_H W4) (ms_mem msO) a).
    { intros a Ha. apply HJhio; [lia | rewrite WO; lia]. }
    jafter_call_keep_pi HSo 80%nat regs5 (mrestrict (w_H W5) mem5) HP5 rb_keep_o HSc.
    match type of HSc with ?tq -> _ => assert (HRK : tq); [|specialize (HSc HRK); clear HRK] end.
    { cbn [ms_mem restrict].
      repeat apply Forall_cons; try apply Forall_nil; split;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
      - rewrite Usp2 in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KF5. lia.
      - intros _. apply (apresent_writable SEGS). rewrite Usp2 in Ha. apply HJpres5. rewrite WS. lia. }
    rewrite <- restrict_mkst_fx in HSc.
    remember (havoc E2 80 (map (getr regs5) CLOB)) as Eo eqn:HE3 in HSc.
    assert (HEIo : img_env VAL A_LIM Eo) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
    assert (OLD3 : forall j, (j < 80)%nat -> ew Eo j = ew E2 j) by (intros j Hj; rewrite HE3; apply YN3v.ew_havoc_old; exact Hj).
    assert (HAE3 : env_agree 32 (Ereg regs (map (Z_to_bv 64) [SHADOW_OFF; cnt; fail; Ledger.lsum Lam; ran; k; peak; most])) Eo)
      by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
    assert (Usp3 : bv_unsigned (ew Eo 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
    assert (SHOK3 : sh_ok SEGS RB_Bx rb_SH0 Eo (mrestrict (w_H W5) mem5)) by constructor.
    clear HE3.
    (* the jump back to the shared epilogue (+512 -> +80), a0 = 0, the restores, ret at +108 *)
    paj_run_tok_x_invR (RUNMR mem) HSc HJ5 SHOK3 HPM5 RB_Bspan; [rb_wr Usp3 |].
    clear HF HG. rb_keep0 K8 Usp3.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
      prreg HSx (1%bv : bv 5) Z1; prreg HSx (10%bv : bv 5) Z10;
      apply (SRr_SRrG SEGS RR (wle_wle' SEGS YGcfRehidePost.RZ_cf));
      eapply (RET W5 _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
      unfold fpostmR, fpostR, apost_base_xR, fQmn;
      exists ly5, S5, Hp5, (ms_regs msc), (ms_mem msc); do 2 eexists;
      split; [cbn [ms_regs]; rewrite Z1, OLD3, F1 by lia; rewrite Hra; reflexivity|];
      split; [apply (ajournal_x_materializeR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR); exact HJ5|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Eo _ _ regs _ HSx); [exact HAE3 | vm_compute; reflexivity]|];
      rb_gen msc msF
    end.
    split; [|exact HPM5].
    apply tfrP_Q_of_R with (res := 0).
    refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
      tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
    { rewrite Z10; reflexivity. }
    { rewrite ES5; exact HRL4. }
    (* THE HULL USE: the refused realloc's (own keeps the state) *)
    { rewrite ES5, Ep0. exact HHU4. }
    { intros _; rewrite ES5; exact (rb_pos_nil S S4 HPOS4). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    { intros H0; exfalso; exact (H0 eq_refl). }
    (* THE OUTCOME: p <> 0; this arm is excluded at a consumer HRe (HREF) *)
    { intros H0; exfalso; exact (Hp0 H0). }
    { intros _ qsm qx qos qi qH0 qhist qHP qHr qHc _; exfalso; exact (HREF qsm qx qos qi qH0 qhist qHP qHr qHc). }
    right; right; left. apply tfrP_A3_of_R.
    refine {| tfrP3_nonnull := Hp0; tfrP3_notchosen := Hc0; tfrP3_res0 := eq_refl; tfrP3_hp := _; tfrP3_ablocks := _;
      tfrP3_bytes := _; tfrP3_evidence := _; tfrP3_errno := _; tfrP3_ledger := _ |}.
    { rewrite EHp5, EHp4; exact (prh_hp_reown_perm B ly S Hp W mem Lam p k HLB HinL). }
    { rewrite Eab5, Eab4; reflexivity. }
    { unfold bytes_at. apply (rb_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
      intros j Hj. apply (prh_mbyte_of_aview (PA := PA)).
      assert (Hj' : p <= p + Z.of_nat j < p + k) by lia.
      destruct (HBK (p + Z.of_nat j) Hj') as (B1 & B2 & B3).
      assert (Y : aview SEGS (w_H W5) mem5 (p + Z.of_nat j) = aview SEGS (w_H W4) (ms_mem msO) (p + Z.of_nat j)).
      { replace (p + Z.of_nat j) with ((p - 16) + (16 + Z.of_nat j)) by lia.
        apply (HJbo5 (p - 16) (k + 16) (16 + Z.of_nat j));
          [rewrite Eab4; exact Hblk | rewrite Eab5, Eab4; exact Hblk | rewrite Hreq; lia |].
        intros Hx. apply inFP_cons in Hx as [Hx | Hx]; [cbn [fst snd] in Hx; lia | exact (inFP_nil _ Hx)]. }
      rewrite (K8 _ B1 B2), Y, (K7 _ B1 B2 B3), (KX _ B1 B2 B3). exact (HOLD4 _ Hj'). }
    { rewrite ES5; exact HNP. }
    { intros kk Hkk. specialize (Herr4 kk Hkk).
      set (ae := as_errno B + Z.of_nat kk) in *.
      assert (Hae : 0 <= ae < kLowMemEnd) by (apply Hsegs; apply (proj1 (proj2 HENV)); unfold ae; lia).
      assert (Hnp : ~ rb_obj_byte ae)
        by (intros Hx; destruct (pal_pst_ok _ (rb_obj_pst _ Hx)) as [_ Hne]; apply Hne; unfold ae; lia).
      rewrite (K8 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia)).
      rewrite (Herr5 ae ltac:(unfold ae; lia)).
      rewrite (K7 ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp).
      rewrite (KX ae ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kLowMemEnd in *; lia) Hnp). exact Herr4. }
    replace (p - 16 + cf_head) with p in HLED5 by (rewrite rb_cf_head; lia).
    replace (Ledger.lsum (l1 ++ l2) + k) with (Ledger.lsum Lam) in HLED5 by lia.
    rewrite (Z.max_l peak' (Ledger.lsum Lam)) in HLED5 by (rewrite Hpeak'; lia).
    rewrite Hpeak', Hran' in HLED5.
    apply (rb_ledger_perm ly5 S5 Hp5 W5 (ms_mem msF) ((p, k) :: l1 ++ l2) Lam); [| rewrite ELam; apply Permutation_middle].
    apply (prh_ledger_kept_aview B ly5 S5 Hp5 W5 mem5 ly5 S5 Hp5 W5 (ms_mem msF) _ _ _ fail _ most own HLED5).
    + intros a Ha. pose proof (rb_pst_low a Ha). apply K8; unfold SHADOW_OFF in *; lia.
    + intros a ka i Hin Hi.
      destruct (prh_ledger_hblock B ly5 S5 Hp5 W5 mem5 _ _ _ _ _ a ka most own HLED5 Hin) as (Hka & Hbl5 & _).
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR5 Hbl5) as (_ & Hb45 & Hbc5 & _).
      assert (Hrq : req_size (ka + cf_head) = ka + 16)
        by (unfold req_size; rewrite rb_cf_head; destruct (Z.eqb_spec (ka + 16) 0); lia).
      rewrite Hrq, rb_cf_head in Hbc5. rewrite rb_cf_head in Hb45 |- *. apply K8; lia.
    + intros a ka _ Hbl. exact Hbl.
    + apply Permutation_refl.

}
(* the peak test: taken iff held <= g_peak (pk) *)
YSRrG.psrr_branch_tokR RUN BRR HSb SHOK2 RB_Bspan.
1: change (branch_taken BC_GEU (sv_denot E2 (SOff 38 0)) (sv_denot E2 rb_held) = true) in Hc.
2: change (branch_taken BC_GEU (sv_denot E2 (SOff 38 0)) (sv_denot E2 rb_held) = false) in Hc.
all: rewrite rb_denot0, F38, Dheld, rb_bgeu in Hc by lia.
all: rename Hc into Hpkc.
(* to the g_most test (bltu g_most, n at +484): taken iff most < n (mo) *)
all: paj_run_tok_x_invR (RUNMR mem) HSb HJ4 SHOK2 HPM RB_Bspan; [rb_wr Usp2 |].
all: clear HF HG; rb_keep K6 Usp2.
all: YSRrG.psrr_branch_tokR RUN BRR HSb SHOK2 RB_Bspan.
all: rewrite !rb_denot0, F39, F11, rb_bltu in Hc by lia.
all: lazymatch goal with HSx : st_ok_pi _ _ _ ?s (restrict _ ?msx) |- SRrG _ _ _ (mkCfg ?msx ?mdx) _ =>
  first [ assert (Ess : s = rb_br (rb_xf_pk true) true) by (vm_compute; reflexivity); apply (TAIL true true)
        | assert (Ess : s = rb_br (rb_xf_pk true) false) by (vm_compute; reflexivity); apply (TAIL true false)
        | assert (Ess : s = rb_br (rb_xf_pk false) true) by (vm_compute; reflexivity); apply (TAIL false true)
        | assert (Ess : s = rb_br (rb_xf_pk false) false) by (vm_compute; reflexivity); apply (TAIL false false) ];
  [ symmetry; exact Hpkc | symmetry; exact Hc | rewrite <- Ess; exact HSx | exact HJ4 | exact HPM
  | intros a Ha H1 H2; rewrite (K6 a Ha H1 H2), (K5 a Ha H1 H2); exact (K4 a Ha H1 H2) ] end.
Qed.

(* ===== SUCCESS: the new block at res; a1 = n, the frame popped, own (res, n) tail-called at +436 ===== *)
Lemma rb_succ : forall ly S Hp (W : world SEGS) regs mem md ch p k n old Lam peak cnt
  fail ran most own l1 l2 E2 (W4 : world SEGS) regs4 mem4 md4 ly4 S4 Hp4 k4 res b1 b2,
  afn_pre_x SEGS B ARcfx STK_fuzz_realloc ly S Hp W regs mem md ch ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W) mem) ->
  spZ regs + 64 <= ly_stk_hi ly -> raZ regs < alloc_ceiling -> YK0o.frm_zero (@YK11.fp_csr fx) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= most < 2 ^ 64 ->
  Lam = l1 ++ (p, k) :: l2 -> p <> 0 -> cnt <> fail -> bytes_at W mem p old -> Z.of_nat (length old) = k ->
  0 <= n < 2 ^ 29 -> blocks_bytes S + (n + 16) <= LIVE_MAX ->
  rb_envR E2 regs p n cnt fail (Ledger.lsum Lam) ran k peak most res ->
  st_ok_pi SEGS VAL E2 rb_sr (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + (rb_pc0 + 404))) mem4 (seg_rom SEGS))) ->
  ajournal_xR (SK := SK) SEGS B PST ARcfx RR STK_fuzz_realloc (spZ regs) (ablocks_fp [(p - 16, k + 16)]) ly S Hp W
    mem md [] ly4 S4 Hp4 W4 mem4 md4 k4 ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem4) ->
  prh_most (PA := PA) W4 mem4 most -> prh_own (PA := PA) W4 mem4 own ->
  room_live_cf S4 ->
  (* the hull use of the granted realloc (A14's secs_call_post of its path, in rb_nz) *)
  PresetHullBudget.hull_used S S4 [PresetReqAt.HRe (k + 16) (n + 16)] ->
  (forall sm x os i H0 hist, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe (k + 16) (n + 16)) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S4) ->
  4096 <= res -> res mod 16 = 0 -> Hp4 = remove Z.eq_dec (p - 16) (remove Z.eq_dec (p - 16) Hp) ->
  ablocks B ly S = b1 ++ (p - 16, k + 16) :: b2 -> ablocks B ly4 S4 = b1 ++ b2 ++ [(res, n + 16)] ->
  (forall i, 0 <= i < Z.min k n -> aview SEGS (w_H W4) mem4 (res + 16 + i) = aview SEGS (w_H W) mem (p + i)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W4 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + (rb_pc0 + 404))) mem4 (seg_rom SEGS)) md4)
    (fpostmR B ARcfx SK RR STK_fuzz_realloc (ablocks_fp [(p - 16, k + 16)]) regs ly S Hp W mem md
      (tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own l1 l2 E2 W4
  regs4 mem4 md4 ly4 S4 Hp4 k4 res b1 b2 HAFN HROD HSHI HRAC HFRM HLED Rmost ELam Hp0 Hc0 Hold Hlen Hn Hlv HENVR HSb HJ4
  HPM HM4 HO4 HRL4 HHU4 HPOS4 H4096 Hal_r EHp4 Eab_c Eab4 HCOPY.
unfold SRr'.
assert (Ep0 : (p =? 0) = false) by (apply Z.eqb_neq; exact Hp0).
destruct HENVR as (HEI2 & F1 & F2 & F3 & F4 & F8 & F10 & F11 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39 & F64 & HAE2).
pose proof (@pa_segs_low rc B_prog_listing PA) as Hsegs.
pose proof rb_STK_v as WS. pose proof rb_stk_own as WO.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
set (FP := ablocks_fp [(p - 16, k + 16)]).
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HLED) as (Rlp & Rpk & Rcnt & Rfail & Rran).
assert (HinL : In (p, k) Lam) by (rewrite ELam; apply in_or_app; right; left; reflexivity).
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran p k most own HLED HinL) as (Hk0 & Hblk & HinHp & Hp16 & Hhd).
rewrite rb_cf_head in Hblk, HinHp, Hhd.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) HAR Hblk) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & Hpw).
assert (Hreq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
pose proof (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HND.
assert (Hlsum : Ledger.lsum Lam = Ledger.lsum (l1 ++ l2) + k) by (rewrite ELam; apply prh_lsum_split).
assert (Hsz : Forall (fun ak => 0 <= snd ak) Lam) by exact (prh_ledger_sizes B ly S Hp W mem Lam peak cnt fail ran most own HLED).
assert (Hl12 : 0 <= Ledger.lsum (l1 ++ l2)).
{ apply prh_lsum_nonneg. rewrite Forall_forall in Hsz |- *. intros x Hx. apply Hsz. rewrite ELam.
  apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]. }
assert (Hpnot : ~ In p (map fst (l1 ++ l2))) by (rewrite ELam in HND; exact (prh_lam_rest_notin l1 l2 p k HND)).
assert (HLB : prh_lblocks B ly S Hp W mem Lam)
  by exact (proj2 (proj1 (prh_ledger_iff B ly S Hp W mem Lam peak cnt fail ran most own) HLED)).
assert (Hsum : Ledger.lsum (l1 ++ l2) + n < 2 ^ 64).
{ pose proof (proj2 (prh_live_room B ly S Hp W mem Lam peak cnt fail ran n most own HLED
    (prh_ablocks_nonneg_cf B ly S Hp W mem md (proj1 HAR)) Hlv)). lia. }
assert (HHB : forall a ka i, In (a, ka) Lam -> 0 <= i < 8 ->
  In (a - 16, ka + 16) (ablocks B ly S) /\ 0 <= ka /\ (a <> p -> ~ inFP FP (a - 16 + i))).
{ intros a ka i Hin Hi.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HLED Hin) as (Hka & Hbl & _ & _ & _).
  rewrite rb_cf_head in Hbl.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & Hb4 & Hbc & _).
  assert (Hrq : req_size (ka + 16) = ka + 16) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
  split; [exact Hbl|]. split; [exact Hka|].
  intros Hne (r & Hr & Hrr). unfold FP, ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []].
  cbn [fst snd] in Hrr. rewrite Hreq in Hrr.
  pose proof (rb_pw_disj (ablocks B ly S) (a - 16, ka + 16) (p - 16, k + 16) Hpw Hbl Hblk ltac:(cbn; lia)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, Hreq in Hd. lia. }
assert (Rcnt1 : 0 <= (cnt + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite F2; reflexivity).
assert (SHOK2 : sh_ok SEGS RB_Bx rb_SH0 E2 (mrestrict (w_H W4) mem4)) by constructor.
assert (Dlive : sv_denot E2 rb_live1 = Z_to_bv 64 (Ledger.lsum (l1 ++ l2))).
{ unfold rb_live1. rewrite (rb_sub_denot E2 (Ledger.lsum Lam) k F35 F37) by lia. f_equal. lia. }
assert (Hin4 : In (res, n + 16) (ablocks B ly4 S4))
  by (rewrite Eab4; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
pose proof HJ4 as (HAR4 & Hly4 & _).
destruct (alx_blocks _ _ _ LAWS ly4 S4 Hp4 W4 mem4 md4 res (n + 16) HAR4 Hin4) as (_ & _ & Hbc4 & _ & _ & Hpw4).
assert (Hrqn : req_size (n + 16) = n + 16) by (unfold req_size; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hrqn in Hbc4.
assert (Hperm4 : Permutation (ablocks B ly4 S4) ((res, n + 16) :: b1 ++ b2)).
{ rewrite Eab4, app_assoc. apply Permutation_sym, Permutation_cons_append. }
assert (Hfresh : ~ In (res + 16) (map fst (l1 ++ l2))).
{ rewrite ELam in HLB. exact (prh_fresh_realloc_app B ly S Hp W mem ly4 S4 l1 l2 p k res n b1 b2 HLB ltac:(lia) Eab_c Eab4 Hpw4). }
assert (Hnew : ~ In (res, n + 16) (b1 ++ b2)).
{ intros Hin. apply (rb_new_block (b1 ++ b2) (res, n + 16) ltac:(cbn; lia)); [|exact Hin].
  rewrite <- app_assoc, <- Eab4. exact Hpw4. }
(* ---- the NULL test (beqz a0 at +404): not taken, res <> 0 ---- *)
paj_run_tok_x_invR (RUNMR mem) HSb HJ4 SHOK2 HPM RB_Bspan; [rb_wr Usp2 |].
clear HF HG. rb_keep K4 Usp2.
YSRrG.psrr_branch_tokR RUN BRR HSb SHOK2 RB_Bspan.
all: rewrite rb_denot0, F64 in Hc; cbn [sv_denot] in Hc; unfold w64 in Hc; rewrite rb_beq in Hc by lia.
1: { exfalso. apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* ---- a1 = n, the restores, the frame popped, the tail jump to own at +436 ---- *)
paj_run_tok_x_invR (RUNMR mem) HSb HJ4 SHOK2 HPM RB_Bspan; [rb_wr Usp2 |].
clear HF HG. rb_keep K5 Usp2.
lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HSx (1%bv : bv 5) T1; prreg HSx (2%bv : bv 5) T2; prreg HSx (3%bv : bv 5) T3;
  prreg HSx (4%bv : bv 5) T4; prreg HSx (8%bv : bv 5) T8; prreg HSx (10%bv : bv 5) T10;
  prreg HSx (11%bv : bv 5) T11;
  pose proof (st_ok_mem_ok SEGS E2 ssx (restrict (w_H W4) msc) HSx) as HMO;
  cbn [ss_mem restrict ms_mem setpc] in HMO;
  let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
  rename HSx into HSt; rename HJ4 into HJt; rb_gen msc msT
end.
pose proof HJt as (HART & Hlyt & _ & _ & _ & _ & _ & _ & HJhit & HJbt & _).
pose proof Hlyt as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ rb_obj_byte a ->
  aview SEGS (w_H W4) (ms_mem msT) a = aview SEGS (w_H W4) mem4 a)
  by (intros a Ha H1 H2; rewrite (K5 a Ha H1 H2); exact (K4 a Ha H1 H2)).
set (mT := mrestrict (w_H W4) (ms_mem msT)).
pose proof (rb_chunk_val E2 mT _ 1 _ 0 8 (SOff 33 1) ((cnt + 1) mod 2 ^ 64) HMO eq_refl
  ltac:(cbn; left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite F33, unsigned_lit_small by lia; symmetry; apply rb_wrap)
  Rcnt1 ltac:(cbn; lia)) as Mc'.
pose proof (rb_chunk_val E2 mT _ 2 _ 0 8 (SOff 34 0) fail HMO eq_refl
  ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F34; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mf'.
pose proof (rb_chunk_val E2 mT _ 3 _ 0 8 rb_live1 (Ledger.lsum (l1 ++ l2)) HMO eq_refl
  ltac:(cbn; left; reflexivity) Dlive ltac:(cbn; lia) ltac:(cbn; lia)) as Ml'.
pose proof (rb_chunk_val E2 mT _ 4 _ 0 1 (SOff 36 0) ran HMO eq_refl
  ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F36; reflexivity)
  ltac:(cbn; destruct Rran; lia) ltac:(cbn; lia)) as Mr0.
pose proof (rb_chunk_val E2 mT _ 5 _ 0 8 (SOff 38 0) peak HMO eq_refl
  ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, F38; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mp'.
rb_objv Mc' pi_g_count. rb_objv Mf' pi_g_fail. rb_objv Ml' pi_g_live. rb_objv Mr0 pi_g_ran_out. rb_objv Mp' pi_g_peak.
(* g_most and g_own_ran_out at the tail call: the runs since the realloc call write neither *)
assert (HMT : prh_most (PA := PA) W4 (ms_mem msT) most /\ prh_own (PA := PA) W4 (ms_mem msT) own)
  by (apply (rb_om_kept W4 W4 mem4 (ms_mem msT) most own); [rb_far_by KT | exact HM4 | exact HO4]).
assert (HGt : prh_glob (PA := PA) W4 (ms_mem msT) (Ledger.lsum (l1 ++ l2)) peak ((cnt + 1) mod 2 ^ 64) fail ran most own).
{ exact (prh_glob_final_le W mem W4 (ms_mem msT) (Ledger.lsum Lam) peak cnt fail ran _ _ _ _ most own
    (prh_ledger_glob B ly S Hp W mem Lam peak cnt fail ran most own HLED) Ml' ltac:(lia) Mp' Mc' Rcnt1 Mf' ltac:(lia) Mr0 Rran
    (proj1 HMT) (proj2 HMT)). }
assert (HLEDt : prh_ledger B ly4 S4 Hp4 W4 (ms_mem msT) (l1 ++ l2) peak ((cnt + 1) mod 2 ^ 64) fail ran most own).
{ apply (prh_ledger_disown B ly S Hp W mem ly4 S4 Hp4 W4 (ms_mem msT) l1 l2 p k peak cnt fail ran
    peak ((cnt + 1) mod 2 ^ 64) fail ran most own).
  - rewrite <- ELam. exact HLED.
  - exact HGt.
  - intros a ka i Hin Hi. apply (prh_mbyte_of_aview (PA := PA)).
    assert (HinL' : In (a, ka) Lam).
    { rewrite ELam. apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
    destruct (HHB a ka i HinL' Hi) as (Hbl & Hka & Hfp).
    assert (Hne : a <> p) by (intros ->; apply Hpnot; apply in_map_iff; exists (p, ka); split; [reflexivity | exact Hin]).
    rewrite rb_cf_head. apply (HJbt (a - 16) (ka + 16) i Hbl); [| | exact (Hfp Hne)].
    + exact (prh_blocks_kept_realloc B ly S ly4 S4 b1 b2 p k (res, n + 16) a ka Eab_c Eab4 Hne Hbl).
    + unfold req_size. destruct (Z.eqb_spec (ka + 16) 0); lia.
  - intros a ka Hin Hbl.
    assert (Hne : a <> p) by (intros ->; apply Hpnot; apply in_map_iff; exists (p, ka); split; [reflexivity | exact Hin]).
    exact (prh_blocks_kept_realloc B ly S ly4 S4 b1 b2 p k (res, n + 16) a ka Eab_c Eab4 Hne Hbl).
  - rewrite EHp4, rb_cf_head. apply prh_remove_idem. }
assert (Hspt : spZ (ms_regs msT) = spZ regs) by (unfold spZ at 1; rewrite T2; rewrite ?rb_denot0; rewrite F2; reflexivity).
assert (Hrat : raZ (ms_regs msT) = raZ regs) by (unfold raZ at 1; rewrite T1, F1; reflexivity).
eapply (SRrG_mono SEGS RR).
{ eapply (aj_call_xR (SK := SK) SEGS B PST ARcfx LAWS Hsegs RR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (wle'_trans SEGS YGcfRehidePost.RZ_cf) W4 E2 _ msT STK_fuzz_realloc (spZ regs)
    FP ly S Hp W mem md [] ly4 S4 Hp4 _ _ STK_own [(res, res + 8)] 0 (getr regs 2) (getr regs 1) ch _ HSt eq_refl HJt).
  - rewrite T2; rewrite ?rb_denot0; reflexivity.
  - exact F2.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite WO; lia.
  - rewrite WO, WS; lia.
  - rewrite T3, F3. exact Hgp.
  - rewrite T4, F4. exact Htp.
  - rewrite T1, F1. reflexivity.
  - exact Hra.
  - exact Hra4.
  - rewrite Z.add_0_r.
    assert (Hs0t : s0Z (ms_regs msT) = s0Z regs) by (unfold s0Z; rewrite T8, F8; reflexivity).
    rewrite Hs0t. apply (achain_ly_top ly ly4); [exact Etop|].
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
    intros a Ha. apply HJhit; lia.
  - intros HPREt. apply rb_callee_lift.
    refine (OWN ly4 S4 Hp4 W4 (ms_regs msT) (ms_mem msT) _ ch res n (l1 ++ l2) peak ((cnt + 1) mod 2 ^ 64)
      fail ran most own (conj HPREt (conj _ (conj _ (conj _ HFRM)))) _ _ ltac:(lia) _ Hal_r H4096 _ Hsum HLEDt).
    + apply (rb_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJt); [|exact HROD].
      apply sink_closed_ablocks_fp. repeat constructor. cbn. lia.
    + rewrite Hspt, Ehi. exact HSHI.
    + rewrite Hrat. exact HRAC.
    + rewrite T10, F64. reflexivity.
    + rewrite T11, F11. reflexivity.
    + exact Hin4.
    + replace (res + cf_head) with (res + 16) by (rewrite rb_cf_head; lia). exact Hfresh.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [| destruct (inFP_nil a Ha)].
    destruct (Z.eq_dec res (p - 16)) as [Eq | Neq].
    + left. unfold FP, ablocks_fp. cbn [map fst snd]. apply inFP_cons. left. rewrite Hreq. lia.
    + right; left. exists res, (n + 16). split; [exact Hin4|]. split; [|rewrite Hrqn; lia].
      intros Hin. rewrite Eab_c in Hin. apply in_app_or in Hin as [Hin | [Heq | Hin]].
      * apply Hnew. apply in_or_app; left; exact Hin.
      * injection Heq as Eq1 _. lia.
      * apply Hnew. apply in_or_app; right; exact Hin. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k5 & -> & HJ5 & HJown & HP5 & HQ5).
unfold fQmn in HQ5. destruct HQ5 as ((Hrk5 & ES5 & Ely5 & R5a & EHp5 & Eab5 & Herr5 & HLED5) & Hmn5).
pose proof HJ5 as (HAR5 & _).
pose proof HJown as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJbo5 & _).
unfold fpostmR, fpostR, apost_base_xR, fQmn.
exists ly5, S5, Hp5, regs5, mem5, md5. eexists.
split; [reflexivity|]. split; [exact HJ5|].
split.
{ eapply rb_apres_trans; [| exact HP5].
  eapply (aregs_preserved_of_st_ok SEGS _ E2 _ _ regs _ HSt); [exact HAE2 | vm_compute; reflexivity]. }
split; [|intros H0; exact (Hmn5 (HPM H0))].
apply tfrP_Q_of_R with (res := res + 16).
refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
  tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
{ exact R5a. }
{ rewrite ES5; exact HRL4. }
(* THE HULL USE: the granted realloc's (own keeps the state) *)
{ rewrite ES5, Ep0. exact HHU4. }
{ intros H0; exfalso; lia. }
{ intros _ H0; exfalso; exact (Hp0 H0). }
{ intros _ _; rewrite ES5; exact (rb_pos_one S S4 _ HPOS4). }
(* THE OUTCOME: p <> 0; the realloc granted (res >= 4112) and the advance is the HRe step above *)
{ intros H0; exfalso; exact (Hp0 H0). }
{ intros _ qsm qx qos qi qH0 qhist qHP qHr _ _; split; [lia|].
  rewrite ES5; exact (rb_pos_one S S4 _ HPOS4 qsm qx qos qi qH0 qhist qHP qHr). }
right; right; right.
assert (Hin5 : In (res, n + 16) (ablocks B ly5 S5)) by (rewrite Eab5; exact Hin4).
destruct (AR_shadow_law_ok_cf SEGS B ly5 S5 Hp5 W5 mem5 md5 res (n + 16) (proj1 HAR5) Hin5) as [Hbs Hhv].
assert (Hhd5 : hd_skip Hp5 res = 16).
{ unfold hd_skip. rewrite EHp5. cbn [existsb]. rewrite Z.eqb_refl. reflexivity. }
rewrite Hhd5, Hrqn in Hbs. rewrite Hrqn in Hhv.
apply tfrP_A4_of_R with (l1 := l1) (l2 := l2).
refine {| tfrP4_nonnull := Hp0; tfrP4_notchosen := Hc0; tfrP4_res_min := _; tfrP4_res_align := _; tfrP4_lam := ELam;
  tfrP4_fresh := Hfresh; tfrP4_hp := _; tfrP4_ablocks := _; tfrP4_bytes := _; tfrP4_addressable := _; tfrP4_hull := _;
  tfrP4_ledger := _ |}.
{ rewrite rb_cf_head; lia. }
{ rewrite Zplus_mod, Hal_r; reflexivity. }
{ rewrite EHp5, EHp4, rb_cf_head, prh_remove_idem; f_equal; lia. }
{ exists b1, b2. rewrite rb_cf_head. split; [exact Eab_c|]. rewrite Eab5.
  replace (res + 16 - 16) with res by lia. split; [exact Hnew | exact Hperm4]. }
(* the new block's bytes: the first min (k, n) are the old block's *)
{ apply (rb_bytes_success (mrestrict (w_H W) mem) (mrestrict (w_H W5) mem5) p (res + 16) old k n Hold Hlen Hk0 ltac:(lia)).
  - intros i Hi. apply rb_mbyte_of_aview2.
    assert (Hrb : 0 <= res + (16 + i) < 2 ^ 64 /\ ~ (spZ regs - 48 <= res + (16 + i) < spZ regs) /\
      ~ rb_obj_byte (res + (16 + i))).
    { split; [lia|]. split; [lia|]. intros Hx.
      apply (blk_img_x SEGS B ARcfx LAWS ly4 S4 Hp4 W4 mem4 md4 res (n + 16) (res + (16 + i)) HAR4 Hin4);
        [rewrite Hrqn; lia | exact (pst_in_img_B _ (rb_obj_pst _ Hx))]. }
    destruct Hrb as (B1 & B2 & B3).
    replace (res + 16 + i) with (res + (16 + i)) by lia.
    rewrite (HJbo5 res (n + 16) (16 + i) Hin4 ltac:(rewrite Eab5; exact Hin4) ltac:(rewrite Hrqn; lia)).
    2: { intros Hx. apply inFP_cons in Hx as [Hx | Hx]; [cbn [fst snd] in Hx; lia | exact (inFP_nil _ Hx)]. }
    rewrite (KT _ B1 B2 B3). replace (res + (16 + i)) with (res + 16 + i) by lia. exact (HCOPY i Hi).
  - intros i Hi.
    destruct (alx_blocks _ _ _ LAWS ly5 S5 Hp5 W5 mem5 md5 res (n + 16) HAR5 Hin5) as (_ & _ & _ & _ & Hpr5 & _).
    destruct (Hpr5 (res + 16 + i) ltac:(rewrite Hrqn; lia)) as ((Hh & b & Hb) & _).
    exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
{ destruct (Z.eq_dec n 0) as [-> | Hn1]; [apply range_addressable_nil; lia|].
  apply (block_shadow_range _ SHADOW_OFF (res + 16) (n + 16 - 16) (res + 16) n Hbs); lia. }
(* its shadow hull is visible *)
{ intros Hn1 s Hs. apply Hhv.
  pose proof (shadow_mono res (res + 16) ltac:(lia)) as M1.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
    by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). replace (res + (n + 16) - 1) with (res + 16 + n - 1) by lia. lia. }
replace (res + 16) with (res + cf_head) by (rewrite rb_cf_head; lia). exact HLED5.
Qed.

(* ===== p <> NULL: g_count += 1; CHOSEN-FAIL, or the main path: unpoison (p - 16, 16) at +248, the head read,
   g_live -= k, realloc (p - 16, n + 16) at +400, then the two continuations ===== *)
Lemma rb_nz : forall ly S Hp (W : world SEGS) regs mem md ch p k n old Lam peak cnt fail ran most own,
  fpre B ARcfx STK_fuzz_realloc ly S Hp W regs mem md ch -> room_live_cf S ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* the text's hull budget at p <> 0 (the realloc's one event HRe) *)
  PresetHullBudget.hull_budget S [PresetReqAt.HRe (k + cf_head) (n + cf_head)] ->
  In [cf_pc_realloc_ra0] (as_universe B) -> In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (as_universe B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n -> 0 <= n -> n + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  p <> 0 -> In (p, k) Lam -> bytes_at W mem p old -> Z.of_nat (length old) = k ->
  (cnt <> fail -> blocks_bytes S + (n + cf_head) <= LIVE_MAX) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at SEGS (SIGMA AS_fuzz_realloc) regs mem md)
    (fpostmR B ARcfx SK RR STK_fuzz_realloc (ablocks_fp [(p - cf_head, k + cf_head)]) regs ly S Hp W mem md
      (tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own)).
Proof.
intros ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own
  HPRE HRL HSEC H24 HHBg HU0 HU1 H10 H11 Hn0 Hnmax HLED Hp0 HinL Hold Hlen HLIVE.
destruct HPRE as (HAFN & HROD & HSHI & HRAC & HFRM).
(* ROUTE STOP + LIFT: the plain segments up to the realloc call are lifted ONCE, here, by the layer's shared helper;
   the walk switches to the primed relation at the cut before the call (below) *)
apply YGcfRhLift.ra_rh_of_SRr.
assert (Ep0 : (p =? 0) = false) by (apply Z.eqb_neq; exact Hp0).
pose proof (@pa_segs_low rc B_prog_listing PA) as Hsegs.
pose proof rb_STK_v as WS. pose proof rb_stk_own as WO.
pose proof rb_cf_head as Hcf. rewrite !Hcf.
pose proof rb_cf_max as Hcmax.
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hnmax as Hnm. rewrite Hcf, Hcmax in Hnm.
pose proof HLIVE as Hlv. rewrite Hcf in Hlv.
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (pal_env B PAL) as HENV.
set (FP := ablocks_fp [(p - 16, k + 16)]).
(* the ledger, through its named projections *)
pose proof (prh_ledger_live B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mlive.
pose proof (prh_ledger_peak B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mpeak.
pose proof (prh_ledger_count B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mcnt.
pose proof (prh_ledger_fail B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mfail.
pose proof (prh_ledger_ran B ly S Hp W mem Lam peak cnt fail ran most own HLED) as Mran.
pose proof (prh_ledger_bounds B ly S Hp W mem Lam peak cnt fail ran most own HLED) as (Rlp & Rpk & Rcnt & Rfail & Rran).
pose proof (prh_ledger_glob B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HGl.
pose proof (prh_ledger_most B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HMOST.
(* PRH_Base's projection, qualified: S1Ledger's OWN arm lemma has the same short name prh_ledger_own *)
pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HOWN.
destruct (rb_most_val W mem most HMOST) as [Mmost Rmost].
pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran p k most own HLED HinL) as (Hk0 & Hblk & HinHp & Hp16 & Hhd).
rewrite Hcf in Hblk, HinHp, Hhd.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (p - 16) (k + 16) HAR Hblk) as (Hb16 & Hb4096 & Hbceil & Happ & Hbpres & Hpw).
assert (Hreq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
rewrite Hreq in Hbceil, Happ, Hbpres.
destruct (in_split (p, k) Lam HinL) as (l1 & l2 & ELam).
pose proof (prh_ledger_nodup B ly S Hp W mem Lam peak cnt fail ran most own HLED) as HND.
assert (Hlsum : Ledger.lsum Lam = Ledger.lsum (l1 ++ l2) + k) by (rewrite ELam; apply prh_lsum_split).
assert (Hp8 : (p - 16) mod 8 = 0).
{ apply Z.mod_divide in Hb16 as [x Hx]; [|lia]. rewrite Hx.
  replace (x * 16) with ((x * 2) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hshd : forall a, (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  ~ (shadow_addr (p - 16) <= a < shadow_addr (p - 16) + 2)).
{ intros a Ha. unfold shadow_addr.
  assert (D1 : 0 <= (p - 16) / 8) by (apply Z.div_pos; lia).
  assert (D2 : (p - 16) / 8 < 2 ^ 44 - 2) by (apply Z.div_lt_upper_bound; lia).
  unfold kHighMemBeg, SHADOW_OFF in *. lia. }
(* the old block's bytes: no frame, no static, below the ESTACK window and off the head's shadow *)
assert (HBK : forall a, p - 16 <= a < p + k -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 48 <= a < spZ regs) /\
  ~ rb_obj_byte a /\ ~ (spZ regs + -48 - ESTACK <= a < spZ regs + -48) /\
  ~ (shadow_addr (p - 16) <= a < shadow_addr (p - 16) + 2)).
{ intros a Ha. split; [lia|]. split; [lia|]. split.
  { intros Hx. apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md (p - 16) (k + 16) a HAR Hblk);
      [rewrite Hreq; lia | exact (pst_in_img_B a (rb_obj_pst a Hx))]. }
  split; [rewrite Hes; lia|]. apply Hshd. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
(* the heads of Lam's blocks *)
assert (HHB : forall a ka i, In (a, ka) Lam -> 0 <= i < 8 ->
  0 <= a - 16 + i < 2 ^ 64 /\ ~ (spZ regs - 48 <= a - 16 + i < spZ regs) /\ ~ rb_obj_byte (a - 16 + i)).
{ intros a ka i Hin Hi.
  pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a ka most own HLED Hin) as (Hka & Hbl & _ & _ & _).
  rewrite Hcf in Hbl.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hbl) as (_ & Hb4 & Hbc & _).
  assert (Hrq : req_size (ka + 16) = ka + 16) by (unfold req_size; destruct (Z.eqb_spec (ka + 16) 0); lia).
  rewrite Hrq in Hbc.
  split; [lia|]. split; [lia|].
  intros Hx. apply (blk_img_x SEGS B ARcfx LAWS ly S Hp W mem md _ _ (a - 16 + i) HAR Hbl);
    [rewrite Hrq; lia | exact (pst_in_img_B _ (rb_obj_pst _ Hx))]. }
(* THE HULL at the realloc call (route (b), threaded): the text's entry budget for the call's one event HRe gives the
   admission cf_hull_ok (QMm_cf's) and the entry headroom cf_hull_adm (the realloc tree's) at S, the call's state (the
   unpoison keeps S) *)
rewrite Hcf in HHBg.
pose proof (PresetHullPay.hull_ok_of_budget S _ HHBg) as HHOK.
pose proof (PresetHullPay.hull_adm_of_budget_re S _ _ HHBg) as HADM.
(* ---- the entry state ---- *)
set (xs := [SHADOW_OFF; cnt; fail; Ledger.lsum Lam; ran; k; peak; most]).
destruct (rb_entry _ ly S Hp W regs mem md ch p n k cnt fail (Ledger.lsum Lam) peak ran most HAFN
  ltac:(rewrite WS; lia) H10 H11 ltac:(lia) Hblk Hk0 Hhd Mlive Mpeak Mcnt Mfail Mran Mmost Rlp Rpk Rcnt Rfail Rran Rmost)
  as [HS SHOK].
fold xs in HS, SHOK.
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARcfx STK_fuzz_realloc FP ly S Hp W regs mem md ch HAFN) as HJ.
remember (RB_EI regs xs) as E eqn:HE.
rb_envfacts E regs xs HEI EL.
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cnt) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fail) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Ledger.lsum Lam)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ran) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 k) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 peak) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 most) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) xs)) E)
  by (split; [intros j Hj; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Up : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE EL.
assert (Rcnt1 : 0 <= (cnt + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
unfold cfg_at. rewrite rb_entry_pc. change (w64 (BASE + rb_pc0)) with (Z_to_bv 64 (BASE + rb_pc0)).
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
(* ---- the frame, the saves, g_count += 1; the CHOSEN-FAIL test (bne g_count, g_fail_at at +68) ---- *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM RB_Bspan; [rb_wr Usp |].
clear HF HG. rb_keep K1 Usp.
psrr_branch_tok RUN BR HS SHOK RB_Bspan.
all: rewrite !rb_denot0, E33, E34, rb_bne in Hc by lia.
2: {
  (* ===== CHOSEN-FAIL: g_count = g_fail_at; g_fail_at := SIZE_MAX, the shared epilogue, return 0 at +108 ===== *)
  apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM RB_Bspan; [rb_wr Usp |].
  clear HF HG. rb_keep K2 Usp.
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
    prreg HSx (1%bv : bv 5) R1; prreg HSx (10%bv : bv 5) R10;
    pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ssx) (restrict (w_H W) msc) HSx) as HMO;
    cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
    let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
    eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity)); intros mat';
    apply (YSRrG.SRr'_ret SEGS YGcfRehidePost.RZ_cf); apply rb_post_lift;
    unfold fpostm, fpost, apost_base_x, fQmn;
    exists ly, S, Hp, (ms_regs msc), (ms_mem msc); eexists; exists 0;
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARcfx LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (map (Z_to_bv 64) xs) HSx);
            [exact HAE | vm_compute; reflexivity]|];
    rb_gen msc msF
  end.
  split; [|exact HPM].
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ rb_obj_byte a ->
    aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
    by (intros a Ha H1 H2; rewrite (K2 a Ha H1 H2); exact (K1 a Ha H1 H2)).
  assert (OM : prh_most (PA := PA) W (ms_mem msF) most /\ prh_own (PA := PA) W (ms_mem msF) own)
    by (apply (rb_om_kept W W mem (ms_mem msF) most own); [rb_far_by KF | exact HMOST | exact HOWN]).
  apply tfrP_Q_of_R with (res := 0).
  refine {| tfrP_ret := _; tfrP_room := _; tfrP_hull := _; tfrP_pos_null := _; tfrP_pos_malloc := _;
    tfrP_pos_realloc := _; tfrP_outcome_malloc := _; tfrP_outcome_realloc := _; tfrP_arm := _ |}.
  { rewrite R10; reflexivity. }
  { exact HRL. }
  (* THE HULL USE: no allocator call on this arm (S' = S) *)
  { exact (PresetHullBudget.hull_used_refl S _). }
  { intros _; exact (rb_pos_nil S S (fun _ _ _ _ _ _ HP => HP)). }
  { intros H0; exfalso; exact (H0 eq_refl). }
  { intros H0; exfalso; exact (H0 eq_refl). }
  (* THE OUTCOME: p <> 0, and cnt = fail here contradicts its cnt <> fail *)
  { intros H0; exfalso; exact (Hp0 H0). }
  { intros _ qsm qx qos qi qH0 qhist _ _ _ qnf; exfalso; exact (qnf Hc). }
  right; left. apply tfrP_A2_of_R.
  refine {| tfrP2_nonnull := Hp0; tfrP2_chosen := Hc; tfrP2_res0 := eq_refl; tfrP2_hp := eq_refl;
    tfrP2_ablocks := eq_refl; tfrP2_bytes := _; tfrP2_ledger := _ |}.
  { unfold bytes_at. apply (rb_garr8_keep (mrestrict (w_H W) mem)); [exact Hold|].
    intros j Hj. apply (prh_mbyte_of_aview (PA := PA)).
    destruct (HBK (p + Z.of_nat j) ltac:(lia)) as (B1 & B2 & B3 & _). exact (KF _ B1 B2 B3). }
  set (mF := mrestrict (w_H W) (ms_mem msF)).
  pose proof (rb_chunk_val E mF _ 3 _ 0 8 (SOff 33 1) ((cnt + 1) mod 2 ^ 64) HMO eq_refl
    ltac:(cbn; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; symmetry; apply rb_wrap)
    Rcnt1 ltac:(cbn; lia)) as Mc'.
  pose proof (rb_chunk_val E mF _ 4 _ 0 8 (SLit 18446744073709551615) SIZE_MAXZ HMO eq_refl
    ltac:(cbn; left; reflexivity) ltac:(cbn [sv_denot]; unfold SIZE_MAXZ; reflexivity)
    ltac:(unfold SIZE_MAXZ; cbn; lia) ltac:(cbn; lia)) as Mf'.
  pose proof (rb_chunk_val E mF _ 5 _ 0 8 (SOff 35 0) (Ledger.lsum Lam) HMO eq_refl
    ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, E35; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Ml'.
  pose proof (rb_chunk_val E mF _ 8 _ 0 8 (SOff 38 0) peak HMO eq_refl
    ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, E38; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Mp'.
  pose proof (rb_chunk_val E mF _ 6 _ 0 1 (SOff 36 0) ran HMO eq_refl
    ltac:(cbn; left; reflexivity) ltac:(rewrite rb_denot0, E36; reflexivity)
    ltac:(cbn; destruct Rran; lia) ltac:(cbn; lia)) as Mr0.
  rb_objv Mc' pi_g_count. rb_objv Mf' pi_g_fail. rb_objv Ml' pi_g_live. rb_objv Mp' pi_g_peak. rb_objv Mr0 pi_g_ran_out.
  apply (prh_ledger_frame B ly S Hp W mem ly S Hp W (ms_mem msF) Lam peak cnt fail ran
    peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran most own HLED).
  - exact (prh_glob_final_le W mem W (ms_mem msF) _ peak cnt fail ran _ _ _ _ most own HGl Ml' Rlp Mp' Mc' Rcnt1 Mf'
      ltac:(unfold SIZE_MAXZ; lia) Mr0 Rran (proj1 OM) (proj2 OM)).
  - intros a ka i Hin Hi. apply (prh_mbyte_of_aview (PA := PA)).
    destruct (HHB a ka i Hin Hi) as (B1 & B2 & B3). rewrite Hcf. exact (KF _ B1 B2 B3).
  - intros a ka _ Hbl. exact Hbl.
  - apply Permutation_refl. }
apply Bool.negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hc0.
(* the per-call LIVE premise, owed at cnt <> fail *)
specialize (Hlv Hc0).
(* ---- the decided TOOBIG and UBSan tests, s1 = p - 16, unpoison (p - 16, 16) at +248 (ret +252) ---- *)
paj_run_tok_x_inv (RUNM mem) HS HJ SHOK HPM RB_Bspan; [rb_wr Usp |].
clear HF HG. rb_keep K2 Usp.
lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HSx (1%bv : bv 5) U1; prreg HSx (3%bv : bv 5) U3;
  prreg HSx (4%bv : bv 5) U4; prreg HSx (10%bv : bv 5) U10; prreg HSx (11%bv : bv 5) U11;
  rename HSx into HSu; rename HJ into HJu; rb_gen msc msU
end.
eapply SRr_bind.
{ eapply (@YGcallMxmn.aj_unpoison_x_m fx rc SK SEGS B PST ARcfx cf_head _ LAWS Hsegs cf_pc_unpoison AUNPOISONx
    W E _ msU STK_fuzz_realloc (spZ regs) FP ly S Hp W mem md [] ly S Hp _ 0
    (p - 16) (k + 16) (-48) (ew E 2) (Z_to_bv 64 (BASE + (rb_pc0 + 252))) HSu).
  - cbn [ss_pc setpc]. exact pal_unpoison.
  - reflexivity.
  - exact HJu.
  - rewrite U10, E10, unsigned_lit_small by lia. unfold w64. f_equal; lia.
  - rewrite U11, Hcf. reflexivity.
  - rewrite Hcf. reflexivity.
  - exact HinHp.
  - exact Hblk.
  - rewrite Hcf, Hreq. lia.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ msU 2%bv HSu).
  - reflexivity.
  - exact Usp.
  - reflexivity.
  - lia.
  - rewrite Hes, WS. lia.
  - rewrite U3, E3. exact Hgp.
  - rewrite U4, E4. exact Htp.
  - exact U1.
  - apply rb_ret_ok. lia. }
cbv beta. intros Wu cu _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsh0 & Hkeep & Hpres2 & Hmn2).
pose proof (fun H0 => Hmn2 (HPM H0)) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
rewrite Hcf in Hsh0, Hkeep. change (16 / 8) with 2 in Hkeep.
assert (KPu : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msU) a).
{ intros a Hx. pose proof (rb_pst_low a Hx).
  apply Hkeep; [lia | rewrite Hes; unfold SHADOW_OFF in *; lia | apply Hshd; left; lia]. }
assert (KFu : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msU) a).
{ intros a Ha. apply Hkeep; [lia | rewrite Hes; lia | apply Hshd; right; unfold kHighMemBeg; lia]. }
assert (KBu : forall a, p - 16 <= a < p + k -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem msU) a).
{ intros a Ha. destruct (HBK a Ha) as (B1 & _ & _ & B4 & B5). apply Hkeep; [exact B1 | exact B4 | exact B5]. }
jafter_call_keep_pi HSu 40%nat regs2 (mrestrict (w_H W) mem2) HP2 rb_keep_u HSa.
match type of HSa with ?tq -> _ => assert (HRK : tq); [|specialize (HSa HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite Usp in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KFu. lia.
  - intros _. apply (apresent_writable SEGS). rewrite Usp in Ha. apply HJpres2. rewrite WS. lia.
  - rb_stk Ha KPu.
  - rb_stw Ha.
  - rb_stk Ha KPu.
  - rb_stw Ha.
  - rb_stk Ha KPu.
  - rb_stw Ha.
  - rb_stk Ha KPu.
  - rb_stw Ha.
  - rewrite Up in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KBu. lia.
  - intros _. exfalso. lia.
  - rb_stk Ha KPu.
  - rb_stw Ha.
  - rb_stk Ha KPu.
  - intros _. exfalso. lia. }
rewrite <- restrict_mkst_fx in HSa.
remember (havoc E 40 (map (getr regs2) CLOB)) as Eu eqn:HE1 in HSa.
assert (HEIu : img_env VAL A_LIM Eu) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall j, (j < 40)%nat -> ew Eu j = ew E j) by (intros j Hj; rewrite HE1; apply YN3v.ew_havoc_old; exact Hj).
assert (HAE1 : env_agree 32 (Ereg regs (map (Z_to_bv 64) xs)) Eu)
  by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (Usp1 : bv_unsigned (ew Eu 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp).
clear HE1.
(* after the unpoison the head's 16 bytes read shadow 0 *)
assert (SHOK1 : sh_ok SEGS RB_Bx rb_SH1 Eu (mrestrict (w_H W) mem2)).
{ unfold rb_SH1, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem2 Eu RB_Bx 10%nat (p - 16) 16 p (-16) 0).
  - apply (zero_shadow_range (aview SEGS (w_H W) mem2) SHADOW_OFF (p - 16) 16 Hp8 eq_refl).
    intros i Hi. change (16 / 8) with 2 in Hi.
    replace (shadow_of_addr SHADOW_OFF (p - 16) + i) with (shadow_addr (p - 16 + i * 8))
      by (unfold shadow_addr, shadow_of_addr; rewrite Z.div_add by lia; lia).
    apply Hsh0. lia.
  - unfold U, RB_Bx. cbn [sv_denot]. rewrite (OLD1 32%nat) by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  - unfold U. cbn [sv_denot]. rewrite (OLD1 10%nat) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Up.
  - lia.
  - lia.
  - intros x Hx. pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
    unfold app_addr, kLowShadowBeg, kHighMemBeg in Hx'. unfold SHADOW_OFF. lia. }
(* ---- the two head checks (decided by the shadow entry), the head read, g_live -= k, a1 = n + 16, realloc at +400
   (ret +404) ---- *)
paj_run_tok_x_inv (RUNM mem) HSa HJ2 SHOK1 HPM RB_Bspan; [rb_wr Usp1 |].
clear HF HG. rb_keep K3 Usp1.
lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc) |- _ =>
  prreg HSx (1%bv : bv 5) V1; prreg HSx (2%bv : bv 5) V2; prreg HSx (3%bv : bv 5) V3;
  prreg HSx (4%bv : bv 5) V4; prreg HSx (8%bv : bv 5) V8; prreg HSx (10%bv : bv 5) V10; prreg HSx (11%bv : bv 5) V11;
  rename HSx into HSr; rename HJ2 into HJr; rb_gen msc msR
end.
assert (HOLDR : forall a, p <= a < p + k -> aview SEGS (w_H W) (ms_mem msR) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (HBK a ltac:(lia)) as (B1 & B2 & B3 & _).
  rewrite (K3 a B1 B2 B3), (KBu a ltac:(lia)), (K2 a B1 B2 B3). exact (K1 a B1 B2 B3). }
assert (HMR : prh_most (PA := PA) W (ms_mem msR) most /\ prh_own (PA := PA) W (ms_mem msR) own).
{ apply (rb_om_kept W W mem (ms_mem msR) most own); [|exact HMOST | exact HOWN].
  intros a Ha. destruct (rb_far_obj a Ha) as [Hnb Hps]. pose proof (rb_pst_low a Hps).
  rewrite (K3 a ltac:(lia) ltac:(unfold SHADOW_OFF in *; lia) Hnb), (KPu a Hps).
  rewrite (K2 a ltac:(lia) ltac:(unfold SHADOW_OFF in *; lia) Hnb). exact (K1 a ltac:(lia) ltac:(unfold SHADOW_OFF in *; lia) Hnb). }
assert (Hsp1 : spZ (ms_regs msR) = spZ regs - 48).
{ unfold spZ at 1. rewrite V2. rewrite ?rb_denot0. cbn [sv_denot]. rewrite Usp1. rewrite unsigned_lit_small by lia. lia. }
assert (Hs01 : s0Z (ms_regs msR) = n).
{ unfold s0Z. rewrite V8, OLD1, E11 by lia. apply unsigned_lit_small. lia. }
assert (Hra1 : raZ (ms_regs msR) = BASE + (rb_pc0 + 404)).
{ unfold raZ. rewrite V1. apply unsigned_lit_small. split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. }
pose proof (YGcfAmx2.universe_ok_of_ARcf SEGS B ly S Hp W mem md (proj1 HAR)) as HUok.
(* the realloc call's old block is not hidden at the call: its base left Hp at the unpoison (rxhide: aj_realloc_x's
   premise `~ In pa Hpc`, YGcallRx.v blob 929b45781ba3) *)
assert (Hhid : ~ In (p - 16) (remove Z.eq_dec (p - 16) Hp)) by apply remove_In.
(* the P'' universe set (c-omx-alloc-univwiden): the realloc rule takes the univcore admission at the call state and
   posts its journal at the budget WS ++ [call trace]. This call's trace is FIXED (membership in u_fix, the text's two
   realloc-trace premises), so it is admitted at every state (YCbqG.admits_ct_fix) and leaves the post journal's budget
   (YCbqG.ajournal_xw_fix1R at wle' SEGS RZ_cf); the stretch before it stores no wild trace (WS = []) *)
assert (Htrc0 : In (call_trace ly cf_pc_realloc_ra0 (ms_regs msR) []) (as_universe B)).
{ unfold call_trace. destruct (frame0_ok ly (ms_regs msR)); [|exact HU0].
  unfold unwind_of_chain. rewrite Hra1, rb_ret_site. unfold prh_trace in HU1. exact HU1. }
(* QMm_cf at the CALL memory (the round-6g arity; part 3c took memnorm out): the state part from the room and the
   hull admission above, the call memory's RELRO fact arodata_ok_cf from fpre's reader form arodata_okP carried along
   the journal of the run (YGcallcf.arodata_ok_cf_of_journal_P, with CfImg_B's image rows from lib/AU/CfAroPresetB.v and
   the stand-in pal_errno_relro; the statics PST are no read-only byte, S1ImgB.pst_not_ro_B) *)
assert (HPSTro : forall a, aro_addr_cf a -> ~ Exists (in_zr a) PST).
{ intros a Ha Hx. apply (pst_not_ro_B a Hx). destruct Ha as [Ha | Ha].
  - right. unfold PAImg_prog.B_prog_relro_lo, PAImg_prog.B_prog_relro_hi.
    cbv [cf_relro_lo cf_relro_hi CfImg_B] in Ha. lia.
  - left. apply Exists_exists in Ha as (r0 & Hr0 & Hrr0).
    pose proof CfAroPresetB.ro_reads_nw_preset_AU as RN0. unfold YGcfAroBridge.ro_reads_nw_t in RN0.
    rewrite Forall_forall in RN0. destruct (RN0 r0 Hr0) as (_ & sg0 & Hsg0 & NW0 & L0a & L0b).
    exists sg0. split; [exact Hsg0|]. split; [exact NW0|]. unfold in_zr in Hrr0. lia. }
assert (HFPsk : ~ YI16.sink_open_fp FP) by (unfold FP; apply sink_closed_ablocks_fp; repeat constructor; cbn; lia).
assert (HARO : arodata_ok_cf SEGS B (ms_mem msR))
  by exact (arodata_ok_cf_of_journal_P (SK := SK) SEGS B PST ARcfx (@wle SEGS) _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJr
    CfAroPresetB.relro_seg_preset_AU pal_errno_relro CfAroPresetB.relro_top_preset_AU
    CfAroPresetB.ro_reads_nw_preset_AU HPSTro HFPsk HROD).
assert (HQM : QMm_cf SEGS B S (ms_mem msR)).
{ pose proof HJr as (HARr & _).
  exact (QMm_cf_of_room SEGS B _ _ _ _ _ _ (proj1 HARr) HQT (YGcfRoomLive.room_live_room S HRL) HHOK HARO). }
(* THE CUT before the realloc call (ROUTE STOP + LIFT): the plain run stops here and the walk continues in the primed
   relation R := wle' SEGS RZ_cf, its journal lifted once (YCbqG.ajournal_xwR_mono at YA0nH.wle_wle'); the call is the
   primed _k rule with the memnorm keep, YGcallRkKeep.aj_realloc_x_cfR_keep, over AREAL_cf as it stands *)
apply SRr_ret. cbv beta. unfold SRr'.
pose proof (ajournal_xwR_mono (SK := SK) SEGS B PST ARcfx (@wle SEGS) RR (wle_wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJr) as HJrR.
eapply (SRrG_bind SEGS RR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YGcallRkKeep.aj_realloc_x_cfR_keep (SK := SK) SEGS B PST LAWS Hsegs HENV OWNLOW WFL XSL HUok 0%nat
    (SIGMA AS___wrap_realloc) AREAL_cf (* WS := *) []
    W Eu _ msR STK_fuzz_realloc (spZ regs) FP ly S Hp W mem md [] ly S (remove Z.eq_dec (p - 16) Hp) _ _
    (p - 16) (k + 16) (n + 16) (-48) (getr regs 2) (Z_to_bv 64 (BASE + (rb_pc0 + 404))) [] HSr eq_refl eq_refl HJrR).
  - exact Hblk.
  - exact Hhid.
  - rewrite V10, OLD1, E10 by lia. rewrite unsigned_lit_small by lia. unfold w64. f_equal; lia.
  - rewrite V11, OLD1, E11 by lia. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite Hcmax. lia.
  - exact Hlv.
  - rewrite V2; rewrite ?rb_denot0; reflexivity.
  - rewrite OLD1 by lia. exact E2.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite Has, WS. lia.
  - rewrite V3, OLD1, E3 by lia. exact Hgp.
  - rewrite V4, OLD1, E4 by lia. exact Htp.
  - exact V1.
  - apply rb_ret_ok. lia.
  - exact HQM.
  - split; [exact HQT|]. split; [exact (YGcfRoomLive.room_live_room_k S HRL) | exact HADM].
  - unfold chain_pre. split; [rewrite Hra1; exact (rb_ret_hi 404 ltac:(lia))|].
    assert (Hbn : bad_next (spZ (ms_regs msR)) (ly_top ly) (s0Z (ms_regs msR)) = true).
    { unfold bad_next. apply orb_true_iff. left. apply orb_true_iff. left. apply Z.leb_le. rewrite Hsp1, Hs01. lia. }
    destruct (frame0_ok ly (ms_regs msR)); [rewrite Hbn|]; reflexivity.
  - exact (admits_ct_fix (as_universe B) ly cf_pc_realloc_ra0 (ms_regs msR) [] S Htrc0).
  - intros _ i Hi. unfold FP, ablocks_fp. cbn [map fst snd]. apply inFP_cons. left. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Hres & Hfrs4 & HPREr & Htrr &
  (pq & q & Hpq & Hpin & Hqres & Hqiff & (trc & Hpath & Hgf) & Hleaf) & HARM).
apply (ajournal_xw_fix1R Htrc0) in HJ4.
(* the realloc leaf's last conjunct keeps memnorm: at the leaf's memory, which is the call's post memory *)
pose proof Hleaf as Hleaf0.
destruct Hleaf as (lyL & regsL & memL & mdL & EcL & _ & _ & _ & _ & _ & _ & HmnL).
unfold cfg_at in EcL. injection EcL as _ _ EmL _. subst memL.
pose proof (fun H0 => HmnL (HPM H0)) as HPM4. clear HmnL.
(* the room: the cf layer's RL_realloc_step at the preset figures *)
assert (HRL4 : room_live_cf S4).
{ change S4 with (snd (q, S4)).
  eapply (YGcfRoomLive.RL_realloc_step SEGS B ly S (remove Z.eq_dec (p - 16) Hp) W (ms_regs msR) (ms_mem msR) _ []
    (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) pq (n + 16) _ trc).
  - exact (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREr).
  - exact Htrr.
  - rewrite Hcmax. lia.
  - exact Hlv.
  - exact (CfRoomLivePreset.preset_rl_sec_ok S HSEC).
  - exact (CfRoomLivePreset.preset_rl_b24_ok S H24).
  - lia.
  - exact HRL.
  - exact Hpath. }
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & _ & _ & _ & HJhi4 & HJb4 & HJi4 & _ & _ & HJpres4 & _).
assert (Hkc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs + -48 - ASTACK <= a < spZ regs + -48) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) (ms_mem msR) a).
{ destruct HARM as [(_ & _ & _ & _ & (K & _) & _) | (_ & _ & _ & _ & _ & (K & _))]; exact K. }
assert (Hki : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) (ms_mem msR) a).
{ destruct HARM as [(_ & _ & _ & _ & (_ & _ & K & _) & _) | (_ & _ & _ & _ & _ & (_ & _ & K & _))]; exact K. }
assert (KPr : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) (ms_mem msR) a).
{ intros a Hx. destruct (pal_pst_ok a Hx) as [H1 H2]. exact (Hki a (pst_in_img_B a Hx) H1 H2). }
assert (KFr : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W) (ms_mem msR) a).
{ intros a Ha. apply Hkc; [lia | rewrite Has; lia]. }
assert (HMO4 : prh_most (PA := PA) W4 mem4 most /\ prh_own (PA := PA) W4 mem4 own)
  by (apply (rb_om_kept W W4 (ms_mem msR) mem4 most own);
      [intros a Ha; destruct (rb_far_obj a Ha) as [_ Hps]; exact (KPr a Hps) | exact (proj1 HMR) | exact (proj2 HMR)]).
jafter_call_keep_pi HSr 60%nat regs4 (mrestrict (w_H W4) mem4) HP4 rb_keep_r HSb.
match type of HSb with ?tq -> _ => assert (HRK : tq); [|specialize (HSb HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite Usp1 in Ha. apply (prh_mbyte_of_aview (PA := PA)). apply KFr. lia.
  - intros _. apply (apresent_writable SEGS). rewrite Usp1 in Ha. apply HJpres4. rewrite WS. lia.
  - rb_stk Ha KPr.
  - rb_stw Ha.
  - rb_stk Ha KPr.
  - rb_stw Ha.
  - rb_stk Ha KPr.
  - rb_stw Ha.
  - rb_stk Ha KPr.
  - rb_stw Ha.
  - rb_stk Ha KPr.
  - rb_stw Ha.
  - rb_stk Ha KPr.
  - intros _. exfalso. lia. }
rewrite <- restrict_mkst_fx in HSb.
remember (havoc Eu 60 (map (getr regs4) CLOB)) as Ef eqn:HE2 in HSb.
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HE2; apply img_env_havoc; [exact HEIu | cbv; lia]).
assert (OLD2 : forall j, (j < 60)%nat -> ew Ef j = ew Eu j) by (intros j Hj; rewrite HE2; apply YN3v.ew_havoc_old; exact Hj).
assert (E2_64 : ew Ef 64 = w64 res) by (rewrite HE2; unfold havoc; cbn [ew]; exact Hres).
assert (HAE2 : env_agree 32 (Ereg regs (map (Z_to_bv 64) xs)) Ef)
  by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
clear HE2.
lazymatch type of HSb with st_ok_pi _ _ _ ?ss2 _ =>
  assert (Ess : ss2 = rb_sr) by (vm_compute; reflexivity); rewrite Ess in HSb; clear Ess end.
assert (HENVR : rb_envR Ef regs p n cnt fail (Ledger.lsum Lam) ran k peak most res).
{ unfold rb_envR. split; [exact HEIf|].
  split; [rewrite OLD2, OLD1 by lia; exact E1|]. split; [rewrite OLD2, OLD1 by lia; exact E2|].
  split; [rewrite OLD2, OLD1 by lia; exact E3|]. split; [rewrite OLD2, OLD1 by lia; exact E4|].
  split; [rewrite OLD2, OLD1 by lia; exact E8|]. split; [rewrite OLD2, OLD1 by lia; exact E10|].
  split; [rewrite OLD2, OLD1 by lia; exact E11|]. split; [rewrite OLD2, OLD1 by lia; exact E32|].
  split; [rewrite OLD2, OLD1 by lia; exact E33|]. split; [rewrite OLD2, OLD1 by lia; exact E34|].
  split; [rewrite OLD2, OLD1 by lia; exact E35|]. split; [rewrite OLD2, OLD1 by lia; exact E36|].
  split; [rewrite OLD2, OLD1 by lia; exact E37|]. split; [rewrite OLD2, OLD1 by lia; exact E38|].
  split; [rewrite OLD2, OLD1 by lia; exact E39|]. split; [exact E2_64 | exact HAE2]. }
assert (Hn29 : 0 <= n < 2 ^ 29) by lia.
(* THE HULL USE of the realloc at its end state (granted or refused): A14's per-call rule along the call's path
   (YGcfSecsStep.secs_realloc_step), read as the use of the one event HRe *)
pose proof (PresetHullBudget.hull_used_of_call_re (k + 16) (n + 16) S q S4
  (YGcfSecsStep.secs_realloc_step pq (n + 16) _ S trc (q, S4) Hpath)) as HHU4.
destruct HARM as [(Hr0 & EHp4 & Eab4 & Ebl4 & Kc & Herr & Hoom & Hrefused) |
                  (H4096 & Hal_r & EHp4 & (b1 & b2 & Eab_c & Eab4) & Hcopy & Kc)].
- (* ===== REFUSED ===== *)
  assert (HqN : q = PNull) by (apply Hqiff; exact Hr0). subst q. rewrite Hr0 in HENVR.
  destruct Kc as (_ & Kc2 & _).
  apply (rb_refd ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own
    l1 l2 Ef W4 regs4 mem4 md4 ly4 S4 Hp4 _ HAFN HROD HSHI HFRM HLED Rmost ELam Hp0 Hc0 Hold Hlen Hn29 HENVR HSb HJ4 HPM4
    (proj1 HMO4) (proj2 HMO4) HRL4 HHU4).
  + intros qsm qx qos qi qH0 qhist HP.
    exact (PresetRoomPosKeep.room_pos_keep_realloc_null SEGS B ly S _ W _ _ _ [] qsm qx qos qi qH0 qhist
      pq (n + 16) _ trc S4 (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREr) ltac:(rewrite Hcmax; lia) Hlv Htrc0 Hpath HP).
  + exact EHp4.
  + exact Eab4.
  + intros a Ha. replace a with ((p - 16) + (a - (p - 16))) by lia.
    rewrite (Kc2 (p - 16) (k + 16) (a - (p - 16)) Hblk ltac:(rewrite Hreq; lia) (fun H => H)).
    replace ((p - 16) + (a - (p - 16))) with a by lia. exact (HOLDR a Ha).
  + exact Herr.
  + (* the refusal evidence, world-free: YGcfRealloc.realloc_cf_refused_state from the leaf's NULL witness *)
    exact (realloc_cf_refused_state (n + 16) _ S S4
      (YGcfPath.shape_cf_of_WfP_cf _ _ _ _ _ (amc_wf _ _ _ _ _ (proj1 (proj1 HAR)))) Hrefused).
  + (* THE OUTCOME's exclusion: the realloc leaf's NULL witness mt_refused at the call's allocator state S (the
       unpoison kept ly S) is PRH_Refute's prh_granted_null S; with Wf_cf at S from the entry's ARcf, PRH_Refute.prh_refute_at
       at the run's consumer HRe *)
    intros qsm qx qos qi qH0 qhist qHP qHr qHc.
    exact (PRH_Refute.prh_refute_at (as_universe B) qsm qx qos qi 1 _ qH0 qhist S qHc ltac:(lia)
      (proj1 (PRH_Base.prh_run_at_one qsm qx qos qi _) qHr) eq_refl qHP
      (amc_wf _ _ _ _ _ (proj1 (proj1 HAR))) (or_intror (ex_intro _ (n + 16) (ex_intro _ _ (ex_intro _ S4 Hrefused))))).
- (* ===== SUCCESS ===== *)
  assert (Hres0 : res <> 0) by lia.
  assert (Hqn : q <> PNull) by (intros E0; apply Hres0; apply Hqiff; exact E0).
  assert (Hpqn : pq <> PNull) by (intros ->; unfold sptr_addr in Hpq; cbn in Hpq; lia).
  apply (rb_succ ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own
    l1 l2 Ef W4 regs4 mem4 md4 ly4 S4 Hp4 _ res b1 b2 HAFN HROD HSHI HRAC HFRM HLED Rmost ELam Hp0 Hc0 Hold Hlen Hn29 Hlv
    HENVR HSb HJ4 HPM4 (proj1 HMO4) (proj2 HMO4) HRL4 HHU4).
  + intros qsm qx qos qi qH0 qhist HP He.
    exact (PresetRoomPosKeep.room_pos_keep_realloc SEGS B ly S _ W _ _ _ [] qsm qx qos qi qH0 qhist
      pq (k + 16) (n + 16) _ trc q S4 (acall_pre_x_xs_cf SEGS B _ _ _ _ _ _ _ _ HPREr)
      (YGcfRoomLive.room_live_room_k S HRL) ltac:(rewrite Hcmax; lia) Hlv (YG01.admits_fix _ _ S HUok Htrc0) Hpin Hpqn
      Hpath Hqn HP He).
  + exact H4096.
  + exact Hal_r.
  + exact EHp4.
  + exact Eab_c.
  + exact Eab4.
  + intros i Hi. replace (res + 16 + i) with (res + (16 + i)) by lia.
    rewrite (Hcopy (16 + i) ltac:(lia)). replace (p - 16 + (16 + i)) with (p + i) by lia. exact (HOLDR (p + i) ltac:(lia)).
Qed.

(* ==== the theorem: the primed text itself (SRr' segs RZ_cf, the post fpostmR at wle' segs RZ_cf), at image B', its
   whole-program listing, preset's CfParams, the room instance prh_room_live_a8, CfImg_B and the allocator relation
   ARcfx, by the text's case split: p = 0 is rb_p0 (plain, no free crossed) lifted to the primed post; p <> 0 is rb_nz
   (lifted inside, at its entry) ==== *)
Theorem fuzz_realloc_holds_B' : tfuzz_realloc_specX (L := B_prog_listing) (PA := PA) B ARcfx SK.
Proof.
unfold tfuzz_realloc_specX.
intros ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own
  HPRE HRL HUNIV HSEC H24 HHB HU0 HU1 H10 H11 Hn0 Hnmax HLED HOLD HLIVE.
destruct (Z.eq_dec p 0) as [-> | Hp0].
- destruct HOLD as [(_ & -> & ->) | (HinL & _ & _)].
  + apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf). eapply SRr_mono.
    { exact (rb_p0 ly S Hp W regs mem md ch n Lam peak cnt fail ran most own
        HPRE HRL HUNIV HSEC H24 HHB H10 H11 Hn0 Hnmax HLED HLIVE). }
    intros W' c' _ HP. apply rb_post_lift. exact HP.
  + (* no harness block has user address 0: its allocator block is at >= 4096 *)
    exfalso. destruct HPRE as ((HAR & _) & _).
    pose proof (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran 0 k most own HLED HinL) as (Hk0 & Hblk & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & Hb4096 & _).
    rewrite rb_cf_head in Hb4096. lia.
- destruct HOLD as [(Hp00 & _) | (HinL & Hold & Hlen)]; [contradiction|].
  assert (Ep0 : (p =? 0) = false) by (apply Z.eqb_neq; exact Hp0).
  (* the budget and the footprint at p <> 0; the post's own `if p =? 0` stays, as tfrP_Q states it *)
  rewrite Ep0 in HHB.
  replace (if p =? 0 then [] else ablocks_fp [(p - cf_head, k + cf_head)])
    with (ablocks_fp [(p - cf_head, k + cf_head)]) by (rewrite Ep0; reflexivity).
  exact (rb_nz ly S Hp W regs mem md ch p k n old Lam peak cnt fail ran most own
    HPRE HRL HSEC H24 HHB HU0 HU1 H10 H11 Hn0 Hnmax HLED Hp0 HinL Hold Hlen HLIVE).
Qed.

End f.
End w.
