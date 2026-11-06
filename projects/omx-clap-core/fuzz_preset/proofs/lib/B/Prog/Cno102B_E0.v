(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): Section allocm takes
   YGcallx's new QMm (the call's conjuncts on the state and the call memory) and QMQ (QMm S mem -> QM S); its eight
   _m rules take `QMm Sc <call memory>` instead of `QM Sc`, and pass QMm / QMQ to YGcallx's rules. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the free _m rules are proved once over the journal's
   world relation R and the callee's call post APOST (aj_free_x_ct_mR / aj_free_at_x_ct_mR; the old _m names are the
   instances at wle and acall_post_x; aj_free_x_mR / aj_free_at_x_mR likewise); every other call rule here with a
   journal takes it at any R, the old names being their wle instances: aj_intrin_at_xmR, aj_poison_at_x_mR and
   aj_poison_x_mR take R alone; aj_intrin_at_xm_frR, aj_bcmp_at_xmR, aj_strcmp_at_xroR, aj_strlen_at_xroR,
   aj_strcmp_at_xromR, aj_strlen_at_xromR, aj_strlen_at_xmR, aj_stack_malloc_at_xmR, aj_set_shadow_at_xmR,
   aj_unpoison_at_x_mR and aj_unpoison_x_mR take R reflexive and transitive, binders first (the stack-malloc form uses
   both to compose the call's own journal into the caller's); the malloc _m rules aj_malloc_x_mR, aj_malloc_x_ct_mR,
   aj_malloc_at_x_mR and aj_malloc_at_x_ct_mR also take wle inside R (YGcallx's malloc R forms); section 12 states the cf
   free forms under the re-hide (aj_free_x_ct_m_rh / aj_free_at_x_ct_m_rh: SRr' segs RZ_cf, the journal at wle' segs
   RZ_cf). *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: memnorm out of every call text): YGcallx.v's leaves
   malloc_leaf_x / free_leaf_x / free_leaf_xA lost their memnorm keep, the conjunct family 4's keep was read from. So
   the eight _m malloc / free rules of section 10, their R forms (_mR) and section 12's two cf free forms (_m_rh) drop
   the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) from their conclusion: each _m / _mR rule is now its
   YGcallx.v original VERBATIM (the _mR forms are proved by it), under its own name for the walks that apply it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallMxmn.v, with its module paths and module names changed; 948 of its 1094 lines of code are new or changed and 2183 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b):
   SEGMENT CB0 Entry of the re-walk of check_no_overread (cno, entry B' 0x819f0 = slot 201 of the whole-program
   listing), from the function's entry to the cut CNB_FRAME (B' 0x81a94, entry + 164). Row R7-4 of
   the internal file FREE-PIECES-102.md (a Theorem Labs lane's CB0; plan, the internal file PLAN-cno-caw-102.md sections 5.0 / 5.2,
   row "CB0 Entry").
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (by path; all at this branch's base, the B' cno segments on the kit's CUT a working branch
   7cdbb61b5fa0, a working branch 0e85941c7687):
     THE CONTRACT lib/B/Prog/Cno102B_Base.v 06098b64f859: cnb_pre CTX0 D (no DW), cnb_set_fpos, cnb_at_frame (cnb_base
     at the spent wild budget 0, cnb_prog D [] S, the progress fact for no event), cnb_J (the budgeted journal),
     cnb_ex_frame, the record cnb_img B (cnbi_entry, cnbi_pst_rw, cnbi_pst_ok), the listing tables PL_cno_B. Nothing
     here re-states the contract.
     LISTING lib/B/Listing_prog.v c97cc46b3e13 (objects numbered
     by symbol: A_OBJ 0 = the GOT word of __asan_shadow_memory_dynamic_address, A_OBJ 1 = the GOT word of
     __asan_option_detect_stack_use_after_return, A_OBJ 12 = __asan_shadow_memory_dynamic_address; the facts are
     YC1fP.v's PALib record). lib/B/PAImg_prog.v is NOT Required: this file is
     PARAMETRIC over {PA : PAImg B_prog_listing} (owner 12:48Z).
     The kit texts at the cut: lib/A/PRH_Base.v ef7c8ca98529 (prh_ledger with g_most / g_own_ran_out as fields, prh_pst,
     kept_at, fpre), lib/A/PRH_FnCheck.v c40cf3fdcd2a
     (tcheck_no_overread_specX, the frame cap ck_FRAMES_CAP / FR_check_no_overread), lib/A/PRH_FnReader.v
     f1ae32e3b2cd (prhReader_home), lib/B/PRH_ImgB.v 3216eca68342 (prh_img_B).
     ENGINE at the cut: YC80x.v (srr_inv_laws), YC1fPx.v 7814b594066f (paj_run_to_x_inv / paj_run_x_inv and their
     tactics), YSRrMemnorm.v (srr_inv_call), YGcallMxmn.v 3c08bbab8292 (astack_malloc_realizes_xm, the frame-area
     text with the memnorm keep; aj_stack_malloc_at_xm, whose proof cnb0_sm_at below copies with the text's own view
     keep as a conclusion conjunct), YCbqG.v 219748197d6b (ajournal_x = ajournal_xw at the empty budget, read through
     the ajx_* projections; AR_laws_x; wild_part_same), YCbqGwild.v 0c63874858e4 (wbudget), YGcallx.v fffbc375ffac
     (call_effect_journal_x at a budget), YGcallcf.v / YG0lawscf.v (the ARcfx laws), YG0sshcf.v
     (AR_shadow_law_ok_cf), YGcallScf.v (stack_malloc_x_any, xs_placed_cf_set_fs), lib/A/Prog/S1Ledger.v
     (8cf15eeb6311: prh_ledger_kept_aview), lib/A/Prog/PRW_StepKit.v 0df3991c13f4.
     PORTED BY PATH (image-free, the numbers not carried): a working branch 4ab1ca20acf7
     lib/A/Prog/Ent102L0A.v (blob 8dc69284befb: l0_land_m32 / l0_and_m32 / l0_land_neg32 / l0_val_mem_of_rd32 /
     l0_chunk8 / l0_chunk4 / l0_val_mem_agree / l0_aview_kept and the shape of seg_L0a_A: the prologue, the two GOT
     loads, the flag, the frame call); lib/B/Prog/FuzzStrdupB.v at the base (sd_req / sd_hull_sub / sd_hull_img /
     sd_garr8_move / the shadow cases of sd_src_shadow); lib/Reusable/YCem.v rdword_of_val_mem;
     a working branch 91c2bea0273 lib/B/Prog/Cno102B_F.v cnob_arodata_J.
   THE SEGMENT (DERIVED byte offsets inside check_no_overread, pinned by cnb0_slots on the listing of record):
       0 `addi sp, sp, -0xa0`, `sd zero, 0(sp)`, the thirteen saves ra .. s11 at sp0 - 8 .. sp0 - 104, `addi s0, sp,
         0xa0`, `andi sp, sp, -0x20`, `mv s1, sp`, `mv s7, a1`, the hi pair and the two GOT loads (a2 = [A_OBJ 1],
         a1 = [A_OBJ 0])                                                       stretch 1, to CNB0_UAR
      92 `lw a2, 0(a2)`: the use-after-return option, 1 (AR_laws_x alx_const)   stretch 2, to CNB0_SB
      96 `ld s2, 0(a1)` (s2 = the shadow base), `mv s8, a0`, `beqz a2` NOT taken (a2 = 1), `li a0, 0x140`
     112 `jal __asan_stack_malloc_3`: THE CAPACITY RULE - the frame-area text astack_malloc_realizes_cf of class 3
         with the memnorm keep (YGcallMxmn's astack_malloc_realizes_xm at ARcf, lifted to ARcfx), its premise
         `count_cid 3 (frames S) < fs_frames 3` discharged at the function's own entry state (cnb_pre's frame cap:
         at most ck_FRAMES_CAP - FR_check_no_overread live frames, far below fs_frames 3), the call's S the entry's
         by the journal (own = [] before the call). It returns F = frame_addr ly 3 pos, 4096 <= F (ARx_sep_law).
     116 `mv s11, a0`, `j +8`, `mv s3, s11`, `bnez s11` TAKEN (F <> 0)           stretch 4, to CNB_FRAME
     REFUTED: the flag-0 arm 124 (`mv s11, zero`: the beqz at 104 is not taken, alx_const reads 1) and the real-stack
     fallback 136 .. 160 (`addi a0, sp, -0x140` .. the page-probe loop `sd zero, 0(sp)` / `blt s3, sp` .. `mv sp,
     s3`: the bnez at 132 is taken since F >= 4096). Both are decided by the symbolic engine from the facts the seats
     carry (atom 12 = 1 at 104, atom 10 in [4096, 2 ^ 47] at 132); the four runs stop only at CNB0_UAR, CNB0_SB, the
     call and CNB_FRAME.
   THE FORM (the internal file lane-102.md :29-31; the contract's :639-643): FORWARD, generic P. The segment crosses one RUNTIME call
   (__asan_stack_malloc_3, not a kit text): its rule gives P's carrier only as the memnorm keep implication (no rule
   has more: YGcallMxmn.v header), so P crosses it by srr_inv_call; srr_inv_laws alone does NOT suffice here.
   THE CUT (re-fit from the f97c contract b5421fc37cbc to the cut's 06098b64f859): cnb_pre takes no DW, so the
   Section variable DW and its argument are gone (the one premise change; the named arguments below are unchanged);
   cnb_pre's conjuncts are picked BY THEIR TYPE (cnb0_pick, CB9's cnb9_pick), never by position; every journal is
   read through YCbqG's ajx_* projections. THE WILD BUDGET: the exit's journal is cnb_J D 0 at WS = [] (wbudget [] 0
   [] by computation). The entry journal is ajournal_x_init's (the empty budget), the four runs keep it, and the one
   call (__asan_stack_malloc_3, a FIXED-trace runtime row) is composed at the empty budget (ajournal_x_sub; the call
   journal keeps the depot, set_fs: wild_part_same), so this segment spends no wild budget.
   NAMED ARGUMENTS (each ONE Section hypothesis; none is a stand-in lemma):
     PAL   - YC1fP.PALib B, the image binding of the runtime's cells at the whole-program listing (proved at PI_prog_B).
     IMG   - the contract's record cnb_img B (cnbi_entry; cnbi_pst_rw for arodata_okP; cnbi_pst_ok carries the
             ledger's statics, g_most and g_own_ran_out across the frame call, whose rule keeps exactly the bytes the
             runtime owns neither before nor after).
     SM3   - the listing's __asan_stack_malloc_3 is the code record's class-3 entry (the class-1 twin is Ent102CutsA's
             ei_sm1 / Rtt102EA's pal_stack_malloc1): pc_stack_malloc (as_code B) 3 = pa_sigma AS___asan_stack_malloc_3.
     ASM3  - the capacity rule's text: YGcallMxmn.astack_malloc_realizes_xm at ARcf, class 3 (astack_malloc_realizes_cf
             plus the memnorm keep; YGcallMxmn.astack_malloc_realizes_xm_forget gives astack_malloc_realizes_cf back).
     ISV   - cnb0_img_shadow_vis, THE B' RANGE FACT: the shadow of every byte of the image band [pa_lo, pa_hi) is
             present at every ARcf state (= YImgShadowCoverCf.img_shadow_vis_cf_at SEGS B pa_lo pa_hi by conversion;
             RE-FIT to the kit Batch 2: kept_at bounds a kept global by pa_lo / pa_hi, at the cut PRH_Base.v ef7c8ca98529
             :1723 / :1746,
             not by YImgTop's IMG_LO / IMG_TOP, so the fact is stated over the same band; at the instance, the cover
             check of B''s generated lists, YImgShadowCoverCf.img_shadow_vis_cf_at_of_cover).
             Used ONLY by cnb0_img_hull, the one step that needs it: the shadow hull of an input that is a read-only
             image global (kept_at's in_zs / kept_img arms) after the frame call.
   Numerals: offsets 0 / 92 / 96 / 112 / 116 / 164 (DERIVED, 4 * slot); 160 (LENGTH: the frame), 32 (LENGTH: the
   realignment), 8 / 4 (LENGTH: word widths), 13 saved words at 8 .. 104 below sp0 (LENGTH); 3 (the frame class);
   4096 (DERIVED: ESTACK); 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (DERIVED: stack bounds and word width); atom and register
   numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf YG0sshcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre FCiface YGcallx YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfRoomKeep YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off; the realignment and shadow arithmetic here
   needs it on (Cno102A_Ro.v's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.

(* ---- this segment's stops: DERIVED byte offsets inside check_no_overread ---- *)
Definition CNB0_UAR : Z := 92.
Definition CNB0_SB : Z := 96.
Definition CNB0_RET : Z := 116.
(* LENGTH: the prologue's frame (`addi sp, sp, -0xa0`) *)
Definition CNB0_SAVE : Z := 160.

(* THE SLOT CHECK on the listing of record: the 42 slots of the segment (offsets 0 .. 164) *)
Lemma cnb0_slots :
  map (fun k => nth_error B_prog_listing (CNB_SLOT + k))
    [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
     29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41]%nat =
  [Some (PW 0xf6010113); Some (PW 0x13023); Some (PW 0x8113c23); Some (PW 0x8813823); Some (PW 0x8913423);
   Some (PW 0x9213023); Some (PW 0x7313c23); Some (PW 0x7413823); Some (PW 0x7513423); Some (PW 0x7613023);
   Some (PW 0x5713c23); Some (PW 0x5813823); Some (PW 0x5913423); Some (PW 0x5a13023); Some (PW 0x3b13c23);
   Some (PW 0xa010413); Some (PW 0xfe017113); Some (PW 0x10493); Some (PW 0x58b93);
   Some (PHi (11%bv : bv 5) 5); Some (PHi (12%bv : bv 5) 6);
   Some (PLdHi (12%bv : bv 5) (12%bv : bv 5) 6 (A_OBJ 1) 0x0 SZ8 true);
   Some (PLdHi (11%bv : bv 5) (11%bv : bv 5) 5 (A_OBJ 0) 0x0 SZ8 true);
   Some (PW 0x62603); Some (PW 0x5b903); Some (PW 0x50c13); Some (PW 0x60a63); Some (PW 0x14000513);
   Some (PCall AS___asan_stack_malloc_3 (1%bv : bv 5));
   Some (PW 0x50d93); Some (PW 0x80006f); Some (PW 0xd93); Some (PW 0xd8993); Some (PW 0x20d9063);
   Some (PW 0xec010513); Some (PW 0xfe057993); Some (PW 0x1537); Some (PW 0x40a10133); Some (PW 0x13023);
   Some (PW 0xfe29cce3); Some (PW 0x98113); Some (PW 0x334b823)].
Proof. vm_compute. reflexivity. Qed.

(* ==== IMAGE-FREE HELPERS ==== *)
(* Ent102L0A.v l0_land_m32 / l0_and_m32 / l0_land_neg32 (by path) *)
Lemma cnb0_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x / 32 * 32.
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.shiftl (Z.ones 59) 5) by (vm_compute; reflexivity).
assert (E2 : x / 32 * 32 = Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
rewrite E1, E2. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i 5) as [H5|H5].
- rewrite !(Z.testbit_neg_r _ (i - 5)) by lia. apply Bool.andb_false_r.
- rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia.
  destruct (Z.lt_ge_cases (i - 5) 59) as [H59|H59].
  + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
  + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r.
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. symmetry. apply Z.mod_pow2_bits_high. lia.
Qed.
Lemma cnb0_land_neg32 : forall x, 0 <= x -> Z.land x (-32) = x / 32 * 32.
Proof.
intros x Hx.
assert (E2 : x / 32 * 32 = Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
assert (E1 : (-32) = Z.lnot (Z.ones 5)) by (vm_compute; reflexivity).
rewrite E1, E2. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.shiftl_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 5) as [H5|H5].
- rewrite (Z.testbit_neg_r _ (i - 5)) by lia. rewrite Z.ones_spec_low by lia. apply Bool.andb_false_r.
- rewrite Z.ones_spec_high by lia. rewrite Bool.andb_true_r.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.
(* the engine's word for `addi sp, sp, -160; andi sp, sp, -32` (Rtt102EA.v re_R_word's form) *)
Lemma cnb0_S1_word : forall (regs : bvmap 5 word), CNB0_SAVE <= spZ regs ->
  alu64 ALU_AND (Z_to_bv 64 (bv_unsigned (getr regs 2) + - CNB0_SAVE)) (Z_to_bv 64 (-32)) =
  w64 (Z.land (spZ regs - CNB0_SAVE) (-32)).
Proof.
intros regs H160. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr.
change (bv_modulus 64) with (2 ^ 64) in Hr. change (bv_unsigned (getr regs 2)) with (spZ regs) in *.
apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
unfold CNB0_SAVE in *.
rewrite (Z.mod_small (spZ regs + - 160)) by lia. change ((-32) mod 2 ^ 64) with (2 ^ 64 - 32).
rewrite cnb0_land_m32 by lia. rewrite cnb0_land_neg32 by lia.
pose proof (Z.mul_div_le (spZ regs - 160) 32 ltac:(lia)).
pose proof (Z.div_pos (spZ regs - 160) 32 ltac:(lia) ltac:(lia)).
replace (spZ regs + - 160) with (spZ regs - 160) by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma cnb0_add0_word : forall w : word, alu64 ALU_ADD w (Z_to_bv 64 0) = w.
Proof.
intros w. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_0_l by lia. rewrite Z.add_0_r.
apply Z.mod_small. exact (bv_unsigned_in_range 64 w).
Qed.
(* the realigned base: 32-aligned, at most 191 bytes below the entry sp minus 160 *)
Lemma cnb0_S1_range : forall sp0, sp0 mod 16 = 0 -> 192 <= sp0 ->
  sp0 - 192 < Z.land (sp0 - CNB0_SAVE) (-32) <= sp0 - CNB0_SAVE /\ Z.land (sp0 - CNB0_SAVE) (-32) mod 32 = 0.
Proof.
intros sp0 Hal H. unfold CNB0_SAVE. rewrite cnb0_land_neg32 by lia.
pose proof (Z.mul_div_le (sp0 - 160) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)).
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)).
split; [lia | apply Z.mod_mul; lia].
Qed.
(* a class count is at most the list's length *)
Lemma cnb0_count_le : forall c l, count_cid c l <= Z.of_nat (length l).
Proof.
intros c l. induction l as [|[c' p] t IH]; cbn [count_cid length]; [lia|].
destruct (c' =? c); lia.
Qed.
Lemma cnb0_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma cnb0_req_ge : forall z, z <= req_size z.
Proof. intros z. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma cnb0_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
destruct Ha as [p ->]. destruct Hb as [q ->]. replace (p * 32 - q * 16) with ((2 * p - q) * 16) by lia.
apply Z.mod_mul. lia.
Qed.
(* FuzzStrdupB.v sd_hull_sub / sd_hull_img (by path) *)
Lemma cnb0_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma cnb0_hull_img : forall L H a n s, 0 < n -> L + 64 <= a -> a + n + 64 <= H ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ L <= 8 * (s - SHADOW_OFF) < H.
Proof.
intros L H a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
(* a byte the restricted memory agrees on keeps its presence *)
Lemma cnb0_apresent_keep : forall (H : word -> bool) (m m' : word -> option byte) a,
  mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a E [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in E. rewrite Hh in E.
rewrite E. exact Hb.
Qed.

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* Ent102L0A.v l0_val_mem_of_rd32 / l0_val_mem_agree / l0_aview_kept (by path); YCem.v rdword_of_val_mem *)
Lemma cnb0_val_mem_of_rd32 : forall H mem a v,
  rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hr; [|discriminate Hr].
injection Hr as Hb. f_equal. cbv [YO0f.le_byte YG0f.le_byte] in *. rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cnb0_val_mem_agree : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hag Hv k Hk. pose proof (Hv k Hk) as Hk'.
specialize (Hag (Z.of_nat k) ltac:(lia)). unfold aview in Hag. rewrite Hk' in Hag.
destruct (mbyte segs (mrestrict H' m') (a + Z.of_nat k)) as [b|] eqn:Eb;
cbn [option_map] in Hag; [|discriminate Hag].
injection Hag as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma cnb0_aview_kept : forall (H : word -> bool) E rs (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview segs H m' a = aview segs H m a.
Proof.
intros H E rs m m' a HFr Ha Hw. unfold aview, mbyte.
rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_small by lia. exact Hw.
Qed.
Lemma cnb0_present_kept : forall (H : word -> bool) E rs (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> apresent H m a -> apresent H m' a.
Proof.
intros H E rs m m' a HFr Ha Hw. apply cnb0_apresent_keep. apply HFr.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_small by lia. exact Hw.
Qed.
Lemma cnb0_rdword_of_val_mem : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. cbv [YO0f.le_byte YG0f.le_byte].
  apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
(* FuzzStrdupB.v sd_garr8_move (by path) *)
Lemma cnb0_garr8_move : forall (H H' : word -> bool) m m' x l, garr8 segs (mrestrict H m) x l ->
  (forall j, (j < length l)%nat -> aview segs H' m' (x + Z.of_nat j) = aview segs H m (x + Z.of_nat j)) ->
  garr8 segs (mrestrict H' m') x l.
Proof.
intros H H' m m' x l Hg HA j Hj. destruct (Hg j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte segs (mrestrict H' m') (x + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
(* Ent102L0A.v l0_chunk8 / l0_chunk4 (by path) *)
Lemma cnb0_chunk8 : forall (E : env) (m : word -> option byte) (e : sv) (base v : Z),
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem segs m base 8 v ->
  YP09.chunk_ok segs E m base (YP09.mkChunk 0 (CVal 8 e)).
Proof.
intros E m e base v He Hv Hm.
apply (YI04.chunk_ok_val segs E m base 0 8 e v He).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- change (Z.of_N 8) with 8. lia.
- change (N.to_nat 8) with 8%nat. replace (base + 0) with base by lia. exact Hm.
Qed.
Lemma cnb0_chunk4 : forall (E : env) (m : word -> option byte) (e : sv) (base v : Z),
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> val_mem segs m base 4 v ->
  YP09.chunk_ok segs E m base (YP09.mkChunk 0 (CVal 4 e)).
Proof.
intros E m e base v He Hv Hm.
apply (YI04.chunk_ok_val segs E m base 0 4 e v He).
- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
- change (Z.of_N 4) with 4. lia.
- change (N.to_nat 4) with 4%nat. replace (base + 0) with base by lia. exact Hm.
Qed.
(* a saved word of the prologue, as a value of the symbolic memory's chunk *)
Lemma cnb0_saved_chunk : forall (EV : env) (H : word -> bool) (mm : word -> option byte) base off (n : nat),
  YP09.chunk_ok segs EV (mrestrict H mm) base (YP09.mkChunk off (CVal 8 (SOff n 0))) ->
  val_mem segs (mrestrict H mm) (base + off) 8 (bv_unsigned (ew EV n)).
Proof.
intros EV H mm base off n HC.
assert (Hd : sv_denot EV (SOff n 0) = Z_to_bv 64 (bv_unsigned (ew EV n)))
  by (cbn; rewrite Z.add_0_r; reflexivity).
pose proof (bv_unsigned_in_range 64 (ew EV n)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
pose proof (val_of_chunk_ok segs EV (mrestrict H mm) base off 8 (SOff n 0) (bv_unsigned (ew EV n)) HC Hd
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as HV.
change (N.to_nat 8) with 8%nat in HV. exact HV.
Qed.
(* a stretch with no write window leaves every byte of the view and every present byte *)
Lemma cnb0_aview_nowin : forall (H : word -> bool) E rs (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros H E rs m m' HFr Hn a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a) (Hn _)). reflexivity. Qed.
Lemma cnb0_present_nowin : forall (H : word -> bool) E rs (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
  forall a, apresent H m a -> apresent H m' a.
Proof. intros H E rs m m' HFr Hn a. apply cnb0_apresent_keep. exact (HFr (Z_to_bv 64 a) (Hn _)). Qed.
(* a word of the view at bytes the view agrees on *)
Lemma cnb0_rdword_kept : forall (rd rd' : reader) x,
  (forall i, 0 <= i < 8 -> rd' (x + i) = rd (x + i)) -> rdword rd' x = rdword rd x.
Proof.
intros rd rd' x Hk. unfold rdword.
assert (E0 : rd' x = rd x) by (rewrite <- (Z.add_0_r x); apply Hk; lia).
rewrite E0, (Hk 1), (Hk 2), (Hk 3), (Hk 4), (Hk 5), (Hk 6), (Hk 7) by lia. reflexivity.
Qed.
End mem.

(* ==== THE FRAME CALL WITH ITS VIEW KEEP: YGcallMxmn.v 3c08bbab8292 aj_stack_malloc_at_xm (:629-693), statement
   and proof copied (the journal read through ajx_*, call_effect_journal_x at the empty budget WS = []), with one more
   conclusion conjunct: the text's own view keep (astack_malloc_realizes_xm's
   `~ aowned .. -> ~ aowned .. -> ~ window -> aview' a = aview a`, which the engine's rule folds into acall_kept_x).
   The frame call keeps the ledger's statics by it (they are owned by the runtime neither before nor after), with no
   errno fact. The conjuncts this segment does not read (st_nev, zero_shadow, the frame's presence, acall_kept_x, the
   call journal) are dropped. ==== *)
Section smr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Local Abbreviation code := (as_code B).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).

Lemma cnb0_sm_at : forall cid, YGcallMxmn.astack_malloc_realizes_xm segs B ARx cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own) lyc S2 Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
blocks_bytes S2 = blocks_bytes Sc /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
   aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(exists f, S2 = set_fs f Sc) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros cid ASM Hcid W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk. pose proof (ajx_hi HJ) as F1. pose proof (ajx_blk HJ) as F2.
pose proof (ajx_img HJ) as F3. pose proof (ajx_frm HJ) as F4. pose proof (ajx_gone HJ) as Hgone.
pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstatic. pose proof (ajx_extra HJ) as F5.
pose proof (ajx_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
destruct (SMX lyc Sc Hpc W memT mdc cid HAR Hcid Hcnt) as (pos & S2 & Hpath & (f & ES2) & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc Hpc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2 & Hmn).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal_x segs B [] ARx ESTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [(cid, pos)] lyc S2 Hpc W mem2 md2 0).
{ eapply (call_effect_journal_x segs B ARx LAWS segs_low errno_low OWNLOW ESTACK lyc Sc Hpc W regsT memT mdc lyc S2 Hpc W
    mem2 md2 (fun _ => False) [] [(cid, pos)] 0 []);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR
  | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | | ].
  - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p n i Hp0 Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp0.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
  - rewrite ES2. apply wild_part_same. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
  eapply (ajournal_x_sub segs B PST ARx LAWS segs_low);
  [exact HJ | exact (ajournal_x_nil_pst segs B ARx PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hbb|]. split; [exact Hflag|].
split; [intros a H0 H1 H2 H3; apply (Hfr a H0 H1 H2); rewrite Hsp'; exact H3|].
split; [exists f; exact ES2 | exact Hmn].
Qed.
End smr.

(* ==== THE SYMBOLIC SEATS (closed literals, no image number) ==== *)
(* stretch 1: the 160-byte frame below the entry sp (atom 2, written), the two GOT words (read; the UAR GOT word holds
   the option cell's address, the extra atom 32) *)
Definition cnb0_r_gotu : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition cnb0_rs0 : smem := [stack_region CNB0_SAVE; got_regionP; cnb0_r_gotu].
Definition cnb0_G0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition cnb0_ss0 : sstate := mkSS CNB_OFF sr_atoms cnb0_rs0 None cnb0_G0.
(* stretch 2: the option cell (a2 = atom 12) holds 1 *)
Definition cnb0_r_uar : YP09.region :=
  YP09.mkRegion (Some 12%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition cnb0_ss1 : sstate := mkSS (CNB_OFF + CNB0_UAR) sr_atoms [cnb0_r_uar] None (mkFacts [] [] []).
(* stretch 3: the shadow-base cell (a1 = atom 11), the option a2 = 1 *)
Definition cnb0_r_sb : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit SHADOW_OFF))].
Definition cnb0_ss2 : sstate :=
  mkSS (CNB_OFF + CNB0_SB) sr_atoms [cnb0_r_sb] None (mkFacts [(12%nat, mkAF 1 1 0)] [] []).
(* stretch 4: a0 = F, 32-aligned in [4096, 2 ^ 47] *)
Definition cnb0_ss3 : sstate :=
  mkSS (CNB_OFF + CNB0_RET) sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 5)] [] []).

(* ==== THE IMAGE B' WALK CONTEXT (as Cno102B_F.v): preset's CfParams, the room invariant of record, PrhImg
   prh_img_B, the contract's listing tables; the PAImg instance is a PARAMETER ==== *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Instance CF_cp : CfParams := CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Instance CF_RL : PrhRoomLive := prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Instance CF_PL : PAListing B_prog_listing := PL_cno_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* the walk's allocator relation, the cf instance (S1KitAlloc's ARxs, YGcallcf.v; Cno102B_F.v :181) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Variable SK : YI16.sink_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
Variables (CTX0 : list (list Z)).
(* ---- THE NAMED ARGUMENTS (header) ---- *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PA) B.
Hypothesis IMG : cnb_img (PA := PA) B.
Hypothesis SM3 : pc_stack_malloc (as_code B) CNB_CID = SIGMA AS___asan_stack_malloc_3.
Hypothesis ASM3 : forall fz : YK11.FPState,
  YGcallMxmn.astack_malloc_realizes_xm (fx := fz) SEGS B (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md) CNB_CID.
Definition cnb0_img_shadow_vis : Prop :=
  forall ly S Hp (W : world SEGS) mem md a, ARcf SEGS B ly S Hp W mem md ->
  @pa_lo _ _ PA <= a < @pa_hi _ _ PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis ISV : cnb0_img_shadow_vis.

Let LAWS_cf : AR_laws_cf SEGS B := AR_laws_ok_cf SEGS B.
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B LAWS_cf.
Let OWNLOW : ARx_owned_low_law SEGS B ARcfx := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let SMXx : forall ly S Hp W mem md cid, ARcfx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S) :=
  fun ly S Hp W mem md cid HAR Hc Hn => stack_malloc_x_any SEGS ARcfx ly S Hp W mem md cid HAR Hc Hn.
Let ASMx : YGcallMxmn.astack_malloc_realizes_xm SEGS B ARcfx CNB_CID :=
  YGcallMxmn.astack_malloc_realizes_xm_conj SEGS B (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md)
    xs_placed_cf CNB_CID xs_placed_cf_set_fs (ASM3 fx).

Lemma cnb0_stk_ge : 4096 + 256 <= STK.
Proof. vm_compute. discriminate. Qed.
Lemma cnb0_off_val : CNB_OFF = 804.
Proof. reflexivity. Qed.
Lemma cnb0_fsb : fs_frame_bytes CNB_CID = 512.
Proof. vm_compute. reflexivity. Qed.

(* ---- what ARcfx gives about the runtime's four cells (Ent102L0A.v l0_syms / l0_cells / l0_const) ---- *)
Lemma cnb0_cells : forall ly S Hp W mem md, ARcfx ly S Hp W mem md ->
  (4096 <= as_shadow_cell B /\ as_shadow_cell B + 8 <= kImgEnd) /\
  (4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kImgEnd) /\
  (4096 <= as_got_shadow B /\ as_got_shadow B + 8 <= kImgEnd) /\
  (4096 <= as_got_uar B /\ as_got_uar B + 8 <= kImgEnd).
Proof.
intros ly S Hp W mem md [HAR _]. pose proof (amc_syms _ _ _ _ _ (proj1 HAR)) as SY.
pose proof (asyms_area_bound B (as_shadow_cell B, 8) SY ltac:(cbn; tauto)) as X1.
pose proof (asyms_area_bound B (as_uar_cell B, 4) SY ltac:(cbn; tauto)) as X2.
pose proof (asyms_area_bound B (as_got_shadow B, 8) SY ltac:(cbn; tauto)) as X3.
pose proof (asyms_area_bound B (as_got_uar B, 8) SY ltac:(cbn; tauto)) as X4.
cbn [fst snd] in X1, X2, X3, X4. tauto.
Qed.

(* ---- the entry seat ---- *)
Definition cnb0_E0 (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 (as_uar_cell B)]).
Definition cnb0_E (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).
Lemma cnb0_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (@Eimg _ B_prog_listing PA (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (u5_range r) as Hu.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hn).
Qed.
(* a register a stretch set from another register (`mv`) or left alone *)
Lemma cnb0_reg_at : forall (H : word -> bool) ss ms regs extra (r : bv 5) n (r' : bv 5),
  st_ok_pi SEGS VAL (@Eimg _ B_prog_listing PA (Ereg regs extra)) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros H ss ms regs extra r n r' HS Hsr Hn.
rewrite (st_ok_pi_restrict_reg (PI := PA) H _ ss ms r HS), Hsr. cbn [sv_denot].
rewrite (cnb0_E_reg regs extra n r' Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
(* a register a stretch set from an atom of its environment *)
Lemma cnb0_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hsr. rewrite (st_ok_pi_restrict_reg (PI := PA) H _ ss ms r HS), Hsr. cbn [sv_denot].
rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
(* the realigned sp of stretch 1 (`addi sp, sp, -160; andi sp, sp, -32`) and its copy `mv s1, sp` *)
Lemma cnb0_reg_S1 : forall (H : word -> bool) ss ms regs extra (r : bv 5),
  st_ok_pi SEGS VAL (@Eimg _ B_prog_listing PA (Ereg regs extra)) ss (restrict H ms) ->
  (sr_get (ss_regs ss) r = SAlu ALU_AND (SOff 2 (- CNB0_SAVE)) (SLit (-32)) \/
   sr_get (ss_regs ss) r = SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (- CNB0_SAVE)) (SLit (-32))) (SLit 0)) ->
  CNB0_SAVE <= spZ regs ->
  getr (ms_regs ms) r = w64 (Z.land (spZ regs - CNB0_SAVE) (-32)).
Proof.
intros H ss ms regs extra r HS Hsr H160.
rewrite (st_ok_pi_restrict_reg (PI := PA) H _ ss ms r HS).
destruct Hsr as [Hsr | Hsr]; rewrite Hsr; cbn [sv_denot];
  rewrite (cnb0_E_reg regs extra 2 2%bv eq_refl); [|rewrite cnb0_add0_word]; exact (cnb0_S1_word regs H160).
Qed.
(* the same at a call state (the runner's st_ok form after a PCall) *)
Lemma cnb0_reg_at_s : forall (H : word -> bool) ss ms regs extra (r : bv 5) n (r' : bv 5),
  st_ok SEGS (@Eimg _ B_prog_listing PA (Ereg regs extra)) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros H ss ms regs extra r n r' HS Hsr Hn.
rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hsr. cbn [sv_denot].
rewrite (cnb0_E_reg regs extra n r' Hn), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma cnb0_reg_lit_s : forall (H : word -> bool) E ss ms (r : bv 5) z,
  st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof.
intros H E ss ms r z HS Hsr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hsr. reflexivity.
Qed.
(* a register a stretch set to a constant *)
Lemma cnb0_reg_lit : forall (H : word -> bool) E ss ms (r : bv 5) z,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof.
intros H E ss ms r z HS Hsr. rewrite (st_ok_pi_restrict_reg (PI := PA) H _ ss ms r HS), Hsr. reflexivity.
Qed.

Lemma cnb0_entry0 : forall ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARcfx STK ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (cnb0_E0 regs) cnb0_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CNB_OFF)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit SHADOW_OFF) [] (cnb0_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cnb0_stk_ge as HSTK.
destruct (alx_const SEGS B ARcfx LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
destruct (cnb0_cells ly S Hp W mem md HAR) as ((D1 & D2) & (D3 & D4) & (D5 & D6) & (D7 & D8)).
rewrite (pal_got_shadow B PAL) in Kgot, D5, D6.
rewrite (pal_cell B PAL) in Kgot, Kcell, D1, D2.
rewrite (pal_got_uar B PAL) in Kguar, D7, D8.
pose proof (pal_got_uar_disj B PAL) as (Hdisj01 & Hdisj112).
pose proof (pal_got_cell B PAL) as Hdisj012.
rewrite restrict_mkst_fx.
set (E := cnb0_E0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cnb0_E0; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; unfold cnb0_E0; exact (cnb0_E_reg regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B))
  by (subst E; unfold cnb0_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply HEI; unfold A_TEXT, A_OBJ, A_LIM; lia).
unfold kImgEnd in *.
assert (R12 : 0 <= VAL (A_OBJ 12) < 2 ^ 64) by lia.
assert (RU : 0 <= as_uar_cell B < 2 ^ 64) by lia.
split.
- unfold cnb0_ss0. apply pa_entry_st_ok_full.
  + subst E. unfold cnb0_E0. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cnb0_rs0, stack_region, got_regionP, cnb0_r_gotu.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [unfold CNB0_SAVE; lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. unfold CNB0_SAVE in Hq. lia.
    * rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (cnb0_chunk8 SEGS E _ (SOff (A_OBJ 12) 0) (VAL (A_OBJ 0)) (VAL (A_OBJ 12)));
      [ cbn [sv_denot]; rewrite Z.add_0_r; apply bv_eq; rewrite U12, Z_to_bv_unsigned;
        unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); rewrite Z.mod_small by lia; reflexivity
      | exact R12
      | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot) ].
    * rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (cnb0_chunk8 SEGS E _ (SOff 32 0) (VAL (A_OBJ 1)) (as_uar_cell B));
      [ cbn [sv_denot]; rewrite Z.add_0_r, E32; apply Z_to_bv_bv_unsigned
      | exact RU
      | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar) ].
  + apply pairwise_disjoint_of_extents.
    unfold cnb0_rs0, stack_region, got_regionP, cnb0_r_gotu, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U0, U1.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold CNB0_SAVE. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok cnb0_G0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- the seats of stretches 2 - 4 (Ent102L0A.v's HS1 / HS2 blocks; the fourth has no region) ---- *)
Lemma cnb0_seat1 : forall (W : world SEGS) regs mem,
  getr regs 12 = Z_to_bv 64 (as_uar_cell B) -> 4096 <= as_uar_cell B -> as_uar_cell B + 4 <= kImgEnd ->
  val_mem SEGS (mrestrict (w_H W) mem) (as_uar_cell B) 4 1 ->
  st_ok_pi SEGS VAL (cnb0_E regs) cnb0_ss1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (CNB_OFF + CNB0_UAR))) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit SHADOW_OFF) [] (cnb0_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem R12 Hlo Hhi HU. unfold kImgEnd in Hhi.
assert (U12 : bv_unsigned (ew (cnb0_E regs) 12) = as_uar_cell B).
{ unfold cnb0_E. rewrite (cnb0_E_reg regs [] 12 12%bv eq_refl), R12. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold cnb0_ss1. apply pa_entry_st_ok_full.
- unfold cnb0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cnb0_r_uar.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (cnb0_chunk4 SEGS _ _ (SLit 1) (as_uar_cell B) 1); [vm_compute; reflexivity | lia | exact HU].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I|]. split; exact I.
Qed.
Lemma cnb0_seat2 : forall (W : world SEGS) regs mem,
  getr regs 11 = Z_to_bv 64 (as_shadow_cell B) -> getr regs 12 = Z_to_bv 64 1 ->
  4096 <= as_shadow_cell B -> as_shadow_cell B + 8 <= kImgEnd ->
  val_mem SEGS (mrestrict (w_H W) mem) (as_shadow_cell B) 8 SHADOW_OFF ->
  st_ok_pi SEGS VAL (cnb0_E regs) cnb0_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (CNB_OFF + CNB0_SB))) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit SHADOW_OFF) [] (cnb0_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem R11 R12 Hlo Hhi HSB. unfold kImgEnd in Hhi.
assert (U11 : bv_unsigned (ew (cnb0_E regs) 11) = as_shadow_cell B).
{ unfold cnb0_E. rewrite (cnb0_E_reg regs [] 11 11%bv eq_refl), R11. apply unsigned_lit_small. lia. }
assert (U12 : bv_unsigned (ew (cnb0_E regs) 12) = 1).
{ unfold cnb0_E. rewrite (cnb0_E_reg regs [] 12 12%bv eq_refl), R12. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold cnb0_ss2. apply pa_entry_st_ok_full.
- unfold cnb0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cnb0_r_sb.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U11.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (cnb0_chunk8 SEGS _ _ (SLit SHADOW_OFF) (as_shadow_cell B) SHADOW_OFF);
  [vm_compute; reflexivity | unfold SHADOW_OFF; lia | exact HSB].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U12. split; [lia|]. split; [reflexivity | lia].
Qed.
Lemma cnb0_seat3 : forall (W : world SEGS) regs mem F,
  getr regs 10 = w64 F -> 4096 <= F <= 2 ^ 47 -> F mod 32 = 0 ->
  st_ok_pi SEGS VAL (cnb0_E regs) cnb0_ss3
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (CNB_OFF + CNB0_RET))) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SLit SHADOW_OFF) [] (cnb0_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem F R10 HF HF32.
assert (U10 : bv_unsigned (ew (cnb0_E regs) 10) = F).
{ unfold cnb0_E. rewrite (cnb0_E_reg regs [] 10 10%bv eq_refl), R10. unfold w64. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold cnb0_ss3. apply pa_entry_st_ok_full.
- unfold cnb0_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10. change (2 ^ 5) with 32. split; [lia|]. split; [exact HF32 | lia].
Qed.
(* the input's home at a state with the same blocks *)
Lemma cnb0_home_eq : forall ly S Hp ly' S' Lam p n,
  PRH_FnReader.prhReader_home B ly S Hp Lam p n -> ablocks B ly' S' = ablocks B ly S ->
  PRH_FnReader.prhReader_home B ly' S' Hp Lam p n.
Proof.
intros ly S Hp ly' S' Lam p n [H | (b & m & Hin & Hn & Hb & Hm)] E; [left; exact H|].
right. exists b, m. rewrite E. split; [exact Hin|]. split; [exact Hn|]. split; [exact Hb | exact Hm].
Qed.

(* ---- THE PST KEEP: the one place the contract's cnbi_pst_ok enters. A program static is no byte the
   runtime owns, at any ARx state (AR_laws_x field alx_owned_image: on image bytes, owned = an owned static) ---- *)
Lemma cnb0_pst_unowned : forall ly S Hp W mem md a, ARcfx ly S Hp W mem md -> Exists (in_zr a) prh_pst ->
  ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Ha Hown. destruct ((cnbi_pst_ok B IMG) a Ha) as (Him & Hno).
apply Hno. exact (proj1 (alx_owned_image SEGS B ARcfx LAWS ly S Hp W mem md a HAR Him) Hown).
Qed.
(* the statics lie below the allocator ceiling (prh_img_B's generated addresses; Caw102B_WB0.v caw_pst_low) *)
Lemma cnb0_pst_low : forall a, Exists (in_zr a) prh_pst -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.

(* ---- THE IMAGE HULL: the one step that needs THE B' RANGE FACT cnb0_img_shadow_vis (ISV). The shadow hull of a
   range 64 bytes inside the image band [pa_lo, pa_hi) (kept_at's bounds, PRH_Base.v ef7c8ca98529 :1723 / :1746) is the
   shadow of image-band bytes ---- *)
Lemma cnb0_img_hull : forall ly S Hp W mem md p n, ARcf SEGS B ly S Hp W mem md -> 0 < n ->
  @pa_lo _ _ PA + 64 <= p -> p + n + 64 <= @pa_hi _ _ PA -> shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md p n HAR Hn Hlo Hhi s Hs.
destruct (cnb0_hull_img _ _ p n s Hn Hlo Hhi Hs) as [E Hr]. rewrite E.
exact (ISV ly S Hp W mem md _ HAR Hr).
Qed.

(* ---- arodata_okP across the segment, through the entry journal (Cno102B_F.v cnob_arodata_J, by path) ---- *)
Lemma cnb0_arodata_J : forall STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k,
  AJ STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W0) mem0) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Proof.
intros STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k HJ HRO a Hro Hown Herr.
pose proof (ajx_img HJ) as Himg.
assert (Hin : in_img SEGS a).
{ destruct Hro as [(sg & Hsg & _ & Hlo & Hhi) | Hrel];
  [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hrel)]. }
rewrite (Himg a Hin Hown Herr (fun HP => (cnbi_pst_rw B IMG) a HP Hro)
  (fp_spares_closed [] a sink_closed_nil)).
exact (HRO a Hro Hown Herr).
Qed.

(* ---- THE INPUT'S BYTES at a later state of the entry journal (FuzzStrdupB.v sd_src_kept's cases, plus a live
   allocator block that is no harness head - prhReader_home's second arm) ---- *)
Lemma cnb0_in_img_ro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
Lemma cnb0_src_kept : forall STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k Lam peak cnt fail ran most own0
    p n,
  AJ STKa sp0 [] ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  prh_ledger B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran most own0 ->
  (forall x, In x (ablocks B ly0 S0) -> In x (ablocks B ly S)) ->
  PRH_FnReader.prhReader_home B ly0 S0 Hp0 Lam p n ->
  forall a, p <= a < p + n -> aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a.
Proof.
intros STKa sp0 ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k Lam peak cnt fail ran most own0 p n HJ HL Hbl HH a Ha.
pose proof (ajx_blk HJ) as F2. pose proof (ajx_img HJ) as F3.
destruct HH as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & Hnhp & Hb & Hm)].
- destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt fail ran b m most own0 HL Hin) as (Hm0 & Hab & _).
  change (@cf_head CF_cp) with 16 in *.
  replace a with (b - 16 + (a - (b - 16))) by lia.
  apply (F2 (b - 16) (m + 16) (a - (b - 16)) Hab (Hbl _ Hab)); [rewrite cnb0_req by lia; lia | apply inFP_nil].
- destruct (Hro a Ha) as (Hr & Hno & Her).
  apply F3; [exact (cnb0_in_img_ro a Hr) | exact Hno | exact Her | exact (fun Hx => (cnbi_pst_rw B IMG) a Hx Hr) |].
  apply fp_spares_closed. exact sink_closed_nil.
- destruct (Hro a Ha) as (Hr & Hno & Her & _).
  apply F3; [exact (cnb0_in_img_ro a Hr) | exact Hno | exact Her | exact (fun Hx => (cnbi_pst_rw B IMG) a Hx Hr) |].
  apply fp_spares_closed. exact sink_closed_nil.
- replace a with (b + (a - b)) by lia.
  pose proof (cnb0_req_ge m).
  apply (F2 b m (a - b) Hin (Hbl _ Hin)); [lia | apply inFP_nil].
Qed.

(* ---- THE INPUT'S SHADOW at an ARcfx state (FuzzStrdupB.v sd_src_shadow's three kept_at arms, plus the live
   non-head block): a harness block past its head and a plain live block by ARcf's shadow law, a registered
   global by the zero-shadow law and the image hull (cnb0_img_hull), an image string by its const-shadow cells ---- *)
Lemma cnb0_src_shadow : forall ly S Hp W mem md Lam p n,
  ARcfx ly S Hp W mem md -> 0 < n ->
  (forall b m, In (b, m) Lam -> 0 <= m /\ In (b - 16, m + 16) (ablocks B ly S) /\ In (b - 16) Hp) ->
  PRH_FnReader.prhReader_home B ly S Hp Lam p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n /\ shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
intros ly S Hp W mem md Lam p n HAR Hn HLam
  [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & _) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnhp & Hb & Hm)].
- destruct (HLam b m Hin) as (Hm0 & Hab & Hhp).
  destruct (AR_shadow_law_ok_cf SEGS B ly S Hp W mem md (b - 16) (m + 16) (proj1 HAR) Hab) as [Hbs Hhu].
  assert (Hsk : hd_skip Hp (b - 16) = 16).
  { unfold hd_skip. replace (existsb (Z.eqb (b - 16)) Hp) with true; [reflexivity|]. symmetry.
    apply existsb_exists. exists (b - 16). split; [exact Hhp | apply Z.eqb_refl]. }
  rewrite Hsk in Hbs. rewrite cnb0_req in Hbs, Hhu by lia.
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (cnb0_hull_sub _ (b - 16) (m + 16) p n Hhu); lia.
- destruct Hzs as (q & m & Hin & Hq & Hqm).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
    as (Z1 & Z2 & Z3 & Z4 & Z5).
  cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
  pose proof (alc_zshadow SEGS B LAWS_cf ly S Hp W mem md (q, m) (proj1 HAR)
    ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
  cbn [fst snd] in Hz.
  split.
  + apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF q m p n); [|exact Hq|exact Hqm].
    exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz).
  + exact (cnb0_img_hull ly S Hp W mem md p n (proj1 HAR) Hn Hlo Hhi).
- split.
  + intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
    * destruct Hzg as (q & m & Hin & Hq & Hqm).
      pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) (q, m) Hin)
        as (Z1 & Z2 & Z3 & Z4 & Z5).
      cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
      pose proof (alc_zshadow SEGS B LAWS_cf ly S Hp W mem md (q, m) (proj1 HAR)
        ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
      cbn [fst snd] in Hz.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
    * pose proof (proj1 (Forall_forall _ _) (alx_const_cells SEGS B ARcfx LAWS ly S Hp W mem md HAR) _ (Hcell ly))
        as Hc.
      unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
      specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
      pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
      assert (Hb : YG0f.le_byte v 1 0 = v).
      { unfold YG0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
        replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
        change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
      exists v. split; [|exact Hv].
      change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite Hc, Hb. reflexivity.
  + exact (cnb0_img_hull ly S Hp W mem md p n (proj1 HAR) Hn Hlo Hhi).
- destruct (AR_shadow_law_ok_cf SEGS B ly S Hp W mem md b m (proj1 HAR) Hin) as [Hbs Hhu].
  assert (Hsk : hd_skip Hp b = 0).
  { unfold hd_skip. destruct (existsb (Z.eqb b) Hp) eqn:Ee; [|reflexivity].
    apply existsb_exists in Ee as (h & Hh & Ehb). apply Z.eqb_eq in Ehb. subst h. contradiction. }
  rewrite Hsk, Z.add_0_r, Z.sub_0_r in Hbs.
  pose proof (cnb0_req_ge m).
  split.
  + eapply block_shadow_range; [exact Hbs | lia | lia].
  + apply (cnb0_hull_sub _ b (req_size m) p n Hhu); lia.
Qed.

(* a conjunct of cnb_pre picked BY ITS TYPE (CB9's cnb9_pick, Cno102B_E9.v): cnb_pre grew at the cut, so no conjunct
   is read by its position *)
Ltac cnb0_pick H :=
  lazymatch type of H with
  | _ /\ _ => first [ exact (proj1 H) | let H' := fresh "Hpk" in pose proof (proj2 H) as H'; cnb0_pick H' ]
  | _ => exact H
  end.

(* ---- THE STATEMENT (the contract's FORWARD form, the internal file lane-102.md :29-31; Cno102B_Base.v :639-643): generic P with its
   runner laws and the call law (the frame call's rule keeps memnorm only, header) ---- *)
Definition cnb_seg_e0P : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D, cnb_pre B ARcfx CTX0 D -> P (bi_mem D) ->
  SRr SEGS (bi_W D) (cfg_at SEGS (SIGMA AS_check_no_overread) (bi_regs D) (bi_mem D) (bi_md D))
    (fun W' c' => cnb_ex_frame (SK := SK) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c'))).

Theorem cnb_seg_e0 : cnb_seg_e0P.
Proof.
unfold cnb_seg_e0P.
intros P PLAW PCALL D HPRE HP0.
destruct D as [ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 data x Lam peak cnt ran most fpos0].
unfold cnb_pre, cnb_size in HPRE. cbv zeta in HPRE.
cbn [bi_ly bi_S bi_Hp bi_W bi_regs bi_mem bi_md bi_ch bi_data
  bi_x bi_Lam bi_peak bi_cnt bi_ran bi_most bi_fpos] in HPRE, HP0 |- *.
assert (HFP : fpre (fx := fx) B ARcfx STK ly0 S0 Hp0 W0 regs0 mem0 md0 ch0) by cnb0_pick HPRE.
assert (H10 : getr regs0 10 = w64 data) by cnb0_pick HPRE.
assert (H11 : getr regs0 11 = w64 (Z.of_nat (length x))) by cnb0_pick HPRE.
assert (Hsz : Z.of_nat (length x) <= 3 * 2 ^ 20) by cnb0_pick HPRE.
assert (HSRC : src_rd W0 mem0 data x) by cnb0_pick HPRE.
assert (HHOME : 0 < Z.of_nat (length x) ->
  PRH_FnReader.prhReader_home B ly0 S0 Hp0 Lam data (Z.of_nat (length x))) by cnb0_pick HPRE.
assert (HLED : prh_ledger B ly0 S0 Hp0 W0 mem0 Lam peak cnt SIZE_MAXZ ran most 0) by cnb0_pick HPRE.
assert (HCNT : cnt < 2 ^ 62 - 2 ^ 30) by cnb0_pick HPRE.
assert (HRAN : ran = 0) by cnb0_pick HPRE.
assert (HRQ : PRH_FnPj.RQ_pj_parse x <= most) by cnb0_pick HPRE.
assert (HLIVE : blocks_bytes S0 + LIVE_check_no_overread x <= LIVE_MAX) by cnb0_pick HPRE.
assert (HMM1 : Z.of_nat (length x) + 16 < cf_malloc_max) by cnb0_pick HPRE.
assert (HMM2 : PRH_FnPj.RQ_pj_parse x + cf_head < cf_malloc_max) by cnb0_pick HPRE.
assert (HFRM : Z.of_nat (length (frames S0)) <= ck_FRAMES_CAP - FR_check_no_overread) by cnb0_pick HPRE.
assert (HRL : room_live_cf S0) by cnb0_pick HPRE.
assert (HFRZ : ck_frm0 (fx := fx)) by cnb0_pick HPRE.
(* the text's hull premise, the whole call's budget at the entry state (cnb_pre's last conjunct) *)
assert (HHULL : PresetHullBudget.hull_budget S0 (cnb_hev_all x)) by cnb0_pick HPRE.
clear HPRE.
destruct HFP as (HAFN & HROD & HSHI & HRAC).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cnb0_stk_ge as HSTK.
destruct (cnb0_entry0 ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 HAFN) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B prh_pst ARcfx STK [] ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 HAFN) as HJ.
assert (HEI : img_env VAL A_LIM (cnb0_E0 regs0)) by (unfold cnb0_E0; apply Eimg_env).
assert (Usp : bv_unsigned (ew (cnb0_E0 regs0) 2) = spZ regs0)
  by (unfold cnb0_E0; rewrite (cnb0_E_reg regs0 _ 2 2%bv eq_refl); reflexivity).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_cno_B PA B prh_pst ARcfx _ LAWS P PLAW).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_cno_B PA B prh_pst ARcfx _ LAWS P PLAW).
assert (Hpc : w64 (SIGMA AS_check_no_overread) = Z_to_bv 64 (BASE + CNB_OFF)) by (rewrite (cnbi_entry B IMG); reflexivity).
unfold cfg_at. rewrite Hpc.
(* ---- STRETCH 1: 0 .. CNB0_UAR ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HP0 (0, 0) (CNB_OFF + CNB0_UAR).
{ intros a (r & Hr & Ha). unfold cnb0_ss0, cnb0_rs0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [stack_region got_regionP cnb0_r_gotu YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?Usp in Ha; unfold awr_byte.
  - left. unfold CNB0_SAVE in *. lia.
  - exfalso. lia.
  - exfalso. lia. }
rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
pmkst HS.
assert (HAE0 : env_agree 32 (Ereg regs0 [Z_to_bv 64 (as_uar_cell B)]) (cnb0_E0 regs0))
  by (split; [intros n Hn; unfold cnb0_E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew (cnb0_E0 regs0) 32 = Z_to_bv 64 (as_uar_cell B))
  by (unfold cnb0_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)).
assert (E253 : ew (cnb0_E0 regs0) (A_OBJ 12) = Z_to_bv 64 (as_shadow_cell B))
  by (unfold cnb0_E0; rewrite Eimg_img by (unfold A_TEXT, A_OBJ, A_LIM; lia); rewrite (pal_cell B PAL); reflexivity).
(* the saved words, read back from the stack region's chunks *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMO & _).
cbn [ss_mem] in HMO. apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HCH).
cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in HCH. rewrite Usp in HCH.
pose proof (proj1 (Forall_forall _ _) HCH) as HCA.
assert (SAV : forall (off : Z) (n : nat) (r : bv 5),
  In (YP09.mkChunk off (CVal 8 (SOff n 0)))
    [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 27 0))] ->
  Z.of_nat n = bv_unsigned r ->
  val_mem SEGS (rdW W0 (ms_mem ms)) (spZ regs0 + off) 8 (bv_unsigned (getr regs0 r))).
{ intros off n r Hin Hr. rewrite <- (cnb0_E_reg regs0 [Z_to_bv 64 (as_uar_cell B)] n r Hr).
  apply (cnb0_saved_chunk SEGS (cnb0_E0 regs0) (w_H W0) (ms_mem ms) (spZ regs0) off n).
  apply HCA. cbn [In] in Hin |- *. tauto. }
clear HCA HCH.
(* the registers stretch 1 left *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  pose proof (cnb0_reg_S1 _ ss ms regs0 _ 2%bv HS ltac:(left; vm_compute; reflexivity) ltac:(unfold CNB0_SAVE; lia))
    as R2;
  pose proof (cnb0_reg_S1 _ ss ms regs0 _ 9%bv HS ltac:(right; vm_compute; reflexivity) ltac:(unfold CNB0_SAVE; lia))
    as R9;
  pose proof (cnb0_reg_at _ ss ms regs0 _ 8%bv 2 2%bv HS ltac:(vm_compute; reflexivity) eq_refl) as R8;
  pose proof (cnb0_reg_at _ ss ms regs0 _ 23%bv 11 11%bv HS ltac:(vm_compute; reflexivity) eq_refl) as R23;
  pose proof (cnb0_reg_atom _ _ ss ms 11%bv (A_OBJ 12) HS ltac:(vm_compute; reflexivity)) as R11;
  pose proof (cnb0_reg_atom _ _ ss ms 12%bv 32 HS ltac:(vm_compute; reflexivity)) as R12;
  pose proof (regs_kept_of_st_ok_pi (PI := PA) _ ss _ regs0 [Z_to_bv 64 (as_uar_cell B)] ([3; 4; 10]%bv)
    HS HAE0 ltac:(vm_compute; reflexivity)) as KK1
end.
cbn [ms_regs restrict] in KK1.
rewrite E32 in R12. rewrite E253 in R11.
(* ---- STRETCH 2: CNB0_UAR, the option cell ---- *)
destruct (cnb0_cells _ _ _ _ _ _ (ajx_ar HJ)) as ((DS1 & DS2) & (DU1 & DU2) & _).
destruct (alx_const SEGS B ARcfx LAWS _ _ _ _ _ _ (ajx_ar HJ)) as (_ & K2 & _ & _).
destruct (cnb0_seat1 W0 (ms_regs ms) (ms_mem ms) R12 DU1 DU2 (cnb0_val_mem_of_rd32 SEGS _ _ _ _ K2)) as [HS1 SHOK1].
clear K2.
assert (HEIa : img_env VAL A_LIM (cnb0_E (ms_regs ms))) by (unfold cnb0_E; apply Eimg_env).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pc) _ _) _) _ =>
  change pc with (BASE + (CNB_OFF + CNB0_UAR)) end.
paj_run_to_tok_x_inv RUNTO HS1 HJ SHOK1 HP0 (0, 0) (CNB_OFF + CNB0_SB).
{ intros a (r & Hr & Ha). unfold cnb0_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[]]. cbn [cnb0_r_uar YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
pmkst HS1.
assert (KEEP2 : forall a, aview SEGS (w_H W0) (ms_mem ms0) a = aview SEGS (w_H W0) (ms_mem ms) a).
{ apply (cnb0_aview_nowin SEGS (w_H W0) (cnb0_E (ms_regs ms)) (ss_mem cnb0_ss1) _ _ HFr2).
  intros a (r & Hr & Hb). unfold cnb0_ss1 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [cnb0_r_uar YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia. }
lazymatch type of HS1 with st_ok_pi _ _ _ ?ss _ =>
  pose proof (cnb0_reg_at _ ss ms0 (ms_regs ms) _ 11%bv 11 11%bv HS1 ltac:(vm_compute; reflexivity) eq_refl) as Q11;
  pose proof (cnb0_reg_lit _ _ ss ms0 12%bv 1 HS1 ltac:(vm_compute; reflexivity)) as Q12;
  pose proof (regs_kept_of_st_ok_pi (PI := PA) _ ss _ (ms_regs ms) [] ([2; 3; 4; 8; 9; 10; 23]%bv)
    HS1 ltac:(split; [intros n Hn; unfold cnb0_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity])
    ltac:(vm_compute; reflexivity)) as KK2
end.
cbn [ms_regs restrict] in KK2.
rewrite R11 in Q11.
(* ---- STRETCH 3: CNB0_SB .. the frame call ---- *)
destruct (alx_const SEGS B ARcfx LAWS _ _ _ _ _ _ (ajx_ar HJ)) as (K1 & _ & _ & _).
destruct (cnb0_seat2 W0 (ms_regs ms0) (ms_mem ms0) Q11 Q12 DS1 DS2 (val_mem_of_rdword SEGS _ _ _ _ K1))
  as [HS2 SHOK2].
clear K1.
assert (HEIb : img_env VAL A_LIM (cnb0_E (ms_regs ms0))) by (unfold cnb0_E; apply Eimg_env).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pc) _ _) _) _ =>
  change pc with (BASE + (CNB_OFF + CNB0_SB)) end.
paj_run_tok_x_inv RUN HS2 HJ SHOK2 HP0 (0, 0).
{ intros a (r & Hr & Ha). unfold cnb0_ss2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[]]. cbn [cnb0_r_sb YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
rename HF into HF3. rename HFr into HFr3. rename HG into HG3.
assert (KEEP3 : forall a, aview SEGS (w_H W0) (ms_mem ms1) a = aview SEGS (w_H W0) (ms_mem ms0) a).
{ apply (cnb0_aview_nowin SEGS (w_H W0) (cnb0_E (ms_regs ms0)) (ss_mem cnb0_ss2) _ _ HFr3).
  intros a (r & Hr & Hb). unfold cnb0_ss2 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [cnb0_r_sb YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia. }
(* the registers at the frame call, chained back to the entry *)
lazymatch type of HS2 with st_ok _ _ ?ss _ =>
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 2%bv 2 2%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T2;
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 3%bv 3 3%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T3;
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 4%bv 4 4%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T4;
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 8%bv 8 8%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T8;
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 9%bv 9 9%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T9;
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 23%bv 23 23%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T23;
  pose proof (cnb0_reg_at_s _ ss ms1 (ms_regs ms0) [] 24%bv 10 10%bv HS2 ltac:(vm_compute; reflexivity) eq_refl) as T24;
  pose proof (cnb0_reg_lit_s _ _ ss ms1 18%bv SHADOW_OFF HS2 ltac:(vm_compute; reflexivity)) as T18
end.
prreg HS2 (1%bv : bv 5) T1.
rewrite (KK2 2%bv ltac:(cbn; tauto)), R2 in T2.
rewrite (KK2 3%bv ltac:(cbn; tauto)), (KK1 3%bv ltac:(cbn; tauto)) in T3.
rewrite (KK2 4%bv ltac:(cbn; tauto)), (KK1 4%bv ltac:(cbn; tauto)) in T4.
rewrite (KK2 8%bv ltac:(cbn; tauto)), R8 in T8.
rewrite (KK2 9%bv ltac:(cbn; tauto)), R9 in T9.
rewrite (KK2 23%bv ltac:(cbn; tauto)), R23, H11 in T23.
rewrite (KK2 10%bv ltac:(cbn; tauto)), (KK1 10%bv ltac:(cbn; tauto)), H10 in T24.
destruct (cnb0_S1_range (spZ regs0) Hal16 ltac:(lia)) as ((HS1a & HS1b) & HS1c).
remember (Z.land (spZ regs0 - CNB0_SAVE) (-32)) as S1v eqn:ES1v in *.
assert (HspT : spZ (ms_regs ms1) = S1v)
  by (unfold spZ at 1; rewrite T2; unfold w64; apply unsigned_lit_small; unfold CNB0_SAVE in *; lia).
(* ---- THE FRAME CALL (offset 112): __asan_stack_malloc_3 under the capacity rule ---- *)
pmkst HS2.
rewrite <- SM3.
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + (CNB_OFF + CNB0_RET)))).
{ apply ret_ok_codeptr_v; [rewrite cnb0_off_val; unfold CNB0_RET; lia | reflexivity]. }
assert (Hcap : count_cid CNB_CID (frames S0) < fs_frames CNB_CID).
{ pose proof (cnb0_count_le CNB_CID (frames S0)) as Hc.
  assert (E1 : fs_frames CNB_CID = 2048) by (vm_compute; reflexivity).
  assert (E2 : ck_FRAMES_CAP - FR_check_no_overread <= 64) by (vm_compute; discriminate).
  rewrite E1. lia. }
eapply SRr_bind.
{ eapply (cnb0_sm_at (SK := SK) SEGS B prh_pst ARcfx LAWS (@pa_segs_low _ _ PA) (pal_env B PAL) OWNLOW SMXx
    CNB_CID ASMx ltac:(unfold CNB_CID; lia))
  with (o := S1v - spZ regs0) (raw := Z_to_bv 64 (BASE + (CNB_OFF + CNB0_RET))).
  - exact HJ.
  - rewrite HspT. lia.
  - apply cnb0_mod16; [exact HS1c | exact Hal16].
  - unfold CNB0_SAVE in *. lia.
  - unfold ESTACK, CNB0_SAVE in *. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - exact T1.
  - exact Hraw.
  - exact Hcap. }
cbv beta. intros W2 c2 Hwle (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HPRES & Ha0 & Eab2 & Hfrs2 & Hfresh
  & Hbb2 & Hflag & HRAW & (ff & ES2) & HMN2).
pose proof (PCALL _ _ HMN2 HP0) as HP2.
assert (P2 : getr regs2 2%bv = getr (ms_regs ms1) 2%bv) by exact (HPRES 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr (ms_regs ms1) 3%bv) by exact (HPRES 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr (ms_regs ms1) 4%bv) by exact (HPRES 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr (ms_regs ms1) 8%bv) by exact (HPRES 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr (ms_regs ms1) 9%bv) by exact (HPRES 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18%bv = getr (ms_regs ms1) 18%bv) by exact (HPRES 18 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23%bv = getr (ms_regs ms1) 23%bv) by exact (HPRES 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24%bv = getr (ms_regs ms1) 24%bv) by exact (HPRES 24 ltac:(unfold acallee_saved; lia)).
(* the frame's facts at the call's post state *)
assert (Hin2 : In (CNB_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (alx_sep SEGS B ARcfx LAWS _ _ _ _ _ _ (ajx_ar HJ2)) as (_ & HFF).
pose proof (proj1 (Forall_forall _ _) HFF (CNB_CID, pos) Hin2) as (HF4096 & HFceil). cbn [fst snd] in HF4096, HFceil.
destruct (alx_frames SEGS B ARcfx LAWS _ _ _ _ _ _ CNB_CID pos (ajx_ar HJ2) Hin2) as (HF32 & _ & _ & _).
pose proof cnb0_fsb as HFB.
(* ---- STRETCH 4: CNB0_RET .. CNB_FRAME: s11 = s3 = F, the bnez to the real-stack fallback NOT taken ---- *)
destruct (cnb0_seat3 W0 regs2 mem2 (frame_addr ly0 CNB_CID pos) Ha0 ltac:(lia) HF32) as [HS3 SHOK3].
assert (HEIc : img_env VAL A_LIM (cnb0_E regs2)) by (unfold cnb0_E; apply Eimg_env).
paj_run_to_tok_x_inv RUNTO HS3 HJ2 SHOK3 HP2 (0, 0) (CNB_OFF + CNB_FRAME).
{ intros a (r & Hr & _). unfold cnb0_ss3 in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
rename HF into HF4. rename HFr into HFr4. rename HG into HG4.
pmkst HS3.
assert (KEEP4 : forall a, aview SEGS (w_H W0) (ms_mem ms2) a = aview SEGS (w_H W0) mem2 a).
{ apply (cnb0_aview_nowin SEGS (w_H W0) (cnb0_E regs2) (ss_mem cnb0_ss3) _ _ HFr4).
  intros a (r & Hr & _). unfold cnb0_ss3 in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ =>
  pose proof (cnb0_reg_at _ ss ms2 regs2 [] 19%bv 10 10%bv HS3 ltac:(vm_compute; reflexivity) eq_refl) as U19;
  pose proof (cnb0_reg_at _ ss ms2 regs2 [] 27%bv 10 10%bv HS3 ltac:(vm_compute; reflexivity) eq_refl) as U27;
  pose proof (regs_kept_of_st_ok_pi (PI := PA) _ ss _ regs2 [] ([2; 3; 4; 8; 9; 18; 23; 24]%bv) HS3
    ltac:(split; [intros n Hn; unfold cnb0_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity])
    ltac:(vm_compute; reflexivity)) as KK4
end.
cbn [ms_regs restrict] in KK4.
rewrite Ha0 in U19, U27.
(* ---- THE CUT CNB_FRAME ---- *)
(* the exit registers *)
assert (X2 : getr (ms_regs ms2) 2%bv = w64 S1v) by (rewrite (KK4 2%bv ltac:(cbn; tauto)), P2; exact T2).
assert (X3 : getr (ms_regs ms2) 3%bv = getr regs0 3%bv) by (rewrite (KK4 3%bv ltac:(cbn; tauto)), P3; exact T3).
assert (X4 : getr (ms_regs ms2) 4%bv = getr regs0 4%bv) by (rewrite (KK4 4%bv ltac:(cbn; tauto)), P4; exact T4).
assert (X8 : getr (ms_regs ms2) 8%bv = getr regs0 2%bv) by (rewrite (KK4 8%bv ltac:(cbn; tauto)), P8; exact T8).
assert (X9 : getr (ms_regs ms2) 9%bv = w64 S1v) by (rewrite (KK4 9%bv ltac:(cbn; tauto)), P9; exact T9).
assert (X18 : getr (ms_regs ms2) 18%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (KK4 18%bv ltac:(cbn; tauto)), P18; exact T18).
assert (X23 : getr (ms_regs ms2) 23%bv = w64 (Z.of_nat (length x)))
  by (rewrite (KK4 23%bv ltac:(cbn; tauto)), P23; exact T23).
assert (X24 : getr (ms_regs ms2) 24%bv = w64 data) by (rewrite (KK4 24%bv ltac:(cbn; tauto)), P24; exact T24).
(* the program statics (the ledger's cells, g_most, g_own_ran_out) across the segment: stretch 1 writes only its
   frame, stretches 2 - 4 write nothing, the frame call keeps every byte owned by the runtime neither before nor
   after (cnb0_pst_unowned: cnbi_pst_ok) *)
assert (KPST : forall a, Exists (in_zr a) prh_pst ->
  aview SEGS (w_H W0) (ms_mem ms2) a = aview SEGS (w_H W0) mem0 a).
{ intros a Ha. pose proof (cnb0_pst_low a Ha) as Hlow.
  rewrite KEEP4.
  rewrite (HRAW a ltac:(lia) (cnb0_pst_unowned _ _ _ _ _ _ a HAR Ha) (cnb0_pst_unowned _ _ _ _ _ _ a (ajx_ar HJ2) Ha)
    ltac:(unfold ESTACK, CNB0_SAVE in *; lia)).
  rewrite KEEP3, KEEP2.
  apply (cnb0_aview_kept SEGS (w_H W0) (cnb0_E0 regs0) (ss_mem cnb0_ss0) mem0 (ms_mem ms) a HFr1 ltac:(lia)).
  intros (r & Hr & Hb). unfold cnb0_ss0, cnb0_rs0 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]];
  cbn [stack_region got_regionP cnb0_r_gotu YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
  rewrite ?Usp in Hb; unfold CNB0_SAVE in Hb; lia. }
(* the saved words: stretch 1's chunks, kept by stretches 2 - 4 and by the frame call (stack bytes, never owned) *)
assert (KST : forall a, spZ regs0 - CNB0_SAVE <= a < spZ regs0 ->
  aview SEGS (w_H W0) (ms_mem ms2) a = aview SEGS (w_H W0) (ms_mem ms) a).
{ intros a Ha. unfold CNB0_SAVE in *.
  assert (Hst0 : ~ aowned B ly0 S0 a) by (apply (alx_stack SEGS B ARcfx LAWS _ _ _ _ _ _ a HAR); lia).
  assert (Hst2 : ~ aowned B ly0 S2 a) by (apply (alx_stack SEGS B ARcfx LAWS _ _ _ _ _ _ a (ajx_ar HJ2)); lia).
  rewrite KEEP4, (HRAW a ltac:(lia) Hst0 Hst2 ltac:(unfold ESTACK; lia)), KEEP3, KEEP2. reflexivity. }
assert (SAVe : forall (p : Z) (n : nat) (r : bv 5),
  In (YP09.mkChunk (p - 160) (CVal 8 (SOff n 0)))
    [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 27 0))] ->
  Z.of_nat n = bv_unsigned r -> 56 <= p <= 152 ->
  rdword (aview SEGS (w_H W0) (ms_mem ms2)) (spZ regs0 - 160 + p) = Some (bv_unsigned (getr regs0 r))).
{ intros p n r Hin Hr Hp. apply cnb0_rdword_of_val_mem.
  - replace (spZ regs0 - 160 + p) with (spZ regs0 + (p - 160)) by lia.
    apply (cnb0_val_mem_agree SEGS (w_H W0) (w_H W0) (ms_mem ms) (ms_mem ms2) _ 8 _); [|exact (SAV _ n r Hin Hr)].
    intros i Hi. apply KST. unfold CNB0_SAVE. lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb. }
(* the ledger, its blocks' heads by the journal's block clause *)
assert (HLED2 : prh_ledger B ly0 S2 Hp0 W0 (ms_mem ms2) Lam peak cnt SIZE_MAXZ ran most 0).
{ apply (prh_ledger_kept_aview B ly0 S0 Hp0 W0 mem0 ly0 S2 Hp0 W0 (ms_mem ms2) Lam peak cnt SIZE_MAXZ ran most 0 HLED).
  - exact KPST.
  - intros a k i Hin Hi.
    destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt SIZE_MAXZ ran a k most 0 HLED Hin) as (Hk0 & Hab & _).
    pose proof (ajx_blk HJ2) as F2.
    change (@cf_head CF_cp) with 16 in *.
    apply (F2 (a - 16) (k + 16) i Hab ltac:(rewrite Eab2; exact Hab)); [rewrite cnb0_req by lia; lia | apply inFP_nil].
  - intros a k _ H. rewrite Eab2. exact H.
  - apply Permutation_refl. }
(* the input *)
assert (HSRC2 : src_rd W0 (ms_mem ms2) data x).
{ pose proof HSRC as (Hby & H4096 & Hcl & Ham & Hra' & Hhv).
  split; [|split; [exact H4096|split; [exact Hcl|split; [exact Ham|]]]].
  - apply (cnb0_garr8_move SEGS (w_H W0) (w_H W0) mem0 (ms_mem ms2) data x Hby).
    intros j Hj.
    apply (cnb0_src_kept _ _ ly0 S0 Hp0 W0 mem0 md0 _ ly0 S2 Hp0 W0 (ms_mem ms2) _ _ Lam peak cnt SIZE_MAXZ ran most 0 data
      (Z.of_nat (length x)) HJ2 HLED); [intros y Hy; rewrite Eab2; exact Hy | apply HHOME; lia | lia].
  - destruct (Z_le_gt_dec (Z.of_nat (length x)) 0) as [H0 | H0].
    + split; [apply range_addressable_nil; exact H0 | intros; lia].
    + destruct (cnb0_src_shadow ly0 S2 Hp0 W0 (ms_mem ms2) _ Lam data (Z.of_nat (length x)) (ajx_ar HJ2) ltac:(lia))
        as [HRA HHV].
      * intros b m Hin.
        destruct (prh_ledger_hblock B ly0 S0 Hp0 W0 mem0 Lam peak cnt SIZE_MAXZ ran b m most 0 HLED Hin) as (Hm0 & Hab & Hhp & _).
        change (@cf_head CF_cp) with 16 in *. rewrite Eab2. split; [exact Hm0|]. split; [exact Hab | exact Hhp].
      * apply (cnb0_home_eq ly0 S0 Hp0 ly0 S2); [apply HHOME; lia | exact Eab2].
      * split; [exact HRA | intros _; exact HHV]. }
apply SRr_ret. split; [|exact HP2].
unfold cnb_ex_frame.
exists pos, fx, ly0, S2, Hp0, (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy md2) mat2 md2), 0.
split.
{ unfold cnb_cfg, cnb_pc, CNB_FRAME, w64. rewrite <- Z.add_assoc. reflexivity. }
unfold cnb_at_frame, cnb_base, cnb_J, cnb_frame, cnb_saved, cnb_pre_mid, cnb_regsat,
  cnb_S1, cnb_sp0, cnb_F, cnb_size, cnb_set_fpos.
cbn [bi_ly bi_S bi_Hp bi_W bi_regs bi_mem bi_md bi_ch bi_data
  bi_x bi_Lam bi_peak bi_cnt bi_ran bi_most bi_fpos].
assert (ES1' : Z.land (spZ regs0 - 160) (-32) = S1v) by (rewrite ES1v; reflexivity).
rewrite ES1'.
split.
{ (* cnb_base *)
  split; [unfold ck_frm0 in HFRZ; exact HFRZ|].
  split; [intros r Hr; reflexivity|].
  split; [exists []; split; [exact HJ2 | exact (Nat.le_refl 0)]|].
  split.
  { (* the frame *)
    destruct (alx_frames SEGS B ARcfx LAWS _ _ _ _ _ _ CNB_CID pos (ajx_ar HJ2) Hin2) as (_ & _ & Hby & Hsh).
    split; [exact Hfrs2|]. split; [exact Hfresh|].
    split; [rewrite (cnb0_rdword_kept (aview SEGS (w_H W0) mem2) (aview SEGS (w_H W0) (ms_mem ms2)) _
              (fun i _ => KEEP4 _)); exact Hflag|].
    split; [intros a Ha; exact (proj1 (Hby a Ha))|].
    intros a Ha.
    replace a with (shadow_addr (frame_addr ly0 CNB_CID pos) + (a - shadow_addr (frame_addr ly0 CNB_CID pos))) by lia.
    exact (proj1 (Hsh (a - shadow_addr (frame_addr ly0 CNB_CID pos)) ltac:(lia))). }
  split.
  { (* the thirteen saved words *)
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    match goal with |- rdword _ (_ - 160 + ?p) = Some (bv_unsigned (getr _ ?r)) =>
      apply (SAVe p (Z.to_nat (bv_unsigned r)) r);
      [vm_compute; repeat (first [left; reflexivity | right]) | vm_compute; reflexivity | lia] end. }
  split; [exact X3|]. split; [exact X4|].
  exact (cnb0_arodata_J _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD). }
split.
{ (* the registers *)
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact X2.
  - rewrite X8. unfold w64, spZ. symmetry. apply Z_to_bv_bv_unsigned.
  - exact X9.
  - exact X18.
  - exact U19.
  - exact X23.
  - exact X24.
  - exact U27. }
split.
{ (* the state facts before the readings *)
  split; [reflexivity|]. split; [exact HLED2|].
  split; [rewrite ES2; apply RL_set_fs; exact HRL|].
  split; [exact HSRC2|].
  intros H0. apply (cnb0_home_eq ly0 S0 Hp0 ly0 S2); [exact (HHOME H0) | exact Eab2]. }
split.
{ (* the progress fact for no event: the frame take is a set_fs, which neither the live set nor a run position reads *)
  unfold cnb_prog. cbn [bi_S]. split.
  - rewrite ES2. apply Permutation_refl.
  - intros sm x0 os i H0 hist HRP _. exists hist. rewrite Nat.add_0_r, ES2.
    apply PresetRoomPosKeep.room_pos_set_fs. exact HRP. }
split; [exact Eab2|]. split; [exact Hbb2|].
(* the hull budget survives the frame take: a set_fs keeps st_secs, so both meters (PresetHullBudget.hull_budget_same) *)
apply (PresetHullBudget.hull_budget_same S0 S2); [apply YGcfSecsStep.secs_same_of_secs; rewrite ES2; reflexivity|].
exact HHULL.
Qed.

End cf.
