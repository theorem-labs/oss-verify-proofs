(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* ctrl_lay_block (0x83bfc, 992 bytes) on image B, for the one call the program makes: reac_ctrl_stamp_headamp
   passes p, the row B_ROW = CTRL_FRAMES + 240 (0x9d4d0, byte +2 = 2 = BLOCK_TMPL), a null model pointer and
   g = its class-0 frame + 32.

   The walk follows the code by address (an internal excerpt and block map):
     0x83bfc .. 0x83c40  the 128-byte frame, `andi sp,sp,-32`
     0x83c40 .. 0x83c70  the side-stack flag (1) and the call of __asan_stack_malloc_1 (a0 = 96); the class-1
                         contract returns frame_addr lyc 1 fpos <> 0, so `bnez s2` at 0x83c84 is taken and the
                         machine-stack carve 0x83c88 .. 0x83ca0 is not reached
     0x83c74 .. 0x83d30  the frame header, its shadow (4..7 0xf8, 0..3 0xf1, 8..11 0xf3), the traps
                         0x83d10 (p = 0) and 0x83d18 (p >= 2^64 - 18), both false from 0 < p, p + 50 <= 2^47 - 8,
                         and shadow 4..7 := 0
     0x83d3c             __asan_memset (p + 18, 0, 32)
     0x83d40 .. 0x83d84  the trap 0x83d44 (row not 8-aligned; false: B_ROW mod 8 = 0), the checked load of the
                         row's byte +2 (= 2), the bound check 0x83d64 (2 <= 9: not taken) and the `jr` through
                         entry 2 of the table to slot 0x33d4 = 0x83e10
     0x83e10 .. 0x83e7c  the checked load of the row's word +8 (TM) and __asan_memcpy (p + 18, TM, 32)
     0x83e80 .. 0x83ec8  g <> 0; the checked loads of the row's bytes +17 (3) and +16 (18); the trap 0x83ebc
                         (`not a1,s5; bltu a1,a0`: p + 36 >= 2^64; false) and __asan_memcpy (p + 36, g, 3)
     0x83ecc .. 0x83fa8  the inline release of the class-1 frame and the return.
   OBL_box_call_not_taken: the arms into the call of reac_box_model_block at 0x83e64 (table entries 3 .. 9 and the
   index above 9) are refuted by the walk itself: the row's byte +2 is 2, the bound check passes, and the `jr`
   goes to 0x83e10, which reaches 0x83e7c and never 0x83e58 .. 0x83e64. This file takes no contract of
   reac_box_model_block and none of any __asan_report_* entry: every report branch is refuted from the shadow
   facts, every trap branch from the premises.

   The 32 bytes [p + 18, p + 50) are client bytes of a live frame (cb, pb) of the caller's side stack for frames
   (not machine-stack bytes as on image A), so the walk runs over the caller's own journal (twr_ok gives the right
   to write them) and proves tcj_kept from the calls' kept-facts and the frames of the runs. *)
(* PREMISE MAP. What tb_ctrl_lay_block_spec (GrantBContracts.v; its block is the same text at a22dd31ae27 and
   4d7ced43548) adds over image A's tctrl_lay_block_spec (lib/A/Prog/CtrlLayBlockSpec.v, a working branch 5aae1e8a0ce),
   from a diff of the two statement texts. "Used at" names the lines of this file that consume the premise. Every
   premise is discharged by the caller, reac_ctrl_stamp_headamp's walk (the image facts through IMG_CTRL_STAMP).
   1. TM (a new quantified variable) and `tmpl_place TM`. Image A: TM is a Section Variable of A's walk (A's
      CtrlLayBlock.v:91), its range and in_zs Section hypotheses. tmpl_place: UNUSED (bound as HTp at :1180 and
      dropped; the walk takes TM's place from IMG_CTRL_TMPL's own conjuncts).
   2. `IMG_CTRL_ROW_LAY TM`: the row's bytes +2 = 2, +8 = TM, +16 = 18, +17 = 3, in the image view. Why: the code reads
      them after the class-1 frame call 0x83c70 (at 0x83d5c / 0x83e1c / 0x83e98 / 0x83eb4), and that call keeps an
      image byte only off the owned statics and the errno cell; arodata_okP carries the same side condition, so the
      image-view form survives the call (rod_two). Image A: Section hypotheses HROW_k / HROW_tm / HROW_ao / HROW_al.
      Used at :192 (Section hypothesis HROWL) and :824 (the row region's four chunks: the switch index 2 and the
      bound check 0x83d64, TM, the offset 18 for the trap 0x83ebc, and the copy length 3).
   3. `IMG_CTRL_TMPL TM`: TM's range and in_zs, TM apart from the row and the table, and its 32 bytes T32z in the image
      view. Why: the template is copied at 0x83e7c, after 0x83c70 (as in 2). Image A: Section hypotheses HTM_rng,
      HZS_TM, HTMPL. Used: the range at :1190 (HTM_rng, :181); in_zs at :941 (the copy's source shadow); the bytes
      at :933 (the source is present) and :952 (the 32 bytes after the copy). Its two ls_apart conjuncts: UNUSED.
   4. `p <> 0`. Why: image B's UBSan trap 0x83d10 (`beqz s6`: an offset applied to a null pointer); image A has no
      such check. Used at :751 (atom 10's fact 1 .. 2^47 - 58, which with p + 50 <= 2^47 - 8 refutes the traps
      0x83d10 and 0x83d18).
   5. The in-image recast `p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 18`, for A's `forall x, p + 18 <= x < p + 50 ->
      ~ in_img SEGS x`. Why: image B's walk layer states every image range with GrantTop.v's bounds (pa_img_range).
      Used at :939 (the first copy's destination apart from TM), :954, :966 and :1091 (the 32 bytes and the
      template kept across the copies) and :1155 (tcj_kept's image clause).
   6. The frame (cb, pb): `In (cb, pb) (frames Sc)`, `frame_addr lyc cb pb <= p + 18` and `p + 50 <= frame_addr lyc
      cb pb + fs_frame_bytes cb`. These REPLACE A's machine-stack placement `spZ regs <= p + 18 -> p + 50 <= sp0`,
      which image B drops. Why: on image B the caller's scratch lies in a frame of the side stack for frames
      (reac_ctrl_build_grant_sweep's), not on the machine stack. Used at :442 and :456 (p + 50 <= alloc_ceiling,
      below this call's stack window), :446 .. :450 (the frame's class and 8-alignment, for the shadow map), :690
      and :695 (apart from the class-1 frame and from the shadow band), :773 .. :779 (the 32 bytes' shadow is
      the frame's shadow, which the class-1 call keeps), and :802 .. :805, :927 .. :930, :1042 .. :1046
      (range_addressable and shadow_hull_vis at the three runtime calls).
   7. `range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32`. Why: image A derives it from the machine
      stack's zero shadow (A's stack_ra); image B's bytes are client bytes of (cb, pb), whose shadow the caller sets.
      Used at :802 (memset), :927 (the first copy) and :1044 (the second copy's sub-range [p + 36, p + 39)), each
      carried across 0x83c70 by ra_of_kept.
   8. The pin `In (cg, pg) (frames Sc)` and `g = frame_addr lyc cg pg + 32`. UNUSED (bound as Hcgin / Hgeq at
      :1181 and dropped; the walk takes g's frame from afobj, as image A's does).
   9. `spZ regs <= p + 18 \/ p + 50 <= spZ regs - STK_ctrl_lay_block`. UNUSED (bound as Hstkd at :1181 and dropped;
      6 gives p + 50 <= alloc_ceiling <= spZ regs - 4240, :453 and :456).
   Changed, not added: a1 = B_ROW = object 18 + 240 (image A: VAL (A_OBJ A_ROW)); the frame bound `Z.of_nat (length
   (frames Sc)) <= 10` (image A: <= 9), used at :584 (count_cid 1 < fs_frames 1 = 8192 at 0x83c70); the stack need
   STK_ctrl_lay_block = 128 + 16 + ESTACK (image A: TLAY_STK = 160 + ESTACK); the post's event count k (image A:
   k + EV_LAY, EV_LAY = 0). Entries of hyps_ctrl_lay_block this walk does not use: RT_TP_FS, IMG_CTRL_ROW_IMG, and
   IMG_CTRL_ROW's four ls_apart conjuncts (objects 0 / 1 / 35 / 36). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YN3g YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib YC1g YC1h YC45 YC85 GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1i ACj1 ACbf GrantACjr GrantACja PaJr PaNot.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac lia_ex := match goal with |- (0 <= ?x < 2 ^ 64)%Z => lazymatch goal with Hb : (0 <= x < 2 ^ 64)%Z |- _ => exact Hb end end.
Local Ltac lia_spb := lazymatch goal with Hs : (_ - 144 <= _ <= _ - 128)%Z, Hlo : (2 ^ 46 + 4240 <= _)%Z, Hhi : (_ <= 2 ^ 47)%Z |- _ => clear - Hs Hlo Hhi; lia end.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- address-free helpers ------------------------------------------------------------------------------ *)
Lemma awr_byte_cons_own : forall STK sp0 FP bl0 blc ly own x a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H | [H | [H | (cid & pos & Hin & Hr)]]].
- left. exact H.
- right; left. exact H.
- right; right; left. exact H.
- right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.
Lemma shadow_in_frame : forall f n x, 0 <= f -> f mod 8 = 0 -> n mod 8 = 0 -> f <= x < f + n ->
  in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr f, n / 8).
Proof.
intros f n x Hf Hf8 Hn8 Hx. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite Hf8, Z.add_0_r in Df.
pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Hn8, Z.add_0_r in Dn.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
lia.
Qed.
Lemma ra_of_kept : forall (rd rd' : Z -> option Z) off a n (P : Z -> Prop),
(forall s, P s -> rd' s = rd s) -> (forall x, a <= x < a + n -> P (shadow_of_addr off x)) ->
range_addressable rd off a n -> range_addressable rd' off a n.
Proof.
intros rd rd' off a n P HK HP HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s.
split; [rewrite (HK _ (HP x Hx)); exact Hs | exact Hok].
Qed.
Lemma sfs_set_fs : forall c q S2 Sc f, S2 = set_fs f Sc -> exists f', stack_free_state c q S2 = set_fs f' Sc.
Proof. intros c q S2 Sc f ->. unfold stack_free_state. eexists. destruct Sc; reflexivity. Qed.
Lemma fbytes_mod8 : forall c, 0 <= c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c Hc. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z_mod_mult.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : PaBase.ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Notation SB := YC81.SB.
(* the walk's symbolic entry state: atoms 32, 33, 34 are the shadow base, the template pointer and table entry 2 *)
Definition Bx_LAY : sv := SOff 32 0.
Definition Bspan_LAY : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lay_regions : smem :=
[ stack_region 128; got_regionP; bcell_regionP 32; uar_got_regionP 277; uar_cell_regionP 277 ].
Definition lay_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_lay : sstate := mkSS AF_ctrl_lay_block sr_atoms lay_regions None lay_facts.
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
(* ---- what image B holds (the image-view premises; the composition discharges them) -------------------------
   TM is the template pointer the row carries (0x211c0 on image B); JE is entry 2 of the table (0x62ddc), so the
   `jr` at 0x83d84 goes to VAL 267 + JE = BASE + AF_ctrl_lay_block + 0x214 = 0x83e10. *)
Variable TM : Z.
Variable JE : Z.
Hypothesis HTM_rng : 65600 <= TM /\ TM + 32 + 64 <= 0x5fb000.
Hypothesis HROW_rng : 65600 <= B_ROW /\ B_ROW + 24 + 64 <= 0x5fb000.
Hypothesis HROW_al : B_ROW mod 8 = 0.
Hypothesis HJT_rng : 65600 <= VAL 267%nat /\ VAL 267%nat + 40 + 64 <= 0x5fb000.
Hypothesis HJT_eq : VAL 267%nat + JE = BASE + (AF_ctrl_lay_block + 0x214).
Hypothesis HJE_rng : 0 <= JE < 2 ^ 31.
Hypothesis HROW_JT : ls_apart B_ROW 24 (VAL 267%nat) 40.
Hypothesis HROW_o0 : ls_apart B_ROW 24 (VAL 241%nat) 8.
Hypothesis HROW_o1 : ls_apart B_ROW 24 (VAL 242%nat) 8.
Hypothesis HROW_o35 : ls_apart B_ROW 24 (VAL 276%nat) 8.
Hypothesis HROW_o36 : ls_apart B_ROW 24 (VAL 277%nat) 8.
Hypothesis HROWL : IMG_CTRL_ROW_LAY B TM.
Hypothesis HJT_e : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL 267%nat + 8) 4 JE.
Hypothesis HTMPL : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
garr8 SEGS (mrestrict H mem) TM T32z.
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HZS_ROW : in_zs B B_ROW 24.
Hypothesis HZS_TM : in_zs B TM 32.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Definition lay_extra : list word := map (Z_to_bv 64) [SB; TM; JE].
Lemma denot_atom_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H H1 H2 H3. rewrite denot_lit_U, (U_atom_off E n v c H ltac:(lia) ltac:(lia)). reflexivity. Qed.
Lemma denot_lit0 : forall E k, 0 <= k < 2 ^ 64 -> sv_denot E (SLit k) = Z_to_bv 64 k.
Proof. intros E k Hk. rewrite denot_lit_U, U_SLit, zcanon_id by (rewrite M64_val; lia). reflexivity. Qed.
Lemma denot_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U, (U_atom E n v H Hv). reflexivity. Qed.
Lemma denot_add0 : forall E e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD e (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E e v He Hv. rewrite denot_lit_U, (U_add0 E e), <- denot_lit_U. exact He.
Qed.
(* a live frame's class is 0 .. 10 (the model's well-formedness, wf_fs) *)
Lemma frame_cid_rng : forall ly S (W : world SEGS) mem md cid pos, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> 0 <= cid <= 10.
Proof.
intros ly S W mem md cid pos HAR Hin.
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF. apply wf_fakestack in HWF. apply wfs_live in HWF.
rewrite Forall_forall in HWF. exact (proj1 (HWF (cid, pos) Hin)).
Qed.
(* the image's read-only bytes still read as the image after a journal step *)
Lemma rod_two : forall STK1 sp01 FP1 ly1 S1 W01 mem01 md01 own1 lyc1 Sc1 Wc1 memc1 mdc1 k1
own2 ly2 S2 W2 mem2 md2 k2,
ajournal SEGS B STK1 sp01 FP1 ly1 S1 W01 mem01 md01 own1 lyc1 Sc1 Wc1 memc1 mdc1 k1 ->
ajournal SEGS B STK1 sp01 FP1 ly1 S1 W01 mem01 md01 own2 ly2 S2 W2 mem2 md2 k2 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc1) memc1) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros * HJ1 HJ2 HR a Hro Ho He.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Himg : in_img SEGS a)
by (destruct Hro as [(sg & Hsg & _ & Hr) | Hgot]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hgot)]).
assert (Hsp : fp_spares FP1 a) by (apply (ro_spares SEGS pa_relro_lo pa_relro_hi FP1 a); exact Hro).
rewrite (F2 a Himg Ho He Hsp), <- (F1 a Himg Ho He Hsp). exact (HR a Hro Ho He).
Qed.
(* ---- the entry state ------------------------------------------------------ *)
Lemma lay_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md,
AR SEGS B ly S W mem md ->
2 ^ 46 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - 128 <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs lay_extra)) ss_lay
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ctrl_lay_block)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md HAR Hsplo Hsphi Hal16 Hpres.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TL) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 35 ltac:(lia)) as Hob35. pose proof (pa_obj_img 36 ltac:(lia)) as Hob36.
pose proof (palf_uar_img B TL) as Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof IMG_LO_B_val as HIL. pose proof IMG_TOP_B_val as HIT.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs lay_extra)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j lay_extra (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth lay_extra map] in E32, E33, E34.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E276 : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E277 : ew E (A_OBJ 36) = Z_to_bv 64 (VAL (A_OBJ 36))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Euar : as_uar_cell B = VAL (A_OBJ 36)) by (apply (pal_uar_cell B TL)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_lay. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lay_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
[cbn [sv_denot]; rewrite E276, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E276) by (pose proof (pa_val_range (A_OBJ 35)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 36) 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E277, Euar, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite Euar; pose proof (pa_val_range (A_OBJ 36)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 277%nat (VAL (A_OBJ 36)) E277) by (pose proof (pa_val_range (A_OBJ 36)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 36)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r, <- Euar. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold lay_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) E276) by (pose proof (pa_val_range (A_OBJ 35)); lia).
rewrite (VB 277%nat (VAL (A_OBJ 36)) E277) by (pose proof (pa_val_range (A_OBJ 36)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
rewrite Euar in Hsep. rewrite Euar in Huar.
revert Hsplo Hsphi Hob0 Hob1 Hob35 Hob36 Hsep Huar HIL HIT. clear. intros.
repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok lay_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
split; [split; [lia | split; [exact Hal16 | lia]]|]. split; [|exact I].
unfold SB. lia.
Qed.
(* the shadow checks of the row's bytes: CTRL_FRAMES is a registered global (in_zs) *)
Local Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by (first [clear; lia | lia]);
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 33)) with true => rewrite (AG n) by (first [clear; lia | lia]) end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; first [clear; lia | lia_ex | lia_spb | lia]); unfold SB;
first [ reflexivity
| lazymatch goal with |- _ = _ => lia | |- _ <= _ => lia | |- _ < _ => lia | |- _ <= _ < _ => lia | |- _ <= _ <= _ => lia | |- _ < _ <= _ => lia end
| idtac ].
(* lia on a small context first (the side conditions need only the named facts and sp1's bounds, ESTACK), else on all *)
Local Ltac lia_sp Hd := first [ lazymatch goal with Hs : (_ - 144 <= _ <= _ - 128)%Z, He : ESTACK = _ |- _ => clear - Hd Hs He; lia end | lia ].
Local Ltac lia_sp2 Hd Hr := lazymatch goal with Hs : (_ - 144 <= _ <= _ - 128)%Z |- _ => clear - Hd Hr Hs; lia end.
Ltac obl_row AG E11 E32 HZS HARx rowv :=
lazymatch goal with |- range_addressable _ (U ?Ex ?bx) (U _ (SOff 11 ?c)) ?len =>
rewrite (U_atom_off Ex 11 rowv c);
[| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 11%nat) by lia; exact E11 | lia | lia];
let L := rnLAWS in
eapply (obl_of_range _ _ _ Ex bx _ len rowv 24);
[ exact (ro_usable SEGS _ L _ _ _ _ _ rowv 24 HARx HZS)
| rewrite (U_atom Ex 32 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32 | unfold SB; lia]
| lia | lia ] end.
(* carrying a set of bytes (GP, with its separation facts HGPd) across an engine run *)
Ltac upd_gk GP HGK HFr HGPd AG :=
let HGK2 := fresh "HGK" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HGK with forall a, GP a -> aview ?sg ?Hh _ a = aview _ _ ?me a =>
assert (HGK2 : forall a, GP a -> aview sg Hh (ms_mem msX) a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hdd := fresh "Hdd" in
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros a Ha; pose proof (HGPd a Ha) as Hdd; try unfold SHADOW_OFF in Hdd; etransitivity; [| exact (HGK a Ha)]; apply aview_eq_of; apply HFr;
rewrite unsigned_lit_small by lia;
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first [clear - Hdd Hrg; lia | lia_sp2 Hdd Hrg | match goal with Hs1 : _ <= _ <= _ |- _ => clear - Hdd Hrg Hs1; lia end | lia | fail 2 "upd_gk: a write window meets the predicate"] |]);
solve [destruct Hin]
| clear HGK; rename HGK2 into HGK ] end end.
(* ... and across a runtime call (its frame fact Hfrx) *)
Ltac upd_gk_call GP HGK Hfrx HGPd :=
let HGK2 := fresh "HGK" in
lazymatch type of Hfrx with forall a, _ -> _ -> _ -> aview ?sg ?Hh ?mN a = aview _ _ _ a =>
lazymatch type of HGK with forall a, GP a -> aview _ _ _ a = aview _ _ ?me a =>
assert (HGK2 : forall a, GP a -> aview sg Hh mN a = aview sg Hh me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hdd := fresh "Hdd" in
intros a Ha; pose proof (HGPd a Ha) as Hdd; rewrite (Hfrx a ltac:(lia_sp Hdd) ltac:(lia_sp Hdd) ltac:(lia_sp Hdd)); exact (HGK a Ha)
| clear HGK; rename HGK2 into HGK ] end end.
(* the bytes that are present stay present across an engine run *)
Ltac upd_pr HPR :=
let HPR' := fresh "HPR" in
lazymatch goal with HG : mem_grows (mrestrict ?Hh ?m0) (mrestrict _ ?m1) |- _ =>
lazymatch type of HPR with forall a, apresent _ ?me a -> _ =>
assert (HPR' : forall a, apresent Hh me a -> apresent Hh m1 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply apresent_grows; [exact HG | exact (HPR a Ha)]);
clear HPR; rename HPR' into HPR end end.
(* the bytes the epilogue's run writes: the machine stack, the frame, its shadow, the flag *)
Ltac wrange_lay AG fpos F FL :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; fold FL; clear - Hr; lia
| left; left; unfold STK_ctrl_lay_block, ESTACK in *; lia
| left; right; right; right; exists 1, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; fold F; unfold SB; clear - Hr; lia ]
| fail 2 "wrange_lay: no case for this window" ]
| ]);
solve [destruct Hin].
Ltac awr_lay AG d2 d60 fpos FF EFA :=
awrFL_with ltac:(idtac; lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat d2);
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold STK_ctrl_lay_block, ESTACK in *; lia | cbn [YP09.r_whi]; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat d60);
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold STK_ctrl_lay_block, ESTACK in *; lia | cbn [YP09.r_whi]; lia |]
end) AG fpos FF EFA.
(* ---- the walk ------------------------------------------------------------------------------------------- *)
Theorem lay_core : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p g cb pb ch pm v : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 B_ROW -> getr regs 12 = w64 0 -> getr regs 13 = w64 g ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_ctrl_lay_block -> spZ regs <= sp0 ->
  Z.of_nat (length (frames Sc)) <= 10 ->
  0 <= p -> p + 50 <= 2 ^ 47 - 8 -> p <> 0 -> amem_range (p + 18) 32 ->
  (p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 18) ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
  In (cb, pb) (frames Sc) -> frame_addr lyc cb pb <= p + 18 -> p + 50 <= frame_addr lyc cb pb + fs_frame_bytes cb ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
  g <> 0 -> tsrc_ok W memc (spZ regs) g 3 -> afobj SEGS B lyc Sc W memc g 3 ->
  garr8 SEGS (mrestrict (w_H W) memc) g [ch; pm; v] ->
  (p + 50 <= g \/ g + 3 <= p + 18) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_ctrl_lay_block) regs memc mdc)
    (tb_ctrl_lay_block_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p ch pm v).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p g cb pb ch pm v
HJc HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hal16 Hwlo Hwhi Hfrlen
Hp0 Hp47 Hpn0 Hamr Hnimg Hwr Hcbin Hcblo Hcbhi Hbra Hg0 Hsrc Hgobj Hgarr Hdisj.
box Hnimg. box Hdisj.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof IMG_LO_B_val as HIL. pose proof IMG_TOP_B_val as HIT.
pose proof HJc as (HAR & Hlyc & _ & _ & _ & HfrsC & _ & _ & _ & _ & _ & _ & _ & Hpresc & Hstatic & _ & HQT).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : STK_ctrl_lay_block = 4240) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
(* the frame (cid0, pos0) that holds g, and the frame (cb, pb) that holds the 32 bytes *)
destruct Hgobj as ((cid0 & pos0 & Hgfin & Hgcid & Hgal8 & Hglo & Hghi) & Hg8 & Hgra0).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid0 pos0 HAR Hgfin) as (HG4096 & HGceil & HGapp).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cb pb HAR Hcbin) as (HC4096 & HCceil & HCapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ cb pb HAR Hcbin) as (HCal & _).
set (G0 := frame_addr lyc cid0 pos0) in *.
set (C0 := frame_addr lyc cb pb) in *.
pose proof (frame_cid_rng lyc Sc W memc mdc cb pb HAR Hcbin) as [Hcb0 _].
pose proof (fs_frame_bytes_nonneg cb) as HCbs0. pose proof (fs_frame_bytes_nonneg cid0) as HGbs0.
pose proof (fbytes_mod8 cb Hcb0) as HCbs8. pose proof (fbytes_mod8 cid0 Hgcid) as HGbs8.
assert (HCal8 : C0 mod 8 = 0) by (pose proof (Z.div_mod C0 32 ltac:(lia)) as D; rewrite HCal, Z.add_0_r in D;
  rewrite D; replace (32 * (C0 / 32)) with ((4 * (C0 / 32)) * 8) by lia; apply Z_mod_mult).
assert (Hsplo : 2 ^ 46 + 4240 <= spZ regs) by (unfold STK_ctrl_lay_block, ESTACK in *; lia).
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
assert (Hwin : alloc_ceiling <= spZ regs - 4240) by (unfold STK_ctrl_lay_block, ESTACK in *; lia).
assert (Hpres128 : forall a, spZ regs - 128 <= a < spZ regs -> apresent (w_H W) memc a)
by (intros a Ha; apply Hpresc; unfold STK_ctrl_lay_block, ESTACK in *; lia).
assert (HbufC : p + 50 <= alloc_ceiling) by lia.
pose proof HJc as HJL.
pose proof (lay_entry lyc Sc W regs memc mdc HAR ltac:(lia) Hsphi Hal16 Hpres128) as HS.
assert (SHOK : sh_ok SEGS Bx_LAY (@nil shent) (Eimg (Ereg regs lay_extra)) (mrestrict (w_H W) memc)) by constructor.
remember (Eimg (Ereg regs lay_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 B_ROW) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j lay_extra (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth lay_extra map] in E32, E33, E34.
assert (HAE : env_agree 32 (Ereg regs lay_extra) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
img_factsF E. img_hull_factsF.
(* the image values' bounds, once, in the shape evalE's literal side goals ask for (lia_ex) *)
assert (HV241b : 0 <= VAL 241%nat < 2 ^ 64) by lia. assert (HV242b : 0 <= VAL 242%nat < 2 ^ 64) by lia.
assert (HV276b : 0 <= VAL 276%nat < 2 ^ 64) by lia. assert (HV277b : 0 <= VAL 277%nat < 2 ^ 64) by lia.
assert (HV267b : 0 <= VAL 267%nat < 2 ^ 64) by (clear - HJT_rng; lia). assert (HBRb : 0 <= B_ROW < 2 ^ 64) by (clear - HROW_rng; lia).
unfold cfg_at. change (w64 (BASE + AF_ctrl_lay_block)) with (Z_to_bv 64 (BASE + AF_ctrl_lay_block)).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
(* the bytes off this call's stack window, kept up to the call of __asan_stack_malloc_1 *)
set (Q0 := fun a => 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 4240 <= a < spZ regs)).
assert (HQ0d : forall a, Q0 a -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 4240 <= a < spZ regs)) by (intros a Ha; exact Ha).
assert (HQ0 : forall a, Q0 a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (HPR : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a Ha; exact Ha).
(* the prologue, up to the realigned sp (0x83c40) *)
paj_run_to_tok RUNTO HS HJL SHOK Bspan_LAY 0x3204.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | cbn [ew]; rewrite Usp; lia
| cbn [YP09.r_wlo]; unfold STK_ctrl_lay_block, ESTACK in *; lia
| cbn [YP09.r_whi]; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
upd_gk Q0 HQ0 HFr HQ0d AG. upd_pr HPR.
clear_frames.
pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
(* the realigned stack pointer sp1 = (sp - 128) & -32, in sp and in s1 *)
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
as (Hsp1r & Hsp1al32 & Hsp1al16). fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) R2;
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1)
(denot_add0 Ev (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) sp1
(denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) R9 end.
(* sp1 becomes atom 60, in sp and in s1; the machine frame keeps its own window *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS. ACj1.rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 sp1)
by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R9; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32;
split; [clear - Hsp1 Hsplo Hsphi; lia | split; [exact Hsp1al32 | lia]])) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
(* the machine frame's live window is [sp - 96, sp): the saved registers *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs2 := eval vm_compute in (trim_stack rs (-96) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs2 HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E60, unsigned_lit_small by lia;
split; [clear - Hsp1 Hsplo; lia|]; split; [clear - Hsp1 Hsphi; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres1; unfold STK_ctrl_lay_block, ESTACK in *; clear - Ho Hsp1 Hwlo Hwhi; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; clear - Hsp1 Hsplo Hsphi Hob241 Hob242 Hob276 Hob277 Huar HIL HIT; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
assert (SHOK2 : sh_ok SEGS Bx_LAY (@nil shent) ltac:(lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => exact Ev end)
(mrestrict (w_H W) ltac:(lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) => exact (ms_mem msX) end))) by constructor.
(* on to the call of __asan_stack_malloc_1 (0x83c70) *)
paj_run_tok RUN HS HJL SHOK2 Bspan_LAY.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?ow =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx ow) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0));
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold STK_ctrl_lay_block, ESTACK in *; lia | cbn [YP09.r_whi]; lia |].
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | evalE AG | cbn [YP09.r_wlo]; unfold STK_ctrl_lay_block, ESTACK in *; lia | cbn [YP09.r_whi]; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
upd_gk Q0 HQ0 HFr HQ0d AG. upd_pr HPR.
clear_frames.
aconstsF HJL Kgot0 Kcell0 Kguar0 Kuar0.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2b end.
pmkst HS.
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msY)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJL) end.
- unfold spZ at 1. rewrite R2b. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold STK_ctrl_lay_block, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [unfold AF_ctrl_lay_block; lia | reflexivity].
- change (fs_frames 1) with 8192. clear - Hcnt Hfrlen; lia. }
cbv beta. clear R1 R3 R4 R2b SHOK2.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK.
replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK by lia.
replace (sp0 + (sp1 - sp0)) with sp1 in HK by lia.
(* what the call keeps, relative to the caller's memory memc *)
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (KC1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 4240 <= a < spZ regs) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha Hn. rewrite (K1 a Ha ltac:(lia)). apply HQ0. unfold Q0. split; [lia | exact Hn]. }
assert (KC2 : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
  aview SEGS (w_H W) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)).
{ intros b m i Hb Hi. rewrite (K2 b m i Hb Hi (fun H => H)). apply HQ0. unfold Q0.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _). split; lia. }
assert (KC3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Hi Ho He. rewrite (K3 a Hi Ho He). apply HQ0. unfold Q0. pose proof (Hsegs a Hi). split; lia. }
assert (KC4 : forall cid pos a, In (cid, pos) (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros cid pos a Hin Hr. rewrite (K4 cid pos a Hin Hr (fun H => H)). apply HQ0. unfold Q0.
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4096 & Hfceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  assert (Hd1 : frame_addr lyc cid pos / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (Hd2 : fs_frame_bytes cid / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (Hd0 : 0 <= frame_addr lyc cid pos / 8) by (apply Z.div_pos; lia).
  unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr. split; lia. }
assert (KC5 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 4240 <= a < spZ regs) ->
  apresent (w_H W) memc a -> apresent (w_H W) mem2 a)
by (intros a Ha Hn Hp; apply K5; [exact Ha | lia | exact (HPR a Hp)]).
clear K1 K2 K3 K4 K5 K6 HQ0 HQ0d HPR.
assert (HPR : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem2 a) by (intros a Ha; exact Ha).
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgB _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFoffB.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (EFA0 : forall c q, frame_addr lyc c q = frame_addr lyc c q) by reflexivity.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [keptFL HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)
| fail]).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
(* the frame's flag address and shadow base become atoms 528 and 529 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. ACj1.rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL)
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL lyc S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
(* the flag byte is off image B's range (AR's client-image law, pa_img_cover) *)
assert (HFLoff : FL + 1 <= 65536 \/ 6270976 <= FL).
{ pose proof (al_client_img _ _ LAWS lyc S2 W mem2 md2 FL HAR2 (or_intror (or_intror (ex_intro _ 1 (ex_intro _ fpos (conj Hfin2 eq_refl)))))) as [HnI _].
  pose proof HAR2 as (_ & LG & _). pose proof (pa_img_cover lyc S2 md2 LG) as [Cv1 Cv2].
  unfold in_zr in HnI. rewrite IMG_LO_B_val in Cv1. rewrite IMG_TOP_B_val in Cv2. lia. }
box HFLoff.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32' E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the frame itself, with the flag pointer it carries at +120 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite RF, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128; rewrite RF; evalE AG; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the frames of the caller are apart from the new frame *)
assert (HFsep : forall c q, In (c, q) (frames Sc) -> frame_addr lyc c q + fs_frame_bytes c <= F \/ F + 128 <= frame_addr lyc c q).
{ intros c q Hin. destruct (in_split _ _ Hin) as (l1 & l2 & Egf).
  pose proof (sep_frames_pos SEGS B LAWS lyc S2 W mem2 md2 (1, fpos) (c, q) [] l1 l2 HAR2
  ltac:(rewrite Hfrs2, Egf; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd. lia. }
assert (HFal8 : F mod 8 = 0) by (pose proof (Z.div_mod F 32 ltac:(lia)) as DF32; rewrite HFal, Z.add_0_r in DF32;
rewrite DF32; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HFal8, Z.add_0_r in DF.
pose proof (HFsep cb pb Hcbin) as HFC. fold C0 in HFC. box HFC.
pose proof (HFsep cid0 pos0 Hgfin) as HFG. fold G0 in HFG. box HFG.
assert (HFoff : F + 128 <= 65536 \/ 6270976 <= F) by (rewrite IMG_LO_B_val, IMG_TOP_B_val in HFoffB; exact HFoffB).
clear HFoffB. box HFoff.
assert (HBapp : p + 50 <= 2147450880 \/ 17594333495296 <= p + 18)
by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HCapp; lia). box HBapp.
(* the bytes this call writes from here on: its stack window, the 32 bytes, the new frame, its shadow, the flag *)
set (Q := fun a => 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 4240 <= a < spZ regs) /\ ~ (p + 18 <= a < p + 50) /\
  ~ (F <= a < F + 128) /\ ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) /\ a <> FL).
assert (HQd : forall a, Q a -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 4240 <= a < spZ regs) /\ ~ (p + 18 <= a < p + 50) /\
  ~ (F <= a < F + 128) /\ ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) /\ a <> FL) by (intros a Ha; exact Ha).
assert (HQ : forall a, Q a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by reflexivity.
(* the frames of the caller and their shadow bytes, off the 32 bytes, are such bytes *)
assert (HQfr : forall c q a, In (c, q) (frames Sc) ->
  (in_zr a (frame_rng lyc (c, q)) \/ in_zr a (shadow_addr (frame_addr lyc c q), fs_frame_bytes c / 8)) ->
  ~ (p + 18 <= a < p + 50) -> Q a).
{ intros c q a Hin Hr Hne.
  assert (Hin2 : In (c, q) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc c q HAR Hin) as (Hf4096 & Hfceil & Hfapp).
  destruct (al_frames _ _ LAWS _ _ _ _ _ c q HAR2 Hin2) as (Hfal & _ & Hfno & Hfsno).
  pose proof (HFsep c q Hin) as Hsep.
  pose proof (frame_cid_rng lyc Sc W memc mdc c q HAR Hin) as [Hc0 _].
  pose proof (fs_frame_bytes_nonneg c) as Hnn. pose proof (fbytes_mod8 c Hc0) as Hb8.
  set (f := frame_addr lyc c q) in *. set (nb := fs_frame_bytes c) in *.
  assert (Hf8 : f mod 8 = 0) by (pose proof (Z.div_mod f 32 ltac:(lia)) as D; rewrite Hfal, Z.add_0_r in D;
    rewrite D; replace (32 * (f / 32)) with ((4 * (f / 32)) * 8) by lia; apply Z_mod_mult).
  pose proof (Z.div_mod f 8 ltac:(lia)) as Df. rewrite Hf8, Z.add_0_r in Df.
  pose proof (Z.div_mod nb 8 ltac:(lia)) as Dn. rewrite Hb8, Z.add_0_r in Dn.
  unfold Q. destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr in Hr; cbn [fst snd] in Hr.
  - split; [lia|]. split; [lia|]. split; [exact Hne|]. split; [lia|]. split.
    { intros Hs. apply (fshadow_not_app F 16 f nb a); [lia | lia | exact Hfapp | unfold SHADOW_OFF in Hs; lia | lia]. }
    intros ->. exact (proj2 (Hfno FL Hr) HFLown).
  - unfold SHADOW_OFF in Hr. split; [lia|]. split; [lia|]. split; [exact Hne|]. split.
    { intros Hs. apply (fshadow_not_app f (nb / 8) F 128 a); [lia | lia | exact HFapp | lia | lia]. }
    split; [unfold SHADOW_OFF; lia|].
    intros ->. specialize (Hfsno (FL - shadow_addr f)). unfold shadow_addr, SHADOW_OFF in Hfsno.
    replace (2147450880 + f / 8 + (FL - (2147450880 + f / 8))) with FL in Hfsno by lia.
    exact (proj2 (Hfsno ltac:(lia)) HFLown). }
assert (HSB : SB = SHADOW_OFF) by reflexivity.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- HSB in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E529, unsigned_lit_small by (unfold SB; lia);
split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- HSB in HFSpres;
apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; change (fs_frame_bytes 1) with 128; rewrite E529, RF; evalE AG;
rewrite ?unsigned_lit_small by (unfold SB; first [clear; lia | lia_ex | lia_spb | lia]); unfold SB;
repeat split; first [zone_lia | fail])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* p: 0 < p and p + 50 <= 2^47 - 8 decide the two traps 0x83d10 / 0x83d18 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 10%nat (mkAF 1 (2 ^ 47 - 58) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (AG 10%nat) by lia; rewrite E10, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the frame's magic, description and pc, and its shadow bytes (0xf8, 0xf1, 0xf3, then 0), and the two traps *)
paj_run_to_sh RUNTOP HS HJ2 0x32f4.
{ awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0. }
upd_gk Q HQ HFr HQd AG. upd_pr HPR. clear_frames.
fs_roF HS. reshok HS.
paj_run_tok RUN HS HJ2 SHOK Bspan_LAY.
{ awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0. }
upd_gk Q HQ HFr HQd AG. upd_pr HPR. clear_frames.
(* ---- __asan_memset (p + 18, 0, 32) at 0x83d3c ---- *)
prreg HS (1%bv : bv 5) R1m. prreg HS (3%bv : bv 5) R3m. prreg HS (4%bv : bv 5) R4m.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (p + 18))
(denot_atom_off Ev 10 18 p ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia)) Ra0m;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 0) (denot_lit0 Ev 0 ltac:(lia)) Ra1m;
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 32) (denot_lit0 Ev 32 ltac:(lia)) Ra2m;
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2m end.
pmkst HS.
(* the shadow bytes of the 32 bytes are shadow bytes of the frame (cb, pb), which this call has kept *)
assert (HBsh : forall s, in_zr s (shadow_addr C0, fs_frame_bytes cb / 8) -> Q s).
{ intros s Hs. apply (HQfr cb pb s Hcbin (or_intror Hs)). intros Hb.
  pose proof (Z.mul_div_le (fs_frame_bytes cb) 8 ltac:(lia)).
  apply (fshadow_not_app C0 (fs_frame_bytes cb / 8) C0 (fs_frame_bytes cb) s); [lia | lia | exact HCapp | | lia].
  unfold in_zr, shadow_addr, SHADOW_OFF in Hs; cbn [fst snd] in Hs; lia. }
assert (HBshx : forall x, p + 18 <= x < p + 50 -> in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr C0, fs_frame_bytes cb / 8))
by (intros x Hx; apply shadow_in_frame; [lia | exact HCal8 | exact HCbs8 | lia]).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA GS___asan_memset) AMEMSET W (ms_regs msX) (ms_mem msY)
STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 _ k (p + 18) 0 32 (sp1 - sp0) _ HJ2) end.
- rewrite Ra0m. reflexivity.
- rewrite Ra1m. reflexivity.
- rewrite Ra2m. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite R2m. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold STK_ctrl_lay_block, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3m, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4m, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1m.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + rewrite Eab. apply awr_byte_cons_own. exact (proj1 (Hwr a Ha)).
  + clear - Ha Hsp1 HbufC Hwin Hes; lia.
- exact Hamr.
- eapply (ra_of_kept _ _ SHADOW_OFF (p + 18) 32 (fun s => in_zr s (shadow_addr C0, fs_frame_bytes cb / 8))); [| intros x Hx; apply HBshx; lia | exact Hbra].
  intros s Hs. rewrite (HQ s (HBsh s Hs)). exact (KC4 cb pb s Hcbin (or_intror Hs)).
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cb pb (p + 18) 32 (proj1 HJ2));
  [rewrite Hfrs2; right; exact Hcbin | lia | lia | lia].
- exact I. }
cbv beta.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & Hsame3).
upd_gk_call Q HQ Hfr3 HQd.
assert (HPR3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) by (intros a Ha; apply Hpres3; apply HPR; exact Ha).
clear HPR. rename HPR3 into HPR.
reseat HS HJ3 HP3 [0; 1; 2; 3]%nat AG
ltac:(idtac; first [eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr3;
  pose proof HBapp as HBa; pose proof HFC as HFc; unfold boxed in HBa, HFc; unfold STK_ctrl_lay_block, ESTACK in *; first [clear - Ha HBa HFc Hsp1 Hsplo Hsphi Hp0 Hp47 HIL HIT Hcblo Hcbhi HFq HF8lo HF8hi HCbs0 HCal8 Hwin HbufC HF4096 HFceil HJT_rng HROW_rng HFb; lia | clear - Ha HBa HFc Hni Hsp1 Hsplo Hsphi Hp0 Hp47 HIL HIT Hcblo Hcbhi HFq HF8lo HF8hi HCbs0 HCal8 Hwin HbufC HF4096 HFceil HJT_rng HROW_rng HFb; lia | lia] | exact Hpres3]
| fail]).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJc | exact HJ3 | exact HROD]) end.
(* the row CTRL_FRAMES[CTRL_HEADAMP] and the switch's jump table, read-only image regions *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => img_factsF Ev end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HEIv := rnHEI Ev in
pose proof (img_env_atomP Ev 267%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)) as E267 end.
destruct (HROWL (w_H W) mem3 HROD3) as (HRk & HRtm & HRao & HRal).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 11%nat) 0 24 0 0
[YP09.mkChunk 2 (CVal 1 (SLit 2)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
YP09.mkChunk 16 (CVal 1 (SLit 18)); YP09.mkChunk 17 (CVal 1 (SLit 3))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite (AG 11%nat) by lia; rewrite E11, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ B_ROW 2 1 (SLit 2) 2); [reflexivity | zside | zside | exact HRk]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ B_ROW 8 8 (SOff 33 0) TM);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact HRtm]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ B_ROW 16 1 (SLit 18) 18); [reflexivity | zside | zside | exact HRao]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ B_ROW 17 1 (SLit 3) 3); [reflexivity | zside | zside | exact HRal]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite (AG 11%nat) by lia; rewrite E11; evalE AG; rewrite ?unsigned_lit_small by (unfold SB; first [clear; lia | lia_ex | lia_spb | lia]); unfold SB;
pose proof HFoff as HFo; unfold boxed in HFo;
repeat split; first [zone_lia | fail])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 267%nat) 0 40 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 34 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E267, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (VAL 267%nat) 8 4 (SOff 34 0) JE);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact (HJT_e _ _ HROD3)]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E267, (AG 11%nat) by lia; rewrite E11; evalE AG; rewrite ?unsigned_lit_small by (unfold SB; first [clear; lia | lia_ex | lia_spb | lia]); unfold SB;
pose proof HFoff as HFo; unfold boxed in HFo; pose proof HROW_JT as HRJ; unfold ls_apart in HRJ;
repeat split; first [zone_lia | fail])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 34%nat (mkAF 0 (2 ^ 31 - 1) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 11%nat (mkAF 65600 6270888 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (AG 11%nat) by lia; rewrite E11, unsigned_lit_small by lia;
change (2 ^ 3) with 8; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok HS.
(* the row's alignment (trap 0x83d44), its kind byte, the bound check, the jump table, up to the `jr` at 0x83d84 *)
paj_run_tok RUN HS HJ3 SHOK Bspan_LAY.
1: obl_row AG E11 E32 HZS_ROW (proj1 HJ3) B_ROW.
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk Q HQ HFr HQd AG. upd_pr HPR. clear_frames.
(* the `jr` through the jump table: entry 2 is the template case, slot 0x33d4 = 0x83e10 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (JE + VAL 267%nat))
(denot_add_atoms Ev 34 267 JE (VAL 267%nat) E34 E267 ltac:(lia) ltac:(lia) ltac:(lia)) R10j end.
rewrite Z.add_comm in R10j.
assert (HJTk : VAL (A_OBJ 26) + JE = BASE + (AF_ctrl_lay_block + 0x214)) by exact HJT_eq.
assert (HAFk : 0 <= AF_ctrl_lay_block + 0x214 < 2 ^ 40) by (unfold AF_ctrl_lay_block; lia).
assert (HAF2 : (AF_ctrl_lay_block + 0x214) mod 2 = 0) by (vm_compute; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
assert (Hpcj : plookup pl_tpi (ss_pc ssx) = Some (PW 327783)) by (vm_compute; reflexivity);
assert (Hdecj : decode_any (Z_to_bv 32 327783) = Some (Jalr 0%bv (10%bv : bv 5) 0%bv, 4%Z)) by vm_refl_bv;
eapply (paj_jr_table 26 JE (AF_ctrl_lay_block + 0x214) W Ev ssx msx _ _ 327783 (10%bv : bv 5) HS eq_refl Hpcj Hdecj R10j HJTk HAFk HAF2) end.
intros matj HSj. clear HS R10j. rename HSj into HS.
pose proof (ajournal_materialize SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matj HJ3) as HJ3j. clear HJ3. rename HJ3j into HJ3.
(* the template pointer from the row's word +8, up to the call of __asan_memcpy at 0x83e7c *)
paj_run_tok RUN HS HJ3 SHOK Bspan_LAY.
all: try (obl_row AG E11 E32 HZS_ROW (proj1 HJ3) B_ROW).
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk Q HQ HFr HQd AG. upd_pr HPR. clear_frames. ACj1.rebaseE HS AG HEv2. clear HEv2.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD4 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJc | exact HJ3 | exact HROD]) end.
prreg HS (1%bv : bv 5) R1c. prreg HS (3%bv : bv 5) R3c. prreg HS (4%bv : bv 5) R4c.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (p + 18))
(denot_atom_off Ev 10 18 p ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia)) Ra0c;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 TM) (denot_atom0 Ev 33 TM E33 ltac:(lia)) Ra1c;
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 32) (denot_lit0 Ev 32 ltac:(lia)) Ra2c;
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2c end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msY)
STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 _ k (p + 18) TM 32 (sp1 - sp0) _ HJ3) end.
- rewrite Ra0c. reflexivity.
- rewrite Ra1c. reflexivity.
- rewrite Ra2c. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite R2c. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold STK_ctrl_lay_block, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3c, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4c, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1c.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + rewrite Eab. apply awr_byte_cons_own. exact (proj1 (Hwr a Ha)).
  + clear - Ha Hsp1 HbufC Hwin Hes; lia.
- exact Hamr.
- eapply (ra_of_kept _ _ SHADOW_OFF (p + 18) 32 (fun s => in_zr s (shadow_addr C0, fs_frame_bytes cb / 8))); [| intros x Hx; apply HBshx; lia | exact Hbra].
  intros s Hs. rewrite (HQ s (HBsh s Hs)). exact (KC4 cb pb s Hcbin (or_intror Hs)).
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cb pb (p + 18) 32 (proj1 HJ3));
  [rewrite Hfrs2; right; exact Hcbin | lia | lia | lia].
- split; [lia|]. split; [lia|]. split.
  { intros a Ha. split.
    - pose proof (HTMPL _ _ HROD4) as HT.
      destruct (HT (Z.to_nat (a - TM)) ltac:(cbn [length T32z]; lia)) as [HTv _].
      specialize (HTv 0%nat ltac:(lia)).
      replace (TM + Z.of_nat (Z.to_nat (a - TM)) + Z.of_nat 0) with a in HTv by lia.
      unfold aview. rewrite HTv. discriminate.
    - unfold spZ. rewrite R2c, unsigned_lit_small by lia. lia. }
  split; [pose proof Hnimg as Hni; unfold boxed in Hni; lia|].
  split; [unfold amem_range, kLowMemEnd; left; lia|].
  split; [let L := rnLAWS in exact (ro_usable SEGS _ L _ _ _ _ _ TM 32 (proj1 HJ3) HZS_TM)|].
  intros _. eapply ro_hull; [exact HIMGSH | exact (proj1 HJ3) | | |]; unfold IMG_LO, IMG_HI; rewrite ?IMG_LO_B_val, ?IMG_TOP_B_val; lia. }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff4 & Hfr4 & Hpres4 & Hsame4).
upd_gk_call Q HQ Hfr4 HQd.
assert (HPR4 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem4 a) by (intros a Ha; apply Hpres4; apply HPR; exact Ha).
clear HPR. rename HPR4 into HPR.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD5 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJc | exact HJ4 | exact HROD]) end.
assert (HTMPL4 : garr8 SEGS (mrestrict (w_H W) mem4) (p + 18) T32z).
{ eapply (garr8_aview SEGS (w_H W) (w_H W) mem4 mem4 TM (p + 18) T32z); [| exact (HTMPL _ _ HROD5)].
intros i Hi. cbn [length T32z] in Hi. rewrite (Heff4 i ltac:(lia)). symmetry.
apply (Hfr4 (TM + i)); pose proof Hnimg as Hni; unfold boxed in Hni; unfold STK_ctrl_lay_block, ESTACK in *; lia. }
(* the 32 bytes are kept from here on, except the three argument bytes the last copy writes *)
pose (BP := fun a => p + 18 <= a < p + 50).
assert (HBPd : forall a, BP a -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 4240 <= a < spZ regs) /\ ~ (F <= a < F + 128) /\
  ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) /\ a <> FL).
{ intros a Ha. unfold BP in Ha. pose proof HFC as HFc; unfold boxed in HFc. pose proof HBapp as HBa; unfold boxed in HBa.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold SHADOW_OFF; lia|].
  intros ->. destruct (al_frames _ _ LAWS _ _ _ _ _ cb pb HAR2 ltac:(rewrite Hfrs2; right; exact Hcbin)) as (_ & _ & Hfno & _).
  exact (proj2 (Hfno FL ltac:(fold C0; lia)) HFLown). }
assert (HBUF : forall a, BP a -> aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem4 a) by reflexivity.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr4;
  pose proof HBapp as HBa; pose proof HFC as HFc; pose proof Hnimg as Hni; unfold boxed in HBa, HFc, Hni;
  unfold STK_ctrl_lay_block, ESTACK in *; first [clear - Ha HBa HFc Hsp1 Hsplo Hsphi Hp0 Hp47 HIL HIT Hcblo Hcbhi HFq HF8lo HF8hi HCbs0 HCal8 Hwin HbufC HF4096 HFceil HJT_rng HROW_rng HFb; lia | clear - Ha HBa HFc Hni Hsp1 Hsplo Hsphi Hp0 Hp47 HIL HIT Hcblo Hcbhi HFq HF8lo HF8hi HCbs0 HCal8 Hwin HbufC HF4096 HFceil HJT_rng HROW_rng HFb; lia | lia] | exact Hpres4]
| fail]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 13%nat (mkAF 1 (2 ^ 63) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite (AG 13%nat) by lia; rewrite E13, unsigned_lit_small by (pose proof Hsrc as (_ & _ & _ & _ & Hg0' & Hg3'); lia);
rewrite Z.pow_0_r, Z.mod_1_r; pose proof Hsrc as (_ & _ & _ & _ & Hg0' & Hg3'); lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok HS.
(* the branch on g (not taken), the row's arg_len and arg_off, the trap 0x83ebc, up to __asan_memcpy at 0x83ec8 *)
paj_run_tok RUN HS HJ4 SHOK Bspan_LAY.
all: try (obl_row AG E11 E32 HZS_ROW (proj1 HJ4) B_ROW).
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk Q HQ HFr HQd AG.
upd_gk BP HBUF HFr HBPd AG.
upd_pr HPR. clear_frames.
(* the trap 0x83ebc: `not a1,s5; bltu a1,a0` with s5 = p + 18 and a0 = the row's byte +16 = 18 is taken iff
   p + 36 passes 2^64 - 1; p + 50 <= 2^47 - 8 makes it false *)
psrr_branch_tok RUN BR HS SHOK Bspan_LAY.
{ exfalso.
  lazymatch goal with Hc : branch_taken BC_LTU (sv_denot ?Ev (SAlu ALU_XOR ?x (SLit (-1)))) (sv_denot _ ?y) = true |- _ =>
  rewrite branch_ltu_U, U_not_ltb in Hc;
  rewrite (U_atom_off Ev 10 p 18) in Hc;
  [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 10%nat) by lia; exact E10 | lia | lia];
  rewrite U_SLit, (zcanon_id 18) in Hc by (unfold M64; lia);
  apply Z.ltb_lt in Hc; lia end. }
paj_run_tok RUN HS HJ4 SHOK Bspan_LAY.
1: awr_lay AG (spZ regs - sp0) (sp1 - sp0) fpos F EFA0.
upd_gk Q HQ HFr HQd AG.
upd_gk BP HBUF HFr HBPd AG.
upd_pr HPR. clear_frames. ACj1.rebaseE HS AG HEv5. clear HEv5.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?memx _ _ =>
assert (HROD6 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wx) memx))
by (eapply rod_two; [exact HJc | exact HJ4 | exact HROD]) end.
(* ---- __asan_memcpy (p + 36, g, 3) at 0x83ec8 ---- *)
prreg HS (1%bv : bv 5) R1d. prreg HS (3%bv : bv 5) R3d. prreg HS (4%bv : bv 5) R4d.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (p + 36))
(denot_atom_off Ev 10 36 p ltac:(rewrite (AG 10%nat) by lia; exact E10) ltac:(lia) ltac:(lia) ltac:(lia)) Ra0d;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 g)
(denot_atom0 Ev 13 g ltac:(rewrite (AG 13%nat) by lia; exact E13) ltac:(pose proof Hsrc as (_ & _ & _ & _ & Hg0' & Hg3'); lia)) Ra1d;
rreg_by HS (12%bv : bv 5) (Z_to_bv 64 3) (denot_lit0 Ev 3 ltac:(lia)) Ra2d;
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) (denot_atom0 Ev 60 sp1 E60 ltac:(lia)) R2d end.
pmkst HS.
pose proof Hsrc as (Hsrc1 & _).
(* g's three bytes and the shadow bytes of its frame (cid0, pos0) are kept *)
assert (HQg : forall a, g <= a < g + 3 -> Q a).
{ intros a Ha. apply (HQfr cid0 pos0 a Hgfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; fold G0; lia|].
  pose proof Hdisj as Hd; unfold boxed in Hd; lia. }
assert (HGsh : forall s, in_zr s (shadow_addr G0, fs_frame_bytes cid0 / 8) -> Q s).
{ intros s Hs. apply (HQfr cid0 pos0 s Hgfin (or_intror Hs)). intros Hb.
  pose proof (Z.mul_div_le (fs_frame_bytes cid0) 8 ltac:(lia)).
  apply (fshadow_not_app G0 (fs_frame_bytes cid0 / 8) C0 (fs_frame_bytes cb) s); [lia | lia | exact HCapp | | lia].
  unfold in_zr, shadow_addr, SHADOW_OFF in Hs; cbn [fst snd] in Hs; lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA GS___asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msY)
STK sp0 FP ly S W0 mem0 md0 ((1, fpos) :: own) lyc S2 _ k (p + 36) g 3 (sp1 - sp0) _ HJ4) end.
- rewrite Ra0d. reflexivity.
- rewrite Ra1d. reflexivity.
- rewrite Ra2d. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ at 1. rewrite R2d. rewrite unsigned_lit_small by lia. lia.
- rewrite Zminus_mod, Hsp1al16, Hsp0al. reflexivity.
- clear - Hsp1 Hwhi; lia.
- unfold STK_ctrl_lay_block, ESTACK in *; clear - Hsp1 Hwlo Hwhi; lia.
- rewrite R3d, (AG 3%nat) by lia; rewrite E3; exact Hgp.
- rewrite R4d, (AG 4%nat) by lia; rewrite E4; exact Htp.
- exact R1d.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
  + rewrite Eab. apply awr_byte_cons_own. exact (proj1 (Hwr a ltac:(lia))).
  + clear - Ha Hsp1 HbufC Hwin Hes; lia.
- unfold amem_range in Hamr |- *; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
- eapply (ra_of_kept _ _ SHADOW_OFF (p + 36) 3 (fun s => in_zr s (shadow_addr C0, fs_frame_bytes cb / 8))); [| intros x Hx; apply HBshx; lia | ].
  + intros s Hs. rewrite (HQ s (HBsh s Hs)). exact (KC4 cb pb s Hcbin (or_intror Hs)).
  + intros x Hx. apply Hbra. lia.
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cb pb (p + 36) 3 (proj1 HJ4));
  [rewrite Hfrs2; right; exact Hcbin | lia | lia | lia].
- split; [pose proof Hsrc as (_ & _ & _ & _ & Hg0' & _); lia|].
  split; [pose proof Hsrc as (_ & _ & _ & _ & _ & Hg3'); lia|].
  split.
  { intros a Ha. split.
    - rewrite (HQ a (HQg a Ha)). rewrite (KC4 cid0 pos0 a Hgfin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold G0; lia)).
      exact (proj1 (Hsrc1 a Ha)).
    - unfold spZ. rewrite R2d, unsigned_lit_small by lia. lia. }
  split; [pose proof Hdisj as Hd; unfold boxed in Hd; lia|].
  split; [pose proof Hsrc as (_ & _ & _ & Hamg & _); exact Hamg|].
  split.
  { eapply (ra_of_kept _ _ SHADOW_OFF g 3 (fun s => in_zr s (shadow_addr G0, fs_frame_bytes cid0 / 8))); [| | exact Hgra0].
    - intros s Hs. rewrite (HQ s (HGsh s Hs)). exact (KC4 cid0 pos0 s Hgfin (or_intror Hs)).
    - intros x Hx. apply shadow_in_frame; [lia | exact Hgal8 | exact HGbs8 | lia]. }
  intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W _ _ cid0 pos0 g 3 (proj1 HJ4));
  [rewrite Hfrs2; right; exact Hgfin | lia | lia | lia]. }
cbv beta.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5 & Hsame5).
upd_gk_call Q HQ Hfr5 HQd.
assert (HPR5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem5 a) by (intros a Ha; apply Hpres5; apply HPR; exact Ha).
clear HPR. rename HPR5 into HPR.
(* the 32 bytes now read lay_z ch pm v *)
assert (HLAY : garr8 SEGS (mrestrict (w_H W) mem5) (p + 18) (lay_z ch pm v)).
{ pose proof HTMPL4 as HTa. rewrite <- (firstn_skipn 18 T32z) in HTa.
  destruct (proj1 (garr8_app SEGS _ _ _ _) HTa) as (HT1 & _).
  pose proof HTMPL4 as HTb. rewrite <- (firstn_skipn 21 T32z) in HTb.
  destruct (proj1 (garr8_app SEGS _ _ _ _) HTb) as (_ & HT3).
  change (Z.of_nat (length (firstn 21 T32z))) with 21 in HT3.
  unfold lay_z. apply (proj2 (garr8_app SEGS _ _ _ _)). split.
  - eapply garr8_aview_kept; [| exact HT1]. change (Z.of_nat (length (firstn 18 T32z))) with 18.
    intros a Ha. rewrite (Hfr5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HBUF. unfold BP; lia.
  - change (Z.of_nat (length (firstn 18 T32z))) with 18. apply (proj2 (garr8_app SEGS _ _ _ _)). split.
    + eapply (garr8_aview SEGS (w_H W) (w_H W) memc mem5 g (p + 18 + 18) [ch; pm; v]); [| exact Hgarr].
      intros i Hi. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. replace (p + 18 + 18 + i) with (p + 36 + i) by lia.
      rewrite (Heff5 i ltac:(lia)).
      rewrite <- (Hfr5 (g + i) ltac:(lia) ltac:(pose proof Hdisj as Hd; unfold boxed in Hd; lia) ltac:(lia)).
      rewrite (HQ (g + i) (HQg (g + i) ltac:(lia))).
      apply (KC4 cid0 pos0 (g + i) Hgfin). left. unfold in_zr, frame_rng; cbn [fst snd]; fold G0; lia.
    + change (Z.of_nat (length [ch; pm; v])) with 3. replace (p + 18 + 18 + 3) with (p + 18 + 21) by lia.
      eapply garr8_aview_kept; [| exact HT3].
      intros a Ha. rewrite length_skipn in Ha. change (length T32z) with 32%nat in Ha.
      rewrite (Hfr5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply HBUF. unfold BP; lia. }
(* ---- the epilogue 0x83ecc .. 0x83fa8: the frame marked unusable, its flag released, the return ---- *)
reseat HS HJ5 HP5 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr5;
  pose proof HBapp as HBa; pose proof HFC as HFc; pose proof Hnimg as Hni; unfold boxed in HBa, HFc, Hni;
  unfold STK_ctrl_lay_block, ESTACK in *; first [clear - Ha HBa HFc Hsp1 Hsplo Hsphi Hp0 Hp47 HIL HIT Hcblo Hcbhi HFq HF8lo HF8hi HCbs0 HCal8 Hwin HbufC HF4096 HFceil HJT_rng HROW_rng HFb; lia | clear - Ha HBa HFc Hni Hsp1 Hsplo Hsphi Hp0 Hp47 HIL HIT Hcblo Hcbhi HFq HF8lo HF8hi HCbs0 HCal8 Hwin HbufC HF4096 HFceil HJT_rng HROW_rng HFb; lia | lia] | exact Hpres5]
| fail]).
pose proof (proj1 HJ5) as HAR5.
destruct (FFL _ _ _ _ _ 1 fpos HAR5 Hfin2) as (HFLpres5 & HFLown5 & HFLrng5). fold FL in HFLpres5, HFLown5, HFLrng5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin2) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5. change (128 / 8) with 16 in HFSpres5. fold F in HFpres5, HFSpres5.
assert (HnoF : forall a, F <= a < F + 128 -> ~ aowned B lyc S2 a) by (intros a Ha; exact (proj2 (HFpres5 a Ha))).
fs_rwF HS E529 HFSpres5.
pose proof HFLoff as HFLo; unfold boxed in HFLo.
add_flag_region HS AG E528 HFLpres5 HFLrng5 HFLown5 HnoF HnoF HnoF.
clear HFLo.
pose proof HFLrng5 as ((HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
assert (HBUF5 : forall a, BP a -> aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) mem5 a) by reflexivity.
paj_run_flag_sh RUNF HS HJ5.
- lia.
- wrange_lay AG fpos F FL.
- flag0 E528 EFA0.
- lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  upd_gk BP HBUF5 H HBPd AG; upd_gk Q HQ H HQd AG end.
  upd_pr HPR.
  clear_frames.
  prreg HS (1%bv : bv 5) R1f.
  lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
  intros matr. unfold tb_ctrl_lay_block_post.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
  exists lyc, (stack_free_state 1 fpos S2), rg, mm, mdx end.
  assert (Eabf : ablocks B lyc (stack_free_state 1 fpos S2) = ablocks B lyc Sc).
  { unfold ablocks. rewrite blocks_stack_free_state. unfold ablocks in Eab. exact Eab. }
  split.
  { rewrite R1f. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
    rewrite (AG 1%nat) by lia. rewrite E1, Hra. reflexivity. }
  split.
  { apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ5. }
  split; [apply aregs_preserved_eqs; creg HS AG EE|].
  pose proof HJ5 as (_ & _ & _ & _ & _ & Hfrsf & _ & _ & _ & _ & _ & _ & _ & Hpresf & _).
  split; [rewrite Hfrsf, HfrsC; reflexivity|].
  split; [exact Eabf|].
  split; [exact (sfs_set_fs 1 fpos S2 Sc fS2 ES2)|].
  split.
  { eapply garr8_aview_kept; [| exact HLAY]. intros a Ha.
    assert (Hlz : length (lay_z ch pm v) = 32%nat) by reflexivity. rewrite Hlz in Ha.
    apply HBUF5. unfold BP. lia. }
  (* what the call keeps, off its stack window and the 32 bytes *)
  pose proof (HFLrng) as ((HFLapp0 & HFLimg0) & (HFL40960 & HFLz0 & HFLceil0)).
  unfold tcj_kept. split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw He. cbv beta in He. unfold STK_ctrl_lay_block, ESTACK in Hw.
    assert (HQa : Q a).
    { unfold Q. split; [lia|]. split; [exact Hw|]. split; [exact He|]. split; [lia|]. split; [unfold SHADOW_OFF; lia|].
      intros ->. lia. }
    rewrite (HQ a HQa). exact (KC1 a Ha Hw).
  + intros b m i Hb Hi He. cbv beta in He.
    assert (Hb2 : In (b, m) (ablocks B lyc S2)) by (rewrite Eab; exact Hb).
    destruct (al_blocks _ _ LAWS lyc S2 W mem2 md2 b m HAR2 Hb2) as (_ & Hb4096 & Hbceil & Hbapp & Hbno & _).
    pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b m 1 fpos HAR2 Hb2 Hfin2) as Hbs.
    unfold zdisjoint in Hbs; cbn [fst snd] in Hbs. change (fs_frame_bytes 1) with 128 in Hbs. fold F in Hbs.
    assert (HQb : Q (b + i)).
    { unfold Q. split; [lia|]. split; [lia|]. split; [exact He|]. split; [lia|]. split.
      { intros Hs. apply (fshadow_not_app F 16 b (req_size m) (b + i)); [lia | lia | exact Hbapp | unfold SHADOW_OFF in Hs; lia | lia]. }
      intros Heq. apply (proj2 (Hbno (b + i) ltac:(lia))). rewrite Heq. exact HFLown. }
    rewrite (HQ (b + i) HQb). exact (KC2 b m i Hb Hi).
  + intros a Hi Ho Her.
    pose proof (Hsegs a Hi) as Hal. pose proof (pa_img_range a Hi) as Har.
    assert (HQa : Q a).
    { pose proof Hnimg as Hni; unfold boxed in Hni. pose proof HFoff as HFo; unfold boxed in HFo.
      unfold Q. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold SHADOW_OFF; lia|].
      intros ->. exact (HFLimg0 Hi). }
    rewrite (HQ a HQa). exact (KC3 a Hi Ho Her).
  + intros cid pos a Hin Hr He. cbv beta in He.
    rewrite (HQ a (HQfr cid pos a Hin Hr He)). exact (KC4 cid pos a Hin Hr).
  + intros a Ha Hw Hp. apply HPR. apply KC5; [exact Ha | unfold STK_ctrl_lay_block, ESTACK in Hw; exact Hw | exact Hp].
  + intros a Ha. apply Hpresf. unfold STK_ctrl_lay_block, ESTACK in *; lia.
Qed.
End e.
End d.
End b.

Section t.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg grant_listing}.
Variable B : asyms.
(* The contract of GrantBContracts.v (walk_ctrl_lay_block = hyps_ctrl_lay_block -> tb_ctrl_lay_block_spec), proved
   from lay_core: the hypotheses' image facts (IMG_CTRL_ROW, IMG_CTRL_LAY_JT with laystamp_numbers' slot 0x33d4) and
   the contract's image-view premises (IMG_CTRL_ROW_LAY, IMG_CTRL_TMPL) are lay_core's section hypotheses. RT_TP_FS,
   IMG_CTRL_ROW_IMG, the In (cg, pg) / g = frame + 32 pin and the stack-window disjointness premise are not needed. *)
Theorem pb_walk_ctrl_lay_block : walk_ctrl_lay_block B.
Proof.
unfold walk_ctrl_lay_block, hyps_ctrl_lay_block, tb_ctrl_lay_block_spec.
intros (HL & HTL & HTLF & HML & HSMP & HSM1 & HASF & HFFL & HTPFS & HMS & HMC & HIMGSH & HRO & HROW & HROWI & HJT).
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p g cb pb cg pg ch pm v TM
  HJc HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hal16 Hwlo Hwhi HTp HRL HTC Hfrlen
  Hp0 Hp47 Hpn0 Hamr Hnimg Hwr Hcbin Hcblo Hcbhi Hbra Hcgin Hgeq Hg0 Hsrc Hgobj Hgarr Hstkd Hdisj.
destruct HROW as (HRal & HRlo & HRhi & HRzs & _).
destruct HJT as (JE & HJE & HJTeq & HJTlo & HJThi & HJTap & HJTe).
destruct HTC as (HTlo & HThi & HTzs & _ & _ & HTg).
pose proof IMG_LO_B_val as HIL. pose proof IMG_TOP_B_val as HIT.
unfold IMG_LO, IMG_HI in HRlo, HRhi, HJTlo, HJThi, HTlo, HThi.
pose proof (f_equal (fun t => fst (fst t)) laystamp_numbers) as LN1. cbn beta in LN1. cbn [fst] in LN1. rewrite LN1 in HJTeq.
change (A_OBJ B_JT_LAY) with 267%nat in HJTeq, HJTlo, HJThi, HJTap, HJTe.
exact (@lay_core fx rc SK PI HRO B HTL HL HML HMS HMC HSM1 HSMP HASF HFFL HTLF TM JE
  ltac:(lia) ltac:(lia) HRal ltac:(lia) HJTeq HJE HJTap HRL HJTe HTg HIMGSH HRzs HTzs
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p g cb pb ch pm v
  HJc HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hal16 Hwlo Hwhi Hfrlen Hp0 Hp47 Hpn0 Hamr Hnimg Hwr Hcbin Hcblo Hcbhi Hbra
  Hg0 Hsrc Hgobj Hgarr Hdisj).
Qed.
End t.
