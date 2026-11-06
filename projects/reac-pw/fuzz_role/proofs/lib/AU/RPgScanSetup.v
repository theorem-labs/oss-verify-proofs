(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module paths changed; 468 of its 504 lines of code are new or changed and 433 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanSetup.v at a1fdf6ce036f for
   reac-pw/fuzz_rate's image A: role's pcs (E 0x8212c, O 0x821bc, MAL 0x823fc, ABS 0x82380) become rate's (0x82930,
   0x829c0, 0x82c9c, 0x82b7c), the registers are renamed as rate's code has them (pp + 0x4000 s5 -> s7, the shadow
   offset s7 -> s2, ra := -1 -> s11 := -1, n_ent t2 -> t3, s4 -> s3, s10 -> s9, the operands s11 t3 -> s10 t2), the
   real-frame cells 0x68 / 0x78 / 0x80 / 0x28 become 0xa8 / 0xb8 / 0xc0 / 0x78, the exits' kept registers are rate's
   (s6 and s10 at MAL), the cut file is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_), the list lemmas come from
   lib/A/RtPgScanKit.v, the memory facts from lib/A/RtPgMem.v and the image facts from lib/A/RtPgSteps.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgScanSetup.v at fa28558fbb17 for image B
   (fuzz_rate.asan-ubsan); image B's pcs (E 0x82aac, O 0x82b48, MAL 0x82de0, ABS 0x82d1c) and registers (a0 =
   pp + 0x4008 at E, the shadow offset in s4, rc in s10, the scan's operands s2 a7 t2 s7 s11 t0 t1 t3 s10 a2), the
   real-frame cells 0xf8 / 0x120 / 0x138 / 0x168; image B's set-up writes rc to R+0x170 and 0x4018 to R+0x138, so the
   run's regions carry two write windows and each exit's post states the written memory; the cut file is
   lib/AU/RtPgSegB.v, the list lemmas lib/AU/RtPgScanKitB.v, the model facts lib/AU/RtPgScanFB.v, the memory facts
   lib/AU/RtPgMemB.v and the image facts lib/AU/RtPgStepsB.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgScanSetupB.v at e4ef964f482f for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments are
   lib/AU/Img0.v rsegs, the cut file is lib/AU/RPgSeg.v (rsb_ -> rs_, RSB_ -> RS_, rt_ -> rl_, q_ -> e_, the hz
   cell -> rs_role_at), the kit lib/AU/RPgScanKit.v (skb_ -> sk_), the model facts lib/AU/RPgScanF.v (rkb_ ->
   rk_), the memory and image facts lib/AU/RPgMem.v and RPgSteps.v; role B's pcs (E 0x821dc, O 0x82278, MAL 0x824f8,
   ABS 0x8245c) and registers (the shadow offset s4 -> s11, rc s10 -> s9 (R+0x170 -> R+0x158), the exits' s6 / s7 /
   s10 (mask, flags, rc) -> s6 / s8 / s9 / s10 (pp, flags, rc, F), the scan's operands s2 a7 t2 s7 s11 t3 s10 ->
   s10 a7 t3 t2 s6 t4 s9, pp read into a5 instead of s7), real-frame cells (0xf8 / 0x120 / 0x138 / 0x168 -> 0xe8 /
   0xc0 / 0x120 / 0x140, F R+0x60 -> R+0x38); rate's header cells and mask have no twin. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the set-up of the inlined
   expect_role (fuzz_role.c:41-47) inside LLVMFuzzerTestOneInput (0x80020), from the cut E 0x821dc to the outer scan
   head O 0x82278, the malformed check MAL 0x824f8 or the absent check ABS 0x8245c. Proves no function (kind: segment
   lemma): lib/AU/RPgSeg.v's piece statement rs_piece_W11a_setup_stmt at image B's segments (rk_setup_B).

   THE CODE (a0 = pp + 0x4008, s1 = R, s11 = the runtime's shadow offset K, s9 = rc, the parse's answer)
     0x821dc .. 0x821e4  the instrumented check of a0 (srli, add s11, lb); 0x821e8 bnez -> 0x82700
     0x821ec  lw a1,0(a0)       pp->is_props; 0x821f0 beqz -> MAL
     0x821f4  sd s9,0x158(s1)   R+0x158 := rc
     0x821f8 .. 0x82204  a0 := pp + 0x4010; its instrumented check; 0x82208 bnez -> 0x8277c
     0x8220c  lw a0,0(a0)       pp->params_struct; 0x82210 beqz -> ABS
     0x82214 .. 0x8221c  ld a0,0xe8(s1) (the shadow index (pp + 0x4d14) >> 3 stored before E), add s11, lb;
                         0x82220 bnez -> 0x827ac
     0x82224 .. 0x82274  a2 := 0, s9 := pp->n_ent (through R+0x120 = pp + 0x4d14), a5 := pp (from R+0x140),
                         a3 := -0x3ffd (from R+0xc0) - pp, a4 := 13; s10 := pp + 0x4014, R+0x120 := 0x4018 (0x82260),
                         a7 := pp + 0x4018, t2 := pp + 0x401c, s6 := ~(pp + 0x4014), t3 := pp + 0x401c,
                         t0 := a3 - 32 = ~(pp + 0x401c), t1 := 13 << 35 = 104 << 32, t4 := 8; falls through to O.
   No call, no float instruction, no trap branch. MAL is left before the first store, ABS after the store to R+0x158;
   s6 (pp), s8 (the flags byte), s9 (rc) and s10 (F) hold at both as at E.

   HOW. su_blk is the piece as a block lemma, stated for any float state and applied at the run's own fx2. Its
   entry state holds the registers as atoms, with a0 written as pp (the extra atom 32) plus 0x4008, the four
   real-frame cells R+0xc0, R+0xe8, R+0x120, R+0x140 as one region at R (the cell R+0xe8 holding the shift of
   pp + 0x4d14 by 3, so the third check reads a shadow address of the same form as the first two) whose write
   window is R+0x120's 8 bytes, the cell R+0x158 as a second region at R that is all window, and the three fields
   as one region at pp (n_ent the extra atom 33); is_props and params_struct are split before the run, so each run
   is straight-line. The engine's shadow tokens use s11 as the shadow base and one shadow entry over the whole first
   block (atom pp, [0, 0x4d20)), paid by RPgMem.rm_blk_ra: every byte of the block is marked usable, so each of
   the three `lb` reads 0 and no `bnez` is taken. The two windows lie in the real frame below S, inside the journal's
   stack window, so the journal allows the stores. At each exit the memory is the memory at E outside the two windows
   (the run's frame), and the windows hold what the run stored (read from the last state's regions). rk_setup_B
   reads E's cut, runs su_blk and rebuilds MAL's cut (answer (None, -1), RPgScanF.rk_expect_not_props), ABS's
   (None, 0, rk_expect_no_struct, rc = 0 in R+0x158) or O's at at = 0 (rk_inv_start), the parse's answer being the
   scan's by rk_parse_expect; the cut facts at E carry over because both windows lie in hi_w2 and no other fact of a
   cut names a byte of them. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgScanF RPgScanKit.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgMem RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the code: the 39 words 0x821dc .. 0x82274 ---- *)
Definition su_tbl : ctable := build_table rsegs RS_E 39 TEmpty.
Lemma su_tbl_ok : table_ok rsegs su_tbl.
Proof. apply build_table_ok0. unfold RS_E. lia. Qed.

(* ---- the shadow base of the instrumented checks: s11 holds the runtime's shadow offset (atom 27) ---- *)
Definition su_Bx : sv := SOff 27 0.
Definition su_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the first block [pp, pp + 0x4d20), pp the extra atom 32 *)
Definition su_SH : list shent := [mkSHE 32 0 0x4d20].

(* ---- the entry state ----
   a0 (x10) = pp + 0x4008 is written as the extra atom 32 (pp) plus 0x4008; the real frame's cells R+0xc0, R+0xe8,
   R+0x120, R+0x140 (R = s1, atom 9) are chunks of a region whose write window is [0x120, 0x128), R+0x158 is a
   region that is all window, and the first block's fields is_props (pp + 0x4008), params_struct (pp + 0x4010) and
   n_ent (pp + 0x4d14) are chunks; n_ent is the extra atom 33. R+0xc0 holds -0x3ffd as its 64-bit word. *)
Definition su_ov : list (bv 5 * sv) := [((10%bv : bv 5), SOff 32 0x4008)].
Definition su_regions (ipz psz : Z) : smem :=
[ YP09.mkRegion (Some 9%nat) 0xc0 0x148 0x120 0x128
  [ YP09.mkChunk 0xc0 (CVal 8 (SLit 0xFFFFFFFFFFFFC003));
    YP09.mkChunk 0xe8 (CVal 8 (SAlu ALU_SRL (SOff 32 0x4d14) (SLit 3)));
    YP09.mkChunk 0x120 (CVal 8 (SOff 32 0x4d14));
    YP09.mkChunk 0x140 (CVal 8 (SOff 32 0)) ];
  YP09.mkRegion (Some 9%nat) 0x158 0x160 0x158 0x160 [];
  YP09.mkRegion (Some 32%nat) 0x4008 0x4d18 0 0
  [ YP09.mkChunk 0x4008 (CVal 4 (SLit ipz));
    YP09.mkChunk 0x4010 (CVal 4 (SLit psz));
    YP09.mkChunk 0x4d14 (CVal 4 (SOff 33 0)) ] ].
Definition su_facts : facts :=
mkFacts [ (9%nat, mkAF 140735332499456 140737488354816 0); (27%nat, mkAF 0x7fff8000 0x7fff8000 0); (32%nat, mkAF 4096 140737488335584 0); (33%nat, mkAF 0 32 0) ]
[] [].
Definition su_ss (ipz psz : Z) : sstate := mkSS RS_E (sk_sr su_ov) (su_regions ipz psz) None su_facts.

(* the extra atoms: slot 32 is pp, slot 33 is n_ent *)
Definition su_extra (pp nent : Z) : list word := [Z_to_bv 64 pp; Z_to_bv 64 nent].

(* ---- the registers the cuts after the set-up read and the set-up does not write ----
   O: sp, gp, tp and rs_L_chk's s0, s1, s2, s3, s4, s11; MAL and ABS: those and s6 (pp), s8 (the flags byte),
   s9 (rc), s10 (F) *)
Definition SU_KEPT_O : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 27].
Definition SU_KEPT_X : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 22; 24; 25; 26; 27].

(* ---- the walk's plumbing ---- *)
(* the two write windows lie in the journal's stack window *)
Ltac su_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
lazymatch goal with U9 : bv_unsigned (ew _ 9) = _ |- _ =>
  eapply awr_ok_cons_gen; [reflexivity | exact U9 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply RPgSteps.rl_awr_stk; lia |];
  eapply awr_ok_cons_gen; [reflexivity | exact U9 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply RPgSteps.rl_awr_stk; lia |]
end;
apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
Ltac su_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok su_tbl_ok HS HJ SHOK su_Bspan stop; [su_awr | ] end.
Ltac su_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgSteps.same_io_wvb]; kio] in kio.
(* the symbolic value of register r in the engine's last state, as a closed term *)
Ltac su_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

(* two 64-bit words are equal when their integers agree modulo 2^64 *)
Lemma su_bv_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Lemma su_w64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. intros z. apply su_bv_mod. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma su_lnot : forall x, Z.lnot x = - x - 1.
Proof. intros x. pose proof (Z.add_lnot_diag x). lia. Qed.
(* `not` (xori -1) on a 64-bit word: the bits of x flipped, which is ~x modulo 2^64 *)
Lemma su_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (Z.ones 64) = Z.lnot x mod 2 ^ 64.
Proof.
intros x Hx. rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros n Hn.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia. rewrite !Z.testbit_ones by lia.
rewrite (proj2 (Z.leb_le 0 n) Hn). cbn [andb].
destruct (Z.ltb_spec n 64) as [Hlt | Hge].
- destruct (Z.testbit x n); reflexivity.
- rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the run's frame: every byte outside the two windows is as at the run's start *)
Lemma su_frame : forall E ipz psz (H : word -> bool) (m m' : word -> option byte) R,
bv_unsigned (ew E 9) = R ->
frame_of E (ss_mem (su_ss ipz psz)) (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x120 <= a < R + 0x128) -> ~ (R + 0x158 <= a < R + 0x160) ->
aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E ipz psz H m m' R U9 HFr a Ha H1 H2. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [su_ss su_regions ss_mem In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
[rewrite U9 in Hr; lia | rewrite U9 in Hr; lia | lia].
Qed.

Section d.
Variable B : asyms.

(* the state at one exit of the set-up: the world, the journal at the exit's memory, the I/O state, the kept
   registers, what the exit computes, the memory as at E outside the two windows, and what the windows hold *)
Definition su_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (R pc : Z) (kept : list (bv 5))
(Rr : bvmap 5 word -> Prop) (Rm : (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
(forall r, In r kept -> getr regs2 r = getr regs r) /\ Rr regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x120 <= a < R + 0x128) -> ~ (R + 0x158 <= a < R + 0x160) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
Rm mem2.

Lemma su_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pc kept
(Rr : bvmap 5 word -> Prop) (Rm : (word -> option byte) -> Prop) E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k -> same_io mdc md' ->
(forall r, In r kept -> getr (ms_regs ms) r = getr regs r) -> Rr (ms_regs ms) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x120 <= a < R + 0x128) -> ~ (R + 0x158 <= a < R + 0x160) ->
 aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
Rm (ms_mem ms) ->
su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pc kept Rr Rm W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pc kept Rr Rm E' ss' ms md'
  HS Hrv Hpc HJ Hio Hk HR HK HM.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md'.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hrv) at 1; rewrite Hpc; reflexivity|].
split; [exact HJ|]. split; [exact Hio|]. split; [exact Hk|]. split; [exact HR|]. split; [exact HK | exact HM].
Qed.

(* what the run to O computes, in rs_L_scan's order: t4 = 8 (POD_STRING), s9 = n_ent, s10 = pp + 0x4014,
   a7 = pp + 0x4018, t3 = t2 = pp + 0x401c, s6 = ~(pp + 0x4014), t0 = ~(pp + 0x401c), t1 = 104 << 32, a2 = 0 (at) *)
Definition su_RO (pp nent : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 29) = w64 8 /\ getr regs2 (Z_to_bv 5 25) = w64 nent /\
getr regs2 (Z_to_bv 5 26) = w64 (pp + 0x4014) /\ getr regs2 (Z_to_bv 5 17) = w64 (pp + 0x4018) /\
getr regs2 (Z_to_bv 5 28) = w64 (pp + 0x401c) /\ getr regs2 (Z_to_bv 5 7) = w64 (pp + 0x401c) /\
getr regs2 (Z_to_bv 5 22) = w64 (Z.lnot (pp + 0x4014)) /\ getr regs2 (Z_to_bv 5 5) = w64 (Z.lnot (pp + 0x401c)) /\
getr regs2 (Z_to_bv 5 6) = w64 (104 * 2 ^ 32) /\ getr regs2 (Z_to_bv 5 12) = w64 0.

(* THE BLOCK. From E with s1 = R, s11 = K, a0 = pp + 0x4008, s9 = rc, the four real-frame cells and the three
   fields of the first block: is_props = 0 goes to MAL, params_struct = 0 to ABS (R+0x158 written), else the
   set-up runs to O (R+0x158 and R+0x120 written). *)
Lemma su_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R pp nent rcv : Z) (ip ps : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
getr regs (Z_to_bv 5 10) = w64 (pp + 0x4008) -> getr regs (Z_to_bv 5 25) = w64 rcv ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 0xFFFFFFFFFFFFC003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (Z.shiftr (pp + 0x4d14) 3) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x120) 8 (pp + 0x4d14) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 (Z.b2z ip) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 (Z.b2z ps) ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4d14) 4 nent -> 0 <= nent <= 32 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF pp 0x4d20 ->
in_app pp 0x4d20 -> 4096 <= pp -> pp + 0x4d20 <= 2 ^ 47 -> pp + 0x4d20 <= R ->
140735332499456 <= R -> R + 0x200 <= 2 ^ 47 ->
sp0 - STK <= R + 0x120 -> R + 0x160 <= sp0 ->
SRr rsegs W (cfg_at rsegs RS_E regs memc mdc)
(if ip then
   if ps then su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R RS_O SU_KEPT_O (su_RO pp nent)
     (fun m => val_mem rsegs (mrestrict (w_H W) m) (R + 0x158) 8 (rcv mod 2 ^ 64) /\
               val_mem rsegs (mrestrict (w_H W) m) (R + 0x120) 8 0x4018)
   else su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R RS_ABS SU_KEPT_X (fun _ => True)
     (fun m => val_mem rsegs (mrestrict (w_H W) m) (R + 0x158) 8 (rcv mod 2 ^ 64))
 else su_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R RS_MAL SU_KEPT_X (fun _ => True)
   (fun _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp nent rcv ip ps
HJ H9 H27 H10 H25 Vc0 Ve8 V120 V140 Vip Vps Vn Hn HRA Happ Hpp0 Hpp1 HppR HR0 HR1 HW0 HW1.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
set (E := Ereg regs (su_extra pp nent)).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (exact (eq_trans (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl) H9)).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
  by (exact (eq_trans (ew_Ereg_nat regs _ 27 (Z_to_bv 5 27) eq_refl) H27)).
assert (E25 : ew E 25 = Z_to_bv 64 rcv) by (exact (eq_trans (ew_Ereg_nat regs _ 25 (Z_to_bv 5 25) eq_refl) H25)).
assert (E32 : ew E 32 = Z_to_bv 64 pp) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 nent) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pp) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HE : forall ipz psz, (ipz = 0 \/ ipz = 1) -> (psz = 0 \/ psz = 1) ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4008) 4 ipz ->
  val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4010) 4 psz ->
  st_ok rsegs E (su_ss ipz psz) (restrict (w_H W) (mkst regs (Z_to_bv 64 RS_E) memc (seg_rom rsegs)))).
{ intros ipz psz Hi Hp Vi Vp. rewrite restrict_mkst_fx. unfold su_ss. apply (entry_st_ok_full rsegs).
  - apply sk_regs_ok. repeat constructor.
    + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
    + cbn [fst snd]. exact (eq_trans (sk_soff _ 32 pp 0x4008 E32) (eq_sym H10)).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (RPgMem.rm_rw_region rsegs E (w_H W) memc 9 R 0xc0 0x148 0x120 0x128); [exact U9 | lia | lia | |].
      { intros o Ho. apply Hpres. lia. }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val rsegs E _ R 0xc0 8 _ 0xFFFFFFFFFFFFC003); [reflexivity | | lia | exact Vc0].
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * apply (chunk_ok_val rsegs E _ R 0xe8 8 _ (Z.shiftr (pp + 0x4d14) 3)); [| | lia | exact Ve8].
        -- rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SOff, U_SLit, U32. cbn [zalu_raw].
           unfold zcanon, M64. rewrite (Z.mod_small (pp + 0x4d14)) by lia. change (3 mod 2 ^ 64) with 3.
           change (Z.land 3 63) with 3. apply Z.mod_small. rewrite Z.shiftr_div_pow2 by lia.
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        -- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
           split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
      * apply (chunk_ok_val rsegs E _ R 0x120 8 _ (pp + 0x4d14)); [apply sk_soff; exact E32 | | lia | exact V120].
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * apply (chunk_ok_val rsegs E _ R 0x140 8 _ pp); [| | lia | exact V140].
        -- rewrite (sk_soff E 32 pp 0 E32), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + apply (RPgMem.rm_rw_region rsegs E (w_H W) memc 9 R 0x158 0x160 0x158 0x160); [exact U9 | lia | lia | |].
      { intros o Ho. apply Hpres. lia. }
      apply Forall_nil.
    + apply (RPgMem.rm_ro_region rsegs E (w_H W) memc 32 pp); [exact U32 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val rsegs E _ pp 0x4008 4 _ ipz); [reflexivity | | lia | exact Vi].
        change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * apply (chunk_ok_val rsegs E _ pp 0x4010 4 _ psz); [reflexivity | | lia | exact Vp].
        change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      * apply (chunk_ok_val rsegs E _ pp 0x4d14 4 _ nent); [| | lia | exact Vn].
        -- rewrite (sk_soff E 33 nent 0 E33), Z.add_0_r. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
  - apply pairwise_disjoint_of_extents. unfold su_regions. cbn [map zpairwise_disjoint zall_disjoint].
    unfold extent_of_region, zdisj. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E.
    rewrite U9, U32. lia.
  - split; [|split; [exact I | exact I]]. cbn [su_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E9, E27, E32, E33. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    unfold SHADOW_OFF. repeat split; try lia; apply Z.mod_1_r. }
(* the three instrumented checks read the first block, every byte of which is marked usable *)
assert (SHOK : sh_ok rsegs su_Bx su_SH E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W) memc E su_Bx 32 pp 0x4d20 pp 0 0x4d20 HRA).
  - unfold su_Bx. apply U_atom; [exact E27 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E32 | lia].
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (HAE : env_agree 32 (Ereg regs (su_extra pp nent)) E) by (subst E; apply env_agree_refl).
clearbody E.
unfold cfg_at. change (w64 RS_E) with (Z_to_bv 64 RS_E).
destruct ip, ps; cbn [Z.b2z] in Vip, Vps; cbv beta iota;
pose proof (fun H1 H2 => HE _ _ H1 H2 Vip Vps) as HS; clear HE; specialize (HS ltac:(lia) ltac:(lia));
[su_run RS_O | su_run RS_ABS | su_run RS_MAL | su_run RS_MAL];
lazymatch goal with
| HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?ms)),
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply SRr_ret;
  apply (su_post_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' ss' ms _ HS eq_refl eq_refl HJ);
  [ su_io
  | lazymatch goal with |- forall r, In r ?kl -> _ =>
      intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict (w_H W) ms) regs (su_extra pp nent) kl HS HAE
        ltac:(vm_compute; reflexivity) r Hr) end
  |
  | exact (su_frame _ _ _ (w_H W) memc (ms_mem ms) R U9 HFr)
  | ];
  try exact I
end.
(* rc, stored from s9's own atom, read back from the cell R+0x158 *)
all: assert (D25 : sv_denot E (SOff 25 0) = Z_to_bv 64 (rcv mod 2 ^ 64))
  by (rewrite sk_denot0, E25; apply su_w64_mod).
- (* O: the registers *)
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    unfold su_RO; rewrite !(st_ok_restrict_reg rsegs (w_H W) E' ss' ms _ HS) end.
  repeat split; su_sv;
  lazymatch goal with
  | |- sv_denot _ (SOff 32 _) = _ => exact (sk_soff E 32 pp _ E32)
  | |- sv_denot _ (SOff 33 0) = _ => rewrite (sk_soff E 33 nent _ E33); unfold w64; f_equal; lia
  | |- sv_denot _ (SLit _) = _ => cbn [sv_denot]; apply bv_eq; vm_compute; reflexivity
  | |- sv_denot _ (SAlu ALU_SUB (SLit _) (SOff 32 ?c)) = _ =>
      (* t0 = 0 - (pp + 0x401d) = ~(pp + 0x401c) *)
      rewrite denot_lit_U, U_SAlu, U_SLit, (U_atom_off E 32 pp c E32 ltac:(lia) ltac:(lia)); cbn [zalu_raw];
      unfold w64; apply su_bv_mod; unfold zcanon, M64; rewrite Z.mod_mod by lia; rewrite Z.mod_0_l by lia;
      rewrite su_lnot; f_equal; lia
  | |- sv_denot _ (SAlu ALU_XOR (SOff 32 ?c) (SLit _)) = _ =>
      (* s6 = (pp + 0x4014) xor -1 = ~(pp + 0x4014) *)
      rewrite denot_lit_U, U_SAlu, U_SLit, (U_atom_off E 32 pp c E32 ltac:(lia) ltac:(lia)); cbn [zalu_raw];
      change (zcanon (-1)) with (Z.ones 64); unfold w64; apply su_bv_mod; rewrite su_xor_m1 by lia;
      unfold zcanon, M64; rewrite !Z.mod_mod by lia; reflexivity
  end.
- (* O: the two windows hold rc (R+0x158) and 0x4018 (R+0x120) *)
  cbv beta. split.
  + lazymatch goal with HS : st_ok _ _ ?ss _ |- _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
      lazymatch r with Some ?rg =>
        assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
        pose proof (RPgSteps.rl_region_nth _ _ _ 1 _ _ HS Hr) as Hreg end end.
    exact (sk_field_of_region _ _ _ _ _ _ _ _ _ 0x158 8 (SOff 25 0) (rcv mod 2 ^ 64) Hreg U9 ltac:(cbn; tauto) D25
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia) ltac:(cbn; lia)).
  + lazymatch goal with HS : st_ok _ _ ?ss _ |- _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
      lazymatch r with Some ?rg =>
        assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
        pose proof (RPgSteps.rl_region_nth _ _ _ 0 _ _ HS Hr) as Hreg end end.
    exact (sk_field_of_region _ _ _ _ _ _ _ _ _ 0x120 8 (SLit 0x4018) 0x4018 Hreg U9 ltac:(cbn; tauto) eq_refl
      ltac:(cbn; lia) ltac:(cbn; lia)).
- (* ABS: the window R+0x158 holds rc *)
  cbv beta.
  lazymatch goal with HS : st_ok _ _ ?ss _ |- _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch r with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
      pose proof (RPgSteps.rl_region_nth _ _ _ 1 _ _ HS Hr) as Hreg end end.
  exact (sk_field_of_region _ _ _ _ _ _ _ _ _ 0x158 8 (SOff 25 0) (rcv mod 2 ^ 64) Hreg U9 ltac:(cbn; tauto) D25
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia) ltac:(cbn; lia)).
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* membership in a concrete list of facts *)
Ltac su_in := unfold rs_L_chk; cbn [In app]; repeat (first [left; reflexivity | right]).
Ltac su_kin := first [unfold SU_KEPT_O | unfold SU_KEPT_X]; apply in_map; cbn [In]; lia.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* a list of cut facts holds at a state whose registers agree on kept and whose memory agrees on the 8 bytes of
   each of the list's cells *)
Lemma su_at_move : forall H mem mem' regs regs' e L (kept : list (bv 5)),
(forall r, In r kept -> getr regs' r = getr regs r) -> forallb (sk_locb kept) L = true ->
(forall b o v, In (LCell b o, v) L -> forall k, 0 <= k < 8 ->
  aview rsegs H mem' (rl_xv e b + o + k) = aview rsegs H mem (rl_xv e b + o + k)) ->
rs_at rsegs H mem regs e L -> rs_at rsegs H mem' regs' e L.
Proof.
intros H mem mem' regs regs' e L kept Hk Hb Hc HL.
apply (sk_at_keep H mem' regs regs' e L kept Hk Hb).
unfold rs_at in *. rewrite Forall_forall in *. intros [[r|b o] v] Hx.
- exact (HL _ Hx).
- pose proof (HL _ Hx) as Hv. cbn [rl_at fst snd] in Hv |- *.
  apply (val_mem_kept rsegs H H mem mem'); [|exact Hv].
  intros k Hk8. exact (Hc b o v Hx k Hk8).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* both windows lie in the checking segment's write ranges hi_w2: (XR, 0x120, 0x20) and (XR, 0x148, 0x18) *)
Lemma su_win_E2 : forall (cx : rs_scx rsegs) a,
(e_R (x_e cx) + 0x120 <= a < e_R (x_e cx) + 0x128) \/ (e_R (x_e cx) + 0x158 <= a < e_R (x_e cx) + 0x160) ->
rs_E2 rsegs cx a.
Proof.
intros cx a Ha. left. unfold rl_inw. cbn [hi_w2 role_himg_B].
destruct Ha as [Ha|Ha].
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rl_xv]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd rl_xv]. lia.
Qed.

(* THE PIECE: rs_piece_W11a_setup_stmt at image B's segments *)
Theorem rk_setup_B : rs_piece_W11a_setup_stmt rsegs B MT.
Proof.
unfold rs_piece_W11a_setup_stmt. intros cx POST inp Hst HO HA HM.
unfold rs_from_E. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HE.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HE as (Hbase & Hat & Hrole & Hfl & Hcorr & _).
pose proof Hbase as (Hcore & HFX & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpodin & Hpodnew).
pose proof Hcore as (HJ & H234 & Hfr & Hperm & Hio & Hmo & Hkeep).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
destruct Hst as (Hpre & _).
unfold rs_pre, rl_seg_pre in Hpre.
destruct Hpre as (HJc & _ & _ & _ & _ & HeS & _ & HRsz & HRstk & Hown & HeF & _ & _ & Hppin & _).
cbn [hi_rsz hi_cid role_himg_B] in HRsz, Hown, HeF.
set (e := x_e cx) in *.
pose proof (@alloc_ceiling_lt rc) as Hcl.
pose proof (@ASAN_CEIL_range rc) as (Hcl0 & _). unfold ASAN_CEIL in Hcl0.
unfold T_SEG_STK, ASTACK in HRstk.
(* the frame for locals: class 4, below the allocator's ceiling, its shadow too *)
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))).
{ pose proof HJc as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hown. }
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ (proj1 HJc) Hfin) as (Fm32 & Fapp & _).
rewrite <- HeF in Fm32, Fapp. change (fs_frame_bytes 4) with 1024 in Fapp.
destruct (RPgSteps.rl_fbounds (e_F e) Fm32 Fapp) as (F4096 & Fc & Fsh0 & Fshc & _).
(* the first block: live, marked usable, apart from the shadow map, below the real frame *)
assert (Hin : In (e_pp e, Layout.PP_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hppin).
assert (Hrq : req_size Layout.PP_SIZE = 0x4d20) by reflexivity.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_pp e) Layout.PP_SIZE HAR Hin) as (_ & H4096 & Hpc & Happ & _).
rewrite Hrq in Hpc, Happ.
destruct (RPgMem.rm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp e) Layout.PP_SIZE (e_pp e) 0x4d20 HAR Hin ltac:(lia)
  ltac:(rewrite Hrq; lia)) as (HRA & _).
(* the record's three fields the set-up reads *)
assert (Hb : Z.of_nat (length (buf rec)) <= Layout.POD_BUF_MAX).
{ unfold buf. unfold corrupt in Hcorr. destruct (p_corr rec); [discriminate Hcorr|].
  destruct Hwf as (_ & _ & _ & _ & H5440 & _). unfold Layout.POD_BUF_MAX. lia. }
pose proof (rk_nent_le rec Hwf) as Hn32.
assert (Hs : Forall (fun en => (length (e_body en) <= 96)%nat) (ents rec)).
{ eapply Forall_impl; [|exact (rk_ents_wf rec Hwf)]. intros en (_ & Hl & Hz). lia. }
assert (Hlp : Z.of_nat (length (pp_bytes rec)) = Layout.PP_SIZE).
{ apply Layout.length_pp_image; [first [exact Hb | unfold Layout.POD_BUF_MAX in *; lia] | exact Hn32 | exact Hs]. }
pose proof (RPgMem.rm_pp_is_props rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec)
  (corrupt rec) Hb Hn32 Hs (w_H W2) mem2 (e_pp e) Hpp) as Vip.
pose proof (RPgMem.rm_pp_params_struct rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec)
  (ents rec) (corrupt rec) Hb Hn32 Hs (w_H W2) mem2 (e_pp e) Hpp) as Vps.
pose proof (RPgMem.rm_pp_n_ent rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec)
  (corrupt rec) Hb Hn32 Hs (w_H W2) mem2 (e_pp e) Hpp) as Vn.
(* the registers and the real-frame cells at E *)
unfold rs_at_cx in Hat.
pose proof (sk_at_get _ _ _ _ _ 9 (e_R e) Hat ltac:(su_in)) as R9.
pose proof (sk_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(su_in)) as R27.
pose proof (sk_at_get _ _ _ _ _ 10 (e_pp e + 0x4008) Hat ltac:(su_in)) as R10.
pose proof (sk_at_get _ _ _ _ _ 25 (snd (rs_PA rsegs cx rec)) Hat ltac:(su_in)) as R25.
pose proof (sk_at_get _ _ _ _ _ 22 (e_pp e) Hat ltac:(su_in)) as R22.
pose proof (sk_at_get _ _ _ _ _ 24 (e_fl e) Hat ltac:(su_in)) as R24.
pose proof (sk_at_get _ _ _ _ _ 26 (e_F e) Hat ltac:(su_in)) as R26.
pose proof (sk_at_cell _ _ _ _ _ XR 0xc0 (-0x3ffd) Hat ltac:(su_in)) as Vc0.
pose proof (sk_at_cell _ _ _ _ _ XR 0xe8 (Z.shiftr (e_pp e + 0x4d14) 3) Hat ltac:(su_in)) as Ve8.
pose proof (sk_at_cell _ _ _ _ _ XR 0x120 (e_pp e + 0x4d14) Hat ltac:(su_in)) as V120.
pose proof (sk_at_cell _ _ _ _ _ XR 0x140 (e_pp e) Hat ltac:(su_in)) as V140.
cbn [rl_xv] in Vc0, Ve8, V120, V140.
assert (Hsh : 0 <= Z.shiftr (e_pp e + 0x4d14) 3 < 2 ^ 64)
  by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite Z.mod_small in Ve8 by exact Hsh. rewrite Z.mod_small in V120, V140 by lia.
change ((-0x3ffd) mod 2 ^ 64) with 0xFFFFFFFFFFFFC003 in Vc0.
(* the parse's answer is the scan's: the flags bit is 0 and the record is not corrupted *)
assert (HPA : rs_PA rsegs cx rec = rs_E0 rec)
  by (unfold rs_PA; fold e; rewrite Hfl; apply rk_parse_expect; assumption).
(* the facts every exit keeps: rs_chk_base, rs_L_chk with the cells R+0x38 and R+0x140, and the role cell, at a
   state whose memory is E's outside the two windows *)
assert (COMMON : forall regs3 mem3 md3,
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R e + 0x120 <= a < e_R e + 0x128) -> ~ (e_R e + 0x158 <= a < e_R e + 0x160) ->
   aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  @rs_chk_base fx rc SK rsegs B MT cx fx2 rec ly2 S2 W2 regs3 mem3 md3 /\
  rs_at_cx rsegs cx W2 mem3 regs3 (rs_L_chk rsegs cx ++ [(LCell XR 0x38, e_F e); (LCell XR 0x140, e_pp e)]) /\
  rs_role_at rsegs cx rec W2 mem3).
{ intros regs3 mem3 md3 HJ3 Hio3 Hk3 KM.
  assert (KL : forall a, 0 <= a < e_R e + 0x120 -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a)
    by (intros a Ha; apply KM; lia).
  split; [|split].
  - split; [|split; [exact HFX|split; [|split; [|split; [|exact (conj Hwf (conj Hlen (conj Hpod0 (conj Hpodin Hpodnew))))]]]]].
    + split; [exact HJ3|].
      split; [intros r Hr; rewrite <- (H234 r Hr); apply Hk3; cbn [In]; lia|].
      split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|].
      intros a Ha Hs' Hn. rewrite <- (Hkeep a Ha Hs' Hn).
      apply KM; [exact Ha | intros Hw; apply Hn; apply su_win_E2; left; exact Hw
                 | intros Hw; apply Hn; apply su_win_E2; right; exact Hw].
    + apply (RPgMem.rm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F e) rs_PB Hfsh).
      intros i Hi. change (length rs_PB) with 88%nat in Hi. apply KL. lia.
    + intros a Ha. rewrite <- (Hrom a Ha).
      assert (Hia : in_img rsegs a) by (destruct Ha as (sg' & Hsg' & _ & Hr'); exists sg'; split; [exact Hsg' | exact Hr']).
      pose proof (RPgSteps.rl_segs_low a Hia) as Hl. unfold kLowMemEnd in Hl. apply KL. lia.
    + apply (RPgMem.rm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp e) (pp_bytes rec) Hpp).
      intros x Hx. rewrite Hlp in Hx. apply KL. change Layout.PP_SIZE with 19744 in Hx. lia.
  - assert (Hsub : rs_at rsegs (w_H W2) mem2 regs2 e
      (rs_L_chk rsegs cx ++ [(LCell XR 0x38, e_F e); (LCell XR 0x140, e_pp e)])).
    { apply (sk_at_sub _ _ _ _ _ _ Hat). intros x Hx. apply in_app_or in Hx. apply in_or_app.
      destruct Hx as [Hx|Hx]; [left; exact Hx | right; cbn [In] in Hx |- *; tauto]. }
    unfold rs_at_cx.
    apply (su_at_move (w_H W2) mem2 mem3 regs2 regs3 e _ (map (Z_to_bv 5) [8; 9; 18; 19; 20; 27]));
      [| vm_compute; reflexivity | | exact Hsub].
    + intros r Hr. apply in_map_iff in Hr as (z & <- & Hz). apply Hk3. cbn [In] in Hz |- *. lia.
    + intros b o v Hx k Hk. unfold rs_L_chk in Hx. cbn [In app] in Hx.
      repeat (destruct Hx as [Hx|Hx]; [first [discriminate Hx | injection Hx as <- <- _; cbn [rl_xv]; apply KM; lia] |]).
      destruct Hx.
  - unfold rs_role_at in Hrole |- *. fold e in Hrole |- *.
    apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem3); [|exact Hrole].
    intros k Hk. apply KL. lia. }
eapply SRr_bind.
{ exact (su_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R e) (e_pp e) (Z.of_nat (length (ents rec)))
    (snd (rs_PA rsegs cx rec)) (is_props rec) (params_struct rec) HJ R9 R27 R10 R25 Vc0 Ve8 V120 V140 Vip Vps Vn
    ltac:(lia) HRA Happ H4096 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
intros W3 c3 _ Hpost. revert Hpost.
destruct (is_props rec) eqn:Eip; [destruct (params_struct rec) eqn:Eps|]; cbv beta iota;
intros (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk & HR & KM & HRm);
destruct (COMMON regs3 mem3 md3 HJ3 Hio3
  ltac:(intros r Hr; apply Hk; first [unfold SU_KEPT_O | unfold SU_KEPT_X]; apply in_map; cbn [In] in Hr |- *; lia) KM)
  as (Hbase3 & Hchk3 & Hrole3);
unfold rs_at_cx, rs_at in Hchk3; apply Forall_app in Hchk3 as (HL3 & HX3);
apply Forall_cons_iff in HX3 as (C38 & HX3); apply Forall_cons_iff in HX3 as (C140 & _).
- (* O: the scan starts at at = 0 *)
  destruct HR as (Q29 & Q25 & Q26 & Q17 & Q28 & Q7 & Q22 & Q5 & Q6 & Q12).
  destruct HRm as (M158 & M120).
  apply (HO fx2 ly2 S2 W2 regs3 mem3 md3 rec).
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at, rs_L_scan. cbv zeta. apply Forall_app. split; [apply Forall_app; split; [exact HL3|]|].
    - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd rl_xv].
      + exact M158.
      + change (0x4018 mod 2 ^ 64) with 0x4018. exact M120.
      + exact Q29.
      + exact Q25.
      + exact Q26.
      + exact Q17.
      + exact Q28.
      + exact Q7.
      + exact Q22.
      + exact Q5.
      + exact Q6.
      + exact C38.
      + exact C140.
    - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd]. exact Q12. }
  split; [exact Hrole3|]. split; [exact (rk_inv_start rec Eip Eps)|].
  unfold rs_chk_rec. rewrite HPA. auto.
- (* ABS: the params property's value is not a Struct, the answer is (None, 0), rc = 0 is in R+0x158 *)
  apply (HA fx2 ly2 S2 W2 regs3 mem3 md3 rec).
  assert (HPA0 : rs_PA rsegs cx rec = (None, 0)) by (rewrite HPA; exact (rk_expect_no_struct rec Eip Eps)).
  rewrite HPA0 in HRm. cbn [snd] in HRm.
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact HL3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd rl_xv].
    + exact HRm.
    + exact C38.
    + exact C140. }
  split; [exact Hrole3|]. rewrite HPA0. split; reflexivity.
- (* MAL: not an Object of Props, the answer is (None, -1) *)
  apply (HM fx2 ly2 S2 W2 regs3 mem3 md3 rec).
  assert (HPA1 : rs_PA rsegs cx rec = (None, -1)) by (rewrite HPA; exact (rk_expect_not_props rec Eip)).
  rewrite HPA1 in R25. cbn [snd] in R25.
  split; [exact Hbase3|].
  split.
  { unfold rs_at_cx, rs_at. apply Forall_app. split; [exact HL3|].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [rl_at fst snd rl_xv].
    + rewrite (Hk (Z_to_bv 5 25)) by su_kin. exact R25.
    + rewrite (Hk (Z_to_bv 5 22)) by su_kin. exact R22.
    + rewrite (Hk (Z_to_bv 5 24)) by su_kin. exact R24.
    + rewrite (Hk (Z_to_bv 5 26)) by su_kin. exact R26.
    + exact C38.
    + exact C140. }
  split; [exact Hrole3|]. rewrite HPA1. split; reflexivity.
Qed.
End e.
End c.
