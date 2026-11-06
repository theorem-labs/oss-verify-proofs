(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the head of the top loop of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x865f4 .. 0x86694: the header bytes, the cases r = 1, r = 2 and r >= 3, the 8192 clamp), from LT_LH_stmt's state to the mid point LH_M1_stmt, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment lemma from one point of the function to the next, its seed lemma cl_seedX) and A/ACbk.v (the walk through the branches). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s23.v, with its module paths, module names and numbers changed; 990 of its 1070 lines of code are new or changed and 452 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S04 of the walk of the
   test harness's entry function LLVMFuzzerTestOneInput, 0x85024 .. 0x850f4 (_s14 of the harness walk): the head of
   file turn f - the turn's three header bytes lb, len lo, len hi (fuzz_u8 / fuzz_u16, checks 4-6 at 0x85034,
   0x85070, 0x850a0), the take n' = min(len, left) (fuzz_take), memchr(p, 0, n') when n' > 0 (0x850d8, found or not
   found), n = the bytes before the NUL, and malloc(n + 1) (0x850f4) - from LT_K85024_stmt f to LT_K850f8_stmt f.
   The statement is lt_seg_S04_stmt (LLVMFuzzerTestOneInput_defs.v); the kit is LLVMFuzzerTestOneInput_s14k.v.

   THE STEPS (bottom-up):
   - s14_malloc: the malloc call (PaCall.amalloc04_sub) and the facts of K850f8 after it;
   - s14_after: 0x850dc .. 0x850f4 after memchr returned: n = a0 - p1 (found) or n' (not found), a0 = n + 1;
   - s14_memchr: the memchr call (the kit's s14_aj_memchr, interface row 20) and n = the first NUL's index;
   - s14_head: 0x85024 .. the memchr or the malloc call: the header bytes (their checks vanish by the shadow entry of
     the payload's bytes at the cursor), the take, the slot 152(s1), by the cases curn = 0, 1, 2 (s4 a literal) and
     curn >= 3 (two branches: len < left, n' = 0). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02 LLVMFuzzerTestOneInput_s10k
  LLVMFuzzerTestOneInput_s14k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the callee-saved registers a call keeps *)
Lemma s14_pres : forall regs regs2, aregs_preserved regs regs2 -> forall r, In r S14_SAVED -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 HP r Hr. cbn [S14_SAVED In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ ?rr = _ =>
      let z := eval vm_compute in (bv_unsigned rr) in
      assert (E : Z_to_bv 5 z = rr) by (apply bv_eq; reflexivity);
      rewrite <- E; apply HP; unfold acallee_saved; lia end
  | ]).
destruct Hr.
Qed.
(* a register the symbolic state names by an expression, and its value (fuzz_command _s23.v lhh_reg_U /
   lhh_reg_keep) *)
Lemma s14_reg_U : forall (regs : bvmap 5 word) (rr : bv 5) E e v,
  getr regs rr = sv_denot E e -> U E e = v -> getr regs rr = w64 v.
Proof. intros regs rr E e v H HU. rewrite H. unfold w64. rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma s14_reg_keep : forall (regs regs0 : bvmap 5 word) (rr : bv 5) E (n : nat),
  getr regs rr = sv_denot E (SOff n 0) -> ew E n = getr regs0 rr -> getr regs rr = getr regs0 rr.
Proof. intros regs regs0 rr E n H Hn. rewrite H. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* a + c - b, as the code forms it: a + c + b * (2 ^ 64 - 1) (0x850ec `sub s4,a0,s8`, 0x850f0 `addi a0,s4,1`) *)
Lemma s14_U_sub : forall E (a b : nat) ca va vb k,
  ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> 0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 ->
  0 <= va + ca - vb < 2 ^ 64 -> k mod 2 ^ 64 = 2 ^ 64 - 1 ->
  U E (SAlu ALU_ADD (SOff a ca) (SMd M_MUL (SOff b 0) (SLit k))) = va + ca - vb.
Proof.
intros E a b ca va vb k Ea Eb Ha Hb Hr Hk.
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, Ea, Eb, !unsigned_lit_small by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64. rewrite Hk, Z.add_0_r.
rewrite (Z.mod_small vb) by lia.
rewrite Z.add_mod_idemp_l by lia. rewrite Z.add_mod_idemp_r by lia.
replace (va + ca + vb * (2 ^ 64 - 1)) with ((va + ca - vb) + vb * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. exact Hr.
Qed.
(* a register of a run's last state, as the symbolic state names it (prreg without the normalisation; for a run
   that ends at a call too) *)
Ltac s14_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac s14_mdv := lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ =>
  let x := fresh "mdv" in set (x := d) in *; clearbody x end.
Ltac s14_side := first [repeat (rewrite ew_ewset_other by lia); assumption | lia].
(* a register that is still its own atom after a run: its value at the run's start (EEo names those) *)
Ltac s14_kreg HS r :=
  let P := fresh "P" in s14_prraw HS r P; apply (s14_reg_keep _ _ _ _ _ P);
  repeat (rewrite ew_ewset_other by lia);
  lazymatch goal with EEo : forall (n : nat) (rr : bv 5), _ |- _ => apply EEo end; reflexivity.
Ltac s14_keep_run HS :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [S14_KEEP In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [ lazymatch goal with |- getr _ ?rr = _ => s14_kreg HS rr end | ]);
  destruct Hr.


(* the walk's tactics of the head *)
Ltac s14_rs_side :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr]; [ first [ left; split; [reflexivity | split; reflexivity] | right; cbn; lia ] | ]);
  destruct Hr.
Ltac s14_ew := repeat (rewrite ew_ewset_other by lia).
Ltac s14_awr U9 cx :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia | ]
    | eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
      [ reflexivity | s14_ew; rewrite U9; lia | cbn; unfold STK_LLVMFuzzerTestOneInput; lia | cbn; lia | ] ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the runtime entries this segment calls, at every FP state: the malloc wrapper (fuzz_command's AMALLOC4) and the
   memchr wrapper (interface row 20, MemchrDef.amemchr_realizesM at musl memchr's constant window) *)
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, amalloc04_rule (fx := fx0) SEGS B MT.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  MemchrDef.amemchr_realizesM (fx := fx0) SEGS B memchr_loA memchr_hiA (SIG SS___interceptor_trampoline_memchr).
(* the walk hypotheses (the close discharges them at image A): memchr's window is read-only image bytes no one owns
   (the m_file group's owner's memchr_rom_fact), the listing's library facts, the meter's laws, _s10's image facts and the
   record's symbols (AR's stack-protector cells) *)
Hypothesis MCR : s14_memchr_rom SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the malloc call (0x850f4) to K850f8: the text block joins the blocks, every fact kept ---- *)
Lemma s14_malloc : forall f, LTA_K850f8 B MT f ->
  forall cx ly S (W : world SEGS) regsT memT md k acc c m,
  s14_pt B MT f cx ly S W regsT memT md k acc c m true ->
  getr regsT 10 = w64 (seg_spec.seg_txt_n (x_pl cx) f + 1) -> getr regsT 20 = w64 (seg_spec.seg_txt_n (x_pl cx) f) ->
  getr regsT 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) ->
  getr regsT 26 = w64 (seg_spec.seg_lb (x_pl cx) f) -> getr regsT 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  getr regsT 1 = Z_to_bv 64 (BASE + LO_K850f8) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_malloc)) memT (seg_rom SEGS)) md)
    (lt_post B MT cx).
Proof.
intros f HK cx ly S W regsT memT md k acc c m HP H10 H20 H24 H26 H27 H1.
destruct HP as (HB & Hfrm & Hf & (HFR & HIMG & HBL & HBUD) & HC & HM & R18 & R19 & R21 & R22 & R25 & HSL & HCM & HCNT).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
pose proof (s14_sp B MT cx HB) as (Hal0 & Hsp0 & Hs1 & Hs1a & Hs1o).
pose proof HB as (HPRE0 & HSTP0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s14_fr_bounds B MT cx ly S W memT md k HB HJ) as (Hfin & Hfa & HF4 & HFc & _).
assert (Hnf : (f < length (seg_spec.seg_files (x_pl cx)))%nat) by (unfold x_nf, seg_spec.seg_nfiles in Hf; lia).
pose proof (s14_txt_n_le (x_pl cx) f Hnf) as (Htn & Hnp & _).
assert (Hn1 : 1 <= seg_spec.seg_txt_n (x_pl cx) f + 1 <= 65536) by lia.
set (n1 := seg_spec.seg_txt_n (x_pl cx) f + 1) in *.
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
(* the meter, the events, the live bytes, the frame chain *)
pose proof (mo_malloc_mono MT MTL n1 65536 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL n1 ltac:(lia)) as M0.
pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as M2.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT n1 <= LT_U MT) by (unfold LT_U; lia).
assert (HU0 : 0 <= LT_U MT) by (unfold LT_U; lia).
assert (HR1 : 1 <= 6 + 2 * (x_nf cx - Z.of_nat f)) by lia.
assert (HRU : LT_U MT <= (6 + 2 * (x_nf cx - Z.of_nat f)) * LT_U MT) by nia.
assert (MOK : mo_ok MT S (mo_malloc MT n1)).
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT n1) MTL Hmo B4 M0). lia. }
assert (Hnev2 : st_nev S < EV_MAX) by lia.
assert (Hlv : blocks_bytes S + n1 <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly S). rewrite (bsum_perm _ _ HBL). rewrite bsum_app. cbn [bsum fold_right fst snd].
  unfold x_bl0. rewrite <- (blocks_bytes_bsum B (x_ly cx) (x_S cx)).
  unfold LIVE_LTOI, seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *. lia. }
assert (Hch : exists ch, chain_pre ly (rdW W memT) regsT ch).
{ apply chain_pre_any.
  - unfold raZ. rewrite H1, unsigned_lit_small by (unfold LO_K850f8; lia). unfold LO_K850f8; lia.
  - apply astack_rd_of_pres. apply (astack_pres_mono ly (w_H W) memT (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
    + unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. unfold STK_LLVMFuzzerTestOneInput. lia.
    + eapply astack_pres_journal; [.. | exact HJ | exact HSTP0 | ]; try exact LAWS; try exact pa_segs_low.
      intros a (r & Hr & Hlo & Hhi) Ha. exfalso. unfold ltoi_PG, longlA, A_LONGL, LONGL_N in Hr.
      cbn [In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi. lia.
  - unfold s0Z, spZ. rewrite R8, R2. unfold w64. rewrite !unsigned_lit_small by lia. lia. }
destruct Hch as [ch Hch].
assert (Hsp' : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ exact (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k n1
    (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + LO_K850f8)) ch HJ H10 ltac:(unfold MALLOC_MAX; lia) Hlv Hsp' Hs1o
    ltac:(lia) ltac:(unfold ASTACK, STK_LLVMFuzzerTestOneInput; lia) ltac:(rewrite R3; exact Hgp0)
    ltac:(rewrite R4; exact Htp0) H1 (ret_ok_codeptr_v LO_K850f8 ltac:(unfold LO_K850f8; lia) eq_refl) Hnev2 Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr2 & Hr4 & Hbl & HKp & MLE & _).
destruct HKp as (K1 & K2 & K3 & K4 & _).
pose proof (proj1 HJ2) as HAR2.
pose proof (s14_fr_bounds B MT cx ly2 S2 W2 mem2 md2 (k + 1) HB HJ2) as (Hfin2 & Hfa2 & _).
assert (Hin2 : In (res, n1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res n1 HAR2 Hin2) as (Hr16 & _ & Hrc & Hrapp & _ & Hpw & _).
pose proof (req_size_pos n1 ltac:(lia)) as [Hrq1 Hrq2].
assert (HND : ~ In (res, n1) (ablocks B ly S)).
{ rewrite Hbl in Hpw. exact (s14_pw_snoc (fun b => (fst b, req_size (snd b))) _ _ Hpw ltac:(cbn [snd]; lia)). }
pose proof (proj1 HC) as Hc. pose proof (proj1 HM) as Hm.
assert (Hc2 : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hc).
assert (Hm2 : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hm).
assert (Dc : zdisjoint (c, req_size seg_spec.SEG_C_SIZE) (res, req_size n1)).
{ apply (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 c _ res n1 HAR2 Hc2 Hin2).
  intros E. rewrite E in Hc. exact (HND Hc). }
assert (Dm : zdisjoint (m, req_size seg_spec.SEG_M_SIZE) (res, req_size n1)).
{ apply (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 m _ res n1 HAR2 Hm2 Hin2).
  intros E. rewrite E in Hm. exact (HND Hm). }
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res n1 LT_FCLS (x_fpos cx) HAR2 Hin2 Hfin2) as Df.
rewrite Hfa2 in Df. change (fs_frame_bytes LT_FCLS) with 512 in Df.
unfold zdisjoint in Dc, Dm, Df. cbn [fst snd] in Dc, Dm, Df.
assert (Hsh : 0x7fff8000 + 512 <= x_sh cx /\ x_sh cx + 64 <= 0x10007fff8000).
{ unfold x_sh, shadow_addr, SHADOW_OFF. pose proof (Z.div_le_lower_bound (x_fr cx) 8 512 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (x_fr cx) 8 0xFFFFFF00000 ltac:(lia) ltac:(lia)). lia. }
refine (HK fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT n1) c m res HB Hfrm Hf
  _ _ _ _ Hres _ _ _ _ _ _ _ _ _ _ _ HCNT).
- (* lt_core *)
  split; [|split; [|split]].
  + apply (s14_frame_kept B MT cx ly S W regsT memT md k ly2 S2 W2 regs2 mem2 md2 (k + 1) HB HFR HJ2).
    * intros r Hr. apply (s14_pres regsT regs2 HPr). cbn [In S14_SAVED] in *. tauto.
    * intros a [[[Ha1 Ha2] _] | [Ha | Ha]].
      -- apply K1; [unfold STK_LLVMFuzzerTestOneInput in *; lia | unfold ASTACK; lia].
      -- apply (K4 LT_FCLS (x_fpos cx) a Hfin); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite Hfa;
           change (fs_frame_bytes LT_FCLS) with 512; lia | cbv beta; lia].
      -- apply (K4 LT_FCLS (x_fpos cx) a Hfin); [right; unfold in_zr; cbn [fst snd]; rewrite Hfa;
           change (fs_frame_bytes LT_FCLS / 8) with 64; unfold x_sh in Ha; lia |].
         cbv beta. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hrapp. lia.
  + exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W memT) HAR2 K3 HIMG).
  + unfold lt_blocks. rewrite Hbl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
    apply perm_skip. exact HBL.
  + unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
    assert (E5 : (5 + 2 * (x_nf cx - Z.of_nat f)) * LT_U MT =
      (6 + 2 * (x_nf cx - Z.of_nat f)) * LT_U MT - LT_U MT) by ring.
    rewrite E5. lia.
- exact (s14_hblk_of B ly2 S2 W2 mem2 md2 c _ HAR2 Hc2 ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
- exact (s14_hblk_of B ly2 S2 W2 mem2 md2 m _ HAR2 Hm2 ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
- exact (s14_hblk_of B ly2 S2 W2 mem2 md2 res n1 HAR2 Hin2 ltac:(lia)).
- rewrite (s14_pres regsT regs2 HPr 18%bv) by (cbn; tauto). exact R18.
- rewrite (s14_pres regsT regs2 HPr 19%bv) by (cbn; tauto). exact R19.
- rewrite (s14_pres regsT regs2 HPr 20%bv) by (cbn; tauto). exact H20.
- rewrite (s14_pres regsT regs2 HPr 21%bv) by (cbn; tauto). exact R21.
- rewrite (s14_pres regsT regs2 HPr 22%bv) by (cbn; tauto). exact R22.
- rewrite (s14_pres regsT regs2 HPr 24%bv) by (cbn; tauto). exact H24.
- rewrite (s14_pres regsT regs2 HPr 25%bv) by (cbn; tauto). exact R25.
- rewrite (s14_pres regsT regs2 HPr 26%bv) by (cbn; tauto). exact H26.
- rewrite (s14_pres regsT regs2 HPr 27%bv) by (cbn; tauto). exact H27.
- apply (s14_slots_kept cx (rdW W memT) (rdW W2 mem2) _ HSL). intros o v Hin j Hj.
  assert (Ho : 0 <= o <= 184).
  { apply in_app_or in Hin as [Hin|Hin].
    - unfold LT_L in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; lia|]). destruct Hin.
    - destruct Hin as [Hq|[]]. injection Hq as <- _. lia. }
  apply K1; [lia | unfold ASTACK; lia].
- apply (s14_cm_kept (rdW W memT) (rdW W2 mem2) c m _ HCM); intros i Hi.
  + apply (K2 c seg_spec.SEG_C_SIZE i Hc); [pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)); lia|].
    cbv beta. pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)). lia.
  + apply (K2 m seg_spec.SEG_M_SIZE i Hm); [pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)); lia|].
    cbv beta. pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)). lia.
Qed.

(* ---- the bytes a run that writes nothing leaves (fuzz_command _s41.v aw_nowin_kept_loc) ---- *)
Lemma s14_nowin_kept : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin. cbn [windows map In] in Hin. destruct Hin.
Qed.

(* ---- the payload's bytes at the cursor and at the turn's text, at any point of the walk ---- *)
Lemma s14_cur_mem : forall f cx ly S (W : world SEGS) mem md own k O,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  lt_blocks B cx ly S O ->
  forall i, (i < length (seg_spec.seg_cur (x_pl cx) f))%nat ->
  In (x_p cx, x_n cx) (ablocks B ly S) /\ x_p cx <= x_cur cx f + Z.of_nat i < x_p cx + x_n cx /\
  rdW W mem (x_cur cx f + Z.of_nat i) = Some (nth i (seg_spec.seg_cur (x_pl cx) f) 0).
Proof.
intros f cx ly S W mem md own k O HB HJ HBL i Hi.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & Hpn & Hlen & HGA & _).
pose proof (s14_cur_len (x_pl cx) f) as HL.
destruct Hpn as [[Hn0 _] | [_ Hin0]]; [lia|].
assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hin0. }
assert (Ecur : x_cur cx f = x_p cx + x_n cx - Z.of_nat (length (seg_spec.seg_cur (x_pl cx) f)))
  by (unfold x_cur, seg_spec.seg_cur_at; lia).
split; [exact Hin|]. split; [lia|].
assert (Hj : (length (x_pl cx) - length (seg_spec.seg_cur (x_pl cx) f) + i < length (x_pl cx))%nat) by lia.
replace (x_cur cx f + Z.of_nat i)
  with (x_p cx + Z.of_nat (length (x_pl cx) - length (seg_spec.seg_cur (x_pl cx) f) + i)) by lia.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (blk_off_imgP B _ _ _ _ _ _ _ (proj1 HPRE) Hin0) as Hoff.
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq].
rewrite (F2 (x_p cx) (x_n cx) (Z.of_nat (length (x_pl cx) - length (seg_spec.seg_cur (x_pl cx) f) + i)) Hin0 Hin
  ltac:(lia)).
- unfold aview. rewrite (garr8_mbyte SEGS _ _ _ _ HGA ltac:(rewrite length_map; exact Hj)).
  rewrite (s14_cur_nth (x_pl cx) f i Hi).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite (map_nth (fun b : byte => bv_unsigned b) (x_pl cx) (Z_to_bv 8 0)).
  cbn [option_map]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- intros (r & Hr & Hlo & Hhi). unfold ltoi_PG in Hr. cbn [In] in Hr. destruct Hr as [<- | []].
  cbn [fst snd] in Hlo, Hhi. unfold off_img, longlA, A_LONGL, LONGL_N in *. lia.
Qed.
Lemma s14_tail_mem : forall f cx ly S (W : world SEGS) mem md own k O,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  lt_blocks B cx ly S O ->
  forall i, (i < length (seg_spec.seg_turn_tail (x_pl cx) f))%nat ->
  In (x_p cx, x_n cx) (ablocks B ly S) /\
  x_p cx <= seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + Z.of_nat i < x_p cx + x_n cx /\
  rdW W mem (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + Z.of_nat i) = Some (nth i (seg_spec.seg_turn_tail (x_pl cx) f) 0).
Proof.
intros f cx ly S W mem md own k O HB HJ HBL i Hi.
pose proof Hi as Hi'. rewrite s14_tail, length_skipn in Hi'.
destruct (s14_cur_mem f cx ly S W mem md own k O HB HJ HBL (3 + i) ltac:(lia)) as (Hin & Hr & Hm).
assert (E : seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + Z.of_nat i = x_cur cx f + Z.of_nat (3 + i)).
{ unfold seg_spec.seg_turn_at, x_cur, seg_spec.seg_cur_at. rewrite s14_tail, length_skipn. lia. }
rewrite E. split; [exact Hin|]. split; [exact Hr|]. rewrite Hm. rewrite s14_tail, nth_skipn_add. reflexivity.
Qed.
Lemma s14_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l. induction l as [|a l IH]; intros [|n] [|i] d Hi; cbn [firstn nth]; try reflexivity; try lia.
apply IH. lia.
Qed.

(* ---- 0x850dc .. 0x850f4, after memchr returned: n = a0 - p1 (found) or n' (not found), malloc(n + 1) ---- *)
Lemma s14_after : forall f, LTA_K850f8 B MT f ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m,
  s14_pt B MT f cx ly S W regs mem md k acc c m true ->
  getr regs 10 = (if seg_spec.seg_txt_n (x_pl cx) f <? seg_spec.seg_turn_np (x_pl cx) f
    then w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + seg_spec.seg_txt_n (x_pl cx) f) else w64 0) ->
  getr regs 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) -> getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  0 < seg_spec.seg_turn_at (x_pl cx) (x_p cx) f ->
  seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + seg_spec.seg_turn_np (x_pl cx) f < 2 ^ 63 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x3a8)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros f HK cx ly S W regs mem md k acc c m HP H10 H24 H26 H27 Hx0 Hxn.
pose proof HP as (HB & _ & Hf & ((HJ & _) & _) & _ & _ & _ & _ & _ & _ & _ & HSL & _).
pose proof (s14_sp B MT cx HB) as (_ & Hsp0 & Hs1 & _). unfold STK_LLVMFuzzerTestOneInput in Hsp0.
pose proof asan_consts as (C1 & _).
assert (Hnf : (f < length (seg_spec.seg_files (x_pl cx)))%nat) by (unfold x_nf, seg_spec.seg_nfiles in Hf; lia).
pose proof (s14_txt_n_le (x_pl cx) f Hnf) as (Htn & Hnp & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_s14b
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x3a8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s14b. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - cbn. repeat split. }
assert (SHOK : sh_ok SEGS S14x [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [])) n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
assert (E24 : ew E 24 = Z_to_bv 64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f))
  by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = Z_to_bv 64 (seg_spec.seg_turn_np (x_pl cx) f))
  by (rewrite (EEo 27%nat 27%bv eq_refl); exact H27).
assert (Hslot : forall mem2, (forall a, 0 <= a < 2 ^ 64 -> rdW W mem2 a = rdW W mem a) ->
  rdword (rdW W mem2) (x_s1 cx + 152) = Some (Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))).
{ intros mem2 Hk. rewrite (rdword_ext (rdW W mem) (rdW W mem2)).
  - apply (HSL 152 _). apply in_or_app. right. left. reflexivity.
  - intros j Hj. apply Hk. lia. }
destruct (Z.ltb_spec (seg_spec.seg_txt_n (x_pl cx) f) (seg_spec.seg_turn_np (x_pl cx) f)) as [Hlt|Hge].
- (* found: a0 = p1 + n *)
  assert (E10 : ew E 10 = Z_to_bv 64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + seg_spec.seg_txt_n (x_pl cx) f)).
  { rewrite (EEo 10%nat 10%bv eq_refl), H10. reflexivity. }
  paj_run_tok RUN HS HJ SHOK S14span.
  { apply awr_ok_nil. }
  s14_mdv.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha; exact (s14_nowin_kept _ W mem (ms_mem ms) HFr a Ha)).
  clear HF HFr HG. rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK S14span.
  + exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom _ 10 ((seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) + (seg_spec.seg_txt_n (x_pl cx) f))) in Hc by s14_side.
    rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
  + clear Hc.
    paj_run_tok RUN HS HJ SHOK S14span.
    { apply awr_ok_nil. }
    s14_mdv.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
      by (intros a Ha; rewrite <- (K1 a Ha); exact (s14_nowin_kept _ W _ (ms_mem ms) HFr a Ha)).
    pmkst HS.
    prreg HS (1%bv : bv 5) P1.
    eapply (s14_malloc f HK cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m).
    * apply (s14_pt_keep B MT IMGS BSYM f cx ly S W regs mem md k acc c m true _ _ _ true HP HJ).
      -- s14_keep_run HS.
      -- intros a Ha _. exact (K2 a Ha).
      -- intros _. exact (Hslot _ K2).
    * let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
      rewrite (s14_U_sub _ 10 24 1 ((seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) + (seg_spec.seg_txt_n (x_pl cx) f)) (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) _) by first [s14_side | reflexivity]. lia.
    * let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
      rewrite (s14_U_sub _ 10 24 0 ((seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) + (seg_spec.seg_txt_n (x_pl cx) f)) (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) _) by first [s14_side | reflexivity]. lia.
    * transitivity (getr regs 24); [s14_kreg HS (24%bv : bv 5) | exact H24].
    * transitivity (getr regs 26); [s14_kreg HS (26%bv : bv 5) | exact H26].
    * transitivity (getr regs 27); [s14_kreg HS (27%bv : bv 5) | exact H27].
    * exact P1.
- (* not found: a0 = 0, n = n' *)
  assert (Ekk : seg_spec.seg_txt_n (x_pl cx) f = seg_spec.seg_turn_np (x_pl cx) f) by lia.
  assert (E10 : ew E 10 = Z_to_bv 64 0).
  { rewrite (EEo 10%nat 10%bv eq_refl), H10. reflexivity. }
  paj_run_tok RUN HS HJ SHOK S14span.
  { apply awr_ok_nil. }
  s14_mdv.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
    by (intros a Ha; exact (s14_nowin_kept _ W mem (ms_mem ms) HFr a Ha)).
  clear HF HFr HG. rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK S14span.
  + clear Hc.
    paj_run_tok RUN HS HJ SHOK S14span.
    { apply awr_ok_nil. }
    s14_mdv.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a)
      by (intros a Ha; rewrite <- (K1 a Ha); exact (s14_nowin_kept _ W _ (ms_mem ms) HFr a Ha)).
    pmkst HS.
    prreg HS (1%bv : bv 5) P1.
    eapply (s14_malloc f HK cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m).
    * apply (s14_pt_keep B MT IMGS BSYM f cx ly S W regs mem md k acc c m true _ _ _ true HP HJ).
      -- s14_keep_run HS.
      -- intros a Ha _. exact (K2 a Ha).
      -- intros _. exact (Hslot _ K2).
    * let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
      rewrite (U_atom_off _ 27 (seg_spec.seg_turn_np (x_pl cx) f) 1) by s14_side. lia.
    * let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
      rewrite (U_atom _ 27 (seg_spec.seg_turn_np (x_pl cx) f)) by s14_side. lia.
    * transitivity (getr regs 24); [s14_kreg HS (24%bv : bv 5) | exact H24].
    * transitivity (getr regs 26); [s14_kreg HS (26%bv : bv 5) | exact H26].
    * transitivity (getr regs 27); [s14_kreg HS (27%bv : bv 5) | exact H27].
    * exact P1.
  + exfalso. rewrite branch_eq_U in Hc. rewrite (U_atom _ 10 0) in Hc by s14_side.
    rewrite U_lit in Hc by lia. cbn in Hc. discriminate Hc.
Qed.

(* ---- the memchr call (0x850d8): n is the index of the turn's first NUL, or n' ---- *)
Lemma s14_memchr : forall f, LTA_K850f8 B MT f ->
  forall cx ly S (W : world SEGS) regsT memT md k acc c m,
  s14_pt B MT f cx ly S W regsT memT md k acc c m true ->
  0 < seg_spec.seg_turn_np (x_pl cx) f ->
  getr regsT 10 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) -> getr regsT 11 = w64 0 ->
  getr regsT 12 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  getr regsT 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) ->
  getr regsT 26 = w64 (seg_spec.seg_lb (x_pl cx) f) -> getr regsT 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  getr regsT 1 = Z_to_bv 64 (BASE + 0x3a8) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) md)
    (lt_post B MT cx).
Proof.
intros f HK cx ly S W regsT memT md k acc c m HP Hnp0 H10 H11 H12 H24 H26 H27 H1.
pose proof HP as (HB & Hfrm & Hf & ((HJ & R2 & R3 & R4 & R8 & R9 & _) & HIMG & HBL & HBUD) & _ & _ & _ & _ & _ & _ & _ & HSL & _).
pose proof (proj1 HJ) as HAR.
pose proof (s14_sp B MT cx HB) as (Hal0 & Hsp0 & Hs1 & Hs1a & Hs1o).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & Hlen & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hnf : (f < length (seg_spec.seg_files (x_pl cx)))%nat) by (unfold x_nf, seg_spec.seg_nfiles in Hf; lia).
pose proof (s14_txt_n_le (x_pl cx) f Hnf) as (Htn & Hnp & Hnpt).
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
assert (Hxe0 : seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)) =
  x_p cx + x_n cx) by (unfold seg_spec.seg_turn_at; lia).
assert (Ht0 : (0 < length (seg_spec.seg_turn_tail (x_pl cx) f))%nat) by lia.
destruct (s14_tail_mem f cx ly S W memT md _ k _ HB HJ HBL 0 Ht0) as (Hin & Hx & _).
destruct (al_blocks _ _ LAWS ly S W memT md _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq].
assert (HSRC : src_ok SEGS W regsT memT (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) (seg_spec.seg_turn_np (x_pl cx) f)).
{ intros a Ha.
  destruct (s14_tail_mem f cx ly S W memT md _ k _ HB HJ HBL (Z.to_nat (a - seg_spec.seg_turn_at (x_pl cx) (x_p cx) f))
    ltac:(lia)) as (_ & _ & Hm).
  rewrite Z2Nat.id in Hm by lia. replace (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + (a - seg_spec.seg_turn_at (x_pl cx) (x_p cx) f))
    with a in Hm by lia.
  split; [rewrite Hm; discriminate|].
  unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia. }
assert (Hsp' : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ exact (s14_aj_memchr SEGS B LAWS pa_segs_low (SIG SS___interceptor_trampoline_memchr) RLO_A RHI_A (AMEMCHR fx) MCR
    W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md k (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) 0 (seg_spec.seg_turn_np (x_pl cx) f)
    (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 0x3a8))
    HJ H10 H11 H12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp' Hs1o ltac:(lia)
    ltac:(unfold ESTACK, STK_LLVMFuzzerTestOneInput; lia) ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) H1
    (ret_ok_codeptr_v 0x3a8 ltac:(lia) eq_refl) HSRC
    (amem_range_of_block SEGS B LAWS ly S W memT md (x_p cx) (x_n cx) (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) (seg_spec.seg_turn_np (x_pl cx) f) HAR Hin ltac:(lia) ltac:(lia))
    (range_addressable_of_block SEGS B LAWS ly S W memT md (x_p cx) (x_n cx) (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) (seg_spec.seg_turn_np (x_pl cx) f) HAR Hin ltac:(lia) ltac:(lia))
    (fun Hn => shadow_hull_vis_of_block SEGS B LAWS ly S W memT md (x_p cx) (x_n cx) (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) (seg_spec.seg_turn_np (x_pl cx) f) HAR Hin ltac:(lia) ltac:(lia) Hn)
    (proj1 HIMG)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & kk & -> & HJ2 & HPr & Hfb & Hres & Hkept & Hpres).
assert (Ekk : kk = seg_spec.seg_txt_n (x_pl cx) f).
{ destruct Hfb as (F1 & F2 & F3).
  unfold seg_spec.seg_txt_n. rewrite (s14_txt _ _ Hnf).
  assert (HCL : length (SegModel.cut_nul (firstn (Z.to_nat (seg_spec.seg_turn_np (x_pl cx) f))
    (seg_spec.seg_turn_tail (x_pl cx) f))) = Z.to_nat kk).
  { apply s14_cut_len.
    - rewrite length_firstn. lia.
    - intros i Hi. rewrite s14_nth_firstn by lia.
      destruct (F2 (Z.of_nat i) ltac:(lia)) as (b & Hb & Hb0).
      destruct (s14_tail_mem f cx ly S W memT md _ k _ HB HJ HBL i ltac:(lia)) as (_ & _ & Hm).
      rewrite Hm in Hb. injection Hb as <-. exact Hb0.
    - intros Hl. rewrite length_firstn in Hl. rewrite s14_nth_firstn by lia.
      pose proof (F3 ltac:(lia)) as Hz.
      destruct (s14_tail_mem f cx ly S W memT md _ k _ HB HJ HBL (Z.to_nat kk) ltac:(lia)) as (_ & _ & Hm).
      rewrite Z2Nat.id in Hm by lia. rewrite Hm in Hz. injection Hz as Hz. exact Hz. }
  rewrite HCL. lia. }
subst kk.
apply (s14_after f HK cx ly S W regs2 mem2 md2 k acc c m).
- apply (s14_pt_keep B MT IMGS BSYM f cx ly S W regsT memT md k acc c m true regs2 mem2 md2 true HP HJ2).
  + intros r Hr. apply (s14_pres regsT regs2 HPr). cbn [In S14_KEEP S14_SAVED] in *. tauto.
  + intros a Ha Hw. apply Hkept; [exact Ha|]. unfold ESTACK. lia.
  + intros _. rewrite (rdword_ext (rdW W memT) (rdW W mem2)).
    * apply (HSL 152 _). apply in_or_app. right. left. reflexivity.
    * intros j Hj. apply Hkept; [lia | unfold ESTACK; lia].
- exact Hres.
- rewrite (s14_pres regsT regs2 HPr 24%bv) by (cbn; tauto). exact H24.
- rewrite (s14_pres regsT regs2 HPr 26%bv) by (cbn; tauto). exact H26.
- rewrite (s14_pres regsT regs2 HPr 27%bv) by (cbn; tauto). exact H27.
- lia.
- lia.
Qed.

(* ===================================== the head: 0x85024 .. the memchr or the malloc call ===================================== *)
(* ---- the two ends of the head: the state at a call, from the facts of K85024 ---- *)
Lemma s14_to_malloc : forall f, LTA_K850f8 B MT f ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m regs2 mem2 md2,
  s14_pt B MT f cx ly S W regs mem md k acc c m false ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  (forall r, In r S14_KEEP -> getr regs2 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W mem2 a = rdW W mem a) ->
  rdword (rdW W mem2) (x_s1 cx + 152) = Some (Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f))) ->
  seg_spec.seg_turn_np (x_pl cx) f = 0 ->
  getr regs2 10 = w64 1 -> getr regs2 20 = w64 0 ->
  getr regs2 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) ->
  getr regs2 26 = w64 (seg_spec.seg_lb (x_pl cx) f) -> getr regs2 27 = w64 0 ->
  getr regs2 1 = Z_to_bv 64 (BASE + LO_K850f8) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (SIG SS___interceptor_trampoline_malloc)) mem2 (seg_rom SEGS)) md2)
    (lt_post B MT cx).
Proof.
intros f HK cx ly S W regs mem md k acc c m regs2 mem2 md2 HP HJ2 HR HKm H152 Hnp0 H10 H20 H24 H26 H27 H1.
pose proof HP as (HB & _ & Hf & _).
pose proof (s14_sp B MT cx HB) as (_ & Hsp0 & Hs1 & _). pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
assert (Hnf : (f < length (seg_spec.seg_files (x_pl cx)))%nat) by (unfold x_nf, seg_spec.seg_nfiles in Hf; lia).
pose proof (s14_txt_n_le (x_pl cx) f Hnf) as (Htn & Hnp & _).
assert (Htn0 : seg_spec.seg_txt_n (x_pl cx) f = 0) by lia.
apply (s14_malloc f HK cx ly S W regs2 mem2 md2 k acc c m).
- apply (s14_pt_keep B MT IMGS BSYM f cx ly S W regs mem md k acc c m false regs2 mem2 md2 true HP HJ2 HR).
  + intros a Ha Hw. apply HKm; [exact Ha | lia].
  + intros _. exact H152.
- rewrite Htn0. exact H10.
- rewrite Htn0. exact H20.
- exact H24.
- exact H26.
- rewrite Hnp0. exact H27.
- exact H1.
Qed.
Lemma s14_to_memchr : forall f, LTA_K850f8 B MT f ->
  forall cx ly S (W : world SEGS) regs mem md k acc c m regs2 mem2 md2,
  s14_pt B MT f cx ly S W regs mem md k acc c m false ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  (forall r, In r S14_KEEP -> getr regs2 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W mem2 a = rdW W mem a) ->
  rdword (rdW W mem2) (x_s1 cx + 152) = Some (Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f))) ->
  0 < seg_spec.seg_turn_np (x_pl cx) f ->
  getr regs2 10 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) -> getr regs2 11 = w64 0 ->
  getr regs2 12 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  getr regs2 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) ->
  getr regs2 26 = w64 (seg_spec.seg_lb (x_pl cx) f) -> getr regs2 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  getr regs2 1 = Z_to_bv 64 (BASE + 0x3a8) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (SIG SS___interceptor_trampoline_memchr)) mem2 (seg_rom SEGS)) md2)
    (lt_post B MT cx).
Proof.
intros f HK cx ly S W regs mem md k acc c m regs2 mem2 md2 HP HJ2 HR HKm H152 Hnp0 H10 H11 H12 H24 H26 H27 H1.
pose proof HP as (HB & _).
pose proof (s14_sp B MT cx HB) as (_ & Hsp0 & Hs1 & _). pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
apply (s14_memchr f HK cx ly S W regs2 mem2 md2 k acc c m); try assumption.
apply (s14_pt_keep B MT IMGS BSYM f cx ly S W regs mem md k acc c m false regs2 mem2 md2 true HP HJ2 HR).
- intros a Ha Hw. apply HKm; [exact Ha | lia].
- intros _. exact H152.
Qed.

(* ---- the symbolic values the head computes ---- *)
Lemma s14_U_addk : forall E a k va, U E a = va -> 0 <= k < 2 ^ 64 -> 0 <= va + k < 2 ^ 64 ->
  U E (SAlu ALU_ADD a (SLit k)) = va + k.
Proof. intros E a k va Ha Hk Hr. rewrite U_SAlu, U_SLit, Ha, (zcanon_small k) by lia. cbn [zalu_raw]. apply zcanon_small. exact Hr. Qed.
(* the u16 the code forms: hi << 8 | lo (0x850b4 .. 0x850b8) *)
Lemma s14_U_len : forall E v1 v2, ew E 34 = Z_to_bv 64 v1 -> ew E 35 = Z_to_bv 64 v2 -> 0 <= v1 < 256 -> 0 <= v2 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0)) = v1 + 256 * v2.
Proof.
intros E v1 v2 H1 H2 R1 R2.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 35 v2 H2), (U_atom E 34 v1 H1) by lia. rewrite U_lit by lia.
change (Z.land 8 63) with 8.
assert (Hs : Z.shiftl v2 8 = v2 * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (zcanon_small (Z.shiftl v2 8)) by (rewrite Hs; lia).
rewrite Z.lor_comm, (s14_or8 v1 v2) by lia. apply zcanon_small. lia.
Qed.
Lemma s14_tail_len : forall pl f,
  Z.of_nat (length (seg_spec.seg_turn_tail pl f)) = Z.max 0 (seg_spec.seg_cur_n pl f - 3).
Proof. intros pl f. rewrite s14_tail, length_skipn. unfold seg_spec.seg_cur_n. lia. Qed.
Lemma s14_turn_at : forall pl p f,
  seg_spec.seg_turn_at pl p f = seg_spec.seg_cur_at pl p f + Z.min (seg_spec.seg_cur_n pl f) 3.
Proof.
intros pl p f. unfold seg_spec.seg_turn_at, seg_spec.seg_cur_at, seg_spec.seg_cur_n. rewrite s14_tail, length_skipn. lia.
Qed.

(* ---- the seed: the state at 0x85024 is an instance of ss_s14 ---- *)
Definition s14_E (regs : bvmap 5 word) (b0 b1 b2 : Z) : env := Eimg (Ereg regs (s14_extra b0 b1 b2)).
Lemma s14_E_facts : forall regs b0 b1 b2,
  (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs b0 b1 b2) n = getr regs rr) /\
  ew (s14_E regs b0 b1 b2) 32 = Z_to_bv 64 SHADOW_OFF /\ ew (s14_E regs b0 b1 b2) 33 = Z_to_bv 64 b0 /\
  ew (s14_E regs b0 b1 b2) 34 = Z_to_bv 64 b1 /\ ew (s14_E regs b0 b1 b2) 35 = Z_to_bv 64 b2.
Proof.
intros regs b0 b1 b2. unfold s14_E. split; [|split; [|split; [|split]]].
- intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2).
- rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3).
Qed.
Lemma s14_val1 : forall H (mem : word -> option byte) a v, aview SEGS H mem a = Some v ->
  val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in *.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma s14_chunk1 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> rdW W mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (chunk_ok_val SEGS E _ base off 1 _ v);
  [cbn [sv_denot]; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
exact (s14_val1 _ _ _ _ Hrd).
Qed.
Lemma s14_seed : forall (s4 : option Z) h rlo rhi (W : world SEGS) (regs : bvmap 5 word) mem b0 b1 b2 s1 cur curn,
  0 <= h <= 3 ->
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 184 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  getr regs 24 = w64 cur -> 0 <= cur -> cur + h <= 0x7fffff800000 -> cur + h <= s1 + 152 ->
  getr regs 20 = w64 curn -> rlo <= curn <= rhi -> 0 <= curn < 2 ^ 64 ->
  (forall z, s4 = Some z -> curn = z) ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  (forall o, 152 <= o < 160 -> writable_at SEGS (mrestrict (w_H W) mem) (s1 + o)) ->
  (0 < h -> rdW W mem cur = Some b0) -> (1 < h -> rdW W mem (cur + 1) = Some b1) ->
  (2 < h -> rdW W mem (cur + 2) = Some b2) ->
  st_ok_pi SEGS VAL (s14_E regs b0 b1 b2) (ss_s14 s4 h rlo rhi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85024)) mem (seg_rom SEGS))).
Proof.
intros s4 h rlo rhi W regs mem b0 b1 b2 s1 cur curn Hh R9 Hs1lo Hs1hi Hs1a R24 Hc0 Hch Hcs R20 Hrr Hc64 Hpin
  B0 B1 B2 H176 Hwr H0 H1 H2.
destruct (s14_E_facts regs b0 b1 b2) as (EEo & E32 & E33 & E34 & E35).
remember (s14_E regs b0 b1 b2) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew E 24 = Z_to_bv 64 cur) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E20 : ew E 20 = Z_to_bv 64 curn) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = cur) by (rewrite E24; apply unsigned_lit_small; lia).
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) s14_rslot).
{ unfold YP09.region_ok, s14_rslot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ s1 176 8 (SOff 32 0) SHADOW_OFF);
    [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; unfold SHADOW_OFF; lia | cbn; lia | eapply val_mem_of_rdword; exact H176 ]. }
assert (RP : 0 < h -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) (s14_rpay h)).
{ intros Hh0. unfold YP09.region_ok, s14_rpay.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (C0 : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) cur (YP09.mkChunk 0 (CVal 1 (SOff 33 0))))
    by (apply (s14_chunk1 W mem E cur 0 33 b0 E33 B0); rewrite Z.add_0_r; exact (H0 Hh0)).
  assert (h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | ->]] by lia; unfold s14_chunks;
    [change (Z.to_nat 1) with 1%nat | change (Z.to_nat 2) with 2%nat | change (Z.to_nat 3) with 3%nat];
    cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil; try exact C0.
  + apply (s14_chunk1 W mem E cur 1 34 b1 E34 B1). exact (H1 ltac:(lia)).
  + apply (s14_chunk1 W mem E cur 1 34 b1 E34 B1). exact (H1 ltac:(lia)).
  + apply (s14_chunk1 W mem E cur 2 35 b2 E35 B2). exact (H2 ltac:(lia)). }
unfold ss_s14. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- destruct s4 as [z|].
  + specialize (Hpin z eq_refl). subst curn.
    apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
          let w := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with w end;
        cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        first [ symmetry; apply EEo; reflexivity | symmetry; apply getr_zero | exact R20 | reflexivity ]
      | ]); try (destruct Hr; fail).
  + rewrite HE. unfold s14_E, s14_sr. apply regs_ok_Eimg_Ereg.
- assert (h = 0 \/ h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | [-> | ->]]] by lia; vm_compute; reflexivity.
- unfold s14_regions. destruct (Z.eqb_spec h 0) as [->|Hh0].
  + apply Forall_cons; [exact RS | apply Forall_nil].
  + apply Forall_cons; [exact RS|]. apply Forall_cons; [exact (RP ltac:(lia)) | apply Forall_nil].
- unfold s14_regions. destruct (Z.eqb_spec h 0) as [->|Hh0].
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [s14_rslot s14_rpay YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24.
    repeat split; try exact I; lia.
- split; [|split; [exact I | exact I]].
  cbn [s14_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U24, E20, E32, E33, E34, E35.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the shadow entry of the header bytes: they lie in the payload's live block *)
Lemma s14_shok : forall ly S (W : world SEGS) mem md E p n cur h,
  AR SEGS B ly S W mem md -> (0 < h -> In (p, n) (ablocks B ly S)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 24 = Z_to_bv 64 cur ->
  p <= cur -> 0 <= h -> cur + h <= p + n ->
  sh_ok SEGS S14x (s14_SH h) E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E p n cur h HAR Hin E32 E24 Hpc Hh Hch.
unfold sh_ok, s14_SH. destruct (Z.eqb_spec h 0) as [->|Hh0]; [apply Forall_nil|].
specialize (Hin ltac:(lia)).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hceil & Happ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range SEGS (w_H W) mem E S14x 24 cur h cur 0 h).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md p n); [exact HAR | exact Hin | lia | lia].
- unfold S14x. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia). reflexivity.
- rewrite (U_atom E 24 cur E24) by lia. reflexivity.
- lia.
- lia.
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

(* the bytes a run leaves: all but the slot 152 window of s1 *)
Lemma s14_keep_slot : forall E rs (W : world SEGS) (m m' : word -> option byte) s1,
  bv_unsigned (ew E 9) = s1 ->
  (forall r, In r rs ->
    (YP09.r_base r = Some 9%nat /\ YP09.r_wlo r = 152 /\ YP09.r_whi r = 160) \/ YP09.r_whi r <= YP09.r_wlo r) ->
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 152 <= a < s1 + 160) -> rdW W m' a = rdW W m a.
Proof.
intros E rs W m m' s1 H9 Hrs HF a Ha Hna.
apply (kept_of_frame (segs:=SEGS) E rs (w_H W) m m' (fun x => s1 + 152 <= x < s1 + 160) HF); [|exact Ha|exact Hna].
intros b wlo whi a' Hin Ha'. unfold windows in Hin. apply in_map_iff in Hin as (r & Hr & Hin).
injection Hr as <- <- <-. destruct (Hrs r Hin) as [(Hb & Hlo & Hhi) | Hro].
- rewrite Hb, Hlo, Hhi in Ha'. cbn [base_val] in Ha'. rewrite H9 in Ha'. exact Ha'.
- lia.
Qed.
(* the slot 152 of s1 a state's first region holds *)
Lemma s14_slot_of_region : forall E (W : world SEGS) ms s1 cs lo hi wlo whi e v,
  YP09.region_ok SEGS E (mrestrict (w_H W) ms) (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = s1 -> In (YP09.mkChunk 152 (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> rdword (rdW W ms) (s1 + 152) = Some v.
Proof.
intros E W ms s1 cs lo hi wlo whi e v HR H9 Hin He Hv.
apply (rdword_of_val_mem SEGS); [|exact Hv].
exact (field_of_region E _ 9 s1 cs lo hi wlo whi 152 8 e v HR H9 Hin He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* the slot 152 of s1 a state at a call holds: the state's first region, chunk 152 *)
Ltac s14_slot HS U9 e v :=
  let RG := fresh "RG" in
  epose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG; cbn [ms_mem restrict] in RG;
  apply (s14_slot_of_region _ _ _ _ _ _ _ _ _ e v RG);
  [ s14_ew; exact U9 | cbn [In]; first [left; reflexivity | right; left; reflexivity] | | ].

(* ---- the head: 0x85024 .. the memchr call (0x850d8) or the malloc call (0x850f4) ---- *)
Lemma s14_head : forall f, LTA_K850f8 B MT f -> LT_K85024_stmt B MT f.
Proof.
intros f HK cx ly S W regs mem md k acc c m HB Hfrm Hf HCORE HC HM R18 R19 R20 R21 R22 R24 R25 HSL HCM HCNT.
assert (HP : s14_pt B MT f cx ly S W regs mem md k acc c m false).
{ refine (conj HB (conj Hfrm (conj Hf (conj HCORE (conj HC (conj HM (conj R18 (conj R19 (conj R21 (conj R22
    (conj R25 (conj _ (conj HCM HCNT))))))))))))).
  intros o v Hin. apply HSL. apply in_app_or in Hin as [Hin|Hin]; [exact Hin | destruct Hin]. }
pose proof HCORE as ((HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H176 & _) & _ & HBL & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (s14_sp B MT cx HB) as (Hal0 & Hsp0 & Hs1 & Hs1a & Hs1o).
unfold STK_LLVMFuzzerTestOneInput in Hsp0.
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & Hlen & _).
assert (Hnf : (f < length (seg_spec.seg_files (x_pl cx)))%nat) by (unfold x_nf, seg_spec.seg_nfiles in Hf; lia).
pose proof (s14_cur_len (x_pl cx) f) as HCL.
assert (Ecu : x_cur cx f + x_curn cx f = x_p cx + x_n cx)
  by (unfold x_cur, x_curn, seg_spec.seg_cur_at, seg_spec.seg_cur_n; lia).
assert (Hcn0 : 0 <= x_curn cx f <= x_n cx) by (unfold x_curn, seg_spec.seg_cur_n; lia).
assert (Hcb : 0 <= x_cur cx f /\ x_cur cx f + x_curn cx f <= alloc_ceiling /\ x_curn cx f < 2 ^ 26 /\
  x_p cx <= x_cur cx f).
{ destruct Hpn as [[Hn0 Hpe] | [Hn Hin0]].
  - unfold emptyA in Hpe. lia.
  - assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HBL)); apply in_or_app; right; exact Hin0).
    destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
    pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq]. lia. }
assert (Hwr : forall o, 152 <= o < 160 -> writable_at SEGS (mrestrict (w_H W) mem) (x_s1 cx + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; unfold STK_LLVMFuzzerTestOneInput; lia).
(* the turn's quantities in the cursor's bytes *)
pose proof (s14_lb (x_pl cx) f Hnf) as HLB.
pose proof (s14_len16 (x_pl cx) f) as HLEN.
pose proof (s14_np (x_pl cx) f) as HNP. rewrite HLEN, s14_tail_len in HNP.
pose proof (s14_tail_len (x_pl cx) f) as HTL.
pose proof (s14_turn_at (x_pl cx) (x_p cx) f) as HTA.
change (seg_spec.seg_cur_n (x_pl cx) f) with (x_curn cx f) in HNP, HTL, HTA.
change (seg_spec.seg_cur_at (x_pl cx) (x_p cx) f) with (x_cur cx f) in HTA.
pose proof (s14_cur_byte (x_pl cx) f 0) as B0. pose proof (s14_cur_byte (x_pl cx) f 1) as B1.
pose proof (s14_cur_byte (x_pl cx) f 2) as B2.
assert (HM0 : 0 < x_curn cx f -> rdW W mem (x_cur cx f) = Some (nth 0 (seg_spec.seg_cur (x_pl cx) f) 0)).
{ intros H. pose proof (proj2 (proj2 (s14_cur_mem f cx ly S W mem md _ k _ HB HJ HBL 0
    ltac:(unfold x_curn, seg_spec.seg_cur_n in H; lia)))) as Hm.
  rewrite <- (Z.add_0_r (x_cur cx f)). exact Hm. }
assert (HM1 : 1 < x_curn cx f -> rdW W mem (x_cur cx f + 1) = Some (nth 1 (seg_spec.seg_cur (x_pl cx) f) 0)).
{ intros H. exact (proj2 (proj2 (s14_cur_mem f cx ly S W mem md _ k _ HB HJ HBL 1
    ltac:(unfold x_curn, seg_spec.seg_cur_n in H; lia)))). }
assert (HM2 : 2 < x_curn cx f -> rdW W mem (x_cur cx f + 2) = Some (nth 2 (seg_spec.seg_cur (x_pl cx) f) 0)).
{ intros H. exact (proj2 (proj2 (s14_cur_mem f cx ly S W mem md _ k _ HB HJ HBL 2
    ltac:(unfold x_curn, seg_spec.seg_cur_n in H; lia)))). }
assert (HIN : 0 < x_curn cx f -> In (x_p cx, x_n cx) (ablocks B ly S)).
{ intros H. exact (proj1 (s14_cur_mem f cx ly S W mem md _ k _ HB HJ HBL 0
    ltac:(unfold x_curn, seg_spec.seg_cur_n in H; lia))). }
assert (Hb0z : x_curn cx f = 0 -> nth 0 (seg_spec.seg_cur (x_pl cx) f) 0 = 0).
{ intros H. apply nth_overflow. unfold x_curn, seg_spec.seg_cur_n in H. lia. }
clear HCL.
remember (nth 0 (seg_spec.seg_cur (x_pl cx) f) 0) as b0 eqn:Eb0.
remember (nth 1 (seg_spec.seg_cur (x_pl cx) f) 0) as b1 eqn:Eb1.
remember (nth 2 (seg_spec.seg_cur (x_pl cx) f) 0) as b2 eqn:Eb2.
remember (x_curn cx f) as cn eqn:Ecn. remember (x_cur cx f) as cu eqn:Ecu'.
clear Eb0 Eb1 Eb2.
destruct (s14_E_facts regs b0 b1 b2) as (EEo & E32 & E33 & E34 & E35).
assert (E9 : ew (s14_E regs b0 b1 b2) 9 = Z_to_bv 64 (x_s1 cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew (s14_E regs b0 b1 b2) 24 = Z_to_bv 64 cu) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E20 : ew (s14_E regs b0 b1 b2) 20 = Z_to_bv 64 cn) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
assert (U9 : bv_unsigned (ew (s14_E regs b0 b1 b2) 9) = x_s1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM (s14_E regs b0 b1 b2)) by apply Eimg_env.
unfold cfg_at. change (w64 (BASE + LO_K85024)) with (Z_to_bv 64 (BASE + LO_K85024)).
assert (Hcases : cn = 0 \/ cn = 1 \/ cn = 2 \/ 3 <= cn) by lia.
destruct Hcases as [Hc0 | [Hc1 | [Hc2 | Hc3]]].
- (* no byte left: lb = 0, len = 0, n' = 0 *)
  pose proof (s14_seed (Some 0) 0 0 0 W regs mem b0 b1 b2 (x_s1 cx) cu cn ltac:(lia) R9 ltac:(lia) ltac:(lia) Hs1a
    R24 ltac:(lia) ltac:(lia) ltac:(lia) R20 ltac:(lia) ltac:(lia) ltac:(intros z Hz; injection Hz as <-; lia)
    B0 B1 B2 H176 Hwr ltac:(intros; lia) ltac:(intros; lia) ltac:(intros; lia)) as HS.
  pose proof (s14_shok ly S W mem md (s14_E regs b0 b1 b2) (x_p cx) (x_n cx) cu 0 HAR ltac:(intros; first [lia | apply HIN; lia])
    E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
  remember (s14_E regs b0 b1 b2) as E eqn:HE.
  paj_run_tok RUN HS HJ SHOK S14span.
  { s14_awr U9 cx. }
  s14_mdv.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (refine (s14_keep_slot _ _ _ mem (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]).
  pmkst HS. prreg HS (1%bv : bv 5) P1.
  apply (s14_to_malloc f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
  + s14_keep_run HS.
  + exact K1.
  + rewrite HTL. replace (Z.max 0 (cn - 3)) with 0 by lia. s14_slot HS U9 (SLit 0) 0; [reflexivity | lia].
  + rewrite HNP. lia.
  + let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite (U_atom_off _ 24 cu 0) by s14_side. lia.
  + rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. rewrite (Hb0z Hc0). reflexivity.
  + let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + exact P1.
- (* one byte left: lb, len = 0, n' = 0 *)
  pose proof (s14_seed (Some 1) 1 1 1 W regs mem b0 b1 b2 (x_s1 cx) cu cn ltac:(lia) R9 ltac:(lia) ltac:(lia) Hs1a
    R24 ltac:(lia) ltac:(lia) ltac:(lia) R20 ltac:(lia) ltac:(lia) ltac:(intros z Hz; injection Hz as <-; lia)
    B0 B1 B2 H176 Hwr ltac:(intros; apply HM0; lia) ltac:(intros; lia) ltac:(intros; lia)) as HS.
  pose proof (s14_shok ly S W mem md (s14_E regs b0 b1 b2) (x_p cx) (x_n cx) cu 1 HAR ltac:(intros; first [lia | apply HIN; lia])
    E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
  remember (s14_E regs b0 b1 b2) as E eqn:HE.
  paj_run_tok RUN HS HJ SHOK S14span.
  { s14_awr U9 cx. }
  s14_mdv.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (refine (s14_keep_slot _ _ _ mem (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]).
  pmkst HS. prreg HS (1%bv : bv 5) P1.
  apply (s14_to_malloc f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
  + s14_keep_run HS.
  + exact K1.
  + rewrite HTL. replace (Z.max 0 (cn - 3)) with 0 by lia. s14_slot HS U9 (SLit 0) 0; [reflexivity | lia].
  + rewrite HNP. lia.
  + let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite (U_atom_off _ 24 cu 1) by s14_side. lia.
  + rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite (U_atom _ 33 b0) by s14_side. reflexivity.
  + let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + exact P1.
- (* two bytes left: lb, len = byte 1, n' = 0 *)
  pose proof (s14_seed (Some 2) 2 2 2 W regs mem b0 b1 b2 (x_s1 cx) cu cn ltac:(lia) R9 ltac:(lia) ltac:(lia) Hs1a
    R24 ltac:(lia) ltac:(lia) ltac:(lia) R20 ltac:(lia) ltac:(lia) ltac:(intros z Hz; injection Hz as <-; lia)
    B0 B1 B2 H176 Hwr ltac:(intros; apply HM0; lia) ltac:(intros; apply HM1; lia) ltac:(intros; lia)) as HS.
  pose proof (s14_shok ly S W mem md (s14_E regs b0 b1 b2) (x_p cx) (x_n cx) cu 2 HAR ltac:(intros; first [lia | apply HIN; lia])
    E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
  remember (s14_E regs b0 b1 b2) as E eqn:HE.
  paj_run_tok RUN HS HJ SHOK S14span.
  { s14_awr U9 cx. }
  s14_mdv.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (refine (s14_keep_slot _ _ _ mem (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]).
  pmkst HS. prreg HS (1%bv : bv 5) P1.
  apply (s14_to_malloc f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
  + s14_keep_run HS.
  + exact K1.
  + rewrite HTL. replace (Z.max 0 (cn - 3)) with 0 by lia. s14_slot HS U9 (SLit 0) 0; [reflexivity | lia].
  + rewrite HNP. lia.
  + let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite (U_atom_off _ 24 cu 2) by s14_side. lia.
  + rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite (U_atom _ 33 b0) by s14_side. reflexivity.
  + let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
    rewrite U_lit by lia. reflexivity.
  + exact P1.
- (* three bytes or more: lb, len, n' = min(len, cn - 3) *)
  pose proof (s14_seed None 3 3 (2 ^ 26) W regs mem b0 b1 b2 (x_s1 cx) cu cn ltac:(lia) R9 ltac:(lia) ltac:(lia) Hs1a
    R24 ltac:(lia) ltac:(lia) ltac:(lia) R20 ltac:(lia) ltac:(lia) ltac:(intros z Hz; discriminate Hz)
    B0 B1 B2 H176 Hwr ltac:(intros; apply HM0; lia) ltac:(intros; apply HM1; lia) ltac:(intros; apply HM2; lia)) as HS.
  pose proof (s14_shok ly S W mem md (s14_E regs b0 b1 b2) (x_p cx) (x_n cx) cu 3 HAR ltac:(intros; apply HIN; lia)
    E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)) as SHOK.
  remember (s14_E regs b0 b1 b2) as E eqn:HE.
  paj_run_tok RUN HS HJ SHOK S14span.
  { s14_awr U9 cx. }
  s14_mdv.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (refine (s14_keep_slot _ _ _ mem (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]).
  clear HF HFr HG. rename ms into ms1.
  psrr_branch_tok RUN BR HS SHOK S14span.
  + (* len < cn - 3: n' = len *)
    assert (Hlt : b1 + 256 * b2 < cn - 3).
    { rewrite branch_ltu_U in Hc. rewrite (s14_U_len _ b1 b2) in Hc by s14_side.
      rewrite (U_atom_off _ 20 cn (-3)) in Hc by s14_side. apply Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK S14span.
    { s14_awr U9 cx. }
    s14_mdv.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a).
      { intros a Ha Hw. rewrite <- (K1 a Ha Hw). revert a Ha Hw.
        refine (s14_keep_slot _ _ _ _ (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]. }
    clear HF HFr HG. rename ms into ms2.
    psrr_branch_tok RUN BR HS SHOK S14span.
    * (* len = 0: malloc(1) *)
      assert (Hl0 : b1 + 256 * b2 = 0).
      { rewrite branch_eq_U in Hc. rewrite (s14_U_len _ b1 b2) in Hc by s14_side. rewrite U_lit in Hc by lia.
        apply Z.eqb_eq in Hc. exact Hc. }
      clear Hc.
      paj_run_tok RUN HS HJ SHOK S14span.
      { s14_awr U9 cx. }
      s14_mdv.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a).
      { intros a Ha Hw. rewrite <- (K2 a Ha Hw). revert a Ha Hw.
        refine (s14_keep_slot _ _ _ _ (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]. }
      pmkst HS. prreg HS (1%bv : bv 5) P1.
      apply (s14_to_malloc f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
      -- s14_keep_run HS.
      -- exact K3.
      -- rewrite HTL. replace (Z.max 0 (cn - 3)) with (cn - 3) by lia. s14_slot HS U9 (SOff 20 (-3)) (cn - 3).
         ++ cbn [sv_denot]. s14_ew. rewrite E20, unsigned_lit_small by lia. reflexivity.
         ++ lia.
      -- rewrite HNP. lia.
      -- let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (s14_U_addk _ _ 1 0); [reflexivity | | lia | lia].
         rewrite (s14_U_addk _ _ 0 0); [reflexivity | | lia | lia].
         rewrite (s14_U_len _ b1 b2) by s14_side. exact Hl0.
      -- let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (s14_U_addk _ _ 0 0); [reflexivity | | lia | lia].
         rewrite (s14_U_len _ b1 b2) by s14_side. exact Hl0.
      -- rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 24 cu 3) by s14_side. lia.
      -- rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom _ 33 b0) by s14_side. reflexivity.
      -- let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (s14_U_len _ b1 b2) by s14_side. exact Hl0.
      -- exact P1.
    * (* len > 0: memchr(p1, 0, len) *)
      assert (Hl0 : b1 + 256 * b2 <> 0).
      { rewrite branch_eq_U in Hc. rewrite (s14_U_len _ b1 b2) in Hc by s14_side. rewrite U_lit in Hc by lia.
        apply Z.eqb_neq in Hc. exact Hc. }
      clear Hc.
      paj_run_tok RUN HS HJ SHOK S14span.
      { s14_awr U9 cx. }
      s14_mdv.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a).
      { intros a Ha Hw. rewrite <- (K2 a Ha Hw). revert a Ha Hw.
        refine (s14_keep_slot _ _ _ _ (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]. }
      pmkst HS. prreg HS (1%bv : bv 5) P1.
      apply (s14_to_memchr f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
      -- s14_keep_run HS.
      -- exact K3.
      -- rewrite HTL. replace (Z.max 0 (cn - 3)) with (cn - 3) by lia. s14_slot HS U9 (SOff 20 (-3)) (cn - 3).
         ++ cbn [sv_denot]. s14_ew. rewrite E20, unsigned_lit_small by lia. reflexivity.
         ++ lia.
      -- rewrite HNP. lia.
      -- rewrite HTA. let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 24 cu 3) by s14_side. lia.
      -- let P := fresh "P" in s14_prraw HS (11%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite U_lit by lia. reflexivity.
      -- rewrite HNP. let P := fresh "P" in s14_prraw HS (12%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (s14_U_addk _ _ 0 (b1 + 256 * b2)); [lia | | lia | lia].
         rewrite (s14_U_len _ b1 b2) by s14_side. reflexivity.
      -- rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 24 cu 3) by s14_side. lia.
      -- rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom _ 33 b0) by s14_side. reflexivity.
      -- rewrite HNP. let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (s14_U_len _ b1 b2) by s14_side. lia.
      -- exact P1.
  + (* len >= cn - 3: n' = cn - 3 *)
    assert (Hge : cn - 3 <= b1 + 256 * b2).
    { rewrite branch_ltu_U in Hc. rewrite (s14_U_len _ b1 b2) in Hc by s14_side.
      rewrite (U_atom_off _ 20 cn (-3)) in Hc by s14_side. apply Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK S14span.
    { s14_awr U9 cx. }
    s14_mdv.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a).
      { intros a Ha Hw. rewrite <- (K1 a Ha Hw). revert a Ha Hw.
        refine (s14_keep_slot _ _ _ _ (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]. }
    clear HF HFr HG. rename ms into ms2.
    psrr_branch_tok RUN BR HS SHOK S14span.
    * (* cn = 3: malloc(1) *)
      assert (Hl0 : cn = 3).
      { rewrite branch_eq_U in Hc. rewrite (U_atom_off _ 20 cn (-3)) in Hc by s14_side. rewrite U_lit in Hc by lia.
        apply Z.eqb_eq in Hc. lia. }
      clear Hc.
      paj_run_tok RUN HS HJ SHOK S14span.
      { s14_awr U9 cx. }
      s14_mdv.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a).
      { intros a Ha Hw. rewrite <- (K2 a Ha Hw). revert a Ha Hw.
        refine (s14_keep_slot _ _ _ _ (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]. }
      pmkst HS. prreg HS (1%bv : bv 5) P1.
      apply (s14_to_malloc f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
      -- s14_keep_run HS.
      -- exact K3.
      -- rewrite HTL. replace (Z.max 0 (cn - 3)) with (cn - 3) by lia. s14_slot HS U9 (SOff 20 (-3)) (cn - 3).
         ++ cbn [sv_denot]. s14_ew. rewrite E20, unsigned_lit_small by lia. reflexivity.
         ++ lia.
      -- rewrite HNP. lia.
      -- let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 20 cn (-2)) by s14_side. lia.
      -- let P := fresh "P" in s14_prraw HS (20%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 20 cn (-3)) by s14_side. lia.
      -- rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 24 cu 3) by s14_side. lia.
      -- rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom _ 33 b0) by s14_side. reflexivity.
      -- let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 20 cn (-3)) by s14_side. lia.
      -- exact P1.
    * (* cn > 3: memchr(p1, 0, cn - 3) *)
      assert (Hl0 : cn <> 3).
      { rewrite branch_eq_U in Hc. rewrite (U_atom_off _ 20 cn (-3)) in Hc by s14_side. rewrite U_lit in Hc by lia.
        apply Z.eqb_neq in Hc. lia. }
      clear Hc.
      paj_run_tok RUN HS HJ SHOK S14span.
      { s14_awr U9 cx. }
      s14_mdv.
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W (ms_mem ms) a = rdW W mem a).
      { intros a Ha Hw. rewrite <- (K2 a Ha Hw). revert a Ha Hw.
        refine (s14_keep_slot _ _ _ _ (ms_mem ms) _ _ _ HFr); [s14_ew; exact U9 | s14_rs_side]. }
      pmkst HS. prreg HS (1%bv : bv 5) P1.
      apply (s14_to_memchr f HK cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) _ HP HJ).
      -- s14_keep_run HS.
      -- exact K3.
      -- rewrite HTL. replace (Z.max 0 (cn - 3)) with (cn - 3) by lia. s14_slot HS U9 (SOff 20 (-3)) (cn - 3).
         ++ cbn [sv_denot]. s14_ew. rewrite E20, unsigned_lit_small by lia. reflexivity.
         ++ lia.
      -- rewrite HNP. lia.
      -- rewrite HTA. let P := fresh "P" in s14_prraw HS (10%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 24 cu 3) by s14_side. lia.
      -- let P := fresh "P" in s14_prraw HS (11%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite U_lit by lia. reflexivity.
      -- rewrite HNP. let P := fresh "P" in s14_prraw HS (12%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 20 cn (-3)) by s14_side. lia.
      -- rewrite HTA. let P := fresh "P" in s14_prraw HS (24%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 24 cu 3) by s14_side. lia.
      -- rewrite HLB. let P := fresh "P" in s14_prraw HS (26%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom _ 33 b0) by s14_side. reflexivity.
      -- rewrite HNP. let P := fresh "P" in s14_prraw HS (27%bv : bv 5) P; apply (s14_reg_U _ _ _ _ _ P).
         rewrite (U_atom_off _ 20 cn (-3)) by s14_side. lia.
      -- exact P1.
Qed.

(* ===================================== the segment ===================================== *)
Theorem lt_seg_S04 : lt_seg_S04_stmt B MT.
Proof. unfold lt_seg_S04_stmt. exact s14_head. Qed.

End e.
End f.
End d.
Print Assumptions lt_seg_S04.
