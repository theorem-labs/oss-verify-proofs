(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   entry to the memchr call 0x86ef8 (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/A/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ef8; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths, module names and numbers changed; 492 of its 627 lines of code are new or changed and 392 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140): the first half of the
   segment S_MF_ENTRY of m_file's image-B walk, from the entry 0x86140 to the snprintf return 0x862ac, against the
   cut statements of lib/B/Prog/m_file_m.v (MF_ENTRY_stmt) and lib/B/Prog/mf_entry_d.v (MFE_MID_F). A walk lane of the image-B m_file-family owner's G2B (a sub-lane).
   proves no function (kind: segment lemma; the half 0x86140 -> 0x862ac of S_MF_ENTRY in m_file's image-B walk).

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 2-77, 0x86140-0x8626c, and the trap 0x86e84):
     0x86140 addi sp,sp,-320; 0x86144 the probe store sd zero,0(sp); 0x86148-0x86178 the saves ra, s0 .. s11 at
     sp0 - 8 .. sp0 - 104; 0x8617c s0 = sp0; 0x86180/0x86184 s1 = (sp0 - 320) & -32; s6 = a2 (the label), s10 = a1
     (the text), s9 = a0 (c); the two GOT reads (listing objects A_OBJ 0 = 0xa3210, the shadow base's GOT word, and
     A_OBJ 1 = 0xa3268, the use-after-return option's GOT word) and their cells (s2 = the shadow base, a2 = the
     option, AR's constant cell 1); 0x861ac beqz a2 NOT taken (a2 = 1); 0x861b0 a0 = 128 and the call 0x861b4 of
     frame_alloc_1 (__asan_stack_malloc_1), s7 = FB; 0x861c8 bnez s7 TAKEN (FB >= 4096), so the real-stack
     fallback 0x861cc-0x861e4 is not walked; 0x861e8 160(s1) = FB; the frame header FB + 0 = 0x41b58ab3, FB + 8 =
     0x1d8fe (listing object A_OBJ 10), FB + 16 = 0x86140 (A_OBJ 11, m_file itself); 0x86214 120(s1) = FB; s8 =
     shadow(FB); the sixteen shadow stores (the frame's bytes are marked unusable: 0xf1 x 4, 0xf8 x 8, 0xf3 x 4);
     0x86248 a0 = c & 3 and the UBSan trap branch 0x8626c bnez a0 -> unimp 0x86e84, NOT taken.
   UBSan trap branch (one): 0x8626c bnez a0 (a0 = c & 3) -> unimp 0x86e84. Not taken: the entry seed carries the
     fact (10, mkAF 4096 (2 ^ 47 - 8) 4) on a0's atom (c is 2^4-aligned, m_file_pre's c mod 16 = 0), so the
     executor computes andi a0,s9,3 = 0 and decides the branch not taken; the trap instruction is never executed.
   No instrumented check lies in 0x86140-0x86270.
   The call 0x861b4: PaCall.v aj_stack_malloc_atS at pc_stack_malloc (PALibF palf_sm), with SM1, SMP, ML.
   The call 0x862a8 (snprintf) and the run 0x86270 -> 0x862a8: lib/B/Prog/mf_entry_1b.v (mfe_p1_at) with
     lib/B/Prog/mf_entry_1s.v (mfe_snp_step); joined here at the inner cut MFE_P1 = 0x86270 (mf_entry_1c.v).
   Positional names checked against image B's listing (lib/B/Prog/SegAddr.v seg_objs; twin nm): A_OBJ 0 = 0xa3210,
     A_OBJ 1 = 0xa3268, A_OBJ 10 = 0x1d8fe (the frame descriptor, 0x86204's addi), A_OBJ 11 = 0x86140 (m_file),
     A_OBJ 12 = 0xac7b8 (__asan_shadow_memory_dynamic_address), A_OBJ 13 = 0x210a0, A_OBJ 14 = 0x21080. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require PaWalk.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_entry_d mf_entry_k mf_entry_1c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_entry_1s mf_entry_1b.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFSeg RtPFCmd RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================ the entry seed ============================ *)
(* atoms 0..31 are the registers at the entry; 32 the shadow base, 33 the use-after-return option cell, 34 the
   realigned stack pointer s1 = (sp0 - 320) & -32 (the alias names the `andi sp,sp,-32` of 0x86180) *)
Definition mf1_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (-320) (-312) (-320) (-312) [].
Definition mf1_stk1 : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition mf1_slot : YP09.region := YP09.mkRegion (Some 34%nat) 64 168 64 168 [].
Definition mf1_uargot : YP09.region := YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition mf1_uarcell : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition mf1_regions0 : smem :=
[mf1_stk0; mf1_stk1; mf1_slot; got_regionP; bcell_regionP 32; mf1_uargot; mf1_uarcell].
Definition mf1_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 8) 4); (32%nat, mkAF SB SB 0);
  (34%nat, mkAF (2 ^ 46) (2 ^ 47) 5) ].
Definition mf1_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32)), SOff 34 0) ].
Definition ss_mf1 : sstate := mkSS AF_m_file sr_atoms mf1_regions0 None (mkFacts mf1_atoms0 [] mf1_alias0).
Definition mf1_extra (uar sp : Z) : list word := map (Z_to_bv 64) [SB; uar; mf_s1 sp].

(* s1 = (sp0 - 320) & -32 lies 320 or 336 bytes below the 16-aligned sp0 and is 32-aligned *)
Lemma mf1_s1 : forall sp0, sp0 mod 16 = 0 ->
  (mf_s1 sp0 = sp0 - 320 \/ mf_s1 sp0 = sp0 - 336) /\ mf_s1 sp0 mod 32 = 0 /\ mf_s1 sp0 = 32 * ((sp0 - 320) / 32).
Proof.
intros sp0 H16. unfold mf_s1.
pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)) as Hd. pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16.
assert (E : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16) by lia.
split; [destruct E as [E | E]; rewrite E; lia|]. split; [|lia].
replace (sp0 - 320 - (sp0 - 320) mod 32) with (32 * ((sp0 - 320) / 32)) by lia.
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* ============================ the text at any later state ============================ *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition E1 (regs : bvmap 5 word) (uar : Z) : env := Eimg (Ereg regs (mf1_extra uar (spZ regs))).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the text facts at the head of the loop hold at any state the journal from the entry reaches with the entry's
   blocks: the text's bytes lie in a heap block outside the mconf block, so outside M_FILE_FP (the journal's block
   clause keeps them); its slack word is visible at any AR state (AR_block_word_vis); its shadow facts are AR's
   at the state *)
Lemma mf1_loop_now : forall v lyc Sc (Wc : world SEGS) memc mdc own k STK sp0,
  mf_cx B v ->
  ajournal SEGS B STK sp0 (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v)
    (mv_md v) own lyc Sc Wc memc mdc k ->
  Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) ->
  mf_loop v Wc memc (mv_mc v) None 0 (mv_t v) (mv_s v).
Proof.
intros v lyc Sc Wc memc mdc own k STK sp0 CX HJ HP.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _).
destruct HMP as (_ & _ & _ & _ & _ & _ & _ & Hrf & Hov & Ht0 & HSTR & Hlen & HTH & HTA & _ & Hdisj & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct HTH as (bt & mt & Hbt & Hbt1 & Hbt2).
assert (Hbt' : In (bt, mt) (ablocks B lyc Sc)) by exact (Permutation_in _ (Permutation_sym HP) Hbt).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR0 Hbt) as (_ & T4096 & Tceil & _).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrq].
assert (Hspan : Z.of_nat (length (mv_s v)) + 1 <= seg_spec.cstr_span (mv_t v) (mv_s v)).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (mv_t v + Z.of_nat (length (mv_s v)) + 1)) 8 ltac:(lia)). lia. }
unfold sa_disj in Hdisj.
destruct HSTR as ((Hzs & Hnz) & Htl).
destruct HTA as (A1 & A2 & A3 & _ & _).
unfold mf_loop.
replace (skipn (length (mv_s v) - length (mv_s v)) (mv_s v)) with (mv_s v) by (rewrite Nat.sub_diag; reflexivity).
replace (mv_t v + Z.of_nat (length (mv_s v) - length (mv_s v))) with (mv_t v) by (rewrite Nat.sub_diag; lia).
split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split.
{ split; [split; [|exact Hnz]|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    replace (mv_t v + Z.of_nat i) with (bt + (mv_t v + Z.of_nat i - bt)) by lia.
    rewrite (F2 bt mt (mv_t v + Z.of_nat i - bt) Hbt Hbt' ltac:(lia)).
    + replace (bt + (mv_t v + Z.of_nat i - bt)) with (mv_t v + Z.of_nat i) by lia.
      apply Hzs. rewrite length_app. cbn [length]. lia.
    + intros HF. pose proof (mf_fp_in_block B v _ CX HF) as Hc. lia.
  - intros x Hx. apply (AR_block_word_vis SEGS B lyc Sc Wc memc mdc bt mt (mv_t v + Z.of_nat (length (mv_s v))) x HAR Hbt');
      lia. }
split.
{ split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bt mt _ _ HAR Hbt'); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bt mt _ _ HAR Hbt'); lia. }
split; [exact I|]. split; [unfold mv_k0; lia|].
split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ============================ the walk's hypotheses ============================ *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* the ASan reader of a restricted memory is the reader of the memory *)
Lemma mf1_aview_mr : forall H (m : word -> option byte) a, aview SEGS H (mrestrict H m) a = aview SEGS H m a.
Proof. intros H m a. apply (aview_eq_of SEGS). unfold mrestrict. destruct (H (Z_to_bv 64 a)); reflexivity. Qed.

(* the entry seed: the probe word, the saved-register window, the realigned-stack slots 64 .. 168(s1), the
   shadow base's GOT word and cell, the use-after-return option's GOT word and its cell (AR's constant 1) *)
Lemma mf1_entry : forall ly S W (regs : bvmap 5 word) mem md ch c,
afn_pre SEGS B SegInstB.STK_m_file ly S W regs mem md ch ->
getr regs 10 = w64 c -> c mod 16 = 0 -> 4096 <= c -> c <= 2 ^ 47 - 8 ->
st_ok_pi SEGS VAL (E1 regs (as_uar_cell B)) ss_mf1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_m_file)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch c HPRE H10 Hc16 Hc4096 Hc47.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kgu.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
pose proof (palf_sep B TLF) as Hsep.
unfold kImgEnd in HcellR, HgotR, HguR, Huar.
rewrite restrict_mkst_fx.
set (sp := spZ regs) in *.
set (E := E1 regs (as_uar_cell B)).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (mf1_extra (as_uar_cell B) sp)) k)
  by (intros k Hk; subst E; unfold E1; apply Eimg_low; exact Hk).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (mf1_extra (as_uar_cell B) sp) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth mf1_extra map] in E32, E33, E34.
assert (E240 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold E1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold E1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E252 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold E1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; reflexivity).
destruct (mf1_s1 sp Hal16) as (Hs1r & Hs1a & Hs1q).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (Hwr : forall o, sp - 8592 <= o < sp -> writable_at SEGS (mrestrict (w_H W) mem) o)
  by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; rewrite HSTK; lia).
unfold ss_mf1. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold mf1_regions0, mf1_stk0, mf1_stk1, mf1_slot, got_regionP, bcell_regionP, mf1_uargot, mf1_uarcell.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply Hwr. lia.
  * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply Hwr. lia.
  * rewrite (VB 34%nat (mf_s1 sp) E34) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply Hwr. lia.
  * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E240) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E252, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E252) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E241) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgu).
  * rewrite (VB 33%nat (as_uar_cell B) E33) by (lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ apply pairwise_disjoint_of_extents.
  unfold mf1_regions0, mf1_stk0, mf1_stk1, mf1_slot, got_regionP, bcell_regionP, mf1_uargot, mf1_uarcell,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 34%nat (mf_s1 sp) E34) by lia. rewrite (VB 33%nat (as_uar_cell B) E33) by (lia).
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E240) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E241) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E252) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  cbn [zseps zseps_from fst snd] in Hsep.
  revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HcellR HgcD HgotR HguR Huar Hsep Hs1r HSTK. clear. unfold ASAN_CEIL, kImgEnd. intros.
  repeat split; lia.
+ split; [|split; [exact I|]].
  * cbn [mf1_atoms0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hal16 Hc16 Hc4096 Hc47 Hs1r Hs1a HSTK. clear. unfold SB, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  * cbn [mf1_alias0 f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu, U_SOff, U_SLit, U_SOff. cbn [zalu_raw].
    rewrite Usp, E34, unsigned_lit_small by lia.
    replace (sp + -320) with (sp - 320) by lia.
    rewrite (zcanon_id (sp - 320)) by (unfold M64; lia). change (zcanon (-32)) with (2 ^ 64 - 32).
    rewrite PaWalk.land_m32 by lia.
    rewrite !zcanon_id by (unfold M64; pose proof (Z.mul_div_le (sp - 320) 32 ltac:(lia)); lia). lia.
Qed.

(* local tactics of the walk (fuzz_command's check_reply_s1.v s1_* idioms) *)
Ltac mf1_norm HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.
Ltac mf1_U := repeat match goal with H : bv_unsigned (ew ?Ev ?k) = _ |- context [bv_unsigned (ew ?Ev ?k)] => rewrite H end.
Ltac mf1_add HS r0 rok rdj :=
  let r := eval vm_compute in r0 in
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssv ?msv =>
  let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in
  assert (Rok : region_ok sg Ev (ms_mem msv) r); [rok | ];
  assert (Rdj : all_disjoint Ev r (ss_mem ssv)); [rdj | ];
  let HS3 := fresh "HS3" in
  pose proof (st_ok_pi_add_region Ev ssv msv r HS eq_refl Rok Rdj) as HS3;
  clear HS Rok Rdj; rename HS3 into HS; mf1_norm HS end.
Ltac mf1_name_md := try match goal with |- context [with_vm_backing ?a ?b ?c] =>
  let m := fresh "mdv" in set (m := with_vm_backing a b c) in *; clearbody m end.
Ltac mf1_lia := first [lia | unfold SB in *; lia].
Ltac mf1_rok wtac :=
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]; mf1_U;
  split; [mf1_lia|]; split; [mf1_lia|]; split; [first [intros o Ho; lia | wtac] |];
  repeat (apply Forall_cons; [eapply chunk_ok_val;
    [cbn [sv_denot]; mf1_U; rewrite ?Z.add_0_r; reflexivity | first [zside | unfold SB; zside] | zside | eassumption] |]);
  apply Forall_nil.
Ltac mf1_dj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; mf1_U;
  unfold SB in *; repeat split; mf1_lia.
Ltac mf1_inl := repeat (first [left; reflexivity | right]).

(* the walk 0x86140 -> 0x86270, then MFE_P1 *)
Lemma mfe_entry_p1 : MFE_P1_stmt B -> MF_ENTRY_stmt B.
Proof.
intros P1 v CX HFRM.
pose proof CX as (HPRE & HROOM & _ & _ & _ & _ & _ & _ & H10 & Hc64 & H11 & Ht64 & H12 & Hlp64 & HMP & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof HMP as (Hc0 & Hc16 & HMC & HHC & HAC & HTC & _).
destruct (mf_c_entry B v CX) as (bc & mbc & Hbc & Hbc1 & Hbc2 & Hbc4096 & Hbcceil & Hbcimg).
assert (HSM : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
pose proof (mf_heap_addr SEGS B LAWS) as MHA.
(* the seed and the journal from the entry *)
pose proof (mf1_entry (mv_ly v) (mv_S v) (mv_W v) (mv_regs v) (mv_mem v) (mv_md v) (mv_ch v) (mv_c v) HPRE H10 Hc16
  ltac:(lia) ltac:(lia)) as HS.
pose proof (ajournal_init SEGS B SegInstB.STK_m_file (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_regs v) (mv_mem v) (mv_md v) (mv_ch v) HPRE) as HJ.
set (E := E1 (mv_regs v) (as_uar_cell B)) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold E1; apply Eimg_env).
set (sp0 := spZ (mv_regs v)) in *.
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg (mv_regs v) (mf1_extra (as_uar_cell B) sp0)) k)
  by (intros k Hk; subst E; unfold E1; apply Eimg_low; exact Hk).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (mf1_extra (as_uar_cell B) sp0) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr (mv_regs v) r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth mf1_extra map] in E32, E33, E34. clear EX.
assert (E10 : ew E 10 = Z_to_bv 64 (mv_c v)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
destruct (mf1_s1 sp0 Hal16) as (Hs1r & Hs1a & Hs1q).
set (sp1 := mf_s1 sp0) in *.
assert (Hsp1b : sp0 - 336 <= sp1 <= sp0 - 320) by lia.
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_m_file)) with (Z_to_bv 64 (BASE + AF_m_file)).
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H (mv_W v)) (mv_mem v)).
(* 0x86140 .. 0x861b4: the frame of 320, the probe word, the saves, s1, the two GOT reads and their cells, the
   option test `beqz a2` decided not taken (a2 = 1), a0 = 128; the jal to frame_alloc_1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 34%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U34; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the heap bytes the run keeps (it writes only the stack window) *)
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> rdW (mv_W v) (ms_mem msc) a = rdW (mv_W v) m0 a);
  [ intros a Ha; apply (kept_of_frame Ex rs (w_H (mv_W v)) m0 (ms_mem msc) (fun x => alloc_ceiling <= x) HFr);
    [ intros bb wlo whi x Hinw Hr; cbv beta; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; first [rewrite Usp in Hr; lia | rewrite U34 in Hr; lia | lia] |]);
      destruct Hinw
    | lia
    | cbv beta; lia ]
  | ] end.
clear HF HFr HG. mf1_name_md.
(* the frame call: __asan_stack_malloc_1(128) at sp1 = sp0 + (sp1 - sp0) *)
pose proof (proj1 HJ) as HAR1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & _ & Kgot1 & _).
rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
apply (val_mem_of_rdword SEGS) in Kgot1. apply (val_mem_of_rdword SEGS) in Kcell1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
assert (Hsm : pa_sigma SS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1)
  by exact (palf_sm B TLF 1 ltac:(right; left; reflexivity)).
rewrite Hsm.
pose proof (count_cid_le_length 1 (frames (mv_S v))) as Hcnt. unfold sa_room in HROOM.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 (SM1 fx) ltac:(lia) (mv_W v) (ms_regs msX) (ms_mem msX)
    SegInstB.STK_m_file sp0 (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v)
    (mv_md v) [] (mv_ly v) (mv_S v) _ 0 (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2, E34, unsigned_lit_small by lia. lia.
  - replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16)
      by (pose proof (Z.div_mod sp1 32 ltac:(lia)); pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - lia.
  - rewrite HSTK. unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HK & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
apply (val_mem_of_rdword SEGS) in Kgot2. apply (val_mem_of_rdword SEGS) in Kcell2.
(* the state after the call: the probe word, the saves, the realigned slots, the shadow GOT word and cell *)
jafter_call_keep_pi HS 42%nat regs2 (mrestrict (w_H (mv_W v)) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | rewrite HSTK; lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | rewrite HSTK; lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact U34 | lia | rewrite HSTK; lia | lia | lia | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
      [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot1 | exact Kgot2 | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
      [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell1 | exact Kcell2 | lia]. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ev1 := havoc E 42 (map (getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM Ev1) by (apply img_env_havoc; [exact HEI | rewrite length_map; unfold A_TEXT; cbn; lia]).
(* the frame F = frame_addr ly 1 fpos, its flag cell FL, its shadow SB + F / 8 *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
set (F := frame_addr (mv_ly v) 1 fpos) in *. set (FL := flag_addr (mv_ly v) 1 fpos) in *.
assert (RF : 0 <= F < 2 ^ 64) by lia.
assert (HFLb : 4096 <= FL < alloc_ceiling) by (clear - HFLapp HFLce; unfold in_app in HFLapp; lia).
assert (RFL : 0 <= FL < 2 ^ 64) by lia.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (E46a : ew Ev1 46 = Z_to_bv 64 F).
{ subst Ev1. unfold havoc, CLOB. cbn [ew map nth Nat.ltb Nat.leb Nat.sub]. exact Ha0. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 58 Ev1 ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc Ev1 58 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Ev2 eqn:HEv2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HEv2; apply img_env_havoc; [exact HEI1 | unfold A_TEXT; cbn; lia]).
assert (AG : forall k, (k < 42)%nat -> ew Ev2 k = ew E k)
  by (intros k Hk; rewrite HEv2, ew_havoc_old by lia; subst Ev1; apply ew_havoc_old; lia).
assert (E46 : ew Ev2 46 = Z_to_bv 64 F) by (rewrite HEv2, ew_havoc_old by lia; exact E46a).
assert (E58 : ew Ev2 58 = Z_to_bv 64 FL)
  by (rewrite HEv2; exact (ew_havoc_new Ev1 58 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E59 : ew Ev2 59 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HEv2; exact (ew_havoc_new Ev1 58 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HEv2 E46a.
assert (E32' : ew Ev2 32 = Z_to_bv 64 SB) by (rewrite AG by lia; exact E32).
assert (U46 : bv_unsigned (ew Ev2 46) = F) by (rewrite E46; apply unsigned_lit_small; lia).
assert (U58 : bv_unsigned (ew Ev2 58) = FL) by (rewrite E58; apply unsigned_lit_small; lia).
assert (U59 : bv_unsigned (ew Ev2 59) = SB + F / 8) by (rewrite E59; apply unsigned_lit_small; unfold SB; lia).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG by lia; exact Usp).
assert (U34b : bv_unsigned (ew Ev2 34) = sp1) by (rewrite AG by lia; exact U34).
assert (U32 : bv_unsigned (ew Ev2 32) = SB) by (rewrite E32'; apply unsigned_lit_small; unfold SB; lia).
assert (U241 : bv_unsigned (ew Ev2 241) = VAL (A_OBJ 0)) by exact (HEI2 241%nat ltac:(unfold A_TEXT, A_LIM; lia)).
assert (U253 : bv_unsigned (ew Ev2 253) = VAL (A_OBJ 12)) by exact (HEI2 253%nat ltac:(unfold A_TEXT, A_LIM; lia)).
(* FB: 32-aligned, at least 4096 (the `bnez s7` 0x861c8 is decided taken); s8 = shadow(FB) as atom 59 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 46 (HPTR 5) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U46; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HFd8 : F / 8 = 4 * (F / 32))
  by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 59 (mkAF (SB + 512) (SB + 2 ^ 44) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U59; change (2 ^ 2) with 4; unfold SB;
          split; [lia|]; split; [rewrite HFd8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia;
          apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 46 32 59 F SB E46 RF E32' E59)) as HS3 end.
clear HS. rename HS3 into HS. mf1_norm HS.
(* the values the added regions hold after the call: the flag pointer in FB + 120, the frame's zero shadow *)
assert (VFL : val_mem SEGS (mrestrict (w_H (mv_W v)) mem2) (F + 120) 8 FL).
{ replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
assert (VZ : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H (mv_W v)) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz.
  replace (SB + F / 8 + 8 * j + i) with (SHADOW_OFF + F / 8 + (8 * j + i)) by (unfold SB, SHADOW_OFF; lia).
  apply Hz. change (128 / 8) with 16. lia. }
assert (VZ0 : val_mem SEGS (mrestrict (w_H (mv_W v)) mem2) (SB + F / 8 + 0) 8 0)
  by (replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply VZ; lia).
assert (VZ8 : val_mem SEGS (mrestrict (w_H (mv_W v)) mem2) (SB + F / 8 + 8) 8 0)
  by (replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply VZ; lia).
unfold shadow_addr in HFSpres.
(* where the frame and the image objects lie: the frame is off the image (frm_off_imgP), the GOT words and cells
   are image objects *)
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFoff.
change (fs_frame_bytes 1) with 128 in HFoff. fold F in HFoff. unfold off_img, kImgEnd in HFoff.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in HcellR, HgotR.
assert (HFz : F + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= F)
  by (clear - HFapp; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
(* the frame's tail with the flag pointer at 120, its header (writable), its 16 shadow bytes (writable) *)
mf1_add HS (YP09.mkRegion (Some 46%nat) 96 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 58 0))]) ltac:(mf1_rok idtac) ltac:(mf1_dj).
mf1_add HS (YP09.mkRegion (Some 46%nat) 0 32 0 32 [])
  ltac:(mf1_rok ltac:(intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))) ltac:(mf1_dj).
mf1_add HS (YP09.mkRegion (Some 59%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))])
  ltac:(mf1_rok ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite SB_SHADOW_OFF; apply (proj1 (HFSpres o ltac:(lia)))))
  ltac:(mf1_dj).
(* 0x861b8 .. 0x8626c: s7 = FB, `bnez s7` taken, 160(s1) = FB, the frame header, 120(s1) = FB, s8 = shadow(FB), the
   16 shadow stores, a0 = c & 3 = 0 and the trap branch 0x8626c not taken; up to 0x86270 *)
paj_run_to_sh RUNTOP HS HJ2 MFE_P1.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyv ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spx fp b0 bc fr lyv own) end.
  eapply awr_ok_cons_gen with (n := 59%nat) (b := SB + F / 8); [reflexivity | exact U59 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF.
    lia. }
  eapply awr_ok_cons_gen with (n := 46%nat) (b := F); [reflexivity | exact U46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, fpos.
    split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F.
    change (fs_frame_bytes 1) with 128. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 34%nat) (d := sp1 - sp0);
    [reflexivity | rewrite U34b; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  do 2 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the bytes the run keeps: it writes the stack window, the frame header and the frame's 16 shadow bytes *)
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a) -> ~ (F <= a < F + 32) ->
    ~ (SB + F / 8 <= a < SB + F / 8 + 16) -> rdW (mv_W v) (ms_mem msc) a = rdW (mv_W v) m0 a);
  [ intros a Ha H1 H2 H3; apply (kept_of_frame Ex rs (w_H (mv_W v)) m0 (ms_mem msc)
      (fun x => alloc_ceiling <= x \/ (F <= x < F + 32) \/ (SB + F / 8 <= x < SB + F / 8 + 16)) HFr);
    [ intros bb wlo whi x Hinw Hr; cbv beta; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U2, ?U34b, ?U46, ?U59, ?U241, ?U253 in Hr;
         first [lia | unfold SB in *; lia] |]);
      destruct Hinw
    | lia
    | cbv beta; tauto ]
  | ] end.
clear HF HFr HG. mf1_name_md.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (ms3 := msF) in * end.
(* every byte of every entry heap block keeps its entry value *)
destruct HK as (_ & HKb & _).
assert (KB : forall b m a, In (b, m) (ablocks B (mv_ly v) (mv_S v)) -> b <= a < b + req_size m ->
  rdW (mv_W v) (ms_mem ms3) a = rdW (mv_W v) (mv_mem v) a).
{ intros b m a Hin Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & B4096 & Bceil & Bapp & _).
  assert (Hin2 : In (b, m) (ablocks B (mv_ly v) S2)) by (rewrite Eab; exact Hin).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 fpos HAR2 Hin2 Hfin2) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. change (fs_frame_bytes 1) with 128 in Hdj. fold F in Hdj.
  rewrite K3; [| lia | lia | lia |].
  2:{ intros Hs. exact (fshadow_not_app F 16 b (req_size m) a ltac:(lia) ltac:(lia) Bapp ltac:(unfold SB in Hs; lia) Ha). }
  cbn [ms_mem mkst]. rewrite ?mf1_aview_mr.
  replace a with (b + (a - b)) by lia.
  rewrite (HKb b m (a - b) Hin ltac:(lia) (fun H => H)).
  replace (b + (a - b)) with a by lia.
  apply K1. lia. }
(* the registers at 0x86270 *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
assert (AGv : forall k vv, (k < 42)%nat -> ew E k = Z_to_bv 64 vv -> ew Ev2 k = Z_to_bv 64 vv)
  by (intros k vv Hk H; rewrite AG by lia; exact H).
assert (AGr : forall k (r : bv 5), (k < 42)%nat -> Z.of_nat k = bv_unsigned r -> ew Ev2 k = getr (mv_regs v) r)
  by (intros k r Hk Hr; rewrite AG by lia; exact (EE k r Hr)).
assert (W2 : getr (ms_regs ms3) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite Q2, (AGv 34%nat sp1 ltac:(lia) E34); reflexivity).
assert (W3 : getr (ms_regs ms3) 3 = w64 (as_gp B)) by (rewrite Q3, (AGr 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (W4 : getr (ms_regs ms3) 4 = w64 (as_tp B)) by (rewrite Q4, (AGr 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (W8 : getr (ms_regs ms3) 8 = w64 (mv_sp v)).
{ rewrite Q8, (AGr 2%nat 2%bv ltac:(lia) eq_refl). unfold w64, mv_sp, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (W9 : getr (ms_regs ms3) 9 = w64 (mf_s1 (mv_sp v))) by (rewrite Q9, (AGv 34%nat sp1 ltac:(lia) E34); reflexivity).
assert (W18 : getr (ms_regs ms3) 18 = w64 SHADOW_OFF) by (rewrite Q18, E32'; reflexivity).
assert (W23 : getr (ms_regs ms3) 23 = w64 (frame_addr (mv_ly v) 1 fpos)) by (rewrite Q23, E46; reflexivity).
assert (W24 : getr (ms_regs ms3) 24 = w64 (SHADOW_OFF + frame_addr (mv_ly v) 1 fpos / 8)) by (rewrite Q24, E59; reflexivity).
assert (W22 : getr (ms_regs ms3) 22 = w64 (mv_lp v)) by (rewrite Q22, (AGr 12%nat 12%bv ltac:(lia) eq_refl); exact H12).
assert (W25 : getr (ms_regs ms3) 25 = w64 (mv_c v)) by (rewrite Q25, (AGr 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (W26 : getr (ms_regs ms3) 26 = w64 (mv_t v)) by (rewrite Q26, (AGr 11%nat 11%bv ltac:(lia) eq_refl); exact H11).
(* the regions' fields: low.i's eight shadow bytes 0xf8, the flag pointer in FB + 120, the saved registers,
   120(s1) = FB *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r0 := eval vm_compute in (nth 0 rs got_regionP) in
  let r2 := eval vm_compute in (nth 2 rs got_regionP) in
  let r4 := eval vm_compute in (nth 4 rs got_regionP) in
  let r5 := eval vm_compute in (nth 5 rs got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRs;
  pose proof (st_ok_pi_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HRt;
  pose proof (st_ok_pi_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HRk;
  pose proof (st_ok_pi_region_nth Ex ssx msx 5 r5 HS ltac:(vm_compute; reflexivity)) as HRl;
  cbn [ms_mem restrict] in HRs, HRt, HRk, HRl end.
assert (VS : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H (mv_W v)) (ms_mem ms3)) (SHADOW_OFF + frame_addr (mv_ly v) 1 fpos / 8 + i) 1 MF_LOW_OFF).
{ intros i Hi. fold F. rewrite <- SB_SHADOW_OFF.
  assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  repeat (destruct Hc as [-> | Hc];
    [ lazymatch goal with |- val_mem _ _ (?b + ?ii) 1 _ =>
        let V := fresh "V" in
        pose proof (field_of_region_any _ _ 59 b _ 0 16 0 16 ii 1%N _ HRs U59
          ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
        lazymatch type of V with val_mem _ _ _ _ ?x => replace x with MF_LOW_OFF in V by (vm_compute; reflexivity) end;
        change (N.to_nat 1) with 1%nat in V; exact V end |]).
  subst i.
  lazymatch goal with |- val_mem _ _ (?b + ?ii) 1 _ =>
    let V := fresh "V" in
    pose proof (field_of_region_any _ _ 59 b _ 0 16 0 16 ii 1%N _ HRs U59
      ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
    lazymatch type of V with val_mem _ _ _ _ ?x => replace x with MF_LOW_OFF in V by (vm_compute; reflexivity) end;
    change (N.to_nat 1) with 1%nat in V; exact V end. }
assert (VFL3 : val_mem SEGS (mrestrict (w_H (mv_W v)) (ms_mem ms3)) (frame_addr (mv_ly v) 1 fpos + 120) 8
  (flag_addr (mv_ly v) 1 fpos)).
{ fold F FL. exact (field_of_region _ _ _ F _ _ _ _ _ 120 8%N (SOff 58 0) FL HRt U46 ltac:(mf1_inl)
    ltac:(rewrite PaWalk.sv_denot_SOff0; exact E58) ltac:(zside) ltac:(zside)). }
assert (V120 : val_mem SEGS (mrestrict (w_H (mv_W v)) (ms_mem ms3)) (mf_s1 (mv_sp v) + 120) 8
  (frame_addr (mv_ly v) 1 fpos)).
{ fold F. change (mf_s1 (mv_sp v)) with sp1.
  exact (field_of_region _ _ _ sp1 _ _ _ _ _ 120 8%N (SOff 46 0) F HRl U34b ltac:(mf1_inl)
    ltac:(rewrite PaWalk.sv_denot_SOff0; exact E46) ltac:(zside) ltac:(zside)). }
assert (VK : mf_saved (mrestrict (w_H (mv_W v)) (ms_mem ms3)) (mv_sp v) (mv_regs v)).
{ intros j rr Hj.
  do 13 (destruct j as [|j]; [cbn [nth_error mf_saved_regs] in Hj; injection Hj as <-;
    lazymatch goal with |- val_mem _ _ (_ - 8 - 8 * Z.of_nat ?k) _ (bv_unsigned (getr _ (Z_to_bv 5 ?r))) =>
      let off := eval cbv in (- 8 - 8 * Z.of_nat k) in
      let kr := eval cbv in (Z.to_nat r) in
      replace (mv_sp v - 8 - 8 * Z.of_nat k) with (sp0 + off) by (cbn; unfold mv_sp; fold sp0; lia);
      exact (field_of_region _ _ _ sp0 _ _ _ _ _ off 8%N (SOff kr 0) (bv_unsigned (getr (mv_regs v) (Z_to_bv 5 r))) HRk U2
        ltac:(mf1_inl)
        ltac:(rewrite PaWalk.sv_denot_SOff0, (AGr kr (Z_to_bv 5 r)) by (first [lia | reflexivity]); symmetry;
              apply Z_to_bv_bv_unsigned)
        (bv_unsigned_in_range 64 _) ltac:(zside)) end |]).
  cbn in Hj; destruct j; discriminate. }
(* the mconf block still holds the entry's model, addressable, with its slack *)
destruct HHC as (bh & mh & Hinh & Hh1 & Hh2).
assert (Hinh2 : In (bh, mh) (ablocks B (mv_ly v) S2)) by (rewrite Eab; exact Hinh).
pose proof (req_size_pos mh ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ bh mh HAR Hinh) as (_ & _ & _ & _ & _ & _ & Hm); lia))
  as [_ Hrqh].
assert (MC3 : sa_mconf (rdW (mv_W v) (ms_mem ms3)) (mv_c v) (mv_mc v)).
{ apply (mf_mconf_keep (mv_W v) (mv_W v) (mv_mem v) (ms_mem ms3) (fun a => ~ (bh <= a < bh + req_size mh)) (mv_c v) (mv_mc v)).
  - intros a Ha HnR. cbv beta in HnR. apply (KB bh mh a Hinh).
    destruct (Z_le_gt_dec bh a); [|exfalso; apply HnR; intros Hq; lia].
    destruct (Z_lt_ge_dec a (bh + req_size mh)); [lia|exfalso; apply HnR; intros Hq; lia].
  - lia.
  - lia.
  - intros a Ha HR. cbv beta in HR. apply HR. lia.
  - exact HMC. }
assert (MA3 : sa_addr (rdW (mv_W v) (ms_mem ms3)) (mv_c v) seg_spec.SEG_M_SIZE).
{ apply (MHA (mv_ly v) S2 (mv_W v) (ms_mem ms3) _ (mv_c v) seg_spec.SEG_M_SIZE (proj1 HJ2)); [|lia].
  exists bh, mh. split; [exact Hinh2 | lia]. }
assert (MT3 : sa_tail (rdW (mv_W v) (ms_mem ms3)) (mv_c v + seg_spec.SEG_M_SIZE - 1)).
{ intros x Hx. apply (AR_block_word_vis SEGS B (mv_ly v) S2 (mv_W v) (ms_mem ms3) _ bh mh (mv_c v + seg_spec.SEG_M_SIZE - 1) x
    (proj1 HJ2) Hinh2); lia. }
assert (HPerm : Permutation (ablocks B (mv_ly v) S2) (ablocks B (mv_ly v) (mv_S v))) by (rewrite Eab; apply Permutation_refl).
(* 0x86270: the inner cut *)
pmkst HS.
refine (P1 v (mv_ly v) S2 (mv_W v) (ms_regs ms3) (ms_mem ms3) _ fpos CX HFRM _ _ _ KB _ W22 W25 W26).
- split; [reflexivity | exists fS2; exact ES2].
- split; [exact HJ2|]. split; [exact HPerm|]. split; [exact VFL3|]. split; [exact VS|].
  split; [exact VK|]. split; [exact V120|]. split; [exact MC3|]. split; [exact MA3 | exact MT3].
- exact (mf1_loop_now v (mv_ly v) S2 (mv_W v) (ms_mem ms3) _ [(1, fpos)] 0 SegInstB.STK_m_file sp0 CX HJ2 HPerm).
- unfold mf_regs_ex. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W8|].
  split; [exact W9|]. split; [exact W18|]. split; [exact W23 | exact W24].
Qed.

(* ============================ the half: 0x86140 -> 0x862ac ============================ *)
(* image B's snprintf row (the image-B m_file segment table, the owner's corrected text) and m_file_k.v's two hypotheses *)
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.

(* 0x86140 -> 0x86270 here, 0x86270 -> 0x862a8 and the snprintf call by mf_entry_1b.v / mf_entry_1s.v, then the
   cut 0x862ac *)
Lemma mfe_entry_at : MFE_MID_F B -> MF_ENTRY_stmt B.
Proof.
intros MID. apply mfe_entry_p1.
exact (mfe_p1_at B VOBJS (mfe_snp_step B SSP ASNP) MID).
Qed.
(* inside the Sections: the half's hypotheses as its assumptions *)
About mfe_entry_at.
Print Assumptions mfe_entry_at.

End e.
End f.
End d.

(* the half at every FP state *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SM1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIGMA SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.

Lemma mfe_entry_F : MFE_MID_F B -> MF_ENTRY_F B.
Proof. intros MID fx0. eapply (mfe_entry_at (fx := fx0) B); eassumption. Qed.
(* inside the Sections: the half's hypotheses as its assumptions *)
About mfe_entry_F.
Print Assumptions mfe_entry_F.
End i.
End h.
End g.
About mfe_entry_at.
Print Assumptions mfe_entry_at.
About mfe_entry_F.
Print Assumptions mfe_entry_F.
