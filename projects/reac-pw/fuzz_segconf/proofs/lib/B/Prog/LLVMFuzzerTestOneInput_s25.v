(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s6.v, with its module paths, module names and numbers changed; 293 of its 399 lines of code are new or changed and 656 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of
   the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): segment S21, from the cut K85ec8 (0x85ec8) to
   the cut RET (0x85fc8), and the return from RET to the function's post. The statements are lt_seg_S21_stmt and
   lt_seg_RET_stmt of LLVMFuzzerTestOneInput_defs.v (image B's cut-statement commit ea8f5f93fe57).

   The image-B twin of image A's lib/A/Prog/LLVMFuzzerTestOneInput_s25.v (image A's S21 / ret commit 187a26673c08),
   lemma for lemma (lt_seg_RET, lt_seg_S21), renamed by the B map's section 11 (PLAN-asanubsan-main.md: K85c44 ->
   K85ec8, RET 0x85d40 -> 0x85fc8, frame 320 -> 352, the return address of the fill 0x85c64 -> 0x85ee8) and with the
   one change the image-B code makes: SH(FR) is not in a register at K85ec8 (image A: s5) but in the slot 184(s1)
   (lt_frame's last conjunct), which `ld a0,184(s1)` at 0x85edc reads; the seed therefore holds a read-only region at
   s1 with that slot as a chunk (atom 46 = SH(FR)).

   What the code does there (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s, 0x85ec8 .. 0x85fc8): the
   frame-done word 0x45e0360e into FR + 0 through a7 (0x85ed0); a6 = FR <> 0, so the side-stack branch (beqz a6 at
   0x85ed4 not taken); a1 = 64, a0 = 184(s1) = SH(FR), s2 = a6 and meta_fill_f5(SH(FR), 64) (0x85ee4) marks the 64
   shadow bytes of the 512-byte frame 0xf5; ld a0,504(s2) and sb zero,0(a0): the flag byte := 0, which releases the
   frame (0x85ee8 - 0x85eec); j 0x85f88; a0 = 0, sp = s0 - 352, the 13 restores, sp += 352 (0x85f88 - 0x85fc4); ret
   (0x85fc8). The real-stack release 0x85ef4 - 0x85f84 is dead: K85ec8 gives a6 = FR >= 4096. No UBSan trap branch
   and no instrumented check lies in S21 (map section 2.3 row S21: 65 instructions, no check, no trap).

   The walk (the form of plugin-hostd/fuzz_command's lib/B/Prog/chain_words_s6.v:497-844 and of its harness walk's
   LLVMFuzzerTestOneInput_s90.v, origin/ossv/recipes 3abc3740de97): one symbolic run from K85ec8 to the call of
   meta_fill_f5 (PaCallRun.v's SRr_run_pi_AJ_call), the call step aj_set_shadow_atS (LLVMFuzzerTestOneInput_s25k.v),
   a re-seat of the symbolic state over the call (PaLibH.v's jafter_call_keep_hi) with the three regions the release
   reads and writes, one run from the return of the fill to the ret under PaLibF.v's aj_flag_store_pi (the flag
   store turns the journal's own frame [(3, fpos)] into [] and S into stack_free_state 3 fpos S), and the
   continuation LTA_RET at the FP state of the cut (meta_fill_f5 keeps the FP state). The return: SegPaLib.v's
   paj_ret_at into lt_post (apost_baseF with fx' := fx).

   Section hypotheses: ML (the allocator model's laws), MTL / MTFL (the meter's laws, and across set_fs), ASF / FFL
   (the side-stack release law and the flag law), SHF5 (meta_fill_f5's contract RtShadow.aset_shadow_realizes at
   pa_sigma SS___asan_set_shadow_f5 with v = 0xf5, PLAN-asanubsan-main section 5 row 0x85ee4), the names of
   chain_words_c.v:89-93. LAWS is YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaStep PaShadow SegSyms SegList SegPa PaJournal SegPaLib PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_inst.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s25k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The atoms of S21: registers 0 .. 31 are the registers at K85ec8; 32 .. 44 the thirteen registers the prologue
   saved, in LT_SAVED's order (atom 32 + j is the word in the slot SP0 - 8 (j + 1)); 45 the frame's flag pointer FL,
   which the release loads from FR + 504 and stores through; 46 SH(FR), which the release loads from 184(s1). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s25_extra (cx : lcx) : list word := map (getr (x_regs cx)) LT_SAVED ++ [w64 (x_fl cx); w64 (x_sh cx)].

(* K85ec8: the frame (a7 = a6 = FR, atom 17) with the window of the frame-done word (FR + 0 .. FR + 8) and the
   chunk the release reads (FR + 504) *)
Definition s25_frame : YP09.region :=
  YP09.mkRegion (Some 17%nat) 0 512 0 8 [YP09.mkChunk 504 (CVal 8 (SOff 45 0))].
(* K85ec8: the slot 184(s1) = SH(FR) (s1 = S1, atom 9), read only, which ld a0,184(s1) at 0x85edc reads *)
Definition s25_s1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (CVal 8 (SOff 46 0))].
(* the frame is not the null pointer, which decides beqz a6 at 0x85ed4 *)
Definition s25_facts : facts := mkFacts [(17%nat, mkAF 4096 140737488355328 0)] [] [].
Definition ss_s25 : sstate := mkSS LO_K85ec8 sr_atoms [s25_frame; s25_s1] None s25_facts.
(* after the fill: the frame read only at its flag word, the flag byte, the thirteen saved words below s0 = SP0 *)
Definition s25_frame_ro : YP09.region :=
  YP09.mkRegion (Some 17%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 45 0))].
Definition s25_flag : YP09.region := YP09.mkRegion (Some 45%nat) 0 1 0 1 [].
Definition s25_stack : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
   YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SHF5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA SS___asan_set_shadow_f5) 0xf5.

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* ---- the return: 0x85fc8 ret, into the function's post ---- *)
Theorem lt_seg_RET : lt_seg_RET_stmt B MT.
Proof.
unfold lt_seg_RET_stmt, LT_RET_stmt.
intros cx ly S W regs mem md k acc HB0 Hfrm HJ HP R1 R10 HIMG HBL HBUD.
pose proof HB0 as (HPRE & _ & _ & _ & _ & _ & Hpn & _).
pose proof HPRE as (_ & Hra & _).
pose proof HBUD as (Hk0 & _ & Hkev & Hmle & Hacc0 & Hacc).
pose proof HIMG as (_ & _ & HGI).
unfold lt_blocks in HBL. cbn [app] in HBL. unfold x_bl0 in HBL.
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E (mkSS LO_RET sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_RET)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split end; exact I. }
unfold cfg_at. change (w64 (BASE + LO_RET)) with (Z_to_bv 64 (BASE + LO_RET)).
eapply (RET W E _ _ md _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold lt_post, apost_baseF.
exists fx, ly, S, regs, mem, (with_vm_backing (m_vm_lazy md) mat' md).
split.
{ cbn [ms_regs ms_mem mkst]. rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [intros k0 _; reflexivity|].
split; [left; reflexivity|].
split; [eapply ajournal_mono_k; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | lia]|].
split; [exact HP|].
unfold lt_Q.
split; [exact R10|].
split; [exact HBL|].
split.
{ apply (s25_payload_kept B MT cx ly S W mem md [] k HB0 HJ).
  intros Hn. destruct Hpn as [[Hn0 _] | [_ Hin0]]; [lia|].
  exact (Permutation_in _ (Permutation_sym HBL) Hin0). }
split; [exact HGI|].
split; [apply (mo_le_mono MT MTL _ _ _ _ Hmle); lia|].
rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B (x_ly cx) (x_S cx)), (bsum_perm _ _ HBL).
unfold LIVE_LTOI. lia.
Qed.

(* ---- segment S21: K85ec8 (0x85ec8) .. RET (0x85fc8) ---- *)
Theorem lt_seg_S21 : lt_seg_S21_stmt B MT.
Proof.
unfold lt_seg_S21_stmt, LT_K85ec8_stmt.
intros HRET cx ly S W regs mem md k acc HB0 Hfrm HCORE R16 R17.
destruct HCORE as (HFR & HIMG & HBL & HBUD).
destruct HFR as (HJ & Hsp & Hgp & Htp & Hs0 & Hs1 & HSV & _ & _ & _ & Hflag & _ & _ & H184).
pose proof HB0 as (HAFN & _).
pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (x_regs cx)) with (x_sp0 cx) in Hsp0al, Hslo, Hshi.
pose proof asan_consts as (C1 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
(* the frame and its flag, at the layout of the cut *)
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hfin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly 3 (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EFL : flag_addr ly 3 (x_fpos cx) = x_fl cx).
{ unfold x_fl, flag_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly S W mem md 3 (x_fpos cx) HAR Hfin) as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. change (fs_frame_bytes 3) with 512 in HFceil.
pose proof (frm_off_imgP B ly S W mem md 3 (x_fpos cx) HAR Hfin) as HFimg.
rewrite EFA in HFimg. change (fs_frame_bytes 3) with 512 in HFimg.
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hfin) as (_ & HFapp & HFpres & _).
rewrite EFA in HFapp, HFpres. change (fs_frame_bytes 3) with 512 in HFapp, HFpres.
destruct (FFL ly S W mem md 3 (x_fpos cx) HAR Hfin) as (_ & HFLown & _ & (HFL4096 & HFLz & HFLceil)).
rewrite EFL in HFLown, HFL4096, HFLz, HFLceil.
(* the atoms: the registers of the cut, the thirteen saved words, the flag pointer, SH(FR) *)
set (E := Eimg (Ereg regs (s25_extra cx))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r).
{ intros m r Hm. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 15)%nat -> ew E (32 + j) = nth j (s25_extra cx) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESV : forall j, (j < 13)%nat -> ew E (32 + j) = getr (x_regs cx) (nth j LT_SAVED 0%bv)).
{ intros j Hj. rewrite (EX j ltac:(lia)). unfold s25_extra.
  do 13 (destruct j as [|j]; [reflexivity|]). lia. }
assert (E45 : ew E 45 = w64 (x_fl cx)) by exact (EX 13%nat ltac:(lia)).
assert (E46 : ew E 46 = w64 (x_sh cx)) by exact (EX 14%nat ltac:(lia)).
assert (E2 : ew E 2 = w64 (x_s1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), Hgp; exact Hgp0).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), Htp; exact Htp0).
assert (E8 : ew E 8 = w64 (x_sp0 cx)) by (rewrite (EE 8%nat 8%bv eq_refl); exact Hs0).
assert (E9 : ew E 9 = w64 (x_s1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact Hs1).
assert (E17 : ew E 17 = w64 (x_fr cx)) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
(* the realigned s1, the stack above the allocator's ceiling, the frame's shadow *)
pose proof (s25_s1_cases (x_sp0 cx) Hsp0al) as Hs1c.
assert (Hs1b : x_sp0 cx - 368 <= x_s1 cx <= x_sp0 cx - 352) by (unfold x_s1, LT_FRAME; lia).
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ unfold x_s1, LT_FRAME. destruct Hs1c as [Hc | Hc]; rewrite Hc;
  [replace (x_sp0 cx - 352 - x_sp0 cx) with (-352) by lia | replace (x_sp0 cx - 368 - x_sp0 cx) with (-368) by lia];
  reflexivity. }
clear Hs1c.
assert (Hsplo : alloc_ceiling + 32768 <= x_sp0 cx) by lia.
assert (HqS : x_sh cx = shadow_addr (x_fr cx)) by reflexivity.
assert (Hq1 : SHADOW_OFF + 512 <= x_sh cx).
{ rewrite HqS. unfold shadow_addr. pose proof (Z.div_le_mono 4096 (x_fr cx) 8 ltac:(lia) ltac:(lia)) as Hd.
  change (4096 / 8) with 512 in Hd. lia. }
assert (Hq2 : x_sh cx + 64 <= 17594332446784).
{ rewrite HqS. unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_le_mono (x_fr cx) 140737479966720 8 ltac:(lia) ltac:(lia)) as Hd.
  change (140737479966720 / 8) with 17592184995840 in Hd. lia. }
assert (Hq0 : 0 <= x_sh cx) by (unfold SHADOW_OFF in Hq1; lia).
assert (HFq : forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (x_sh cx <= a < x_sh cx + 64)).
{ intros a Ha Hb. destruct HFapp as (_ & [Hlo | (Hhi & _)]); unfold kLowShadowBeg, kHighMemBeg in *;
  unfold SHADOW_OFF in Hq1; lia. }
clear HFapp.
set (F := x_fr cx) in *. set (FL := x_fl cx) in *. set (q := x_sh cx) in *.
set (sp0 := x_sp0 cx) in *. set (s1v := x_s1 cx) in *.
assert (E17u : bv_unsigned (ew E 17) = F) by (rewrite E17; apply unsigned_lit_small; lia).
assert (E45u : bv_unsigned (ew E 45) = FL) by (rewrite E45; apply unsigned_lit_small; lia).
assert (E8u : bv_unsigned (ew E 8) = sp0) by (rewrite E8; apply unsigned_lit_small; lia).
assert (E9u : bv_unsigned (ew E 9) = s1v) by (rewrite E9; apply unsigned_lit_small; lia).
(* the seed of the executor at K85ec8 *)
assert (HS : st_ok_pi SEGS VAL E ss_s25
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85ec8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s25. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold s25_frame, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E17u. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ F 504 8 (SOff 45 0) FL);
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS _ _ _ _ Hflag).
    + unfold s25_s1, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ s1v 184 8 (SOff 46 0) q);
      [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ H184).
  - apply pairwise_disjoint_of_extents. unfold s25_frame, s25_s1, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E17u, E9u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold facts_ok, s25_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E17u, Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia. }
(* a6 and a7 hold the same frame pointer: give them one atom, so that the test of a6 at 0x85ed4 is decided by the
   frame's fact, and the flag word read through s2 = a6 meets the frame's region *)
pose proof (ast_ok_pi_set_reg_fp E _ _ (16%bv : bv 5) (SOff 17 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; cbn [ms_regs restrict mkst]; symmetry; exact R16))
  as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  let v := eval vm_compute in ssx in change ssx with v in HS end.
unfold cfg_at. change (w64 (BASE + LO_K85ec8)) with (Z_to_bv 64 (BASE + LO_K85ec8)).
(* 0x85ec8 .. 0x85ee4: the frame-done word into FR + 0 through a7, beqz a6 (not taken), a1 = 64, a0 = 184(s1) =
   SH(FR), s2 = a6, and the jal of meta_fill_f5 *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 17%nat) (b := F).
  - reflexivity.
  - exact E17u.
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right. right. right. left. exists 3, (x_fpos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  - eapply awr_ok_cons_gen with (n := 9%nat) (b := s1v).
    + reflexivity.
    + exact E9u.
    + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia.
    + apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
  set (mdv1 := mdx) in *; clearbody mdv1 end.
(* the shadow fill: meta_fill_f5(184(s1) = SH(FR), 64) over the frame's own 64 shadow bytes *)
pmkst HS.
assert (Hc10 : getr (ms_regs ms) 10 = w64 q) by (prreg HS (10%bv : bv 5) R; rewrite R; exact E46).
assert (Hc11 : getr (ms_regs ms) 11 = w64 64) by (prreg HS (11%bv : bv 5) R; rewrite R; reflexivity).
assert (Hc3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (prreg HS (3%bv : bv 5) R; rewrite R; exact E3).
assert (Hc4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (prreg HS (4%bv : bv 5) R; rewrite R; exact E4).
(* the return address of `jal meta_fill_f5` at 0x85ee4: 0x85ee8 = BASE + 0x1128 *)
assert (Hc1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 4392)) by (prreg HS (1%bv : bv 5) R; exact R).
assert (Hc2 : spZ (ms_regs ms) = sp0 + (s1v - sp0)).
{ prreg HS (2%bv : bv 5) R. unfold spZ. rewrite R, E2. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ exact (aj_set_shadow_atS SEGS B LAWS pa_segs_low (SIGMA SS___asan_set_shadow_f5) 0xf5 (SHF5 fx)
    W (ms_regs ms) (ms_mem ms) STK_LLVMFuzzerTestOneInput sp0 (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
    (x_mem cx) (x_md cx) [(3, x_fpos cx)] ly S mdv1 k 3 (x_fpos cx) q 64 (s1v - sp0) (Z_to_bv 64 (BASE + 4392))
    HJ ltac:(left; reflexivity) Hc10 Hc11 ltac:(lia)
    ltac:(rewrite EFA, <- HqS; lia)
    ltac:(rewrite EFA, <- HqS; change (fs_frame_bytes 3 / 8) with 64; lia)
    Hc2 Ho16 ltac:(lia) ltac:(unfold ESTACK; rewrite HSTK; lia) Hc3 Hc4 Hc1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity])). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hkeep2 & _ & _).
(* what the run and the fill left alone: everything but the frame-done word and the frame's shadow *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (q <= a < q + 64) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite (Hkeep2 a Ha H2). apply aview_eq_of. apply HFr.
  rewrite unsigned_lit_small by lia. intros (r & Hin & Hrg). cbn [In ss_mem] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  [rewrite E17u in Hrg | ]; lia. }
clear HF HFr HG Hc10 Hc11 Hc3 Hc4 Hc1 Hc2 Hkeep2.
assert (KEEPF : forall a, F + 8 <= a < F + 512 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEEP1; [lia | lia | exact (HFq a ltac:(lia))]. }
assert (KEEPS : forall a, sp0 - 104 <= a < sp0 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEEP1; lia. }
assert (Hflag2 : rdword (aview SEGS (w_H W) mem2) (F + 504) = Some FL).
{ rewrite (rdword_ext (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) (F + 504));
  [exact Hflag | intros kk Hkk; apply KEEPF; lia]. }
assert (HSV2 : lt_saved cx (aview SEGS (w_H W) mem2)).
{ intros i r Hi. pose proof (HSV i r Hi) as Hv.
  assert (Hi13 : (i < 13)%nat) by (change 13%nat with (length LT_SAVED); apply nth_error_Some; rewrite Hi; discriminate).
  rewrite (rdword_ext (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2)); [exact Hv|].
  intros kk Hkk. apply KEEPS. change (x_sp0 cx) with sp0. lia. }
(* re-seat the symbolic state after the call: the three regions the release needs are rebuilt below *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ec := havoc E 1024 (map (getr regs2) CLOB)) in *.
assert (HEI2 : img_env VAL A_LIM Ec) by (unfold Ec; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (AG : forall m, (m < 1024)%nat -> ew Ec m = ew E m) by (intros m Hm; unfold Ec; apply ew_havoc_old; lia).
assert (E17uc : bv_unsigned (ew Ec 17) = F) by (rewrite (AG 17%nat ltac:(lia)); exact E17u).
assert (E45u2 : bv_unsigned (ew Ec 45) = FL) by (rewrite (AG 45%nat ltac:(lia)); exact E45u).
assert (E8u2 : bv_unsigned (ew Ec 8) = sp0) by (rewrite (AG 8%nat ltac:(lia)); exact E8u).
assert (ESVc : forall j, (j < 13)%nat -> sv_denot Ec (SOff (32 + j) 0) = getr (x_regs cx) (nth j LT_SAVED 0%bv)).
{ intros j Hj. cbn [sv_denot]. rewrite (AG (32 + j)%nat ltac:(lia)), (ESV j Hj), Z.add_0_r.
  apply Z_to_bv_bv_unsigned. }
pose proof (proj1 HJ2) as HAR2.
destruct (FFL ly S W mem2 md2 3 (x_fpos cx) HAR2 Hfin) as (HFLpres2 & _ & _ & _).
rewrite EFL in HFLpres2.
(* the saved words below s0 = SP0, read by the 13 restores *)
pose proof (st_ok_pi_add_region Ec _ _ s25_stack HS eq_refl
  ltac:(unfold s25_stack, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E8u2; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?nn 0))) =>
      let j := eval compute in (nn - 32)%nat in
      apply (s25_chunk_ok Ec (w_H W) mem2 cx j (nth j LT_SAVED 0%bv) off HSV2 eq_refl (ESVc j ltac:(lia)));
      lia
    end)
  ltac:(cbn [all_disjoint]; exact I)) as HS2.
clear HS. rename HS2 into HS.
(* the frame's flag word FR + 504, read by ld a0,504(s2) *)
pose proof (st_ok_pi_add_region Ec _ _ s25_frame_ro HS eq_refl
  ltac:(unfold s25_frame_ro, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E17uc; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    constructor; [|constructor];
    apply (chunk_ok_val SEGS Ec _ F 504 8 (SOff 45 0) FL);
    [ cbn [sv_denot]; rewrite (AG 45%nat ltac:(lia)), E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
    | apply val_mem_of_rdword; exact Hflag2 ])
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, s25_stack, s25_frame_ro;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E17uc, E8u2;
    repeat match goal with |- _ /\ _ => split end; try exact I; lia)) as HS2.
clear HS. rename HS2 into HS.
(* the flag byte FL, the one byte the release writes *)
assert (HFLF : FL + 1 <= F + 504 \/ F + 512 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt | Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 512)) as [Hlt2 | Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
pose proof (st_ok_pi_add_region Ec _ _ s25_flag HS eq_refl
  ltac:(unfold s25_flag, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E45u2; split; [lia|]; split; [lia|]; split; [|constructor];
    intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLpres2)
  ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint, s25_stack, s25_frame_ro, s25_flag;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E17uc, E8u2, E45u2;
    repeat match goal with |- _ /\ _ => split end; try exact I; destruct HFLF; lia)) as HS2.
clear HS HFLF. rename HS2 into HS.
(* 0x85ee8 .. 0x85fc4: the release (the store of 0 through FR[504] frees the frame: own [(3, fpos)] -> []),
   j 0x85f88, a0 = 0, sp = s0 - 352, the 13 restores, sp += 352; the run stops at the ret (0x85fc8) *)
paj_run_flag_sh RUNF HS HJ2.
{ lia. }
{ intros a (r & Hin & Hrg). cbn [In ss_mem] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  unfold s25_flag, s25_frame_ro, s25_stack in Hrg;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  [ right; rewrite EFL; rewrite E45u2 in Hrg; lia | exfalso; lia | exfalso; lia ]. }
{ lazymatch goal with |- forall msr, st_ok_pi _ _ _ ?ssx _ -> _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
    intros msr Hmsr;
    pose proof (st_ok_pi_region_nth Ec ssx msr 0%nat r0 Hmsr ltac:(vm_compute; reflexivity)) as HR end.
  destruct HR as (_ & _ & _ & HC). inversion HC as [|ch chs Hch Hrest]. subst.
  destruct (Hch 0 ltac:(cbn; lia)) as (bb & Hbb & Hmb).
  cbn [YP09.r_base YP09.c_off YP09.c_val cbyte YP09.c_len base_val] in Hbb, Hmb.
  rewrite EFL. rewrite E45u2 in Hmb.
  replace (FL + 0 + 0) with FL in Hmb by lia. rewrite Hmb. f_equal.
  cbn in Hbb. injection Hbb as <-. reflexivity. }
lazymatch goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := ?mdx |} _ =>
  set (mdv2 := mdx) in *; clearbody mdv2; set (msF := msx) in *; clearbody msF end.
lazymatch goal with H : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ => rename H into HFr4 end.
(* what the release changed: the flag byte; with the run and the fill before it, the frame-done word and the frame's
   shadow; no image byte *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> FL ->
  aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hne. apply aview_eq_of. apply HFr4.
  rewrite unsigned_lit_small by lia. intros (r & Hin & Hrg). cbn [In ss_mem] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]];
  unfold s25_flag, s25_frame_ro, s25_stack in Hrg;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  [ rewrite E45u2 in Hrg; lia | lia | lia ]. }
assert (KEEPI : forall a, kImgLo <= a < kImgEnd ->
  aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a).
{ intros a Ha. unfold kImgLo, kImgEnd in Ha. pose proof (zone2_img _ _ HFLz) as HFLimg.
  unfold off_img in HFimg, HFLimg. unfold SHADOW_OFF in Hq1.
  rewrite (KEEP2 a ltac:(lia) ltac:(lia)). apply KEEP1; lia. }
(* the cut RET: the journal with own [], the entry's callee-saved registers and ra, a0 = 0 *)
pmkst HS.
pose proof (HRET fx) as HR. unfold LT_RET_stmt in HR.
refine (HR cx ly (stack_free_state 3 (x_fpos cx) S) W (ms_regs msF) (ms_mem msF) mdv2 k acc HB0 Hfrm HJ2
  _ _ _ _ _ _).
- apply aregs_preserved_eqs.
  + prreg HS (2%bv : bv 5) R. rewrite R, (AG 8%nat ltac:(lia)), E8.
    unfold sp0, x_sp0, spZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + prreg HS (3%bv : bv 5) R. rewrite R, (AG 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl). exact Hgp.
  + prreg HS (4%bv : bv 5) R. rewrite R, (AG 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl). exact Htp.
  + prreg HS (8%bv : bv 5) R. rewrite R, (AG 33%nat ltac:(lia)). exact (ESV 1%nat ltac:(lia)).
  + prreg HS (9%bv : bv 5) R. rewrite R, (AG 34%nat ltac:(lia)). exact (ESV 2%nat ltac:(lia)).
  + prreg HS (18%bv : bv 5) R. rewrite R, (AG 35%nat ltac:(lia)). exact (ESV 3%nat ltac:(lia)).
  + prreg HS (19%bv : bv 5) R. rewrite R, (AG 36%nat ltac:(lia)). exact (ESV 4%nat ltac:(lia)).
  + prreg HS (20%bv : bv 5) R. rewrite R, (AG 37%nat ltac:(lia)). exact (ESV 5%nat ltac:(lia)).
  + prreg HS (21%bv : bv 5) R. rewrite R, (AG 38%nat ltac:(lia)). exact (ESV 6%nat ltac:(lia)).
  + prreg HS (22%bv : bv 5) R. rewrite R, (AG 39%nat ltac:(lia)). exact (ESV 7%nat ltac:(lia)).
  + prreg HS (23%bv : bv 5) R. rewrite R, (AG 40%nat ltac:(lia)). exact (ESV 8%nat ltac:(lia)).
  + prreg HS (24%bv : bv 5) R. rewrite R, (AG 41%nat ltac:(lia)). exact (ESV 9%nat ltac:(lia)).
  + prreg HS (25%bv : bv 5) R. rewrite R, (AG 42%nat ltac:(lia)). exact (ESV 10%nat ltac:(lia)).
  + prreg HS (26%bv : bv 5) R. rewrite R, (AG 43%nat ltac:(lia)). exact (ESV 11%nat ltac:(lia)).
  + prreg HS (27%bv : bv 5) R. rewrite R, (AG 44%nat ltac:(lia)). exact (ESV 12%nat ltac:(lia)).
- prreg HS (1%bv : bv 5) R. rewrite R, (AG 32%nat ltac:(lia)). exact (ESV 0%nat ltac:(lia)).
- prreg HS (10%bv : bv 5) R. rewrite R. reflexivity.
- exact (s25_img_kept B cx (w_H W) mem (ms_mem msF) KEEPI HIMG).
- unfold lt_blocks, ablocks in *. rewrite blocks_stack_free_state. exact HBL.
- destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6). unfold lt_bud.
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTFL); exact B4|].
  split; [exact B5 | exact B6].
Qed.

End e.
End c.
End b.
