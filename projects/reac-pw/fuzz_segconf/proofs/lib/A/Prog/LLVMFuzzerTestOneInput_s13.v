(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the head of the top loop of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x865f4 .. 0x86694: the header bytes, the cases r = 1, r = 2 and r >= 3, the 8192 clamp), from LT_LH_stmt's state to the mid point LH_M1_stmt, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment lemma from one point of the function to the next, its seed lemma cl_seedX) and A/ACbk.v (the walk through the branches). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s23.v, with its module paths, module names and numbers changed; 990 of its 1070 lines of code are new or changed and 452 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s14.v, with its module paths and module names changed; 304 of its 340 lines of code are new or changed and 1034 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S03 of the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s13: from the cut K84f98
   (0x84f98, calloc(1, 9236) returned m) to the file loop's head K85024 at turn 0 (0x85024), the statement
   lt_seg_S03_stmt of LLVMFuzzerTestOneInput_defs.v.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan.s lines 155-189):
   - 0x84f98 .. 0x84fec, one token run: sd s6,160(s1) (c); beqz s6 and beqz a0 to the abort pair 0x85d6c, both
     decided not taken in the run by the facts c >= 4096 and m >= 4096 (the allocator's blocks, lt_hblk); a1 := m;
     the slots 56 (FR + 32), 80 (FR + 96), 96 (FR + 176), 104 (FR + 192), 8 (FR), 48 (FR + 256) from s3 = FR;
     32(s1) := lbu 40(s1) (cap < 40); s2 := m + 0x2000 into 184(s1); a0 := c (ld 160(s1)); 168(s1) := m; the jal
     of reac_segconf_init;
   - reac_segconf_init(c) through PaCall.v's cl_callS, its contract (apost_base, EV 0) applied at the segment's FP
     state: c holds rconf0, the callee keeps every byte outside its window and c (sa_kept), the state changes
     only by set_fs (sa_noalloc);
   - 0x84ff0 .. 0x85020, one run to K85024: a0 := ld 168(s1) (m); s2 := 0; 72(s1) := m + 32; s3 := -8;
     64(s1) := ((m + 20) >> 3) + the shadow base (ld 176(s1)); s6 := 1; 144(s1) := s5 (SH(FR)); 88(s1) := s9
     (nfiles); closed by LTA_K85024 at turn 0 (seg_run 0 = (rconf0, mconf0, true); m's zeros encode mconf0).
   The facts of the cut are carried by three reader agreements: each run's frame_of (only its s1 windows change)
   and the callee's sa_kept (only its stack window and [c, c + 16616) change); the frame, its shadow, the image
   bytes and m lie outside them (AR_sep_law, in_app, off_img, sep_blocks), so lt_img needs no image hypothesis.
   THE FORM: fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_s41.v aw_st5 (a run to a point, the NULL tests decided
   by the blocks' facts) and _s65.v lt_rc_call_loc (a program call through cl_callS, the callee's contract
   applied, the caller's facts carried past it) at origin/ossv/recipes 501c0d516c69.
   Section hypotheses: the callee contract reac_segconf_init_contract (lib/A/Prog/reac_segconf_init_c.v) at every
   FP state, seg_sig_prog and ameter_fs_laws; AR_laws is YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67 YG0q YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegPa SegPaLib PaCall PaDenot SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_init_c
LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s13k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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
(* the callee's contract, at every FP state, at the listing's entry of reac_segconf_init and its window *)
Hypothesis HINIT : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_init) STK_reac_segconf_init.
(* the walk's hypotheses: the call targets of the program functions, the meter across a set_fs state change *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis MTFL : ameter_fs_laws MT.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Theorem lt_seg_S03 : lt_seg_S03_stmt B MT.
Proof.
unfold lt_seg_S03_stmt.
intros HK cx ly S W regs mem md k acc c m HBs Hfrm HCORE HC HM HZ R10 R18 R19 R20 R21 R22 R24 R25 HSL.
pose proof HCORE as (HF & HIMG & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H176 & _).
pose proof (s13_sp B MT cx HBs) as (Hsp0 & Hsp16 & Hs1 & Hs32 & Htop0).
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HBUD as (Hb1 & Hb2 & Hb3 & _).
pose proof HC as (HCin & Hc4 & Hc16 & _). pose proof HM as (HMin & Hm4 & Hm16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (_ & _ & Hcc & Hcapp & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & _).
pose proof (blk_off_imgP B ly S W mem md c _ HAR HCin) as Hcoff.
pose proof (s13_fr B MT cx ly S W mem md k HBs HJ) as (HFR4 & HFRc & HFRd).
pose proof (HFRd c _ HCin) as HFRc'.
assert (Hmcd : zdisjoint (m, req_size seg_spec.SEG_M_SIZE) (c, req_size seg_spec.SEG_C_SIZE)).
{ apply (sep_blocks SEGS B LAWS ly S W mem md m _ c _ HAR HMin HCin).
  intros Heq. injection Heq as _ Hsz. unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in Hsz. lia. }
assert (HRC : req_size seg_spec.SEG_C_SIZE = seg_spec.SEG_C_SIZE) by reflexivity.
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
assert (HCS : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
rewrite HRC in Hcc, Hcapp, Hcoff, Hmcd, HFRc'. rewrite HRM in Hmc, Hmcd.
unfold zdisjoint in Hmcd. cbn [fst snd] in Hmcd. unfold off_img in Hcoff.
pose proof asan_consts as (HAC & _ & _ & _ & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HSI : STK_reac_segconf_init = 4112) by reflexivity.
pose proof (s13_cap_range (x_pl cx)) as Hcap.
assert (Hcap' : 0 <= x_cap cx < 40) by (unfold x_cap; exact Hcap).
assert (Hw40 : rdword (rdW W mem) (x_s1 cx + 40) = Some (x_cap cx))
  by (apply HSL; cbn [In]; right; right; left; reflexivity).
pose proof (s13_seed1 W regs mem (x_s1 cx) m c (x_cap cx) R9 ltac:(lia) ltac:(lia) Hs32 R10 ltac:(lia) Hm16
  R22 ltac:(lia) Hc16 ltac:(unfold x_cap; lia) Hw40 (fun a Ha => Hpres a ltac:(lia))) as HS.
assert (SHOK : sh_ok SEGS s13_X [] (s13_E regs (x_cap cx)) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s13_E regs (x_cap cx))) by (unfold s13_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s13_E regs (x_cap cx)) n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold s13_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew (s13_E regs (x_cap cx)) 32 = Z_to_bv 64 (x_cap cx)).
{ unfold s13_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (Usp9 : bv_unsigned (ew (s13_E regs (x_cap cx)) 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
remember (s13_E regs (x_cap cx)) as E eqn:HE. clear HE.
unfold cfg_at.
(* 0x84f98 .. 0x84fec: 160(s1) := c, the NULL tests of c and m (decided false by their facts, >= 4096), a1 := m,
   the slots 56, 80, 96, 104, 8, 48 from s3 = FR, 32(s1) := lbu 40(s1), s2 := m + 0x2000 into 184(s1), a0 := c,
   168(s1) := m; the jal of reac_segconf_init *)
paj_run_tok RUN HS HJ SHOK s13_span.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | apply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
        [reflexivity | rewrite Usp9; lia | cbn; lia | cbn; lia |] ]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
rename ms into ms1.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ s13_w1 (x_s1 cx) a -> rdW W (ms_mem ms1) a = rdW W mem a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (s13_w1 (x_s1 cx)) Hfr); [
   intros b wlo whi a' Hin Hrr; vm_compute in Hin;
   repeat (destruct Hin as [Hq0 | Hin];
     [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp9 in Hrr; unfold s13_w1; lia|]);
   destruct Hin
 | exact Ha | exact Hn ]) end.
(* the slots run 1 wrote, at the reader after it *)
assert (UFR : forall x, 0 <= x <= 256 -> U E (SOff 19 x) = x_fr cx + x).
{ intros x Hx. apply s13_U_atom; [rewrite (EEo 19%nat 19%bv eq_refl); exact R19 | lia | lia]. }
assert (W8 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 8) = Some (x_fr cx)).
{ s13_rd HS 0%nat 8 (SOff 19 0); [exact Usp9 | rewrite (UFR 0) by lia; lia | lia]. }
assert (W32 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 32) = Some (x_cap cx)).
{ s13_rd HS 1%nat 32 (SOff 32 0); [exact Usp9 | rewrite (s13_U_atom E 32 0 (x_cap cx) E32) by lia; lia | lia]. }
assert (W48 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 48) = Some (x_fr cx + 256)).
{ s13_rd HS 3%nat 48 (SOff 19 256); [exact Usp9 | apply UFR; lia | lia]. }
assert (W56 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 56) = Some (x_fr cx + 32)).
{ s13_rd HS 3%nat 56 (SOff 19 32); [exact Usp9 | apply UFR; lia | lia]. }
assert (W80 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 80) = Some (x_fr cx + 96)).
{ s13_rd HS 4%nat 80 (SOff 19 96); [exact Usp9 | apply UFR; lia | lia]. }
assert (W96 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 96) = Some (x_fr cx + 176)).
{ s13_rd HS 5%nat 96 (SOff 19 176); [exact Usp9 | apply UFR; lia | lia]. }
assert (W104 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 104) = Some (x_fr cx + 192)).
{ s13_rd HS 5%nat 104 (SOff 19 192); [exact Usp9 | apply UFR; lia | lia]. }
assert (W160 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 160) = Some c).
{ s13_rd HS 6%nat 160 (SOff 22 0); [exact Usp9 |
    rewrite (s13_U_atom E 22 0 c ltac:(rewrite (EEo 22%nat 22%bv eq_refl); exact R22)) by lia; lia | lia]. }
assert (W168 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 168) = Some m).
{ s13_rd HS 6%nat 168 (SOff 10 0); [exact Usp9 |
    rewrite (s13_U_atom E 10 0 m ltac:(rewrite (EEo 10%nat 10%bv eq_refl); exact R10)) by lia; lia | lia]. }
assert (W184 : rdword (rdW W (ms_mem ms1)) (x_s1 cx + 184) = Some (m + seg_spec.MC_N)).
{ s13_rd HS 7%nat 184 (SAlu ALU_ADD (SOff 10 0) (SOff 18 0)); [exact Usp9 | | unfold seg_spec.MC_N; lia].
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (s13_U_atom E 10 0 m ltac:(rewrite (EEo 10%nat 10%bv eq_refl); exact R10)) by lia.
  rewrite (s13_U_atom E 18 0 seg_spec.MC_N ltac:(rewrite (EEo 18%nat 18%bv eq_refl); exact R18))
    by (unfold seg_spec.MC_N; lia).
  rewrite !Z.add_0_r. apply zcanon_id. unfold M64, seg_spec.MC_N. lia. }
(* the call *)
pmkst HS.
rewrite (SIGP SS_reac_segconf_init ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_init) with AF_reac_segconf_init by (vm_compute; reflexivity).
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
assert (HCn : ~ In (c, seg_spec.SEG_C_SIZE) (x_bl0 B cx)).
{ apply (s13_not_entry B ly S W mem md [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] _ _ HAR HBL);
    [right; left; reflexivity | cbn [snd]; rewrite HRC, HCS; lia]. }
apply (s13_call B MT HINIT cx ly S W (ms_regs ms1) (ms_mem ms1) md1 k c (lt_post B MT cx) HBs HJ).
{ rewrite P2, (EEo 2%nat 2%bv eq_refl). exact R2. }
{ rewrite P3, (EEo 3%nat 3%bv eq_refl). exact R3. }
{ rewrite P4, (EEo 4%nat 4%bv eq_refl). exact R4. }
{ rewrite P8, (EEo 8%nat 8%bv eq_refl). exact R8. }
{ rewrite P1. reflexivity. }
{ rewrite P10, (EEo 22%nat 22%bv eq_refl). exact R22. }
{ exact HCin. }
{ exact HCn. }
{ pose proof (s13_hblk B ly S W (ms_mem ms1) md1 c _ (proj1 HJ) HCin ltac:(rewrite HCS; lia) HRC) as (_ & _ & _ & HA).
  exact HA. }
{ lia. }
intros ly2 S2 W2 regs2 mem2 md2 HJ2 HP HKP HZB (HPm & -> & (fsf & ->)).
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4112 <= a < x_s1 cx) -> ~ (c <= a < c + 16616) ->
  rdW W2 mem2 a = rdW W (ms_mem ms1) a).
{ intros a Ha H1 H2. apply HKP; [exact Ha | | exact H2].
  unfold spZ. rewrite P2, (EEo 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite HSI. exact H1. }
assert (HPr : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms1) r)
  by (intros r z Hz Hr; exact (s13_pres _ _ r z HP Hz Hr)).
assert (R9b : getr regs2 9 = w64 (x_s1 cx)).
{ rewrite (HPr 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P9,
    (EEo 9%nat 9%bv eq_refl). exact R9. }
assert (W168b : rdword (rdW W2 mem2) (x_s1 cx + 168) = Some m).
{ rewrite (rdword_ext (rdW W (ms_mem ms1)) (rdW W2 mem2)); [exact W168|]. intros kk Hk. apply KEEPC; lia. }
assert (W176b : rdword (rdW W2 mem2) (x_s1 cx + 176) = Some SHADOW_OFF).
{ rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact H176|]. intros kk Hk.
  rewrite (KEEPC (x_s1 cx + 176 + kk)) by lia. apply KEEP1; [lia | unfold s13_w1; lia]. }
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof (s13_seed2 W2 regs2 mem2 (x_s1 cx) m R9b ltac:(lia) ltac:(lia) Hs32 ltac:(lia) Hm16 W168b W176b
  (fun a Ha => Hpres2 a ltac:(lia))) as HS2.
assert (SHOK2 : sh_ok SEGS s13_X [] (s13_E regs2 m) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (HEI2 : img_env VAL A_LIM (s13_E regs2 m)) by (unfold s13_E; apply Eimg_env).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s13_E regs2 m) n = getr regs2 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold s13_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32b : ew (s13_E regs2 m) 32 = Z_to_bv 64 m).
{ unfold s13_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0). }
assert (Usp92 : bv_unsigned (ew (s13_E regs2 m) 9) = x_s1 cx).
{ rewrite (EEo2 9%nat 9%bv eq_refl), R9b. unfold w64. apply unsigned_lit_small. lia. }
remember (s13_E regs2 m) as E2 eqn:HE2. clear HE2.
change (w64 (BASE + S13_RA)) with (Z_to_bv 64 (BASE + S13_RA)).
(* 0x84ff0 .. 0x85020: a0 := m (ld 168(s1)), s2 := 0, 72(s1) := m + 32, s3 := -8, 64(s1) := ((m + 20) >> 3) + the
   shadow base (ld 176(s1)), s6 := 1, 144(s1) := s5, 88(s1) := s9; to the file loop's head *)
paj_run_to_tok RUNTO HS2 HJ2 SHOK2 s13_span LO_K85024.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | apply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
        [reflexivity | rewrite Usp92; lia | cbn; lia | cbn; lia |] ]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
rename ms into ms3.
lazymatch goal with Hfr : frame_of E2 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ s13_w2 (x_s1 cx) a -> rdW W2 (ms_mem ms3) a = rdW W2 mem2 a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (s13_w2 (x_s1 cx)) Hfr); [
   intros b wlo whi a' Hin Hrr; vm_compute in Hin;
   repeat (destruct Hin as [Hq0 | Hin];
     [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp92 in Hrr; unfold s13_w2; lia|]);
   destruct Hin
 | exact Ha | exact Hn ]) end.
(* the run-2 slots, at the reader after it *)
pose proof HS2 as HS2o. unfold st_ok_pi in HS2o.
assert (U32b : forall x, 0 <= x <= 32 -> U E2 (SOff 32 x) = m + x)
  by (intros x Hx; apply s13_U_atom; [exact E32b | lia | lia]).
assert (X64 : rdword (rdW W2 (ms_mem ms3)) (x_s1 cx + 64) = Some (shadow_addr (m + 0x14))).
{ s13_rd HS2o 0%nat 64 (SAlu ALU_ADD (SLit 2147450880) (SAlu ALU_SRL (SOff 32 20) (SLit 3)));
    [exact Usp92 | | unfold shadow_addr, SHADOW_OFF; lia].
  rewrite U_SAlu, U_SLit, U_SAlu, U_SLit, (U32b 20) by lia.
  rewrite (zcanon_id 2147450880) by (unfold M64; lia). rewrite (zcanon_id 3) by (unfold M64; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((m + 20) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). unfold shadow_addr, SHADOW_OFF. reflexivity. }
assert (X72 : rdword (rdW W2 (ms_mem ms3)) (x_s1 cx + 72) = Some (m + 0x20)).
{ s13_rd HS2o 0%nat 72 (SOff 32 32); [exact Usp92 | apply U32b; lia | lia]. }
assert (X88 : rdword (rdW W2 (ms_mem ms3)) (x_s1 cx + 88) = Some (x_nf cx)).
{ pose proof (lt_nfiles_range (x_pl cx)) as Hnf.
  s13_rd HS2o 1%nat 88 (SOff 25 0); [exact Usp92 | | unfold x_nf; lia].
  rewrite (s13_U_atom E2 25 0 (x_nf cx)); [lia | | unfold x_nf; lia | unfold x_nf; lia].
  rewrite (EEo2 25%nat 25%bv eq_refl),
    (HPr 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P25,
    (EEo 25%nat 25%bv eq_refl). exact R25. }
assert (X144 : rdword (rdW W2 (ms_mem ms3)) (x_s1 cx + 144) = Some (x_sh cx)).
{ s13_rd HS2o 2%nat 144 (SOff 21 0); [exact Usp92 | | unfold x_sh, shadow_addr, SHADOW_OFF; lia].
  rewrite (s13_U_atom E2 21 0 (x_sh cx)); [lia | | unfold x_sh, shadow_addr, SHADOW_OFF; lia |
    unfold x_sh, shadow_addr, SHADOW_OFF; lia].
  rewrite (EEo2 21%nat 21%bv eq_refl),
    (HPr 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P21,
    (EEo 21%nat 21%bv eq_refl). exact R21. }
(* the bytes kept from each earlier reader *)
assert (K13 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4112 <= a < x_s1 cx) -> ~ (c <= a < c + 16616) ->
  ~ s13_w2 (x_s1 cx) a -> rdW W2 (ms_mem ms3) a = rdW W (ms_mem ms1) a).
{ intros a Ha H1 H2 H3. rewrite (KEEP2 a Ha H3). exact (KEEPC a Ha H1 H2). }
assert (K03 : forall a, 0 <= a < 2 ^ 64 -> ~ s13_w1 (x_s1 cx) a -> ~ (x_s1 cx - 4112 <= a < x_s1 cx) ->
  ~ (c <= a < c + 16616) -> ~ s13_w2 (x_s1 cx) a -> rdW W2 (ms_mem ms3) a = rdW W mem a).
{ intros a Ha H0 H1 H2 H3. rewrite (K13 a Ha H1 H2 H3). exact (KEEP1 a Ha H0). }
assert (Y1 : forall o v, 8 <= o -> o + 8 <= 192 -> rdword (rdW W (ms_mem ms1)) (x_s1 cx + o) = Some v ->
  ~ (64 <= o < 80 \/ 56 < o < 64 \/ 88 <= o < 96 \/ 80 < o < 88 \/ 144 <= o < 152 \/ 136 < o < 144) ->
  rdword (rdW W2 (ms_mem ms3)) (x_s1 cx + o) = Some v).
{ intros o v Ho1 Ho2 Hv Hn. rewrite (rdword_ext (rdW W (ms_mem ms1)) (rdW W2 (ms_mem ms3))); [exact Hv|].
  intros kk Hk. apply K13; [lia | lia | lia | unfold s13_w2; lia]. }
assert (Y0 : forall o v, 8 <= o -> o + 8 <= 192 -> rdword (rdW W mem) (x_s1 cx + o) = Some v ->
  ~ s13_w1 (x_s1 cx) (x_s1 cx + o) -> ~ s13_w1 (x_s1 cx) (x_s1 cx + o + 7) ->
  ~ (64 <= o < 80 \/ 56 < o < 64 \/ 88 <= o < 96 \/ 80 < o < 88 \/ 144 <= o < 152 \/ 136 < o < 144) ->
  rdword (rdW W2 (ms_mem ms3)) (x_s1 cx + o) = Some v).
{ intros o v Ho1 Ho2 Hv Hn1 Hn2 Hn. rewrite (rdword_ext (rdW W mem) (rdW W2 (ms_mem ms3))); [exact Hv|].
  intros kk Hk. apply K03; [lia | unfold s13_w1 in *; lia | lia | lia | unfold s13_w2; lia]. }
(* the frame's bytes and the image's bytes are those of the K84f98 reader *)
assert (HKF : forall a, x_sp0 cx - 104 <= a < x_sp0 cx \/ x_fr cx <= a < x_fr cx + 24 \/
  x_fr cx + LT_FLAGW <= a < x_fr cx + LT_FLAGW + 8 \/ x_s1 cx + 176 <= a < x_s1 cx + 184 \/
  x_sh cx <= a < x_sh cx + 36 -> rdW W2 (ms_mem ms3) a = rdW W mem a).
{ intros a Ha. unfold LT_FLAGW in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply K03; [lia | unfold s13_w1; lia | lia | lia | unfold s13_w2; lia].
  - apply K03; [lia | unfold s13_w1; lia | lia | lia | unfold s13_w2; lia].
  - apply K03; [lia | unfold s13_w1; lia | lia | lia | unfold s13_w2; lia].
  - apply K03; [lia | unfold s13_w1; lia | lia | lia | unfold s13_w2; lia].
  - assert (Hsh : ~ (c <= a < c + 16616)).
    { intros Hx. apply (s13_sh_app (x_fr cx) c seg_spec.SEG_C_SIZE (a - x_sh cx) HFR4 HFRc Hcapp); [lia|].
      unfold x_sh in *. rewrite HCS. lia. }
    unfold x_sh, shadow_addr, SHADOW_OFF in Ha, Hsh.
    apply K03; [lia | unfold s13_w1; lia | lia | exact Hsh | unfold s13_w2; lia]. }
assert (HIE : s13_imgeq (rdW W mem) (rdW W2 (ms_mem ms3))).
{ intros a Ha. unfold kImgEnd in Ha.
  apply K03; [lia | unfold s13_w1; lia | lia | rewrite HCS in Hcoff; lia | unfold s13_w2; lia]. }
(* the registers at the head *)
pmkst HS2.
prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19.
prreg HS2 (20%bv : bv 5) Q20. prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (22%bv : bv 5) Q22.
prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (25%bv : bv 5) Q25.
assert (HCin2 : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly (set_fs fsf S)))
  by exact (Permutation_in _ (Permutation_sym HPm) HCin).
assert (HMin2 : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly (set_fs fsf S)))
  by exact (Permutation_in _ (Permutation_sym HPm) HMin).
apply (HK fx cx ly (set_fs fsf S) W2 (ms_regs ms3) (ms_mem ms3) md3 k acc c m HBs Hfrm).
- pose proof (lt_nfiles_range (x_pl cx)) as Hnf. unfold x_nf. lia.
- replace (6 + 2 * (x_nf cx - Z.of_nat 0)) with (6 + 2 * x_nf cx) by lia.
  split; [|split; [|split]].
  + apply (s13_frame_move B cx ly S W regs mem md k ly (set_fs fsf S) W2 (ms_regs ms3) (ms_mem ms3) md3 k HF HJ2);
      [s13_kr Q2 P2 EEo2 EEo HPr 2%nat (2%bv : bv 5); reflexivity | s13_kr Q3 P3 EEo2 EEo HPr 3%nat (3%bv : bv 5); reflexivity
      | s13_kr Q4 P4 EEo2 EEo HPr 4%nat (4%bv : bv 5); reflexivity | s13_kr Q8 P8 EEo2 EEo HPr 8%nat (8%bv : bv 5); reflexivity
      | s13_kr Q9 P9 EEo2 EEo HPr 9%nat (9%bv : bv 5); reflexivity | exact HKF].
  + exact (s13_img_kept B cx (rdW W mem) (w_H W2) (ms_mem ms3) HIE HIMG).
  + unfold lt_blocks. exact (Permutation_trans HPm HBL).
  + destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
    split; [exact (mo_le_set_fs_r MT MTFL _ _ fsf _ B4)|]. split; [exact B5 | exact B6].
- exact (s13_hblk B ly (set_fs fsf S) W2 (ms_mem ms3) md3 c _ (proj1 HJ2) HCin2 ltac:(rewrite HCS; lia) HRC).
- exact (s13_hblk B ly (set_fs fsf S) W2 (ms_mem ms3) md3 m _ (proj1 HJ2) HMin2 ltac:(rewrite HMS; lia) HRM).
- rewrite Q18. reflexivity.
- rewrite Q19. apply bv_eq. reflexivity.
- s13_kr Q20 P20 EEo2 EEo HPr 20%nat (20%bv : bv 5). exact R20.
- s13_kr Q21 P21 EEo2 EEo HPr 21%nat (21%bv : bv 5). exact R21.
- rewrite Q22. reflexivity.
- s13_kr Q24 P24 EEo2 EEo HPr 24%nat (24%bv : bv 5). exact R24.
- s13_kr Q25 P25 EEo2 EEo HPr 25%nat (25%bv : bv 5). exact R25.
- (* the slots of the file loop *)
  assert (S16 : rdword (rdW W mem) (x_s1 cx + 16) = Some (x_flags cx)) by (apply HSL; cbn [In]; left; reflexivity).
  assert (S24 : rdword (rdW W mem) (x_s1 cx + 24) = Some (x_fr cx)) by (apply HSL; cbn [In]; right; left; reflexivity).
  intros o v Hin. unfold LT_L in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-|]); try destruct Hin.
  + apply Y1; [lia | lia | exact W8 | lia].
  + apply Y0; [lia | lia | exact S16 | unfold s13_w1; lia | unfold s13_w1; lia | lia].
  + apply Y0; [lia | lia | exact S24 | unfold s13_w1; lia | unfold s13_w1; lia | lia].
  + apply Y1; [lia | lia | exact W32 | lia].
  + apply Y0; [lia | lia | exact Hw40 | unfold s13_w1; lia | unfold s13_w1; lia | lia].
  + apply Y1; [lia | lia | exact W48 | lia].
  + apply Y1; [lia | lia | exact W56 | lia].
  + exact X64.
  + exact X72.
  + apply Y1; [lia | lia | exact W80 | lia].
  + exact X88.
  + apply Y1; [lia | lia | exact W96 | lia].
  + apply Y1; [lia | lia | exact W104 | lia].
  + exact X144.
  + apply Y1; [lia | lia | exact W160 | lia].
  + apply Y1; [lia | lia | exact W168 | lia].
  + apply Y1; [lia | lia | exact W184 | lia].
- (* c holds the reader's initial state (reac_segconf_init), m the model's (calloc's zeros) *)
  unfold lt_cm. change (seg_spec.seg_rc (x_st cx 0)) with SegModel.rconf0.
  change (seg_spec.seg_mc (x_st cx 0)) with SegModel.mconf0.
  split.
  + exists (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE)). split; [|exact seg_spec.rconf_enc_zero].
    intros i Hi. rewrite repeat_length in Hi. rewrite KEEP2; [exact (HZB i ltac:(rewrite repeat_length; exact Hi)) | lia |].
    unfold s13_w2. rewrite HCS in Hi. lia.
  + exists (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_M_SIZE)). split; [|exact seg_spec.mconf_enc_zero].
    intros i Hi. rewrite repeat_length in Hi. rewrite HMS in Hi.
    rewrite K03; [| lia | unfold s13_w1; lia | lia | rewrite HMS, HCS in Hmcd; lia | unfold s13_w2; lia].
    rewrite (HZ (Z.of_nat i)) by (rewrite HMS; lia). rewrite s13_nth_repeat by lia. reflexivity.
- unfold lt_cnt. change (x_st cx 0) with (SegModel.rconf0, SegModel.mconf0, true). cbn. lia.
Qed.


End e.
End f.
End d.

Print Assumptions lt_seg_S03.
