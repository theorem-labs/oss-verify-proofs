(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v (rt_hand, fs_roF / fs_rwF) and
   APgStep.v (same_io_wvb) at 6ebe35ba632; adapted to the class-0 frame and the exit of reac_box_pin_parse. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgParse4.v, with its module paths and module names changed; 262 of its 291 lines of code are new or changed and 251 lines of the source are left out. *)
(* check_personality (fuzz_codec.c:256-281) at image A 0x83364, 156 instructions, real frame 32, against
   lib/A/Prog/CPgChkC.v's cdc_check_pers_specX. The walk is cut at the return address of each of its ten calls
   (lib/A/Prog/check_personality_A_cut.v); each segment below runs the engine from one cut to the next call and takes
   the callee's contract there.
   - cp_seg0: 0x83364 addi sp,sp,-32 and the saves of ra, s0, s1, s2 into [sp - 32, sp) (the walk's only stores, in
     the caller's stack allowance by the contract's two window premises), the shadow offset through the .got slot
     and its cell into s2, a0 = 1, 0x83388 jal personality_of: a0 = &personalities[0] (pers_ofA CA_PERS 1).
   - cp_seg1: mv s1,a0; a0 = 2; 0x83394 jal personality_of: a0 = &personalities[1].
   - cp_seg2: 0x83398 beqz s1 / beqz a0 (both not taken: the two addresses are not 0); the 8-byte instrumented check
     of s1 + 8 (its shadow byte, folded to a load of `SOff 32 off`, is 0: personalities[] is a registered global of
     48 bytes, globs_marked); ld a0 = the announce name 0x21360; a1 = .str 0x20f60; 0x833c4 jal strcmp wrapper:
     "CNTRL|24" against "CNTRL|24", a0 = 0.
   - cp_seg3: bnez a0 (not taken); the four 1-byte checks and loads of s1 + 16 .. s1 + 19 (1, 0x18, 4, 0x19, each
     equal to the constant it is compared with); the 8-byte check of s0 + 8; ld a0 = 0x21380; a1 = .str.2 0x20f80;
     0x8346c jal strcmp wrapper: "MAINUNIT" against "MAINUNIT", a0 = 0.
   - cp_seg4: bnez a0; the four checks and loads of s0 + 16 .. s0 + 19 (0, 8, 8, 9); a0 = 0; 0x834f4 jal
     personality_of: a0 = 0.
   - cp_seg5 .. cp_seg9: bnez a0 / bne a0,s1 / bne a0,s0 (each not taken: a0 is the value compared with); a0 = the
     literal .str, .str.2, .str.4, .str.5, .str.6 ("CNTRL|24", "MAINUNIT", "CNTRL|2", "MAINUNITS", ""); jal
     personality_from_name: a0 = &personalities[0], &personalities[1], 0, 0, 0 (from_name_resA).
   - cp_seg10: bnez a0 (not taken); the restores of ra, s0, s1, s2 from the save slots, addi sp,sp,32, ret.
   Every branch to the abort call at 0x83564 compares image data with a constant, and every instrumented check reads
   a shadow byte of personalities[] that is 0, so the engine decides each of them and never reaches 0x83564 or an
   error path (0x8356c .. 0x835d0). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Rt Require Import StrcmpDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgEncC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkImg CPgWalkKept CPgWalkRo CPgWalkStr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import check_personality_A_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis RF : cpw_rows_free B CA_ROSTRS.
Hypothesis POF : cdc_pers_of_specX tfibsegs B MT A_PERS_OF CA_PERS.
Hypothesis FN : cdc_from_name_specX tfibsegs B MT CA_RLO CA_RHI CA_PERS CA_ROSTRS A_FROM_NAME.
Hypothesis STR : astrcmp_realizes tfibsegs B A_STRCMP.
Variable X : cpctx.
Hypothesis HOK : cp_ok B X.

Lemma cp_seg0 : cp_rest B MT X 0x8338c cp_R1 ->
  SRr tfibsegs (c_W X) (cfg_at tfibsegs A_CHECK_PERS (c_regs X) (c_memc X) (c_mdc X)) (cp_post B MT X).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT.
pose proof HOK as (HE & HC).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hwhi & Hev & Hlive).
pose proof HJ as (HAR & _). cw_keep_j0 HJ HJ0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
destruct (cp_sp B X HOK) as (H46 & H47 & Hal & Hce & Hw1 & Hw2).
pose proof (cw_entry_base B TL LAWS A_CHECK_PERS 32 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T_check_pers HE
  ltac:(rewrite cp_T; lia) ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg (c_regs X) (cw_extra [])) as E eqn:HEE.
assert (B2 : bv_unsigned (ew E 2) = spZ (c_regs X)) by (subst E; rewrite (ew_Ereg_nat (c_regs X) _ 2 2%bv eq_refl); reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (c_regs X) r)
  by (intros n r Hn; subst E; exact (cw_ew_reg (c_regs X) [] n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
clear HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H (c_W X)) (c_memc X))) by constructor.
rewrite cp_T in Hwin.
unfold cfg_at. change (w64 A_CHECK_PERS) with (Z_to_bv 64 A_CHECK_PERS).
(* 0x83364 .. 0x83388: the prologue, the shadow offset, a0 = 1, jal personality_of *)
cw_run_to cw_awr_stk A_PERS_OF.
(* what the run kept: everything but the save area *)
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
  pose proof (cw_kept_run (fun a => spZ (c_regs X) - 32 <= a < spZ (c_regs X)) E rs (w_H (c_W X)) m0 m0 m1
    (fun _ _ _ => eq_refl) HFr ltac:(cw_kwr_stk)) as KE end.
pose proof (cw_kept0 B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ (c_regs X)) T_check_pers cno_wr HJ0
  ltac:(rewrite cp_T; lia) Hwhi) as KT0.
lazymatch goal with HG : mem_grows (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
  pose proof (cw_kept_step B LAWS T_check_pers (c_lyc X) (c_Sc X) (c_W X) (c_memc X) (c_mdc X) (c_W X) m0 m1
    (spZ (c_regs X)) cno_wr (fun a => spZ (c_regs X) - 32 <= a < spZ (c_regs X)) ltac:(rewrite cp_T; lia) HAR KT0
    (fun a Ha Hz => KE a Ha Hz) ltac:(intros a Ha; left; cbv beta in Ha; rewrite cp_T; lia)
    ltac:(intros a Hp; exact (apresent_grows _ _ _ a HG Hp))) as KT1 end.
(* the env of the run's end agrees with E below 33 *)
lazymatch goal with HS : st_ok _ ?Ev _ _ |- _ =>
  assert (AG : forall n, (n < 33)%nat -> ew Ev n = ew E n)
  by (first [ exact (fun n _ => eq_refl)
            | lazymatch goal with |- forall n, _ -> ew (extK ?E0 ?K ?ws) n = _ =>
                intros n Hn; destruct (env_agree_extK E0 K ws) as [HA _]; apply HA; lia end ]) end.
(* the save slots and the registers at the call *)
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
  let r := eval vm_compute in (nth 0 (ss_mem ssv) got_region) in
  pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) 0 r HS ltac:(vm_compute; reflexivity)) as HR0;
  cbn [ms_mem restrict] in HR0;
  pose proof (cp_slots0 X Ev _ _ HR0 ltac:(intros n r0 Hn Hr; exact (eq_trans (AG n ltac:(lia)) (EE n r0 Hr)))) as HSL;
  pose proof (cp_rg0 B X HOK Ev ssv Hh msv HS ltac:(intros n r0 Hn Hr; exact (eq_trans (AG n ltac:(lia)) (EE n r0 Hr)))
    ltac:(exact (eq_trans (AG 32%nat ltac:(lia)) E32)) ltac:(vm_compute; reflexivity)) as HRG1 end.
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?md1 _ |- _ =>
  assert (HM1 : cp_mem B MT X (c_lyc X) (c_Sc X) (c_W X) m1 md1);
  [ split; [exact HJ|]; split; [reflexivity|]; split; [apply Permutation_refl|];
    split; [apply cw_same_io_wvb|]; split; [apply mo_le_refl; exact MTL|];
    split; [exact KT1 | exact HSL]
  | ] end.
(* 0x83388 jal personality_of with a0 = 1, ra = 0x8338c *)
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); rreg HS (10%bv : bv 5) R10; rreg HS (1%bv : bv 5) R1 end.
eapply (cp_call_po B MT MTL LAWS X HOK _ _ _ _ _ _ 1 0x8338c cp_R1 POF HM1 HRG1).
- rewrite R10. reflexivity.
- lia.
- rewrite R1. reflexivity.
- reflexivity.
- lia.
- intros regs2 _ H10. unfold cp_R1. rewrite H10. reflexivity.
- exact NEXT.
Qed.

(* a segment from a cut: the start state, the run to stop, then the cut facts at the stop (HM1, HRG1) *)
Ltac cp_seg_run HM HRG HR start pins_ok pc stop :=
lazymatch type of HM with cp_mem _ _ _ ?ly2 ?S2 ?W2 ?mem2 ?md2 => lazymatch type of HRG with cp_rg ?Xv ?regs2 =>
  let HS := fresh "HS" in
  pose proof (start ly2 S2 W2 regs2 mem2 md2 pc _ HM HRG (pins_ok regs2 HRG HR)) as HS;
  let HJ := fresh "HJ" in pose proof HM as (HJ & _); unfold cp_jr in HJ;
  assert (SHOK : sh_ok tfibsegs CW_Bx [] (cp_E Xv regs2) (mrestrict (w_H W2) mem2)) by constructor;
  assert (B2 : bv_unsigned (ew (cp_E Xv regs2) 2) = spZ (c_regs Xv) - 32) by (eapply cp_E2; eassumption);
  pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
  cw_run_to cw_awr_stk stop;
  lazymatch goal with
  | HS2 : st_ok _ ?Ev ?ss (restrict _ ?ms), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m' ?md' _,
    HFr : frame_of _ ?rs _ _, HG : mem_grows _ _ |- _ =>
    let HM1 := fresh "HM1" in let HRG1 := fresh "HRG1" in
    pose proof (cp_mem_run B MT LAWS Xv HOK ly2 S2 W2 mem2 m' md2 md' HM
      (cp_ro_view _ rs (w_H W2) mem2 m' ltac:(cw_kwr_ro) HFr) HG HJ2 (cw_same_io_wvb _ _ _)) as HM1;
    pose proof (cp_rg_run Xv regs2 Ev ss (w_H W2) ms HRG HS2 ltac:(first [exact (fun n _ => eq_refl) | exact (cp_agree _ _ _ ltac:(lia))])
      ltac:(vm_compute; reflexivity)) as HRG1;
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS2 eq_refl)
  end
end end.

Lemma cp_seg1 : cp_rest B MT X 0x83398 cp_R2 -> cp_rest B MT X 0x8338c cp_R1.
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_seg_run HM HRG HR (cp_start0 B MT TL LAWS X HOK) (cp_pins1_ok X) 0x8338c A_PERS_OF.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
  rreg HS (10%bv : bv 5) R10; rreg HS (1%bv : bv 5) R1; rreg HS (9%bv : bv 5) R9 end.
eapply (cp_call_po B MT MTL LAWS X HOK _ _ _ _ _ _ 2 0x83398 cp_R2 POF HM1 HRG1).
- rewrite R10. reflexivity.
- lia.
- rewrite R1. reflexivity.
- reflexivity.
- lia.
- intros regs3 HP H10. split; [rewrite H10; reflexivity|].
  assert (P : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr _ (Z_to_bv 5 r)) by exact HP.
  rewrite <- cp_r9, (P 9 ltac:(unfold acallee_saved; lia)), cp_r9, R9. reflexivity.
- exact NEXT.
Qed.
(* the strcmp segments: a0 the announce name loaded from the personality, a1 the literal *)
Lemma cp_seg2 : cp_rest B MT X 0x833c8 (cp_Rs 0) -> cp_rest B MT X 0x83398 cp_R2.
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_seg_run HM HRG HR (cp_start1 B MT TL LAWS GM X HOK) (cp_pins2_ok X) 0x83398 A_STRCMP.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
  rreg HS (10%bv : bv 5) R10; rreg HS (11%bv : bv 5) R11; rreg HS (1%bv : bv 5) R1;
  rreg HS (9%bv : bv 5) R9; rreg HS (8%bv : bv 5) R8 end.
eapply (cp_call_str B MT TL LAWS RF X HOK _ _ _ _ _ _ 0x21360 0x20f60 9 9 NAME_C24A NAME_C24A 0x833c8 (cp_Rs 0) STR HM1 HRG1).
- rewrite R10. reflexivity.
- rewrite R11. reflexivity.
- apply globs_In_b. vm_compute. reflexivity.
- apply globs_In_b. vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite R1. reflexivity.
- reflexivity.
- lia.
- intros regs3 HP H10. eapply (cp_Rs_next _ regs3 _ 0 HP); [rewrite R9; reflexivity | rewrite R8; reflexivity | exact H10 | vm_compute; reflexivity].
- exact NEXT.
Qed.
Lemma cp_seg3 : cp_rest B MT X 0x83470 (cp_Rs 0) -> cp_rest B MT X 0x833c8 (cp_Rs 0).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_seg_run HM HRG HR (cp_start1 B MT TL LAWS GM X HOK) (fun r H1 H2 => cp_pins_s_ok X r 0 H1 H2) 0x833c8 A_STRCMP.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
  rreg HS (10%bv : bv 5) R10; rreg HS (11%bv : bv 5) R11; rreg HS (1%bv : bv 5) R1;
  rreg HS (9%bv : bv 5) R9; rreg HS (8%bv : bv 5) R8 end.
eapply (cp_call_str B MT TL LAWS RF X HOK _ _ _ _ _ _ 0x21380 0x20f80 9 9 NAME_PCA NAME_PCA 0x83470 (cp_Rs 0) STR HM1 HRG1).
- rewrite R10. reflexivity.
- rewrite R11. reflexivity.
- apply globs_In_b. vm_compute. reflexivity.
- apply globs_In_b. vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- rewrite R1. reflexivity.
- reflexivity.
- lia.
- intros regs3 HP H10. eapply (cp_Rs_next _ regs3 _ 0 HP); [rewrite R9; reflexivity | rewrite R8; reflexivity | exact H10 | vm_compute; reflexivity].
- exact NEXT.
Qed.
(* s0's four fields, then personality_of(0) *)
Lemma cp_seg4 : cp_rest B MT X 0x834f8 (cp_Rs 0) -> cp_rest B MT X 0x83470 (cp_Rs 0).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_seg_run HM HRG HR (cp_start1 B MT TL LAWS GM X HOK) (fun r H1 H2 => cp_pins_s_ok X r 0 H1 H2) 0x83470 A_PERS_OF.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
  rreg HS (10%bv : bv 5) R10; rreg HS (1%bv : bv 5) R1; rreg HS (9%bv : bv 5) R9; rreg HS (8%bv : bv 5) R8 end.
eapply (cp_call_po B MT MTL LAWS X HOK _ _ _ _ _ _ 0 0x834f8 (cp_Rs 0) POF HM1 HRG1).
- rewrite R10. reflexivity.
- lia.
- rewrite R1. reflexivity.
- reflexivity.
- lia.
- intros regs3 HP H10. eapply (cp_Rs_next _ regs3 _ 0 HP); [rewrite R9; reflexivity | rewrite R8; reflexivity | exact H10 | vm_compute; reflexivity].
- exact NEXT.
Qed.
(* the five calls of personality_from_name *)
Ltac cp_fn_seg HM HRG HR a0 pc q n retpc a1 :=
cp_seg_run HM HRG HR (cp_start0 B MT TL LAWS X HOK) (fun r H1 H2 => cp_pins_s_ok X r a0 H1 H2) pc A_FROM_NAME;
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
  let R10 := fresh "R10" in let R1 := fresh "R1" in let R9 := fresh "R9" in let R8 := fresh "R8" in
  rreg HS (10%bv : bv 5) R10; rreg HS (1%bv : bv 5) R1; rreg HS (9%bv : bv 5) R9; rreg HS (8%bv : bv 5) R8;
  lazymatch goal with HM1 : cp_mem _ _ _ _ _ _ _ _, HRG1 : cp_rg _ _ |- _ =>
  eapply (cp_call_fn B MT MTL TL LAWS RF X HOK _ _ _ _ _ _ q n retpc (cp_Rs a1) FN HM1 HRG1);
  [ rewrite R10; reflexivity
  | apply globs_In_b; vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite R1; reflexivity
  | reflexivity
  | lia
  | let regs3 := fresh "regs3" in let HP := fresh "HP" in let H10 := fresh "H10" in
    intros regs3 HP H10; eapply (cp_Rs_next _ regs3 _ a1 HP);
    [rewrite R9; reflexivity | rewrite R8; reflexivity | exact H10 | vm_compute; reflexivity]
  | assumption ] end end.
Lemma cp_seg5 : cp_rest B MT X 0x83508 (cp_Rs CA_PERS) -> cp_rest B MT X 0x834f8 (cp_Rs 0).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_fn_seg HM HRG HR 0 0x834f8 0x20f60 9 0x83508 CA_PERS.
Qed.
Lemma cp_seg6 : cp_rest B MT X 0x83518 (cp_Rs (CA_PERS + 24)) -> cp_rest B MT X 0x83508 (cp_Rs CA_PERS).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_fn_seg HM HRG HR CA_PERS 0x83508 0x20f80 9 0x83518 (CA_PERS + 24).
Qed.
Lemma cp_seg7 : cp_rest B MT X 0x83528 (cp_Rs 0) -> cp_rest B MT X 0x83518 (cp_Rs (CA_PERS + 24)).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_fn_seg HM HRG HR (CA_PERS + 24) 0x83518 0x20fa0 8 0x83528 0.
Qed.
Lemma cp_seg8 : cp_rest B MT X 0x83538 (cp_Rs 0) -> cp_rest B MT X 0x83528 (cp_Rs 0).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_fn_seg HM HRG HR 0 0x83528 0x20fc0 10 0x83538 0.
Qed.
Lemma cp_seg9 : cp_rest B MT X 0x83548 (cp_Rs 0) -> cp_rest B MT X 0x83538 (cp_Rs 0).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros NEXT W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
cp_fn_seg HM HRG HR 0 0x83538 0x20fe0 1 0x83548 0.
Qed.
(* the return *)
Lemma cp_seg10 : cp_rest B MT X 0x83548 (cp_Rs 0).
Proof using MTL TL LAWS GM RF POF FN STR HOK.
intros W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HM & HRG & HR).
pose proof (cp_start0 B MT TL LAWS X HOK ly2 S2 W2 regs2 mem2 md2 0x83548 _ HM HRG (cp_pins_s_ok X regs2 0 HRG HR)) as HS.
pose proof HM as (HJ & _). unfold cp_jr in HJ.
assert (SHOK : sh_ok tfibsegs CW_Bx [] (cp_E X regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (B2 : bv_unsigned (ew (cp_E X regs2) 2) = spZ (c_regs X) - 32) by (eapply cp_E2; eassumption).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
cw_run cw_awr_stk.
lazymatch goal with
| HS2 : st_ok _ ?Ev ?ss (restrict _ ?ms), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m' ?md' _,
  HFr : frame_of _ ?rs _ _, HG : mem_grows _ _ |- _ =>
  pose proof (cp_mem_run B MT LAWS X HOK ly2 S2 W2 mem2 m' md2 md' HM
    (cp_ro_view _ rs (w_H W2) mem2 m' ltac:(cw_kwr_ro) HFr) HG HJ2 (cw_same_io_wvb _ _ _)) as HM1;
  destruct (cp_fin_regs B X HOK regs2 Ev ss (w_H W2) ms HRG HS2
    ltac:(first [exact (fun n _ => eq_refl) | exact (cp_agree _ _ _ ltac:(lia))]) ltac:(vm_compute; reflexivity)) as (HP & H1);
  eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W2 Ev); [exact HS2 | reflexivity | vm_compute; reflexivity |];
  intros mat'; exact (cp_post_ret B MT LAWS X HOK ly2 S2 W2 m' md' (ms_regs ms) mat' HM1 HP H1)
end.
Qed.
End b.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* check_personality's A-level contract, from the contracts of the functions it calls (personality_of at 0x84888,
   personality_from_name at 0x847dc, the strcmp wrapper at 0x422d4), the start-up certificate of the registered
   globals and that the string literals are none of the runtime's own bytes (lib/A/Prog/CPgWalkRo.v) *)
Theorem check_personality_A_holds :
  cdc_pers_of_specX tfibsegs B MT A_PERS_OF CA_PERS ->
  cdc_from_name_specX tfibsegs B MT CA_RLO CA_RHI CA_PERS CA_ROSTRS A_FROM_NAME ->
  astrcmp_realizes tfibsegs B A_STRCMP ->
  globs_marked tfibsegs B CODEC_GLOBS -> cpw_rows_free B CA_ROSTRS ->
  cdc_check_pers_specX tfibsegs B MT CA_RLO CA_RHI CA_PERS CA_ROSTRS A_CHECK_PERS.
Proof using MTL TL LAWS ML.
intros POF FN STR GM RF. unfold cdc_check_pers_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HE HC.
set (X := mkCP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
assert (HOK : cp_ok B X) by (split; [exact HE | exact HC]).
change (SRr tfibsegs (c_W X) (cfg_at tfibsegs A_CHECK_PERS (c_regs X) (c_memc X) (c_mdc X)) (cp_post B MT X)).
apply (cp_seg0 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg1 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg2 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg3 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg4 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg5 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg6 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg7 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg8 B MT MTL TL LAWS GM RF POF FN STR X HOK).
apply (cp_seg9 B MT MTL TL LAWS GM RF POF FN STR X HOK).
exact (cp_seg10 B MT MTL TL LAWS GM RF POF FN STR X HOK).
Qed.
End m.
