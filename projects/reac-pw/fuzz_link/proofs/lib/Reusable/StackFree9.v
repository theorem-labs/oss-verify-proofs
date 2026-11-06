(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the release walk of __asan_stack_free_8, ported from
   proofs/cgif/cgif_rgb_fuzzer/lib/YF3h.v:113 tfx_stack_free_7 (instances YF9b.v:35 / YF9w.v:35) at c8557374ad2e, over
   the shared lib/Reusable kernel and the contract lib/Reusable/StackFreeDef.v (astack_free_realizes, a Theorem Labs lane).

   This file is IMAGE-FREE: every address, the code table and the two symbolic run results are Section variables, so
   both of fuzz_scene's ASan images share this one text. Each image supplies them in its own table file
   (lib/A/Rt/StackFree8Tbl.v for asan, lib/AU/Rt/StackFree8Tbl.v for asan-ubsan), which also instantiates the theorem
   below. It lives in lib/Reusable because it holds no image value and its Require closure is the shared kernel only
   (a Theorem Labs lane). Written by a Theorem Labs lane's two free_8 lanes together; the proof text is one text.

   Changes from the donor: class 8 (frame 16384 bytes, the flag pointer in the frame's last word); __asan::MemToShadow
   and __asan::PoisonShadow are NOT walked here - they are consumed through a Theorem Labs lane's two statements in
   lib/Reusable/AsStackLeaf.v (mem_to_shadow_realizes, poison_shadow_realizes; proofs owned by a Theorem Labs lane), so the walk
   is two symbolic phases over free_8's own 20 words, joined by YI04.st_ok_after_call. The stack window is free_8's own
   frame (32 bytes) instead of the donor's 96, which covered the inlined callees. The memset leaf and every constant
   cell (shadow offset, kHighMemEnd, kMidMemBeg / kMidMemEnd, the can-poison byte, REAL(memset)) are read only inside
   the two summarised callees - free_8's own 20 words read no cell - so this file takes no cell hypothesis and no
   symbol-record hypothesis. *)
(* Class 9: the image-free walk of frame_release_9 (side stack for frames, class 9), `astack_free_9_at`, the class-8
   walk above with the class constants changed. frame_release_9's 20 words differ from frame_release_8's only at +0x18
   (`lui a0, 8`: the flag pointer is the frame's last word, frame + 0x8000 - 8) and in its two pc-relative words
   (the `jal` into MemToShadow and the tail `j` into PoisonShadow), which are the image's business (each image's table
   file). So: FS_B = fs_frame_bytes 9 = 32768, the frame's shadow is at most 32768 / 8 = 4096 bytes, the frame is
   (9, pos) of the model, and the PoisonShadow span is sf_span 9 n = n / 8. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import StackFreeDef AsStackLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* Image-free constants of class 9 and of frame_release_9's own frame.
   SF_WIN 32 = its `addi sp,sp,-0x20`; FS_B 32768 = fs_frame_bytes 9 = its `lui a0,8`. *)
Definition SF_WIN : Z := 32.
Definition FS_B : Z := 32768.
Definition aFLG : nat := 32.
Definition KA : nat := 33.
Definition keep2 : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition stk_of (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) (- SF_WIN) 0 (- SF_WIN) 0 cs.
Definition rFF : YP09.region :=
YP09.mkRegion (Some 10%nat) (FS_B - 8) FS_B (FS_B - 8) (FS_B - 8) [YP09.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))].
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [].
Definition rFLG0 : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition sf_facts : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + SF_WIN) kHighMemEnd 4); (10%nat, mkAF 4096 (CEIL_MAX - FS_B) 5);
(11%nat, mkAF 8 FS_B 3); (aFLG, mkAF 4096 (CEIL_MAX - 1) 0)].
Definition sf_mem : smem := [stk_of []; rFF; rFLG].
(* The entry state, and the state the walk resumes in after the call of MemToShadow. *)
Definition ss0_of (entry : Z) : sstate := mkSS entry sr_atoms sf_mem None (mkFacts sf_facts [] []).
Definition ss2_of (retpc : Z) (s : sstate) : sstate := ss_after_call s (ss_mem s) KA retpc.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section img.
Variable segs : list Segment.
Variable SF_ENTRY MTS_ENTRY MTS_RET PS_ENTRY IMG_END : Z.
Variable TBL : ctable.
Variable e1 e2 : sstate.
(* What each image's table file proves of its own bytes. *)
Hypothesis HWX : wx_segs_nowrap segs.
Hypothesis TBL_ok : table_ok segs TBL.
Hypothesis IMG_bound : forall a, YG0d.in_img segs a -> a < IMG_END.
Hypothesis IMG_END_small : IMG_END <= 0x654000.
(* The two segment facts of the image. Each image's table file proves them from its own copy of the kernel's
   segment lemmas (lib/Reusable/YCe5.v for asan, lib/AU/YCe5.v for asan-ubsan), which this file must not reach. *)
Hypothesis FSEG_none : forall a, ~ YG0d.in_img segs a -> find_segment segs a 1 = None.
Hypothesis ROM_none : forall a, 0 <= a < 2 ^ 64 -> ~ YG0d.in_img segs a -> seg_rom segs (Z_to_bv 64 a) = None.
Hypothesis MTS_RET_ok : YK0s.ret_ok (Z_to_bv 64 MTS_RET).
Hypothesis MTS_RET_small : 0 <= MTS_RET < 2 ^ 64.
Hypothesis r_sf1 : sym_runN segs TBL FUEL (ss0_of SF_ENTRY) = (e1, RS_stopped SR_fetch).
Hypothesis r_sf2 : sym_runN segs TBL FUEL (ss2_of MTS_RET e1) = (e2, RS_stopped SR_fetch).
Hypothesis e1_pc : ss_pc e1 = MTS_ENTRY.
Hypothesis e1_resv : ss_resv e1 = None.
Hypothesis e1_a0 : sr_get (ss_regs e1) 10%bv = SOff 10 0.
Hypothesis e1_ra : sr_get (ss_regs e1) 1%bv = SLit MTS_RET.
Hypothesis e1_atoms : ss_atoms_lt KA e1 = true /\ regions_wf (ss_mem e1) = true /\
no_cdata (ss_mem e1) = true /\ mem_atoms_lt KA (ss_mem e1) = true.
Hypothesis e1_mem : exists cs, ss_mem e1 = [stk_of cs; rFF; rFLG0].
Hypothesis e2_pc : ss_pc e2 = PS_ENTRY.
Hypothesis e2_resv : ss_resv e2 = None.
Hypothesis e2_r10 : sr_get (ss_regs e2) 10%bv = SOff 10 0.
Hypothesis e2_r11 : sr_get (ss_regs e2) 11%bv = SOff 11 0.
Hypothesis e2_r12 : sr_get (ss_regs e2) 12%bv = SLit 0xf5.
Hypothesis e2_keepb : forallb (fun r => sv_eqb (sr_get (ss_regs e2) (Z_to_bv 5 r)) (SOff (Z.to_nat r) 0)) keep2 = true.
Hypothesis e2_mem : exists cs, ss_mem e2 = [stk_of cs; rFF; rFLG0].

Lemma sf_phase : forall (W : world segs) E ss ss' st ms md,
st_ok segs E ss (restrict (w_H W) ms) -> sym_runN segs TBL FUEL ss = (ss', st) ->
SRr segs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall segs E ss' (restrict (w_H W) ms1) | _ => st_ok segs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen segs TBL TBL_ok HWX W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.

(* Memory helpers. Each is the generic form of a lemma of the relocated cgif_file A/AF0x.v or A/AE7f.v, whose files
   Require A/AF0m.v; stating them here over `segs` keeps that file out of this closure. *)
Lemma apresent_writable : forall H (m : word -> option byte) a, apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma apresent_mbyte : forall (H : word -> bool) m a, apresent H m a -> exists b, mbyte segs (mrestrict H m) a = Some b.
Proof. intros H m a [Hh [b Hb]]. exists b. unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity. Qed.
Lemma apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ YG0d.in_img segs a -> writable_at segs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by lia. rewrite (FSEG_none a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
try rewrite Eb in Hw. exfalso. apply Hw. reflexivity.
Qed.
Lemma mbyte_apresent : forall (H : word -> bool) m a b,
0 <= a < 2 ^ 64 -> ~ YG0d.in_img segs a -> mbyte segs (mrestrict H m) a = Some b -> apresent H m a.
Proof.
intros H m a b Ha Hni Hb. unfold mbyte, mrestrict in Hb.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [rewrite (ROM_none a Ha Hni) in Hb; discriminate|].
destruct (m (Z_to_bv 64 a)) as [b'|] eqn:E; [|rewrite (ROM_none a Ha Hni) in Hb; discriminate].
split; [exact Hh | exists b'; exact E].
Qed.
Lemma not_img_high : forall a, IMG_END <= a -> ~ YG0d.in_img segs a.
Proof. intros a Ha Hin. pose proof (IMG_bound a Hin). lia. Qed.
Lemma mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
aview segs H m' a = aview segs H m a -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte segs (mrestrict H m') a) as [b'|] eqn:E1; destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:E2;
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma apresent_transfer : forall (H : word -> bool) (m m' : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ YG0d.in_img segs a -> aview segs H m' a = aview segs H m a -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Ha Hni E Hp. destruct (apresent_mbyte H m a Hp) as [b Hb].
apply (mbyte_apresent H m' a b Ha Hni). rewrite (mbyte_of_aview H m m' a E). exact Hb.
Qed.
Lemma st_ok_window_writable : forall (H : word -> bool) E ss ms i r a,
st_ok segs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
writable_at segs (mrestrict H (ms_mem ms)) a.
Proof.
intros H E ss ms i r a HS Hi Ha.
pose proof (st_ok_mem_ok segs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Lemma st_ok_window_apresent : forall (H : word -> bool) E ss ms i r a,
st_ok segs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
0 <= a < 2 ^ 64 -> ~ YG0d.in_img segs a -> apresent H (ms_mem ms) a.
Proof.
intros H E ss ms i r a HS Hi Ha Hr Hni. apply apresent_of_writable; [exact Hr | exact Hni|].
eapply st_ok_window_writable; eassumption.
Qed.
Lemma aview_same : forall (H : word -> bool) (mem mem' : word -> option byte) a,
mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) -> aview segs H mem' a = aview segs H mem a.
Proof. intros H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_some_of_apresent : forall H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma in_band_rw_u64 : forall a, in_band_rw a -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia. Qed.
Lemma Z_to_bv64_of_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_mod : forall H (m : word -> option byte) a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv64_of_mod. reflexivity. Qed.
Lemma aview_byte_ex : forall H mem a v,
aview segs H mem a = Some v -> exists b : byte, mbyte segs (mrestrict H mem) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. exists b. split; [reflexivity|]. split; [reflexivity|].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H0. cbn in H0. lia.
Qed.
Lemma val_mem_of_rdword : forall H mem a v,
rdword (aview segs H mem) a = Some v -> val_mem segs (mrestrict H mem) a 8 v.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte_ex in E0 as (c0 & M0 & -> & R0). apply aview_byte_ex in E1 as (c1 & M1 & -> & R1).
apply aview_byte_ex in E2 as (c2 & M2 & -> & R2). apply aview_byte_ex in E3 as (c3 & M3 & -> & R3).
apply aview_byte_ex in E4 as (c4 & M4 & -> & R4). apply aview_byte_ex in E5 as (c5 & M5 & -> & R5).
apply aview_byte_ex in E6 as (c6 & M6 & -> & R6). apply aview_byte_ex in E7 as (c7 & M7 & -> & R7).
rewrite ?Z.add_0_r in M0.
set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; lia).
assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YO0f.le_byte v 8 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia];
[ change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r
| change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 | change (Z.of_nat 4) with 4
| change (Z.of_nat 5) with 5 | change (Z.of_nat 6) with 6 | change (Z.of_nat 7) with 7 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; subst v; lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; subst v; lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
(bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; subst v; lia.
- rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
(bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; subst v; lia.
- rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
(bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; subst v; lia.
- rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
(bv_unsigned c7)); cbn; subst v; lia.
- rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
0); cbn; subst v; lia.
Qed.
Lemma flag_zero : forall (H : word -> bool) E ss ms fl,
st_ok segs E ss (restrict H ms) -> nth_error (ss_mem ss) 2 = Some rFLG0 ->
bv_unsigned (ew E aFLG) = fl -> aview segs H (ms_mem ms) fl = Some 0.
Proof.
intros H E ss ms fl HS Hflg U32.
pose proof (st_ok_mem_ok segs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hflg)) as (_ & _ & _ & Hcs).
unfold rFLG0 in Hcs. cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite U32 in Hcs.
pose proof (val_of_chunk_ok segs E _ fl 0 1%N (SLit 0) 0 (Forall_inv Hcs) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
specialize (V 0%nat ltac:(cbn; lia)). rewrite !Z.add_0_r in V. unfold aview. rewrite V. reflexivity.
Qed.
Lemma rng_dec : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi). Proof. intros. lia. Qed.

Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
(* a Theorem Labs lane's two leaf statements (lib/Reusable/AsStackLeaf.v); their proofs are a Theorem Labs lane's. *)
Hypothesis MTS_SUM : mem_to_shadow_realizes segs B MTS_ENTRY.
Hypothesis PS_SUM : poison_shadow_realizes segs B PS_ENTRY.

(* The freed state's AR, from the caller's AR, by astack_free_law_ok: the flag byte reads 0, and every other byte the
   walk changed is present and not owned (frame_release_9's own stack frame). *)
Lemma ar_free_gen : forall ly S W regs mem md pos memX mdX (Wr : Z -> Prop),
ecall_pre segs B ly S W regs mem md -> In (9, pos) (frames S) -> (forall a, Wr a \/ ~ Wr a) ->
aview segs (w_H W) memX (flag_addr ly 9 pos) = Some 0 ->
(forall z : word, ~ Wr (bv_unsigned z) -> bv_unsigned z <> flag_addr ly 9 pos -> memX z = mem z) ->
(forall a, Wr a -> apresent (w_H W) memX a /\ ~ aowned B ly S a) ->
same_but_materialized md mdX ->
AR segs B ly (stack_free_state 9 pos S) W memX mdX.
Proof.
intros ly S W regs mem md pos memX mdX Wr HPRE Hin WrD FL MEQ PW SBM.
pose proof HPRE as (HAR & _).
pose proof (same_but_materialized_frame md mdX SBM) as MF.
destruct (al_flag _ _ LAWS ly S W mem md 9 pos HAR Hin) as (Hflp & Hflo & _ & _).
set (fl := flag_addr ly 9 pos) in *.
apply (astack_free_law_ok segs B ly S W mem md memX mdX 9 pos HAR Hin).
- exact FL.
- intros a Hr Hown Hnf. apply aview_same. apply MEQ; rewrite unsigned_lit_small by lia.
+ intros HW. exact (proj2 (PW a HW) Hown).
+ exact Hnf.
- intros a Hvw. rewrite (aview_mod _ memX a). rewrite (aview_mod _ mem a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z.eq_dec a' fl) as [Ea|Hnf]; [rewrite Ea, FL; discriminate|].
destruct (WrD a') as [HW|HW].
+ apply aview_some_of_apresent. exact (proj1 (PW a' HW)).
+ rewrite (aview_same (w_H W) mem memX a'); [exact Hvw|]. apply MEQ; rewrite unsigned_lit_small by lia; assumption.
- apply MF. - apply MF. - apply MF.
- intros a Hb Hh. pose proof (in_band_rw_u64 a Hb) as Hr. unfold w64 in *.
destruct (Z.eq_dec a fl) as [->|Hnf].
+ exfalso. pose proof (proj1 Hflp) as Hf0. rewrite Hf0 in Hh. discriminate.
+ destruct (WrD a) as [HW|HW].
* exfalso. pose proof (proj1 (proj1 (PW a HW))) as Hf0. rewrite Hf0 in Hh. discriminate.
* apply MEQ; rewrite unsigned_lit_small by lia; assumption.
Qed.

Theorem astack_free_9_at : astack_free_realizes segs B SF_ENTRY 9.
Proof.
intros ly S W regs mem md pos n HPRE Hin G10 G11 Hn Hn8 HTR.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
set (H := w_H W) in *. set (sp0 := spZ regs) in *.
change (fs_frame_bytes 9) with 32768 in *.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HPS : PS_STK = 256) by reflexivity.
pose proof (proj1 HAR) as M.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (lo_stk_ceil ly HLY) as SC. unfold ASAN_CEIL in SC.
assert (HPOS : 0 <= pos < fs_frames 9).
{ pose proof (proj1 (Forall_forall _ _) (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B ly S _ M))) (9, pos) Hin) as [_ X].
cbn [fst snd] in X. exact X. }
destruct (al_frames _ _ LAWS ly S W mem md 9 pos HAR Hin) as (Hal32 & Happ & Hfr & Hsh).
change (fs_frame_bytes 9) with 32768 in Happ, Hfr, Hsh. change (32768 / 8) with 4096 in Hsh.
destruct (al_flag _ _ LAWS ly S W mem md 9 pos HAR Hin) as (Hflp & Hflo & Hflapp & Hflc).
change (w_H W) with H in Hfr, Hsh, Hflp.
pose proof (proj1 (Forall_forall _ _) (proj2 (al_sep _ _ LAWS ly S W mem md HAR)) (9, pos) Hin) as (Hfa_lo & Hfa_hi).
cbn [fst snd] in Hfa_lo, Hfa_hi. change (fs_frame_bytes 9) with 32768 in Hfa_hi.
set (fa := frame_addr ly 9 pos) in *. set (fl := flag_addr ly 9 pos) in *. set (S' := stack_free_state 9 pos S).
pose proof (proj1 alloc_ceiling_val) as HCE.
assert (Hsp : 0x10007fff8000 + 4096 <= sp0 <= 0x800000000000 /\ alloc_ceiling + 4096 <= sp0)
by (unfold sp0 in *; rewrite HES in Hslo; unfold kHighMemBeg, kHighMemEnd in *; lia).
assert (Hfl0 : 4096 <= fl) by (unfold in_app in Hflapp; lia).
assert (FLnimg : ~ YG0d.in_img segs fl).
{ exact (proj2 (al_client_img _ _ LAWS ly S W mem md fl HAR
(or_intror (or_intror (ex_intro _ 9 (ex_intro _ pos (conj Hin eq_refl))))))). }
assert (FLout : fl < fa \/ fa + 32768 <= fl).
{ destruct (Z_lt_le_dec fl fa) as [L|L]; [left; exact L|]. destruct (Z_lt_le_dec fl (fa + 32768)) as [L2|L2]; [|right; exact L2].
exfalso. exact (proj2 (Hfr fl ltac:(lia)) Hflo). }
assert (Hfa8 : 0 <= fa / 8 <= 17592184995840) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
set (sh := shadow_addr fa) in *.
assert (Esh : sh = 0x7fff8000 + fa / 8) by reflexivity.
assert (Hfa8m : fa mod 8 = 0).
{ pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (fa / 32)) with ((4 * (fa / 32)) * 8) by lia. apply Z_mod_mult. }
assert (Hcnt : 1 <= n / 8 <= 4096) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
assert (SHNO : forall i, 0 <= i < n / 8 -> apresent H mem (sh + i) /\ ~ aowned B ly S (sh + i))
by (intros i Hi; apply Hsh; lia).
assert (SHFAR : forall a, sh <= a < sh + n / 8 -> 0x654000 <= a < sp0 - 4096 /\ a <> fl).
{ intros a Ha. split; [lia|]. intros Heq. apply (proj2 (SHNO (a - sh) ltac:(lia))).
replace (sh + (a - sh)) with a by lia. rewrite Heq. exact Hflo. }
assert (WIN_NOWN : forall a, sp0 - 4096 <= a < sp0 -> ~ aowned B ly S a).
{ intros a Ha. apply (al_stack _ _ LAWS ly S W mem md a HAR). rewrite HES in Hslo. unfold sp0 in *. lia. }
assert (WIN_NIMG : forall a, sp0 - 4096 <= a < sp0 -> ~ YG0d.in_img segs a) by (intros a Ha; apply not_img_high; lia).
set (E := Ereg regs [w64 fl]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hr; subst E; apply ew_Ereg_nat; exact Hr).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : bv_unsigned (ew E 10) = fa) by (rewrite (EEreg 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (E11 : bv_unsigned (ew E 11) = n) by (rewrite (EEreg 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 fl) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = fl) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS0 : st_ok segs E (ss0_of SF_ENTRY) (restrict H (mkst regs (Z_to_bv 64 SF_ENTRY) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss0_of, sf_mem. apply (entry_st_ok_full segs); change (Ereg regs [w64 fl]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
+ unfold stk_of, SF_WIN. apply (region_ok_stack segs E _ 2 sp0 (- 32)); [exact E2 | lia | lia |].
intros a Ha. apply apresent_writable. apply HpresE. rewrite HES. lia.
+ unfold rFF, aFLG, FS_B, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E10. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val segs E _ fa (32768 - 8) 8%N (SOff 32 0) fl);
[cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
replace (fa + (32768 - 8)) with (fa + 32768 - 8) by lia. exact (val_mem_of_rdword H mem _ _ HTR).
+ unfold rFLG, aFLG, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. replace (fl + o) with fl by lia. exact (apresent_writable H mem fl Hflp).
- apply pairwise_disjoint_of_extents. unfold stk_of, rFF, rFLG, aFLG, extent_of_region, SF_WIN, FS_B.
cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E10, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok sf_facts]. unfold afact_ok, aFLG. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, U32. unfold SF_WIN, FS_B, kHighMemBeg, kHighMemEnd in *.
change (2 ^ 4) with 16. change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact Hal32 | exact Hn8 | apply Z.mod_1_r | lia]. }
(* Phase 1: the entry to the jal into MemToShadow. *)
unfold cfg_at. change (w64 SF_ENTRY) with (Z_to_bv 64 SF_ENTRY).
eapply SRr_bind; [exact (sf_phase W E _ _ _ _ _ HS0 r_sf1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & _).
change (st_ok segs E e1 (restrict H ms1)) in HS1.
assert (MEQ1 : forall z : word, ~ (sp0 - 32 <= bv_unsigned z < sp0) -> bv_unsigned z <> fl -> ms_mem ms1 z = mem z).
{ intros z Hz1 Hz2. apply HFm1. intros Hw. destruct (in_wrange_windows E _ _ Hw) as (b & lo & hi' & Ht & Hb).
unfold ss0_of, sf_mem in Ht. cbn in Ht.
destruct Ht as [Hq|[Hq|[Hq|[]]]]; injection Hq as <- <- <-; cbn [base_val] in Hb; unfold aFLG in Hb;
rewrite ?E2, ?E10, ?U32 in Hb; unfold SF_WIN, FS_B in *; lia. }
pose proof (st_ok_restrict_mkst segs H E e1 ms1 HS1 e1_resv) as Hms1. rewrite e1_pc in Hms1.
rewrite Hms1. set (regs1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (A10 : getr regs1 10 = w64 fa).
{ unfold regs1. rewrite (st_ok_restrict_reg segs H E e1 ms1 10%bv HS1), e1_a0. cbn [sv_denot]. rewrite E10, Z.add_0_r. reflexivity. }
assert (A1 : getr regs1 1 = Z_to_bv 64 MTS_RET).
{ unfold regs1. rewrite (st_ok_restrict_reg segs H E e1 ms1 1%bv HS1), e1_ra. reflexivity. }
destruct e1_mem as (cs1 & Hmem1).
assert (Hstk1 : nth_error (ss_mem e1) 0 = Some (stk_of cs1)) by (rewrite Hmem1; reflexivity).
assert (Hflg1 : nth_error (ss_mem e1) 2 = Some rFLG0) by (rewrite Hmem1; reflexivity).
assert (PW1 : forall a, sp0 - 32 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. apply (st_ok_window_apresent H E e1 ms1 0 _ a HS1 Hstk1);
[unfold stk_of; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2; unfold SF_WIN; lia
| lia | apply WIN_NIMG; lia]. }
assert (FL1 : aview segs H mem1 fl = Some 0) by exact (flag_zero H E e1 ms1 fl HS1 Hflg1 U32).
assert (FLW1 : apresent H mem1 fl).
{ apply apresent_of_writable; [lia | exact FLnimg|].
apply (st_ok_window_writable H E e1 ms1 2 _ fl HS1 Hflg1).
unfold rFLG0, aFLG. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite U32. lia. }
assert (SBM1 : same_but_materialized md md1) by apply with_vm_backing_same.
assert (AR1 : AR segs B ly S' W mem1 md1).
{ apply (ar_free_gen ly S W regs mem md pos mem1 md1 (fun a => sp0 - 32 <= a < sp0) HPRE Hin (rng_dec _ _) FL1 MEQ1);
[|exact SBM1]. intros a Ha. split; [exact (PW1 a Ha) | apply WIN_NOWN; lia]. }
(* MemToShadow, through a Theorem Labs lane's statement. *)
eapply SRr_bind.
{ apply (MTS_SUM ly S' W regs1 mem1 md1 9 pos fa AR1).
- rewrite A1. exact MTS_RET_ok.
- lia. - exact HPOS. - exact A10. - lia. - change (fs_frame_bytes 9) with 32768. lia. }
cbv beta. intros W2 c2 _ (-> & regsM & memM & mdM & -> & ARM & HPM & SBMM & _ & AVM & APM).
fold H in AVM, APM.
assert (RA1 : raZ regs1 = MTS_RET) by (unfold raZ; rewrite A1; apply unsigned_lit_small; lia).
rewrite RA1.
destruct e1_atoms as (AT1 & WF1 & NC1 & MAT1).
assert (HPR : YO0d.regs_preserved (ms_regs (restrict H ms1)) regsM).
{ rewrite Hms1, restrict_mkst_fx. intros r Hr. apply HPM. exact Hr. }
assert (MB : forall a, 0 <= a < 2 ^ 64 -> mbyte segs (mrestrict H memM) a = mbyte segs (mrestrict H mem1) a)
by (intros a Ha; apply mbyte_of_aview; apply AVM; exact Ha).
assert (KEPT : Forall (region_kept segs E (ms_mem (restrict H ms1)) (mrestrict H memM)) (ss_mem e1)).
{ rewrite Hms1, restrict_mkst_fx. rewrite Hmem1. repeat apply Forall_cons; try apply Forall_nil.
- split.
+ intros a Ha. unfold stk_of in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite E2 in Ha.
apply MB. unfold SF_WIN in Ha. lia.
+ intros a Ha _. unfold stk_of in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite E2 in Ha.
apply apresent_writable. apply APM. apply PW1. unfold SF_WIN in Ha. lia.
- split.
+ intros a Ha. unfold rFF in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite E10 in Ha.
apply MB. unfold FS_B in Ha. lia.
+ intros a Ha _. exfalso. unfold rFF in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
- split.
+ intros a Ha. unfold rFLG0, aFLG in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite U32 in Ha.
apply MB. lia.
+ intros a Ha _. unfold rFLG0, aFLG in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U32 in Ha.
replace a with fl by lia. apply apresent_writable. apply APM. exact FLW1. }
pose proof (st_ok_after_call segs KA E e1 (restrict H ms1) regsM (mrestrict H memM) (ss_mem e1) MTS_RET
HS1 e1_resv AT1 WF1 NC1 MAT1 (submem_refl _) e1_ra HPR KEPT) as HS2.
set (E2' := havoc E KA (map (getr regsM) CLOB)) in HS2.
change (ss_after_call e1 (ss_mem e1) KA MTS_RET) with (ss2_of MTS_RET e1) in HS2.
rewrite <- restrict_mkst_fx in HS2.
assert (EH : forall i, (i < KA)%nat -> ew E2' i = ew E i) by (intros i Hi; apply ew_havoc_old; exact Hi).
(* Phase 2: MemToShadow's return to the tail jump into PoisonShadow. *)
unfold cfg_at. change (w64 MTS_RET) with (Z_to_bv 64 MTS_RET).
eapply SRr_bind; [exact (sf_phase W E2' _ _ _ _ _ HS2 r_sf2)|].
cbv beta. intros W3 c3 _ (-> & ms2 & mat2 & -> & HS3 & HFm2 & _).
change (st_ok segs E2' e2 (restrict H ms2)) in HS3.
assert (MEQ2 : forall z : word, ~ (sp0 - 32 <= bv_unsigned z < sp0) -> bv_unsigned z <> fl -> ms_mem ms2 z = memM z).
{ intros z Hz1 Hz2. apply HFm2. intros Hw. unfold ss2_of, ss_after_call in Hw. cbn [ss_mem] in Hw.
rewrite Hmem1 in Hw. destruct (in_wrange_windows E2' _ _ Hw) as (b & lo & hi' & Ht & Hb).
cbn in Ht. destruct Ht as [Hq|[Hq|[Hq|[]]]]; injection Hq as <- <- <-; cbn [base_val] in Hb; unfold aFLG in Hb;
rewrite ?EH in Hb by (unfold KA; lia); rewrite ?E2, ?E10, ?U32 in Hb; unfold SF_WIN, FS_B in *; lia. }
pose proof (st_ok_restrict_mkst segs H E2' e2 ms2 HS3 e2_resv) as Hms2. rewrite e2_pc in Hms2.
rewrite Hms2. set (regs2 := ms_regs ms2) in *. set (mem2 := ms_mem ms2) in *.
set (md2 := with_vm_backing (m_vm_lazy mdM) mat2 mdM).
assert (EV : forall i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r -> ew E2' i = getr regs r).
{ intros i r Hi Hr. rewrite EH by (unfold KA; lia). apply EEreg. exact Hr. }
assert (B10 : getr regs2 10 = w64 fa).
{ unfold regs2. rewrite (st_ok_restrict_reg segs H E2' e2 ms2 10%bv HS3), e2_r10. cbn [sv_denot].
rewrite (EV 10%nat 10%bv ltac:(lia) eq_refl), G10, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (B11 : getr regs2 11 = w64 n).
{ unfold regs2. rewrite (st_ok_restrict_reg segs H E2' e2 ms2 11%bv HS3), e2_r11. cbn [sv_denot].
rewrite (EV 11%nat 11%bv ltac:(lia) eq_refl), G11, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (B12 : getr regs2 12 = w64 0xf5).
{ unfold regs2. rewrite (st_ok_restrict_reg segs H E2' e2 ms2 12%bv HS3), e2_r12. reflexivity. }
assert (KEEP2 : forall r, In r keep2 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. pose proof e2_keepb as KB. rewrite forallb_forall in KB. specialize (KB r Hr). apply sv_eqb_eq in KB.
unfold regs2. rewrite (st_ok_restrict_reg segs H E2' e2 ms2 _ HS3), KB. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
unfold keep2 in Hr. cbn [In] in Hr. apply EV; [lia|].
repeat (destruct Hr as [<- | Hr]; [reflexivity|]). destruct Hr. }
assert (R1 : getr regs2 1 = getr regs 1) by exact (KEEP2 1 ltac:(unfold keep2; cbn [In]; tauto)).
assert (R2 : getr regs2 2 = getr regs 2) by exact (KEEP2 2 ltac:(unfold keep2; cbn [In]; tauto)).
assert (R3 : getr regs2 3 = getr regs 3) by exact (KEEP2 3 ltac:(unfold keep2; cbn [In]; tauto)).
assert (R4 : getr regs2 4 = getr regs 4) by exact (KEEP2 4 ltac:(unfold keep2; cbn [In]; tauto)).
assert (SP2 : spZ regs2 = sp0) by (unfold spZ; rewrite R2; reflexivity).
destruct e2_mem as (cs2 & Hmem2).
assert (Hstk2 : nth_error (ss_mem e2) 0 = Some (stk_of cs2)) by (rewrite Hmem2; reflexivity).
assert (Hflg2 : nth_error (ss_mem e2) 2 = Some rFLG0) by (rewrite Hmem2; reflexivity).
assert (E2b : bv_unsigned (ew E2' 2) = sp0) by (rewrite EH by (unfold KA; lia); exact E2).
assert (U32b : bv_unsigned (ew E2' aFLG) = fl) by (rewrite EH by (unfold KA, aFLG; lia); exact U32).
assert (PW2 : forall a, sp0 - 32 <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. apply (st_ok_window_apresent H E2' e2 ms2 0 _ a HS3 Hstk2);
[unfold stk_of; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite E2b; unfold SF_WIN; lia
| lia | apply WIN_NIMG; lia]. }
assert (FL2 : aview segs H mem2 fl = Some 0) by exact (flag_zero H E2' e2 ms2 fl HS3 Hflg2 U32b).
assert (AVM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> a <> fl -> aview segs H mem2 a = aview segs H memM a).
{ intros a Ha Hz1 Hz2. apply aview_same. apply MEQ2; rewrite unsigned_lit_small by lia; assumption. }
assert (AV01 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> a <> fl -> aview segs H mem1 a = aview segs H mem a)
by (intros a Ha Hz1 Hz2; apply aview_same; apply MEQ1; rewrite unsigned_lit_small by lia; assumption).
assert (AV02 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> a <> fl -> aview segs H mem2 a = aview segs H mem a)
by (intros a Ha Hz1 Hz2; rewrite (AVM2 a Ha Hz1 Hz2), (AVM a Ha); apply AV01; assumption).
assert (PRES2 : forall a, ~ (sp0 - 32 <= a < sp0) -> a <> fl -> 0 <= a < 2 ^ 64 -> ~ YG0d.in_img segs a ->
apresent H mem a -> apresent H mem2 a).
{ intros a Hz1 Hz2 Ha Hni Hp. apply (apresent_transfer H mem mem2 a Ha Hni); [apply AV02; assumption | exact Hp]. }
assert (SBM2 : same_but_materialized md md2).
{ eapply same_but_materialized_trans; [exact SBM1|].
eapply same_but_materialized_trans; [exact SBMM | apply with_vm_backing_same]. }
assert (MF2 : same_but_materialized mdM md2) by apply with_vm_backing_same.
pose proof (same_but_materialized_frame mdM md2 MF2) as MFF.
assert (AR2 : AR segs B ly S' W mem2 md2).
{ apply (al_frame _ _ LAWS ly S' W memM mdM mem2 md2 ARM).
- intros a Ha Hown. change (w_H W) with H. destruct (Z.eq_dec a fl) as [->|Hnf]; [rewrite FL2; symmetry; rewrite <- FL1; apply AVM; lia|].
destruct (rng_dec (sp0 - 32) sp0 a) as [HW|HW].
+ exfalso. apply (al_stack _ _ LAWS ly S' W memM mdM a ARM ltac:(rewrite HES in Hslo; unfold sp0 in *; lia) Hown).
+ apply AVM2; assumption.
- intros a Hvw. change (w_H W) with H in Hvw |- *. rewrite (aview_mod _ mem2 a). rewrite (aview_mod _ memM a) in Hvw.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z.eq_dec a' fl) as [->|Hnf]; [rewrite FL2; discriminate|].
destruct (rng_dec (sp0 - 32) sp0 a') as [HW|HW].
+ apply aview_some_of_apresent. apply PW2. exact HW.
+ rewrite (AVM2 a' Hr HW Hnf). exact Hvw.
- apply MFF. - apply MFF. - apply MFF.
- intros a Hb Hh. change (w_H W) with H in Hh. pose proof (in_band_rw_u64 a Hb) as Hr. unfold w64 in *.
destruct (Z.eq_dec a fl) as [->|Hnf].
+ exfalso. pose proof (proj1 Hflp) as Hf0. rewrite Hf0 in Hh. discriminate.
+ destruct (rng_dec (sp0 - 32) sp0 a) as [HW|HW].
* exfalso. pose proof (proj1 (PW2 a HW)) as Hf0. rewrite Hf0 in Hh. discriminate.
* apply MEQ2; rewrite unsigned_lit_small by lia; assumption. }
(* PoisonShadow, through a Theorem Labs lane's statement, at the tail jump. *)
eapply SRr_bind.
{ apply (PS_SUM ly S' W regs2 mem2 md2 9 pos fa n 0xf5 AR2).
- rewrite R1. exact Hra.
- rewrite SP2. exact Hal16.
- rewrite SP2, HPS. rewrite HES in Hslo. unfold sp0 in *. lia.
- rewrite SP2. unfold sp0 in *. lia.
- rewrite SP2, HPS. intros a Ha. destruct (Z_lt_le_dec a (sp0 - 32)) as [L|L]; [|apply PW2; lia].
apply PRES2; [lia | | lia | apply WIN_NIMG; lia | apply HpresE; rewrite HES; lia].
intros ->. unfold in_app in Hflapp. lia.
- rewrite R3. exact Hgp. - rewrite R4. exact Htp.
- lia. - exact HPOS.
- exact B10. - exact B11. - exact B12.
- lia. - lia. - exact Hn8. - exact Hfa8m.
- lia. - change (fs_frame_bytes 9) with 32768. lia.
- intros a Ha. destruct (SHFAR a Ha) as [Hr Hne].
apply PRES2; [lia | exact Hne | lia | apply not_img_high; lia|].
destruct (SHNO (a - sh) ltac:(lia)) as [Hp _]. replace (sh + (a - sh)) with a in Hp by lia. exact Hp. }
cbv beta. intros W4 c4 _ (-> & regs3 & mem3 & md3 & -> & AR3 & HP3 & SBM3 & SH3 & AV3 & PW3).
fold H in SH3, AV3, PW3.
rewrite SP2 in AV3, PW3.
apply SRr_ret. split; [reflexivity|]. exists regs3, mem3, md3.
split; [unfold raZ; rewrite R1; reflexivity|].
split; [exact AR3|].
split.
{ intros r Hr. rewrite (HP3 r Hr). apply KEEP2. unfold acallee_saved in Hr. unfold keep2. cbn [In]. lia. }
split; [eapply same_but_materialized_trans; [exact SBM2 | exact SBM3]|].
split; [change (sf_span 9 n) with (n / 8); intros i Hi; exact (SH3 i Hi)|].
split.
{ change (sf_span 9 n) with (n / 8). intros a Hr Ha Hnf Hs. rewrite HES in Hs.
rewrite (AV3 a Hr Ha ltac:(rewrite HPS; lia)). apply AV02; [exact Hr | lia | exact Hnf]. }
intros a Ha. rewrite HES in Ha. destruct (Z_le_dec (sp0 - PS_STK) a) as [L|L]; [apply PW3; rewrite HPS in *; lia|].
apply (apresent_transfer H mem2 mem3 a ltac:(lia) ltac:(apply WIN_NIMG; rewrite HPS in *; lia)).
- apply AV3; [lia | | rewrite HPS; lia].
intros Hsha. destruct (SHFAR a Hsha) as [Hr _]. rewrite HPS in L. lia.
- destruct (Z_le_dec (sp0 - 32) a) as [L2|L2]; [apply PW2; lia|].
apply PRES2; [lia | | lia | apply WIN_NIMG; lia | apply HpresE; lia].
intros ->. unfold in_app in Hflapp. rewrite HPS in L. lia.
Qed.
End d.
End img.
End w.
