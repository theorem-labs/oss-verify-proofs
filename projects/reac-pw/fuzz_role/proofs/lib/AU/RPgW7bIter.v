(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, awr_ok_cons_gen, as w7_region_nth, w7_field, w7_awr_cons) for reac-pw/fuzz_role's image A; the rest of the file is new: the block-post shape, the code table and the helpers of the walk of LLVMFuzzerTestOneInput from 0x80d14 to 0x8165c. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at 25d4b718638 and the definitions
   w7_kept, w7_hull, w7_strok, w7_strz of proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638, for
   reac-pw/fuzz_headamp's image B: w7_ -> hw7b_, role's image A code and record -> fuzz_headamp.asan-ubsan's (its own
   code table, pcs, registers and real-frame cells, measured on image B), module paths; the statements of the walk's
   blocks and call steps are new (hw7b_*_stmt), one per block of image B's own code; its hw7b_post,
   hw7b_post_of_run, hw7b_kept, hw7b_hull, hw7b_ra_kept, hw7b_hull_kept, hw7b_strok, hw7b_strz, hw7b_strok_kept and
   hw7b_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgW7bBase.v, with its module paths, module names and numbers changed; 105 of its 145 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bIter.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the turn's registers are rate's (x in a0 and s8, n in s9, t in s5; role's s9, s8, s10); RPgMem.rm_hull_sub is lib/A/RtPgMem.v rtm_hull_sub; the strlen and memcpy entries are rate's 0x42194 and 0x51860. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW7bIter.v at 7ef0f92b27f1 for the same unit's image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the turn's registers are image B's (x in a0 and s10, n in s9, t in s11, the length in s6); rtm_hull_sub is lib/AU/RtPgMemB.v rtmb_hull_sub; the strlen and memcpy entries are image B's 0x421ec and 0x518b8; the strlen contract is lib/AU/RtPgW7bCallB.v w7b_astrlen_realizes; the prefix w7_ becomes w7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW7bIterB.v at 9eff5d44f2fd for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; the segments are lib/AU/Img0.v rsegs; the turn's registers are role B's (x in a0 and s10, n in s6, t in s9, the length in s8); rtmb_hull_sub is lib/AU/RPgMem.v rm_hull_sub; the strlen and memcpy entries are role B's 0x41b60 and 0x5116c. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, which holds the same loaded bytes): one turn of
   the parts loop of ent_headamp_key (pod.h:254-260) in the walk of LLVMFuzzerTestOneInput from 0x80dc8 to 0x818d8,
   from the strlen wrapper's entry (0x41b60, called at 0x80e60) to the return of memcpy(t + n, parts[i], l)
   (0x80e88): strlen, block B (the 95 clamp, which never cuts: n + l <= 61), __asan_memcpy (0x5116c). Proves no
   function (kind: segment lemma). The string is any w7b_strok one (an image string or ch in the frame for locals);
   the turn's post is the copied bytes at t + n, the length in s8, the callee-saved registers but s8 as before, and
   every byte outside the callees' stack below R and the copied range as before. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgMem RPgW7bBase RPgW7bKit RPgW7bCall RPgW7bBlkB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


(* the registers a call may change that the turn's post does not name: every callee-saved one but s8 is kept *)
Lemma w7b_cs_bv : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r) = r.
Proof. intros r Hr. unfold acallee_saved in Hr. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Lemma w7b_cs_out : forall r (l : list (bv 5)), acallee_saved r -> ~ In r (map (fun c => bv_unsigned c) l) ->
~ In (Z_to_bv 5 r) l.
Proof.
intros r l Hr Hn Hin. apply Hn. rewrite <- (w7b_cs_bv r Hr). exact (in_map (fun c => bv_unsigned c) l _ Hin).
Qed.

Lemma w7b_reg_eq : forall (regs regs' : bvmap 5 word) (r : bv 5),
getr regs' (Z_to_bv 5 (bv_unsigned r)) = getr regs (Z_to_bv 5 (bv_unsigned r)) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis ASTRLEN : w7b_astrlen_realizes rsegs B W7B_STRLEN.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W7B_MEMCPY.
Lemma w7b_iter : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k (regs : bvmap 5 word) R t n x s
(Q : world rsegs -> config -> Prop),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
getr regs 1 = w64 W7B_AFTER_STRLEN -> getr regs 10 = w64 x -> getr regs 26 = w64 x ->
getr regs 22 = w64 n -> getr regs 25 = w64 t -> getr regs 2 = w64 R ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
R mod 16 = 0 -> sp0 mod 16 = 0 -> R <= sp0 -> 2 * ESTACK - (R - sp0) <= STK -> 2 * ESTACK <= R -> R < 2 ^ 63 ->
w7b_strok W mem R x s -> w7b_aro_unowned rsegs B (aview rsegs (w_H W) mem) ->
(length s <= 21)%nat -> 0 <= n <= 40 -> 0 <= t -> t + 0x80 <= R - 2 * ESTACK ->
(forall a, t + n <= a < t + n + Z.of_nat (length s) -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
amem_range (t + n) (Z.of_nat (length s)) ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF (t + n) (Z.of_nat (length s)) ->
(0 < Z.of_nat (length s) -> shadow_hull_vis (aview rsegs (w_H W) mem) (t + n) (Z.of_nat (length s))) ->
(forall a, w7b_hull (t + n) (Z.of_nat (length s)) a -> 0 <= a < R - 2 * ESTACK) ->
(forall a, w7b_strz x s a -> 0 <= a < R - 2 * ESTACK) ->
(t + n + Z.of_nat (length s) <= x \/ x + Z.of_nat (length s) <= t + n) ->
(forall regs2 mem2 md2,
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k -> same_io md md2 ->
 (forall r, acallee_saved r -> r <> 24 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
 getr regs2 24 = w64 (Z.of_nat (length s)) ->
 (forall j, (j < length s)%nat ->
  aview rsegs (w_H W) mem2 (t + n + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0)))) ->
 w7b_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R \/ t + n <= a < t + n + Z.of_nat (length s)) ->
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
 SRr rsegs W (mkCfg (mkst regs2 (Z_to_bv 64 W7B_AFTER_MEMCPY) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 W7B_STRLEN) mem (seg_rom rsegs)) md) Q.
Proof using LAWS ASTRLEN AMEMCPY.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R t n x s Q
HJ H1 H10 H26 H22 H25 H2 H3 H4 HR16 Hs16 HRs HSTK HRE HR63 HSO HARO Hls Hn Ht0 Ht
Hwr Hamd Hrad Hhud Hhd Hzs Hdis K.
pose proof HSO as (Hx0 & Hk32 & Hx63 & Hbytes & Hnul & Htail & Hstk & Hamx & Hrax & Hhux).
assert (HE : ESTACK = 4096) by reflexivity. rewrite HE in *.
assert (Hsp : spZ regs = sp0 + (R - sp0)) by (unfold spZ; rewrite H2; unfold w64; rewrite unsigned_lit_small; lia).
(* ---- strlen(x) ---- *)
eapply SRr_bind.
{ apply (w7b_strlen_at B LAWS W7B_STRLEN ASTRLEN W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k x (Z.of_nat (length s)) (R - sp0) (w64 W7B_AFTER_STRLEN) HJ);
  try assumption; try lia.
  - rewrite (Zmod_minus_l_hack R sp0) || (rewrite Zminus_mod, HR16, Hs16; reflexivity).
  - apply ret_ok_even; vm_compute; reflexivity.
  - exact (w7b_strok_first_byte W mem R x s HSO).
  - intros a Ha. split.
    + destruct (Z.eq_dec a (x + Z.of_nat (length s))) as [->|Hne]; [rewrite Hnul; discriminate|].
      destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
      replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
    + rewrite Hsp. intros Hc. apply (Hstk a ltac:(lia)). lia.
  - intros a Ha. replace (sp0 + (R - sp0)) with R by lia. exact (Hstk a Ha). }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & HP1 & H10a & HK1 & Hpr1).
replace (sp0 + (R - sp0)) with R in HK1 by lia.
assert (E: forall r, acallee_saved r -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP1.
(* ---- block B ---- *)
eapply SRr_bind.
{ apply (w7b_B B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 (Z.of_nat (length s)) n x t HJ1); try lia.
  all: first
    [ exact H10a
    | rewrite <- H26; exact (E 26 ltac:(unfold acallee_saved; lia))
    | rewrite <- H22; exact (E 22 ltac:(unfold acallee_saved; lia))
    | rewrite <- H25; exact (E 25 ltac:(unfold acallee_saved; lia)) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hr2 & HK2 & Hpr2 & (R1 & R10 & R11 & R12 & R24)).
(* ---- memcpy(t + n, x, l) ---- *)
assert (EB : forall r, acallee_saved r -> r <> 24 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr Hr24. rewrite Hr2; [exact (E r Hr) | rewrite w7b_cs_bv by exact Hr; unfold acallee_saved in Hr; lia |].
  apply w7b_cs_out; [exact Hr|]. unfold acallee_saved in Hr. vm_compute. lia. }
assert (KB : w7b_kept W mem mem2 (fun a => R - 2 * ESTACK <= a < R)).
{ intros a Ha Hz. cbv beta in Hz. rewrite (HK2 a Ha (fun f => f)). exact (HK1 a Ha Hz). }
assert (Hsp2 : spZ regs2 = sp0 + (R - sp0)).
{ unfold spZ. rewrite (w7b_reg_eq regs regs2 2%bv (EB 2 ltac:(unfold acallee_saved; lia) ltac:(lia))). exact Hsp. }
eapply SRr_bind.
{ apply (w7b_memcpy_at B LAWS AMEMCPY W regs2 mem2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md2 k (t + n) x (Z.of_nat (length s)) (R - sp0)
    (w64 W7B_AFTER_MEMCPY) HJ2 R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - exact Hsp2.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - lia.
  - rewrite (w7b_reg_eq regs regs2 3%bv (EB 3 ltac:(unfold acallee_saved; lia) ltac:(lia))). exact H3.
  - rewrite (w7b_reg_eq regs regs2 4%bv (EB 4 ltac:(unfold acallee_saved; lia) ltac:(lia))). exact H4.
  - exact R1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [exact (Hwr a Ha) | lia].
  - exact Hamd.
  - apply (w7b_ra_kept W mem mem2); [exact Hrad | lia |]. intros a Ha. apply KB; cbv beta; unfold ESTACK; pose proof (Hhd a Ha); lia.
  - intros Hl. apply (w7b_hull_kept W mem mem2); [exact (Hhud Hl) |]. intros a Ha. apply KB; cbv beta; unfold ESTACK; pose proof (Hhd a Ha); lia.
  - lia.
  - lia.
  - intros a Ha. split.
    + rewrite (KB a ltac:(pose proof (Hzs a ltac:(left; lia)); lia) ltac:(cbv beta; unfold ESTACK; pose proof (Hzs a ltac:(left; lia)); lia)).
      destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
      replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
    + rewrite Hsp2. pose proof (Hzs a ltac:(left; lia)). lia.
  - exact Hdis.
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ x (Z.of_nat (length s) + 1)); [|lia|lia].
    apply (w7b_ra_kept W mem mem2); [exact Hrax | lia |]. intros a Ha. apply KB; cbv beta; unfold ESTACK; pose proof (Hzs a (or_intror Ha)); lia.
  - intros Hl. apply (rm_hull_sub _ x (Z.of_nat (length s) + 1)); [| lia | lia | lia].
    apply (w7b_hull_kept W mem mem2); [exact Hhux |]. intros a Ha. apply KB; cbv beta; unfold ESTACK; pose proof (Hzs a (or_intror Ha)); lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & HP3 & R10' & HD3 & HK3 & Hpr3).
apply K.
- exact HJ3.
- eapply same_io_trans; [eapply same_io_trans; [exact Hio1 | exact Hio2] | exact Hio3].
- intros r Hr Hr24. rewrite (HP3 r Hr). exact (EB r Hr Hr24).
- rewrite (w7b_reg_eq regs2 regs3 24%bv (HP3 24 ltac:(unfold acallee_saved; lia))). exact R24.
- intros j Hj. rewrite (HD3 (Z.of_nat j) ltac:(lia)).
  rewrite (KB (x + Z.of_nat j) ltac:(pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia) ltac:(cbv beta; unfold ESTACK; pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia)).
  exact (proj1 (Hbytes j Hj)).
- intros a Ha Hz. cbv beta in Hz. rewrite (HK3 a Ha ltac:(lia) ltac:(lia)). apply KB; [exact Ha | cbv beta; unfold ESTACK; lia].
- intros a Ha. exact (Hpr3 a (Hpr2 a (Hpr1 a Ha))).
Qed.
End d.
End b.

Print Assumptions w7b_iter.
