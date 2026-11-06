(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bIter.v at 25d4b718638 (w7_iter) for
   reac-pw/fuzz_headamp's image B: the turn's registers are image B's (the part in s7, the length so far in s10, t
   in s9, l in s4 after block B), the strlen call by HPgW7bKit.hw7b_strlen_at on the turn's cb_strok string, the
   block B by its statement HPgW7bBase.hw7b_B_stmt, the memcpy by HPgW7bKit.hw7b_memcpy_at; w7_ -> hw7b_, module
   paths. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): one turn of the parts loop of
   ent_headamp_key (pod.h:254-257) in the walk of LLVMFuzzerTestOneInput from G 0x81afc to J 0x82618, from the
   strlen wrapper's entry (0x41c18, called at 0x81b94) to the return of memcpy(t + n, parts[i], l) (0x81bbc):
   strlen, block B (the 95 clamp, which never cuts: n + l <= 61), the runtime's memcpy. Proves no function (kind:
   segment lemma). The string is any cb_strok one (an image string or ch in the frame for locals); the turn's
   post is the copied bytes at t + n, the length in s4, the callee-saved registers but s4 as before, and every byte
   outside the callees' stack below R and the copied range as before.
   REGISTERS: ra (x1), sp = R (x2), gp / tp (x3 / x4), a0 .. a2 (x10 .. x12), s4 (x20), s7 = the part (x23),
   s9 = t (x25), s10 = n (x26); no frame cell. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgW7bBase HPgW7bKit HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma hw7b_iter : forall B, astrlen_realizes rsegs B HW7B_STRLEN -> aintrin_realizes rsegs B OCpy HW7B_MEMCPY ->
hw7b_B_stmt B -> hw7b_iter_stmt B.
Proof.
intros B ASTRLEN AMEMCPY HB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs R t n x s Q
HJ H1 H10 H23 H26 H25 H2 H3 H4 HR16 Hs16 HRs HSTK HRE HR63 HSO HARO Hls Hn Ht0 Ht
Hwr Hamd Hrad Hhud Hhd Hzs Hdis K.
pose proof HSO as (Hx0 & Hk32 & Hx63 & Hbytes & Hnul & Htail & Hstk & Hamx & Hrax & Hhux).
assert (HE : ESTACK = 4096) by reflexivity. rewrite HE in *.
assert (Hsp : spZ regs = sp0 + (R - sp0)) by (unfold spZ; rewrite H2; unfold w64; rewrite unsigned_lit_small; lia).
assert (Hmod : (R - sp0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hs16; reflexivity).
(* ---- strlen(x) ---- *)
eapply SRr_bind.
{ apply (hw7b_strlen_at B ASTRLEN W regs mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k x s (R - sp0)
    (w64 HW7B_AFTER_STRLEN) HJ H10 Hsp Hmod ltac:(lia) ltac:(unfold ESTACK; lia) H3 H4 H1).
  - apply ret_ok_even; vm_compute; reflexivity.
  - replace (sp0 + (R - sp0)) with R by lia. exact HSO.
  - exact HARO. }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & Hio1 & HP1 & H10a & HK1 & Hpr1).
replace (sp0 + (R - sp0)) with R in HK1 by lia.
assert (E: forall r, acallee_saved r -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP1.
(* ---- block B ---- *)
eapply SRr_bind.
{ apply (HB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 (Z.of_nat (length s)) n x t HJ1); try lia.
  - exact H10a.
  - rewrite <- H26. exact (E 26 ltac:(unfold acallee_saved; lia)).
  - rewrite <- H23. exact (E 23 ltac:(unfold acallee_saved; lia)).
  - rewrite <- H25. exact (E 25 ltac:(unfold acallee_saved; lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hr2 & HK2 & Hpr2 & (R1 & R10 & R11 & R12 & R20)).
(* ---- memcpy(t + n, x, l) ---- *)
assert (EB : forall r, acallee_saved r -> r <> 20 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr Hr20. rewrite Hr2; [exact (E r Hr) | rewrite cb_cs_bv by exact Hr; unfold acallee_saved in Hr; lia |].
  apply cb_cs_out; [exact Hr|]. unfold acallee_saved in Hr. vm_compute. lia. }
assert (KB : cb_kept W mem mem2 (fun a => R - 2 * 4096 <= a < R)).
{ intros a Ha Hz. cbv beta in Hz. rewrite (HK2 a Ha (fun f => f)). exact (HK1 a Ha Hz). }
assert (Hsp2 : spZ regs2 = sp0 + (R - sp0)).
{ unfold spZ. rewrite (cb_reg_eq regs regs2 2%bv (EB 2 ltac:(unfold acallee_saved; lia) ltac:(lia))). exact Hsp. }
eapply SRr_bind.
{ apply (hw7b_memcpy_at B AMEMCPY W regs2 mem2 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md2 k (t + n) x
    (Z.of_nat (length s)) (R - sp0) (w64 HW7B_AFTER_MEMCPY) HJ2 R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - exact Hsp2.
  - exact Hmod.
  - lia.
  - unfold ESTACK; lia.
  - rewrite (cb_reg_eq regs regs2 3%bv (EB 3 ltac:(unfold acallee_saved; lia) ltac:(lia))). exact H3.
  - rewrite (cb_reg_eq regs regs2 4%bv (EB 4 ltac:(unfold acallee_saved; lia) ltac:(lia))). exact H4.
  - exact R1.
  - apply ret_ok_even; vm_compute; reflexivity.
  - intros a Ha. split; [exact (Hwr a Ha) | unfold ESTACK; lia].
  - exact Hamd.
  - apply (cb_ra_kept W mem mem2); [exact Hrad | lia |]. intros a Ha. apply KB; cbv beta; pose proof (Hhd a Ha); lia.
  - intros Hl. apply (cb_hull_kept W mem mem2); [exact (Hhud Hl) |]. intros a Ha. apply KB; cbv beta; pose proof (Hhd a Ha); lia.
  - lia.
  - lia.
  - intros a Ha. split.
    + rewrite (KB a ltac:(pose proof (Hzs a ltac:(left; lia)); lia) ltac:(cbv beta; pose proof (Hzs a ltac:(left; lia)); lia)).
      destruct (Z.eq_dec a (x + Z.of_nat (length s))) as [->|Hne]; [rewrite Hnul; discriminate|].
      destruct (Hbytes (Z.to_nat (a - x)) ltac:(lia)) as [Hb _]. rewrite Z2Nat.id in Hb by lia.
      replace (x + (a - x)) with a in Hb by lia. rewrite Hb. discriminate.
    + rewrite Hsp2. unfold ESTACK. pose proof (Hzs a ltac:(left; lia)). lia.
  - exact Hdis.
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ x (Z.of_nat (length s) + 1)); [|lia|lia].
    apply (cb_ra_kept W mem mem2); [exact Hrax | lia |]. intros a Ha. apply KB; cbv beta; pose proof (Hzs a (or_intror Ha)); lia.
  - intros Hl. apply (hm_hull_sub _ x (Z.of_nat (length s) + 1)); [| lia | lia | lia].
    apply (cb_hull_kept W mem mem2); [exact Hhux |]. intros a Ha. apply KB; cbv beta; pose proof (Hzs a (or_intror Ha)); lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & HP3 & R10' & HD3 & HK3 & Hpr3).
apply K.
- exact HJ3.
- eapply same_io_trans; [eapply same_io_trans; [exact Hio1 | exact Hio2] | exact Hio3].
- intros r Hr Hr20. rewrite (HP3 r Hr). exact (EB r Hr Hr20).
- rewrite (cb_reg_eq regs2 regs3 20%bv (HP3 20 ltac:(unfold acallee_saved; lia))). exact R20.
- intros j Hj. rewrite (HD3 (Z.of_nat j) ltac:(lia)).
  rewrite (KB (x + Z.of_nat j) ltac:(pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia) ltac:(cbv beta; pose proof (Hzs (x + Z.of_nat j) ltac:(left; lia)); lia)).
  exact (proj1 (Hbytes j Hj)).
- intros a Ha Hz. cbv beta in Hz. rewrite (HK3 a Ha ltac:(lia) ltac:(unfold ESTACK; lia)). apply KB; [exact Ha | cbv beta; lia].
- intros a Ha. exact (Hpr3 a (Hpr2 a (Hpr1 a Ha))).
Qed.
End b.

Print Assumptions hw7b_iter.
