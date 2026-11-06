(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the CALL ADAPTERS of the image-A walk of LLVMFuzzerTestOneInput (0x80bc0) at its five
   soft-float calls, in the inlined pod_nearest of segment M03 (piece value_nearest, pod.h:157-165). Proves no
   function (kind: segment lemma): each lemma turns a soft-float routine's CJ contract into the step a walk lane
   takes at the `jal`.

   THE SITES (capstone over the unstripped twin; the callees' entries are its .symtab addresses, every return
   address is the `jal`'s pc plus 4; no address here is relocated from fuzz_role's image):
     0x834c4 jal __extendsftf2 0x85248, ra 0x834c8: the argument is the binary32 in fa0 (`fmv.s fa0,fs0` 0x834c0);
             the result d in a0:a1 (stored at R+0x90 / R+0x88 by 0x834c8 / 0x834cc);
     0x834d8 jal __floatditf 0x853a4, ra 0x834dc: a0 = s4 = fcvt.l.s of fs0 (0x834d0 .. 0x834d4); the result in a0:a1;
     0x834ec jal __subtf3 0x854c8, ra 0x834f0: a0:a1 from R+0x90 / R+0x88 (0x834e4 / 0x834e8), a2:a3 the __floatditf
             result (0x834dc / 0x834e0); __subtf3 (16 bytes) runs into __addtf3 0x854d8, whose 48-byte frame lies
             below sp; the result in a0:a1;
     0x83500 jal __getf2 0x84ffc, ra 0x83504: a0:a1 the __subtf3 result, a2 = 0 (0x834f8), a3 = R+0xb0, the 0.5 high
             word (0x834fc); the result in a0 (`bgez a0` 0x83504);
     0x83518 jal __lttf2 0x84f34, ra 0x8351c: a0:a1 from R+0x90 / R+0x88 (0x83508 / 0x8350c), a2 = 0 (0x83510),
             a3 = R+0xa8, the -0.5 high word (0x83514); the result in a0 (`bgez a0` 0x8351c). __lttf2 is the same
             address as __letf2, __cmptf2, __eqtf2 and __netf2 (one routine, five names); its CJ contract is
             letf2_contract.
   Every routine's bytes are equal to fuzz_role's image A copy (same sizes 348, 292, 16, 1996, 188, 200).

   WHAT EACH LEMMA GIVES. hc_sf_<routine>_call is lib/A/HPgCalls.v's hc_call at that site: from hc_core at the
   `jal` (pc = the routine's entry, ra = the return address), the argument registers, the read agreement
   rom_view (the seam's premise) and a zero rounding mode, the walk continues at ra with hc_core at the returned
   state, the callee-saved registers, the frames, blocks, I/O state and meter as at the call, every byte as at the
   call (for __subtf3: every byte outside its stack [R - 48, R)), rom_view again at the returned store (the next
   site's premise), the routine's result in a0 (and a1) as its CJ post states it, and a float state fx2 with
   hd_fxk [] fx fx2: EVERY float register as at the call (so fs0 = f, fs1 = -1.0f and fs2 = 256.0f survive the
   call, the plan's risk 5) and a zero rounding mode. The CJ posts keep the float register file F; the posts of
   __extendsftf2, __floatditf, __getf2 and __lttf2 keep fcsr; the post of __subtf3 (through __addtf3) gives some
   fcsr with a zero rounding mode (frm0).

   THE ROUTE. hc_leaf_lift is the generic lift of one leaf call: a lib/Lib evt from the normalized store
   (lib/A/HPgSeamN.v) at pc = the routine's entry, whose post (hc_leaf_post) returns to ra with the callee-saved
   registers, sp, gp and tp kept, F kept, frm0 of the returned fcsr and the store changed at most in [sp - T, sp),
   gives SRr from cfg_at to HPgCSpec's hd_post with FX = hd_fxk [] fx, no effect set and the result registers; the
   caller's journal is extended over [sp - T, sp) by YCbq.ajournal_exec, as fuzz_role's lib/A/RPgNear.v extends it
   for the whole of pod_nearest. hc_br_<routine> turns the CJ library's contract (an evt in
   lib/CJ/Lib) into that lib/Lib evt through lib/U/CJBridge.v, as fuzz_role's lib/Prog/pod_nearest.v br_ext, br_fd,
   br_sub, br_ge, br_le do; the two copies of MemNorm (lib/MemNorm.v, lib/U/MemNorm.v)
   differ only in the module prefix of their imports, so their task_mem is one text (hc_tm_u).

   THE IMAGE RECORD. Headamp's image-A soft-float symbol map (the RImg instance and the CJ instances at image A)
   is Section data here: IMG with HIMG (its segments are lib/A/Img0.v rsegs), the five symbol facts
   HK_EXT (key 0x200dc), HK_FD (0x7f000900), HK_SUB (0x1bc70), HK_GE (0x1b314), HK_LT (0x1b24c), and the five
   contracts C_EXT, C_FD, C_SUB, C_GE, C_LT at IMG. MTL is the meter's laws (the callee keeps the state, so the
   meter clause is mo_le_refl). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require
PropExec MState Mem Exec Frame FP Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib Require MState.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_subtf3 G_getf2 G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgCalls HPgSeamN.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module SF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec.SoftFloat.
Module CMS := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Lib.MState.
Module UMN := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.MemNorm.
Module CJB := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.CJBridge.

(* ======================================== image A: the routines and the return addresses ======================================== *)
Definition A_SF_EXT : Z := 0x85248.     (* __extendsftf2 *)
Definition A_SF_FD : Z := 0x853a4.      (* __floatditf *)
Definition A_SF_SUB : Z := 0x854c8.     (* __subtf3; runs into __addtf3 0x854d8 *)
Definition A_SF_GE : Z := 0x84ffc.      (* __getf2 = __gttf2 *)
Definition A_SF_LT : Z := 0x84f34.      (* __lttf2 = __letf2 = __cmptf2 = __eqtf2 = __netf2 *)
Definition RA_SF_EXT : Z := 0x834c8.
Definition RA_SF_FD : Z := 0x834dc.
Definition RA_SF_SUB : Z := 0x834f0.
Definition RA_SF_GE : Z := 0x83504.
Definition RA_SF_LT : Z := 0x8351c.
(* __addtf3's frame: `addi sp,sp,-48`, six saved registers (G_subtf3.v addtf3_post: munch and stk of
   [sp - 48, sp)). *)
Definition HC_SUB_STK : Z := 48.

(* ======================================== the lib/Lib post of one leaf call ======================================== *)
(* The routine returns to ra (ret_pc of the caller's x1) with the callee-saved registers (sp, gp, tp, s0-s11) and
   ra of the caller, the float register file F of the call, some fcsr with a zero rounding mode, and a store that
   differs from the call's at most in [sp - T, sp), every byte of which is there; Rr is what it computes. *)
Definition hc_leaf_post (segs : list Segment) (T : Z) (regs F : bvmap 5 word) (Rr : bvmap 5 word -> Prop)
(m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (R' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = LMS.MS R' F (LMS.ret_pc (reg_get regs 1)) fc' None m' (LPE.seg_rom segs) /\
aregs_preserved regs R' /\ getr R' (Z_to_bv 5 1) = getr regs (Z_to_bv 5 1) /\ LFP.frm0 fc' /\
LF.munch [(spZ regs - T, spZ regs)] m m' /\ LF.stk segs m' (spZ regs - T) (spZ regs) /\ Rr R'.

(* The results: one 64-bit word in a0 (the comparisons), or a binary128 value in a0:a1 (low word, high word). *)
Definition hc_r1 (v : Z) (R' : bvmap 5 word) : Prop := getr R' 10 = w64 v.
Definition hc_r2 (x : Z) (R' : bvmap 5 word) : Prop := getr R' 10 = w64 (SF.lo64 x) /\ getr R' 11 = w64 (SF.hi64 x).

Lemma hc_r1_ext : forall v (R1 R2 : bvmap 5 word), (forall r, getr R1 r = getr R2 r) -> hc_r1 v R1 -> hc_r1 v R2.
Proof. intros v R1 R2 E H. unfold hc_r1 in *. rewrite <- E. exact H. Qed.
Lemma hc_r2_ext : forall x (R1 R2 : bvmap 5 word), (forall r, getr R1 r = getr R2 r) -> hc_r2 x R1 -> hc_r2 x R2.
Proof. intros x R1 R2 E H. unfold hc_r2 in *. rewrite <- !E. exact H. Qed.
(* The two halves of a binary128 result are 64-bit values (the range premises of the next site's arguments). *)
Lemma hc_lo64_rng : forall x, 0 <= SF.lo64 x < 2 ^ 64.
Proof. intros x. exact (SF.wrap64_range x). Qed.
Lemma hc_hi64_rng : forall x, 0 <= SF.hi64 x < 2 ^ 64.
Proof. intros x. exact (SF.wrap64_range (Z.shiftr x 64)). Qed.

(* ======================================== small bridges ======================================== *)
Lemma hc_getr_xeqv : forall R1 R2 : bvmap 5 word, R6.xregs_eqv R1 R2 -> forall r, getr R1 r = getr R2 r.
Proof.
intros R1 R2 H r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
apply H. rewrite <- LPE.bv_eqb0_is_x0. exact E.
Qed.

(* the two copies of MemNorm state task_mem with one text *)
Lemma hc_tm_u : forall segs m, MN.task_mem segs m -> UMN.task_mem segs m.
Proof. intros segs m H. exact H. Qed.

Lemma hc_spZ_rng : forall regs : bvmap 5 word, 0 <= spZ regs < 2 ^ 64.
Proof.
intros regs. unfold spZ. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. unfold bv_modulus in Hr.
change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. exact Hr.
Qed.

Lemma hc_stk_nil : forall segs m (s : Z), 0 <= s < 2 ^ 64 -> LF.stk segs m (s - 0) s.
Proof. intros segs m s Hs. split; [lia|]. split; [lia|]. intros a Ha. exfalso. lia. Qed.

Lemma hc_munch_nil : forall (m m' : word -> option byte) (s : Z),
LF.munch [] m m' -> LF.munch [(s - 0, s)] m m'.
Proof. intros m m' s H x _. exact (H x I). Qed.

(* An argument register holds the 64-bit value v (r is not x0: getr is reg_get there, by computation). *)
Lemma hc_arg : forall (regs : bvmap 5 word) (r : bv 5) (v : Z), getr regs r = reg_get regs r ->
getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (reg_get regs r) = v.
Proof.
intros regs r v Hr H Hv. rewrite <- Hr, H. apply hc_u64. exact Hv.
Qed.

Lemma hc_arg_wrap : forall (regs : bvmap 5 word) (t : Z), getr regs 10 = w64 t ->
bv_unsigned (reg_get regs 10) = SF.wrap64 t.
Proof.
intros regs t H. change (reg_get regs 10) with (getr regs 10). rewrite H.
change (bv_unsigned (w64 t)) with (bv_unsigned (Z_to_bv 64 t)). rewrite Z_to_bv_unsigned, SF.wrap64_mod.
reflexivity.
Qed.

(* The callee-saved registers of a CJ post's register map (sp, gp, tp, s0-s11 as at entry). *)
Local Ltac hc_pres :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr'" in
  intros r Hr; unfold acallee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [reflexivity .. |];
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25
                \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.

(* ======================================== the five routines, from the CJ library to lib/Lib ======================================== *)
Lemma hc_br_ext : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x200dc = pc ->
@C_extendsftf2.extendsftf2_contract I ->
forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
LFP.frm0 fc -> LM.mem_inv segs m -> MN.task_mem segs m ->
LEx.evt segs (hc_leaf_post segs 0 regs F (hc_r2 (C_extendsftf2.f128_of_f32 (bv_unsigned (reg_get F 10)))) m)
(LMS.MS (R6.mkR_of regs) F (Z_to_bv 64 pc) fc None m (LPE.seg_rom segs)).
Proof.
intros I segs pc HI Hpc C regs F fc m Hfrm MI TM. subst segs pc.
pose proof (C (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
  (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
  (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
  (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
  (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
  (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
  (reg_get regs 31) F fc m (CJB.mem_inv_to_cj _ m MI (hc_tm_u _ m TM))) as E.
refine (CJB.evt_bridge _ _ _ _ _ E).
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & _ & _).
exists (ms_regs ms'), (ms_fcsr ms'), (ms_mem ms'). rewrite Hms. cbn [ms_regs ms_fcsr ms_mem CMS.MS].
split; [reflexivity|]. split; [hc_pres|]. split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (hc_munch_nil m m' (spZ regs) MU)|]. split; [exact (hc_stk_nil _ m' (spZ regs) (hc_spZ_rng regs))|].
unfold hc_r2. split; reflexivity.
Qed.

Lemma hc_br_fd : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x7f000900 = pc ->
@C_floatditf.floatditf_contract I ->
forall (t : Z) (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
bv_unsigned (reg_get regs 10) = SF.wrap64 t ->
LFP.frm0 fc -> LM.mem_inv segs m -> MN.task_mem segs m ->
LEx.evt segs (hc_leaf_post segs 0 regs F (hc_r2 (C_floatditf.f128_of_i64 t)) m)
(LMS.MS (R6.mkR_of regs) F (Z_to_bv 64 pc) fc None m (LPE.seg_rom segs)).
Proof.
intros I segs pc HI Hpc C t regs F fc m Ht Hfrm MI TM. subst segs pc.
pose proof (C (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
  (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
  (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
  (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
  (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
  (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
  (reg_get regs 31) F fc m t (CJB.mem_inv_to_cj _ m MI (hc_tm_u _ m TM)) Ht) as E.
refine (CJB.evt_bridge _ _ _ _ _ E).
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & _ & _).
exists (ms_regs ms'), (ms_fcsr ms'), (ms_mem ms'). rewrite Hms. cbn [ms_regs ms_fcsr ms_mem CMS.MS].
split; [reflexivity|]. split; [hc_pres|]. split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (hc_munch_nil m m' (spZ regs) MU)|]. split; [exact (hc_stk_nil _ m' (spZ regs) (hc_spZ_rng regs))|].
unfold hc_r2. split; reflexivity.
Qed.

(* __subtf3 (and the __addtf3 it runs into) uses the 48 bytes below its sp and rounds with frm. *)
Lemma hc_br_sub : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1bc70 = pc ->
@G_subtf3.subtf3_contract I ->
forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (alo ahi blo bhi : Z),
bv_unsigned (reg_get regs 10) = alo -> bv_unsigned (reg_get regs 11) = ahi ->
bv_unsigned (reg_get regs 12) = blo -> bv_unsigned (reg_get regs 13) = bhi ->
LFP.frm0 fc -> LF.stk segs m (spZ regs - HC_SUB_STK) (spZ regs) -> LM.mem_inv segs m -> MN.task_mem segs m ->
LEx.evt segs (hc_leaf_post segs HC_SUB_STK regs F
  (hc_r2 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) m)
(LMS.MS (R6.mkR_of regs) F (Z_to_bv 64 pc) fc None m (LPE.seg_rom segs)).
Proof.
intros I segs pc HI Hpc C regs F fc m alo ahi blo bhi E0 E1 E2 E3 Hfrm ST MI TM. subst segs pc alo ahi blo bhi.
pose proof (C (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
  (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
  (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
  (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
  (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
  (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
  (reg_get regs 31) F fc m ST (CJB.mem_inv_to_cj _ m MI (hc_tm_u _ m TM)) Hfrm) as E.
refine (CJB.evt_bridge _ _ _ _ _ E).
intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & fc' & m' & Hms & MU & _ & _
            & Hfrm' & ST').
exists (ms_regs ms'), (ms_fcsr ms'), (ms_mem ms'). rewrite Hms. cbn [ms_regs ms_fcsr ms_mem CMS.MS].
split; [reflexivity|]. split; [hc_pres|]. split; [reflexivity|]. split; [exact Hfrm'|].
split; [exact MU|]. split; [exact ST'|].
unfold hc_r2. split; reflexivity.
Qed.

Lemma hc_br_ge : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1b314 = pc ->
@G_getf2.getf2_contract I ->
forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (alo ahi blo bhi : Z),
bv_unsigned (reg_get regs 10) = alo -> bv_unsigned (reg_get regs 11) = ahi ->
bv_unsigned (reg_get regs 12) = blo -> bv_unsigned (reg_get regs 13) = bhi ->
LFP.frm0 fc -> LM.mem_inv segs m -> MN.task_mem segs m ->
LEx.evt segs (hc_leaf_post segs 0 regs F (hc_r1 (SF.f128_ge (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) m)
(LMS.MS (R6.mkR_of regs) F (Z_to_bv 64 pc) fc None m (LPE.seg_rom segs)).
Proof.
intros I segs pc HI Hpc C regs F fc m alo ahi blo bhi E0 E1 E2 E3 Hfrm MI TM. subst segs pc alo ahi blo bhi.
pose proof (C (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
  (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
  (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
  (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
  (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
  (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
  (reg_get regs 31) F fc m (CJB.mem_inv_to_cj _ m MI (hc_tm_u _ m TM))) as E.
refine (CJB.evt_bridge _ _ _ _ _ E).
intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & _ & _).
exists (ms_regs ms'), (ms_fcsr ms'), (ms_mem ms'). rewrite Hms. cbn [ms_regs ms_fcsr ms_mem CMS.MS].
split; [reflexivity|]. split; [hc_pres|]. split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (hc_munch_nil m m' (spZ regs) MU)|]. split; [exact (hc_stk_nil _ m' (spZ regs) (hc_spZ_rng regs))|].
unfold hc_r1. reflexivity.
Qed.

(* __lttf2 is __letf2's code (one address, 0x84f34). *)
Lemma hc_br_le : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1b24c = pc ->
@G_letf2.letf2_contract I ->
forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (alo ahi blo bhi : Z),
bv_unsigned (reg_get regs 10) = alo -> bv_unsigned (reg_get regs 11) = ahi ->
bv_unsigned (reg_get regs 12) = blo -> bv_unsigned (reg_get regs 13) = bhi ->
LFP.frm0 fc -> LM.mem_inv segs m -> MN.task_mem segs m ->
LEx.evt segs (hc_leaf_post segs 0 regs F (hc_r1 (SF.f128_le (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) m)
(LMS.MS (R6.mkR_of regs) F (Z_to_bv 64 pc) fc None m (LPE.seg_rom segs)).
Proof.
intros I segs pc HI Hpc C regs F fc m alo ahi blo bhi E0 E1 E2 E3 Hfrm MI TM. subst segs pc alo ahi blo bhi.
pose proof (C (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
  (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
  (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
  (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
  (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
  (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
  (reg_get regs 31) F fc m (CJB.mem_inv_to_cj _ m MI (hc_tm_u _ m TM))) as E.
refine (CJB.evt_bridge _ _ _ _ _ E).
intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & _ & _).
exists (ms_regs ms'), (ms_fcsr ms'), (ms_mem ms'). rewrite Hms. cbn [ms_regs ms_fcsr ms_mem CMS.MS].
split; [reflexivity|]. split; [hc_pres|]. split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (hc_munch_nil m m' (spZ regs) MU)|]. split; [exact (hc_stk_nil _ m' (spZ regs) (hc_spZ_rng regs))|].
unfold hc_r1. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The read agreement survives a call that keeps every byte outside a range above the image: every read-only
   byte lies in the image, below kLowMemEnd. *)
Lemma hc_rom_view_keep : forall (W W2 : world rsegs) (memc mem2 : word -> option byte) (lo hi : Z),
kLowMemEnd <= lo -> rom_view rsegs W memc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
rom_view rsegs W2 mem2.
Proof.
intros W W2 memc mem2 lo hi Hlo HR Hk a Ha.
assert (Hi : in_img rsegs a) by (destruct Ha as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]).
pose proof (hsn_segs_low a Hi) as Hl.
pose proof asan_consts as (_ & _ & _ & _ & AC5).
rewrite Hk by lia. exact (HR a Ha).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================== the lift of one leaf call ======================================== *)
(* From hd_pre at a call with stack T (the callee uses [sp - T, sp), inside the caller's window) and the read
   agreement: a lib/Lib walk of the routine on the normalized store, which may assume the window present there
   and the two store invariants, is the routine's hd_post: the float registers all kept with a zero rounding
   mode, no write for the caller, and what the routine computes. *)
Theorem hc_leaf_lift : forall (a T : Z) (Rr : bvmap 5 word -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word),
(forall R1 R2 : bvmap 5 word, (forall r, getr R1 r = getr R2 r) -> Rr R1 -> Rr R2) ->
0 <= T ->
hd_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
rom_view rsegs W memc ->
(LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - T) (spZ regs) ->
 LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 LEx.evt rsegs (hc_leaf_post rsegs T regs (@fp_regs fx) Rr (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
 (LMS.MS (R6.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 a) (@fp_csr fx) None
  (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (LPE.seg_rom rsegs))) ->
SRr rsegs W (cfg_at rsegs a regs memc mdc)
(hd_post rsegs B MT STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc
 (hd_fxk [] fx) (fun _ => False) (fun _ regs2 _ => Rr regs2)).
Proof.
intros a T Rr STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs Hext HT HPRE HRV EVF.
destruct HPRE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hios & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4
                  & Hgone & Hpres & Hstk0 & F5 & HQT).
pose proof Hstk0 as (Hsp0al & HSTK0 & Hceil & Hlolo & Hhihi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).

(* ---- the geometry of the callee's stack ---- *)
assert (Hlo_ceil : alloc_ceiling <= spZ regs - T) by lia.
assert (Hsp_hi : spZ regs <= 2 ^ 47) by lia.
assert (Hnoimg : forall x, spZ regs - T <= x < spZ regs -> ~ in_img rsegs x).
{ intros x Hx Hin. pose proof (hsn_segs_low x Hin). lia. }

(* ---- the normalized store ---- *)
assert (HMI : LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
  by (apply (MN.mem_inv_cj_inv rsegs); apply MN.mem_inv_cj_normalize).
assert (HTM : MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
  by (apply (MN.mem_inv_cj_task rsegs); apply MN.mem_inv_cj_normalize).
assert (HSTKm : LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - T) (spZ regs)).
{ split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Hpres x ltac:(lia)) as (HH & bb & Hbb).
  assert (Em : MN.normalize_cj rsegs (mrestrict (w_H W) memc) (LM.wa x) = Some bb).
  { unfold MN.normalize_cj. rewrite (hsn_keep x ltac:(unfold TASK_SIZE; lia) (Hnoimg x Hx)).
    unfold mrestrict, LM.wa. rewrite HH. exact Hbb. }
  split; [unfold wview; rewrite Em; discriminate | exists bb; unfold LM.mrd; rewrite Em; reflexivity]. }
pose proof (EVF HSTKm HMI HTM) as EVW.

(* ---- lifted into SRr ---- *)
apply (hsn_srr_of_norm_evt W a regs memc mdc _ _ HRV EVW).
intros msf can sq model' HQ Hrel Hcjs Heqv Hsm Hcl.
destruct HQ as (R' & fc' & m' & Hsq & Hpres' & Hra' & Hfrm' & Hmu & Hstk' & HRr).
subst sq.
destruct can as [cr cfr cpc csv crv cfc cm cro].
destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hmrel).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom LMS.MS] in
  E1, E2, E3, E4, E5, E6, E7, Hmrel, Hcjs, Heqv.
subst cr cfr cpc csv crv cfc cro.
destruct msf as [fr ffr fpc fsv frv ffc fm fro].
destruct Heqv as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in
  X1, X2, X3, X4, X5, X6, X7, X8.
subst ffr fpc fsv frv ffc fm fro.

(* the write set of the call: the callee's stack *)
pose (Wr := fun x : Z => spZ regs - T <= x < spZ regs).
assert (Wdec : forall x : Z, Wr x \/ ~ Wr x) by (intros x; unfold Wr; lia).

(* every byte outside the write set is the caller's *)
assert (KEEP : forall x : word, ~ Wr (bv_unsigned x) -> cm x = mrestrict (w_H W) memc x).
{ intros x Hx. destruct (MN.cj_drop rsegs x) eqn:Dx.
  - exact (Hcjs x Dx).
  - rewrite <- (MN.mem_rel_cj_keep rsegs cm m' x Hmrel Dx).
    rewrite (Hmu x ltac:(cbn [LF.outside]; split; [exact Hx | exact I])).
    unfold MN.normalize_cj. rewrite Dx. reflexivity. }

(* every byte of the write set is present after the call *)
assert (PRESW : forall x, Wr x -> exists bb, cm (LM.wa x) = Some bb).
{ intros x Hx. unfold Wr in Hx.
  assert (Dx : MN.cj_drop rsegs (LM.wa x) = false)
    by (apply hsn_keep; [unfold TASK_SIZE; lia | exact (Hnoimg x Hx)]).
  destruct Hstk' as (_ & _ & Hs). destruct (Hs x Hx) as (_ & bb & Hbb).
  unfold LM.mrd in Hbb. rewrite (hsn_rom_none x ltac:(lia) (Hnoimg x Hx)) in Hbb.
  destruct (m' (LM.wa x)) as [b0|] eqn:Em'; [|discriminate Hbb].
  exists b0. rewrite <- (MN.mem_rel_cj_keep rsegs cm m' (LM.wa x) Hmrel Dx). exact Em'. }

(* the three facts the journal's execution step asks of the new store *)
assert (HA : forall x : word, ~ Wr (bv_unsigned x) ->
  mrestrict (w_H W) (munrestrict (w_H W) memc cm) x = mrestrict (w_H W) memc x).
{ intros x Hx. rewrite hsn_mrestrict_munrestrict.
  pose proof (KEEP x Hx) as Hk. unfold mrestrict in Hk |- *.
  destruct (w_H W x); [reflexivity | exact Hk]. }
assert (HB : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (munrestrict (w_H W) memc cm))).
{ intros x Hx. rewrite hsn_mrestrict_munrestrict. unfold mrestrict in Hx |- *.
  destruct (w_H W x) eqn:EH; [exact Hx|].
  destruct (Wdec (bv_unsigned x)) as [Hw | Hw].
  - destruct (PRESW (bv_unsigned x) Hw) as (bb & Hbb).
    unfold LM.wa in Hbb. rewrite LMS.Z_to_bv_bv_unsigned in Hbb. rewrite Hbb. discriminate.
  - pose proof (KEEP x Hw) as Hk. unfold mrestrict in Hk. rewrite EH in Hk. rewrite Hk. exact Hx. }
assert (HC : forall x : word, w_H W x = true -> munrestrict (w_H W) memc cm x = memc x).
{ intros x Hx. unfold munrestrict. rewrite Hx. reflexivity. }
assert (HD : forall x, Wr x -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x).
{ intros x Hx. left. unfold Wr in Hx. lia. }

red.
exists (YK11.mkFP (@fp_regs fx) fc'), lyc, Sc, fr, (munrestrict (w_H W) memc cm), model'.
split.
{ unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite (hsn_ret_pc (reg_get regs 1)
            ltac:(change (reg_get regs 1) with (getr regs 1); exact Hra)).
  reflexivity. }
split.
{ split; [intros r _; reflexivity | exact Hfrm']. }
split.
{ exact (ajournal_exec rsegs B (AR_laws_ok rsegs B) hsn_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
          (munrestrict (w_H W) memc cm) model' Wr HJ HA HB HC Hsm HD). }
split.
{ intros r Hr. rewrite <- (hc_getr_xeqv R' fr X1 (Z_to_bv 5 r)). exact (Hpres' r Hr). }
split; [rewrite <- (hc_getr_xeqv R' fr X1 (Z_to_bv 5 1)); exact Hra'|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [exact (same_io_materialized mdc model' Hsm)|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros x Hx Hns _.
  apply (aview_eq_of rsegs (w_H W) memc (munrestrict (w_H W) memc cm) x).
  apply HA. rewrite LMS.unsigned_lit by exact Hx. exact Hns. }
exact (Hext R' fr (hc_getr_xeqv R' fr X1) HRr).
Qed.

(* ======================================== the five call sites ======================================== *)
Section sf.
Variable IMG : RStep.RImg.
Hypothesis HIMG : @RStep.img_segs IMG = rsegs.
Hypothesis HK_EXT : @RStep.sym IMG 0x200dc = A_SF_EXT.
Hypothesis HK_FD : @RStep.sym IMG 0x7f000900 = A_SF_FD.
Hypothesis HK_SUB : @RStep.sym IMG 0x1bc70 = A_SF_SUB.
Hypothesis HK_GE : @RStep.sym IMG 0x1b314 = A_SF_GE.
Hypothesis HK_LT : @RStep.sym IMG 0x1b24c = A_SF_LT.
Hypothesis C_EXT : @C_extendsftf2.extendsftf2_contract IMG.
Hypothesis C_FD : @C_floatditf.floatditf_contract IMG.
Hypothesis C_SUB : @G_subtf3.subtf3_contract IMG.
Hypothesis C_GE : @G_getf2.getf2_contract IMG.
Hypothesis C_LT : @G_letf2.letf2_contract IMG.

(* The continuation a walk gives at a soft-float site: at ra, some fx2 with every float register kept and a zero
   rounding mode, hc_core again, the callee-saved registers, frames, blocks, I/O and meter as at the call, every
   byte outside [R - T, R) as at the call, the read agreement rom_view at the returned store (so the next call's
   premise is there), and Rr of the returned registers. *)
Definition hc_sf_k (T ret : Z) (Rr : bvmap 5 word -> Prop) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc (W : world rsegs) memc mdc (regs : bvmap 5 word) (R : Z) : Prop :=
forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
wle W W2 -> hd_fxk [] fx fx2 ->
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
same_io mdc md2 -> mo_le MT Sc S2 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (R - T <= x < R) -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
rom_view rsegs W2 mem2 ->
Rr regs2 ->
SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 ret) mem2 (seg_rom rsegs)) md2) Q.

(* hc_call at a leaf site: the routine's lib/Lib walk (from the bridge) and the continuation hc_sf_k. *)
Lemma hc_sf_call : forall (a T ret : Z) (Rr : bvmap 5 word -> Prop) (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R : Z),
(forall R1 R2 : bvmap 5 word, (forall r, getr R1 r = getr R2 r) -> Rr R1 -> Rr R2) ->
0 <= T <= T_SEG_STK ->
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
rom_view rsegs W memc ->
(LF.stk rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (spZ regs - T) (spZ regs) ->
 LM.mem_inv rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 MN.task_mem rsegs (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) ->
 LEx.evt rsegs (hc_leaf_post rsegs T regs (@fp_regs fx) Rr (MN.normalize_cj rsegs (mrestrict (w_H W) memc)))
 (LMS.MS (R6.mkR_of regs) (@fp_regs fx) (Z_to_bv 64 a) (@fp_csr fx) None
  (MN.normalize_cj rsegs (mrestrict (w_H W) memc)) (LPE.seg_rom rsegs))) ->
hc_sf_k T ret Rr Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
SRr rsegs W (cfg_at rsegs a regs memc mdc) Q.
Proof.
intros a T ret Rr Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R Hext HT HC Hra Hr1 Hr2 HRV EVF K.
apply (hc_call rsegs B MT a T ret (hd_fxk [] fx) (fun _ => False) (fun _ regs2 _ => Rr regs2) Q
  STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC Hra Hr1 Hr2 HT).
- intros HP. exact (hc_leaf_lift a T Rr STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs Hext
    ltac:(lia) HP HRV EVF).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres _ Hfr Hperm Hio Hmo Hkeep HRr.
  assert (Hk' : forall x, 0 <= x < 2 ^ 64 -> ~ (R - T <= x < R) ->
    aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x)
    by (intros x Hx Hs; exact (Hkeep x Hx Hs (fun H => H))).
  pose proof (hc_core_R rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R HC2) as (HRc & _ & _).
  pose proof asan_consts as (AC1 & _ & _ & _ & AC5).
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hk'); [|exact HRr].
  exact (hc_rom_view_keep W W2 memc mem2 (R - T) R ltac:(lia) HRV Hk').
Qed.

Local Ltac sf_T0 := unfold T_SEG_STK, ASTACK; lia.

(* 0x834c4: d = __extendsftf2(f), f the binary32 in fa0 (v = the 64-bit value of fa0, read by fmv.x.w as its low
   32 bits); d in a0:a1. *)
Lemma hc_sf_extendsftf2_call : forall (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R v : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_SF_EXT ->
bv_unsigned (reg_get (@fp_regs fx) 10) = v ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.lo64 (C_extendsftf2.f128_of_f32 v)) ->
 getr regs2 11 = w64 (SF.hi64 (C_extendsftf2.f128_of_f32 v)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 RA_SF_EXT) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs A_SF_EXT regs memc mdc) Q.
Proof.
intros Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R v HC Hra Hv HRV Hfrm K. subst v.
apply (hc_sf_call A_SF_EXT 0 RA_SF_EXT (hc_r2 (C_extendsftf2.f128_of_f32 (bv_unsigned (reg_get (@fp_regs fx) 10))))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r2_ext _) ltac:(sf_T0) HC Hra
  ltac:(unfold RA_SF_EXT; lia) ltac:(reflexivity) HRV).
- intros _ HMI HTM.
  exact (hc_br_ext IMG rsegs A_SF_EXT HIMG HK_EXT C_EXT regs (@fp_regs fx) (@fp_csr fx) _ Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv (E10 & E11).
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10 | exact E11].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

(* 0x834d8: __floatditf(t), t = a0 = fcvt.l.s of f (any 64-bit two's-complement word); the binary128 value of t in
   a0:a1. *)
Lemma hc_sf_floatditf_call : forall (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R t : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_SF_FD ->
getr regs 10 = w64 t ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.lo64 (C_floatditf.f128_of_i64 t)) ->
 getr regs2 11 = w64 (SF.hi64 (C_floatditf.f128_of_i64 t)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 RA_SF_FD) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs A_SF_FD regs memc mdc) Q.
Proof.
intros Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R t HC Hra H10 HRV Hfrm K.
apply (hc_sf_call A_SF_FD 0 RA_SF_FD (hc_r2 (C_floatditf.f128_of_i64 t))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r2_ext _) ltac:(sf_T0) HC Hra
  ltac:(unfold RA_SF_FD; lia) ltac:(reflexivity) HRV).
- intros _ HMI HTM.
  exact (hc_br_fd IMG rsegs A_SF_FD HIMG HK_FD C_FD t regs (@fp_regs fx) (@fp_csr fx) _
    (hc_arg_wrap regs t H10) Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv (E10 & E11).
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10 | exact E11].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

(* 0x834ec: __subtf3(a, b), a = alo + 2^64 ahi in a0:a1, b = blo + 2^64 bhi in a2:a3; a - b in a0:a1. The callee
   (through __addtf3) writes its 48-byte frame [R - 48, R) and nothing else. *)
Lemma hc_sf_subtf3_call : forall (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R alo ahi blo bhi : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_SF_SUB ->
getr regs 10 = w64 alo -> getr regs 11 = w64 ahi -> getr regs 12 = w64 blo -> getr regs 13 = w64 bhi ->
0 <= alo < 2 ^ 64 -> 0 <= ahi < 2 ^ 64 -> 0 <= blo < 2 ^ 64 -> 0 <= bhi < 2 ^ 64 ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - HC_SUB_STK <= x < R) ->
  aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.lo64 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) ->
 getr regs2 11 = w64 (SF.hi64 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi))) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 RA_SF_SUB) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs A_SF_SUB regs memc mdc) Q.
Proof.
intros Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R alo ahi blo bhi HC Hra H10 H11 H12 H13
  R0 R1 R2 R3 HRV Hfrm K.
apply (hc_sf_call A_SF_SUB HC_SUB_STK RA_SF_SUB (hc_r2 (SF.f128_sub (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r2_ext _)
  ltac:(unfold HC_SUB_STK; sf_T0) HC Hra ltac:(unfold RA_SF_SUB; lia) ltac:(reflexivity) HRV).
- intros HST HMI HTM.
  exact (hc_br_sub IMG rsegs A_SF_SUB HIMG HK_SUB C_SUB regs (@fp_regs fx) (@fp_csr fx) _ alo ahi blo bhi
    (hc_arg regs 10 alo eq_refl H10 R0) (hc_arg regs 11 ahi eq_refl H11 R1)
    (hc_arg regs 12 blo eq_refl H12 R2) (hc_arg regs 13 bhi eq_refl H13 R3) Hfrm HST HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv (E10 & E11).
  exact (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv E10 E11).
Qed.

(* 0x83500: __getf2(a, b), a in a0:a1, b in a2:a3 (the walk: a2 = 0, a3 = the 0.5 high word); the comparison
   result (SoftFloat.f128_ge: 1 / 0 / -1, or -1 when unordered) in a0. *)
Lemma hc_sf_getf2_call : forall (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R alo ahi blo bhi : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_SF_GE ->
getr regs 10 = w64 alo -> getr regs 11 = w64 ahi -> getr regs 12 = w64 blo -> getr regs 13 = w64 bhi ->
0 <= alo < 2 ^ 64 -> 0 <= ahi < 2 ^ 64 -> 0 <= blo < 2 ^ 64 -> 0 <= bhi < 2 ^ 64 ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.f128_ge (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 RA_SF_GE) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs A_SF_GE regs memc mdc) Q.
Proof.
intros Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R alo ahi blo bhi HC Hra H10 H11 H12 H13
  R0 R1 R2 R3 HRV Hfrm K.
apply (hc_sf_call A_SF_GE 0 RA_SF_GE (hc_r1 (SF.f128_ge (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r1_ext _) ltac:(sf_T0) HC Hra
  ltac:(unfold RA_SF_GE; lia) ltac:(reflexivity) HRV).
- intros _ HMI HTM.
  exact (hc_br_ge IMG rsegs A_SF_GE HIMG HK_GE C_GE regs (@fp_regs fx) (@fp_csr fx) _ alo ahi blo bhi
    (hc_arg regs 10 alo eq_refl H10 R0) (hc_arg regs 11 ahi eq_refl H11 R1)
    (hc_arg regs 12 blo eq_refl H12 R2) (hc_arg regs 13 bhi eq_refl H13 R3) Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv E10.
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

(* 0x83518: __lttf2(a, b) (= __letf2's code), a in a0:a1, b in a2:a3 (the walk: a2 = 0, a3 = the -0.5 high word);
   the comparison result (SoftFloat.f128_le: -1 / 0 / 1, or 1 when unordered) in a0. *)
Lemma hc_sf_lttf2_call : forall (Q : world rsegs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R alo ahi blo bhi : Z),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_SF_LT ->
getr regs 10 = w64 alo -> getr regs 11 = w64 ahi -> getr regs 12 = w64 blo -> getr regs 13 = w64 bhi ->
0 <= alo < 2 ^ 64 -> 0 <= ahi < 2 ^ 64 -> 0 <= blo < 2 ^ 64 -> 0 <= bhi < 2 ^ 64 ->
rom_view rsegs W memc -> YK0o.frm_zero (@fp_csr fx) ->
(forall W2 (fx2 : YK11.FPState) ly2 S2 (regs2 : bvmap 5 word) mem2 md2,
 wle W W2 -> hd_fxk [] fx fx2 ->
 hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> frames S2 = frames Sc -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
 same_io mdc md2 -> mo_le MT Sc S2 0 ->
 (forall x, 0 <= x < 2 ^ 64 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H W) memc x) ->
 rom_view rsegs W2 mem2 ->
 getr regs2 10 = w64 (SF.f128_le (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)) ->
 SRr rsegs W2 (mkCfg (@YK11.mkst fx2 regs2 (w64 RA_SF_LT) mem2 (seg_rom rsegs)) md2) Q) ->
SRr rsegs W (cfg_at rsegs A_SF_LT regs memc mdc) Q.
Proof.
intros Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R alo ahi blo bhi HC Hra H10 H11 H12 H13
  R0 R1 R2 R3 HRV Hfrm K.
apply (hc_sf_call A_SF_LT 0 RA_SF_LT (hc_r1 (SF.f128_le (alo + 2 ^ 64 * ahi) (blo + 2 ^ 64 * bhi)))
  Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R (hc_r1_ext _) ltac:(sf_T0) HC Hra
  ltac:(unfold RA_SF_LT; lia) ltac:(reflexivity) HRV).
- intros _ HMI HTM.
  exact (hc_br_le IMG rsegs A_SF_LT HIMG HK_LT C_LT regs (@fp_regs fx) (@fp_csr fx) _ alo ahi blo bhi
    (hc_arg regs 10 alo eq_refl H10 R0) (hc_arg regs 11 ahi eq_refl H11 R1)
    (hc_arg regs 12 blo eq_refl H12 R2) (hc_arg regs 13 bhi eq_refl H13 R3) Hfrm HMI HTM).
- intros W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo Hkeep Hrv E10.
  apply (K W2 fx2 ly2 S2 regs2 mem2 md2 Hle Hfx HC2 Hpres Hfr Hperm Hio Hmo); [| exact Hrv | exact E10].
  intros x Hx. apply Hkeep; [exact Hx | lia].
Qed.

End sf.
End c.
End b.

Print Assumptions hc_br_ext.
Print Assumptions hc_br_fd.
Print Assumptions hc_br_sub.
Print Assumptions hc_br_ge.
Print Assumptions hc_br_le.
Print Assumptions hc_leaf_lift.
Print Assumptions hc_sf_call.
Print Assumptions hc_sf_extendsftf2_call.
Print Assumptions hc_sf_floatditf_call.
Print Assumptions hc_sf_subtf3_call.
Print Assumptions hc_sf_getf2_call.
Print Assumptions hc_sf_lttf2_call.
Print Assumptions hc_rom_view_keep.
