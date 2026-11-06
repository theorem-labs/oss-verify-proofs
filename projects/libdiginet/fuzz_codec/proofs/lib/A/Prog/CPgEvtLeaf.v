(* The link from a leaf's plain-form walk at image A to its A-level contract (lib/A/Prog/CPgEncC.v).

   A plain-form walk (lib/Lib/Exec.v's evt, stepped with lib/Lib/StepF.v over the image's segments) states a run
   from the entry with the register map built by Frame.mkR to the return, the memory and the read-only image
   unchanged. cdc_leaf_evt turns such a run, from the register map of the call (Regs6ss.mkR_of regs) on the
   restricted memory, into the contract's form `SRr segs W (cfg_at segs a regs memc mdc) (cdc_post ...)` for a
   leaf with no stack window (T = 0) that writes no memory (cno_wr): RegisterBridge carries the run to the call's
   own register map, SRr_msteps runs it, and the post holds with the call state, the call's memory and the
   materialized model. The run's end needs a0 = r and every callee-saved register of the call kept; any other
   register is free.
   leaf_a012_evt gives that run from the form the relocated walks state (a0 the result, a1 and a2 written, every
   other register kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YK0i YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require PropExec MState Frame Exec Regs6ss RegisterBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module LPE := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib.Frame.
Module LEx := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib.Exec.
Module LRg := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib.Regs6ss.
Module LRB := OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib.RegisterBridge.

(* lib/Lib/Exec.v's runs are the kit's runs (lib/Reusable/YK0i.v). *)
Lemma cel_msteps : forall segs ms ms', LEx.msteps segs ms ms' -> YK0i.msteps segs ms ms'.
Proof.
intros segs ms ms' H. induction H as [ms|ms ms1 ms2 [Hs Hst] _ IH]; [apply mst_refl|].
eapply mst_step; [exact Hs | exact Hst | exact IH].
Qed.

(* Two register maps that agree on x1..x31 give the same getr. *)
Lemma cel_getr_eqv : forall R R' r, LRg.xregs_eqv R R' -> getr R' r = getr R r.
Proof.
intros R R' r H. unfold getr. rewrite bv_eqb0_is_x0. destruct (is_x0 r) eqn:E; [reflexivity|].
symmetry. apply H. exact E.
Qed.

(* A return address the caller may jump back to (YK0s.ret_ok) is its own `jalr` target. *)
Lemma cel_ret_pc : forall k, YK0s.ret_ok k -> LMS.ret_pc k = k.
Proof.
intros k Hk. unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in Hk.
pose proof (bv_unsigned_in_range 64 k) as Hr. unfold bv_modulus in Hr.
assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
{ rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
assert (Hm : bv_unsigned k mod 2 = 0).
{ rewrite Hz. change ((Z.land (bv_unsigned k) (-2) mod 2 ^ 64) mod 2) with
    ((Z.land (bv_unsigned k) (-2) mod 2 ^ 64) mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 64) (Z.ones 1)) with (Z.ones 1).
  rewrite <- Z.land_assoc. change (Z.land (-2) (Z.ones 1)) with 0. apply Z.land_0_r. }
rewrite <- (LMS.Z_to_bv_bv_unsigned k). apply LMS.ret_pc_even; [exact Hr | exact Hm].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, YG0d.in_img segs a -> 0 <= a < kLowMemEnd.

(* The end of a leaf's run from the call's registers regs on memory m: the return to ra with a0 = r, every
   callee-saved register of regs kept, the floating-point state, the memory and the image unchanged. *)
Definition cel_done (regs : bvmap 5 word) (r : Z) (m : word -> option byte) (ms' : machine_state) : Prop :=
exists R', ms' = LMS.MS R' fp_regs (LMS.ret_pc (reg_get regs 1)) fp_csr None m (LPE.seg_rom segs) /\
reg_get R' 10 = Z_to_bv 64 r /\
(forall n, acallee_saved n -> reg_get R' (Z_to_bv 5 n) = reg_get regs (Z_to_bv 5 n)).

Lemma cel_same_io : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [f [mp lz mt] io fs pr li ti]. repeat split; reflexivity. Qed.

(* The end state of a run on the restricted memory, unrestricted, is the call's config with the run's registers. *)
Lemma cel_unrestrict : forall (H : word -> bool) full (fin : machine_state) pc rom,
ms_fregs fin = fp_regs -> ms_pc_val fin = pc -> ms_svc_pending fin = None -> ms_resv fin = None ->
ms_fcsr fin = fp_csr -> ms_mem fin = mrestrict H full -> ms_rom fin = rom ->
unrestrict H full fin = mkst (ms_regs fin) pc full rom.
Proof.
intros H full fin pc rom HF HP HS HR HC HM HO.
unfold unrestrict, mkst. rewrite HF, HP, HS, HR, HC, HO, HM, munrestrict_mrestrict. reflexivity.
Qed.

(* The link: the plain-form run of a leaf at a, from the call's registers on the call's restricted memory,
   gives the leaf's A-level contract with T = 0, nothing written, and the result a0 = r. *)
Lemma cdc_leaf_evt : forall (a r : Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
cdc_entry segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0 ->
LEx.evt segs (cel_done regs r (mrestrict (w_H W) memc))
  (LMS.MS (LRg.mkR_of regs) fp_regs (Z_to_bv 64 a) fp_csr None (mrestrict (w_H W) memc) (LPE.seg_rom segs)) ->
SRr segs W (cfg_at segs a regs memc mdc)
  (cdc_post segs B MT STK sp0 FP ly S W0 mem0 md0 own k regs 0 cno_wr lyc Sc W memc mdc
    (fun W2 mem2 regs2 => getr regs2 10 = w64 r)).
Proof using Hwx MTL LAWS segs_low.
intros a r STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HE HRUN.
destruct HE as (HJ & Hra & _).
assert (HEQ : LRg.ms_eqv
  (LMS.MS (LRg.mkR_of regs) fp_regs (Z_to_bv 64 a) fp_csr None (mrestrict (w_H W) memc) (LPE.seg_rom segs))
  (restrict (w_H W) (mkst regs (w64 a) memc (seg_rom segs)))).
{ split; [exact (LRg.xregs_eqv_sym _ _ (LRg.mkR_of_eqv regs))|]. repeat split; reflexivity. }
destruct (LRB.evt_register_transport segs _ _ _ HEQ HRUN) as (fin & HMS & can & HD & HCE).
destruct HD as (R' & -> & HR10 & HRs).
unfold cfg_at.
eapply (SRr_msteps segs Hwx W (mkst regs (w64 a) memc (seg_rom segs)) fin mdc _ (cel_msteps _ _ _ HMS)).
intros model' Hsame _.
apply SRr_ret.
destruct HCE as (HX & HF & HP & HS & HRv & HFc & HM & HRo).
assert (Era : LMS.ret_pc (reg_get regs 1) = getr regs 1) by exact (cel_ret_pc (getr regs 1) Hra).
unfold same_but_materialized in Hsame.
red. exists lyc, Sc, (ms_regs fin), memc, model'.
split.
{ try change (ms_mem (mkst regs (w64 a) memc (seg_rom segs))) with memc. f_equal.
  apply cel_unrestrict; [symmetry; exact HF | rewrite <- HP; exact Era | symmetry; exact HS | symmetry; exact HRv
  | symmetry; exact HFc | symmetry; exact HM | rewrite <- HRo; reflexivity]. }
split.
{ unfold EV_CDC. rewrite Z.add_0_r. rewrite Hsame. eapply ajournal_materialize; eassumption. }
split.
{ intros n Hn. rewrite (cel_getr_eqv R' (ms_regs fin) _ HX). unfold getr. rewrite bv_eqb0_is_x0.
  destruct (is_x0 (Z_to_bv 5 n)); [reflexivity|]. exact (HRs n Hn). }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [rewrite Hsame; apply cel_same_io|].
split; [exact (mle_start MT Sc MTL)|].
split.
{ split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros; reflexivity|]. split; [intros x _ _ Hp; exact Hp|]. intros x Hx. exfalso. lia. }
rewrite (cel_getr_eqv R' (ms_regs fin) _ HX). exact HR10.
Qed.

(* The relocated walks' form: from any registers with a0 = a0v, the run to the return with a0 = r, a1 and a2
   written, every other register, the floating-point state, the memory and the image kept. *)
Definition leaf_a012 (a : Z) (a0v : word) (r : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
       (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
LEx.evt segs
  (fun ms' => exists (a1' a2' : word),
     ms' = LMS.MS (LFr.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1' a2' a3
                   a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (LMS.ret_pc ra) fc None m (LPE.seg_rom segs))
  (LMS.MS (LFr.mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 a) fc None m (LPE.seg_rom segs)).

Lemma leaf_a012_evt : forall a r (regs : bvmap 5 word) m,
leaf_a012 a (reg_get regs 10) r ->
LEx.evt segs (cel_done regs r m)
  (LMS.MS (LRg.mkR_of regs) fp_regs (Z_to_bv 64 a) fp_csr None m (LPE.seg_rom segs)).
Proof.
intros a r regs m H.
eapply LEx.evt_mono;
[exact (H (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
  (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13)
  (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
  (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
  (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)
  fp_regs fp_csr m)|].
intros ms' (a1' & a2' & ->). eexists. split; [reflexivity|]. split; [reflexivity|].
intros n Hn. unfold acallee_saved in Hn.
destruct Hn as [->|[->|[->|[->|[->|Hn]]]]]; [reflexivity..|].
assert (Hn' : n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27)
  by lia.
destruct Hn' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

End c.
End b.
