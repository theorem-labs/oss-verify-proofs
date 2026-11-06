From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02 YK1a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN03 YN2b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW06 YW0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN0e YN23 YN0i YN10.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_realloc_stub : fetch_word src0segs (Z_to_bv 64 src0_A_realloc) = Some (0x0040006f%bv : bv 32).
Proof using. rewrite <- (Z_to_bv_bv_unsigned 32 (0x0040006f%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_realloc_stub : decode_any (0x0040006f%bv : bv 32) = Some (Jal 0 (Z_to_bv 21 4), 4%Z).
Proof using. vm_refl_bv. Qed.
Lemma fetch_realloc_beqz : fetch_word src0segs (Z_to_bv 64 0x19148) = Some (0x04050863%bv : bv 32).
Proof using. rewrite <- (Z_to_bv_bv_unsigned 32 (0x04050863%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_realloc_beqz : decode_any (0x04050863%bv : bv 32) = Some (Branch BC_EQ 10 0 (Z_to_bv 13 0x50), 4%Z).
Proof using. vm_refl_bv. Qed.
Lemma fetch_realloc_mv : fetch_word src0segs (Z_to_bv 64 0x19198) = Some (0x00058513%bv : bv 32).
Proof using. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00058513%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_realloc_mv : decode_any (0x00058513%bv : bv 32) = Some (OpImm ALU_ADD 10 11 (Z_to_bv 12 0), 4%Z).
Proof using. vm_refl_bv. Qed.
Lemma fetch_realloc_j : fetch_word src0segs (Z_to_bv 64 0x1919c) = Some (0x8ccff06f%bv : bv 32).
Proof using. rewrite <- (Z_to_bv_bv_unsigned 32 (0x8ccff06f%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_realloc_j : decode_any (0x8ccff06f%bv : bv 32) = Some (Jal 0 (Z_to_bv 21 (-3892)), 4%Z).
Proof using. vm_refl_bv. Qed.
Lemma step_realloc_stub regs mem :
RiscvSemantics.step src0segs (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) =
MachineOk (mkst regs (Z_to_bv 64 0x19148) mem (seg_rom src0segs)).
Proof using.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_realloc_stub eq_refl decode_realloc_stub). do 2 f_equal.
Qed.
Lemma step_realloc_beqz regs mem : getr regs 10 = Z_to_bv 64 0 ->
RiscvSemantics.step src0segs (mkst regs (Z_to_bv 64 0x19148) mem (seg_rom src0segs)) =
MachineOk (mkst regs (Z_to_bv 64 0x19198) mem (seg_rom src0segs)).
Proof using.
intros H. rewrite (step_beq_tk _ _ _ _ _ _ _ _ _ fetch_realloc_beqz eq_refl decode_realloc_beqz).
- do 2 f_equal.
- rewrite H, getr_zero. vm_compute. reflexivity.
Qed.
Lemma step_realloc_mv regs mem :
RiscvSemantics.step src0segs (mkst regs (Z_to_bv 64 0x19198) mem (seg_rom src0segs)) =
MachineOk (mkst (regupd regs 10 (getr regs 11)) (Z_to_bv 64 0x1919c) mem (seg_rom src0segs)).
Proof using.
rewrite (step_addi _ _ _ _ _ _ _ _ _ fetch_realloc_mv eq_refl decode_realloc_mv).
cbn [bv_eqb]. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite v_addi_0. do 2 f_equal.
Qed.
Lemma step_realloc_j regs mem :
RiscvSemantics.step src0segs (mkst regs (Z_to_bv 64 0x1919c) mem (seg_rom src0segs)) =
MachineOk (mkst regs (Z_to_bv 64 src0_A_libc_malloc_impl) mem (seg_rom src0segs)).
Proof using.
rewrite (step_jal_x0 _ _ _ _ _ _ _ fetch_realloc_j eq_refl decode_realloc_j). do 2 f_equal.
Qed.
Ltac bvne := let E := fresh "E" in intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Lemma callee_not_a0 r : callee_saved r -> Z_to_bv 5 r <> (10%bv : reg).
Proof using.
intros Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; bvne.
Qed.
Lemma preserved_a0 regs v regs' : regs_preserved (regupd regs 10 v) regs' -> regs_preserved regs regs'.
Proof using.
intros H r Hr. rewrite (H r Hr). apply getr_other. exact (callee_not_a0 r Hr).
Qed.
Lemma post_alloc_realloc : forall L A regs v mem md L' A' regs' mem' md',
call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md ->
call_post src0_msyms (MRx src0_msyms) L A (regupd regs 10 v) mem md (fun _ => False) L' A' regs' mem' md' ->
call_post_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md'.
Proof using.
intros L A regs v mem md L' A' regs' mem' md' PRE POST.
destruct PRE as (MR & WF & BD & RA & SPA & SPC & SPH & STK & TP & ERR & AUX).
destruct POST as (MR' & WF' & BD' & LL & PA & RP & VM & FR & UB & SCR).
assert (SP : spZ (regupd regs 10 v) = spZ regs).
{ unfold spZ. f_equal. apply getr_other. bvne. }
unfold scratch in FR, SCR. rewrite SP in FR, SCR.
split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact LL|]. split; [exact PA|].
split; [exact (preserved_a0 regs v regs' RP)|]. split; [exact VM|].
split.
- intros a Ha NO NO' NS NE. apply FR; try assumption.
  unfold scratch_k, REALLOC_STACK in NS. intros [H|H]; apply NS; [left; lia | right; exact H].
- split; [exact UB|].
  intros a Ha. unfold scratch_k, REALLOC_STACK in Ha. unfold REALLOC_STACK in SPC, STK.
  destruct (Z_le_dec (errno_addr src0_msyms) a) as [E1|E1];
  [destruct (Z_lt_le_dec a (errno_addr src0_msyms + 4)) as [E2|E2]|].
  + apply SCR. right. lia.
  + destruct (Z_le_dec (spZ regs - ALLOC_STACK) a) as [E3|E3].
    * apply SCR. left. destruct Ha as [Ha|Ha]; lia.
    * assert (Hs : spZ regs - (ALLOC_STACK + 64) <= a < spZ regs - ALLOC_STACK) by (destruct Ha as [Ha|Ha]; lia).
      apply (proj1 (proj2 (FR a ltac:(left; lia)
        ltac:(intros Ho; pose proof (owned_low src0_msyms L A mem md a (MRx_MRc _ _ _ _ _ MR) Ho); lia)
        ltac:(intros Ho; pose proof (owned_low src0_msyms L' A' mem' md' a (MRx_MRc _ _ _ _ _ MR') Ho); lia)
        ltac:(intros [H|H]; lia) ltac:(intros H; exact H)))).
      apply STK. lia.
  + destruct (Z_le_dec (spZ regs - ALLOC_STACK) a) as [E3|E3].
    * apply SCR. left. destruct Ha as [Ha|Ha]; lia.
    * assert (Hs : spZ regs - (ALLOC_STACK + 64) <= a < spZ regs - ALLOC_STACK) by (destruct Ha as [Ha|Ha]; lia).
      apply (proj1 (proj2 (FR a ltac:(left; lia)
        ltac:(intros Ho; pose proof (owned_low src0_msyms L A mem md a (MRx_MRc _ _ _ _ _ MR) Ho); lia)
        ltac:(intros Ho; pose proof (owned_low src0_msyms L' A' mem' md' a (MRx_MRc _ _ _ _ _ MR') Ho); lia)
        ltac:(intros [H|H]; lia) ltac:(intros H; exact H)))).
      apply STK. lia.
Qed.
Theorem src0_realloc_null_realizes : realloc_null_realizes src0_msyms (MRx src0_msyms).
Proof using.
intros pc L A regs mem md n Hpc PRE H10 H11 Hn.
change (ms_realloc src0_msyms) with (Some src0_A_realloc) in Hpc. injection Hpc as <-.
pose proof PRE as PRE0.
destruct PRE as (MR & WF & BD & RA & SPA & SPC & SPH & STK & TP & ERR & AUX).
destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MR)) as (Hh & Hlz & _).
set (regs4 := regupd regs 10 (getr regs 11)).
assert (G1 : getr regs4 1 = getr regs 1) by (apply getr_other; bvne).
assert (G4 : getr regs4 4 = getr regs 4) by (apply getr_other; bvne).
assert (SP : spZ regs4 = spZ regs) by (unfold spZ; f_equal; apply getr_other; bvne).
assert (H10' : getr regs4 10 = Z_to_bv 64 n) by (unfold regs4; rewrite getr_same; [exact H11 | bvne]).
assert (PRE4 : call_pre src0_msyms (MRx src0_msyms) L A regs4 mem md).
{ unfold call_pre. rewrite G1, G4, SP.
  refine (conj MR (conj WF (conj BD (conj RA (conj SPA (conj _ (conj SPH (conj _ (conj TP (conj ERR AUX)))))))))).
  - unfold REALLOC_STACK in SPC. lia.
  - intros a Ha. apply STK. unfold REALLOC_STACK. lia. }
apply (mreal_SR_pre (ms_segs src0_msyms) (realloc None n A) _ _
  (fun c' => c' = mkCfg (mkst regs4 (Z_to_bv 64 src0_A_libc_malloc_impl) mem (seg_rom src0segs)) md)).
- eapply SR_step; [exact Hh | exact Hlz | reflexivity | apply step_realloc_stub |].
  eapply SR_step; [exact Hh | exact Hlz | reflexivity | apply step_realloc_beqz; exact H10 |].
  eapply SR_step; [exact Hh | exact Hlz | reflexivity | apply step_realloc_mv |].
  eapply SR_step; [exact Hh | exact Hlz | reflexivity | apply step_realloc_j |].
  apply SR_ret. reflexivity.
- intros c' ->. change (realloc None n A) with (malloc n A).
  eapply mreal_mono; [| exact (src0_malloc_impl (src0_malloc_realizes_of_hyps src0_alloc_meta src0_alloc_slot)
    L A regs4 mem md n PRE4 H10' Hn)].
  intros r c'' (L' & regs' & mem' & md' & Ec & POST & Hr).
  exists L', regs', mem', md'. split; [rewrite Ec, G1; reflexivity|].
  split; [exact (post_alloc_realloc L A regs (getr regs 11) mem md L' (snd r) regs' mem' md' PRE0 POST)|].
  destruct (fst r) as [q|].
  + destruct Hr as (Ha & Hnz & Hub & _). auto.
  + exact Hr.
Qed.
End a.
