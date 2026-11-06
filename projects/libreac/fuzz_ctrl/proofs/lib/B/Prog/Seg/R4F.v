(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R4.v r4_evt (:102) at a working branch 3803efccea0
     (blob 8243504d5b6eb4d357c8292eb356ac7854066297);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r4_evt calls checked_memset (ASAN_MEMSET 0x52600) at 0x81698, so it is split at that call and has
     no single _of_F. r4_pre_F re-runs R4.v:133 (the four `step`s: 0x8168c li a2,72; 0x81690 ld a0,112(s1);
     0x81694 li a1,0; 0x81698 jal) and stops AT the callee entry; r4_post_F re-runs R4.v:161-168 (the return
     point 0x8169c = the run's end: the ret_pc normalisation and the post of r4_evt), its premises being the
     callee post facts r4_evt uses there (R4.v:151-159). No _F steps through the callee.
   Bridge input only: no top, no W_cutfree_ok, no cut-free twin, no LSCPS join.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R4.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The post of the R4 run (R4.v:114-120), shared by r4_post_F and stated over the run's own start memory m. *)
Definition r4_Q (sp gp tp s0 s1 s2 s3 s7 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (spv fg lo : Z) : machine_state -> Prop :=
  fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
    ms' = MS R F (Z_to_bv 64 0x8169c) fc None m' (seg_rom rsegs) /\
    getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
    getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
    munch [(fg, fg + 72); (spv - 2208, spv)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
    rw_cells rsegs m' fg [CB 72 (repeat (Z_to_bv 8 0) 72)].

(* ---- the pre-call stretch 0x8168c .. 0x81698, stopping at the checked_memset entry 0x52600 ----
   The only access is the 8-byte reload of the fragment record address at [s1 + 112]. *)
Lemma r4_pre_F : forall (RNG : footprint)
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab fg : Z),
    s1 = Z_to_bv 64 Ab -> 0 <= Ab -> Ab + 120 <= 2 ^ 64 ->
    ro_cells rsegs m (Ab + 112) [C8 (Z_to_bv 64 fg)] ->
    rng RNG (Ab + 112) 8 ->
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8169c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                               (Z_to_bv 64 fg) (Z_to_bv 64 0) (Z_to_bv 64 72) a3 a4 a5 a6 a7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x52600) fc None m (seg_rom rsegs))
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8168c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab fg -> HA0 HA64 RO RR.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* ---- the post-call stretch: the return point 0x8169c is the run's end cut ----
   The premises are the facts of the checked_memset post that r4_evt uses at that point (R4.v:151-159). *)
Lemma r4_post_F : forall (RNG : footprint)
  (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (spv fg lo : Z),
    munch [(fg, fg + 72); (spv - 2208, spv)] m m' -> wmono rsegs m m' ->
    mem_inv rsegs m' -> stk rsegs m' lo spv -> asan_cells m' -> shadow_rw m' ->
    rw_cells rsegs m' fg [CB 72 (repeat (Z_to_bv 8 0) 72)] ->
    evtF rsegs RNG (r4_Q sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m spv fg lo)
      (MS (mkR (Z_to_bv 64 0x8169c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (ret_pc (Z_to_bv 64 0x8169c)) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m' spv fg lo MU WM MI ST AC SW RW.
  replace (ret_pc (Z_to_bv 64 0x8169c)) with (Z_to_bv 64 0x8169c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evtF_done. unfold r4_Q. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC|]. split; [exact SW | exact RW].
Qed.
