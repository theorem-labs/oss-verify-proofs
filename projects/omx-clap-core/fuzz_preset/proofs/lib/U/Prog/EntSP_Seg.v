From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import read_members_c.
Import ListNotations.
Open Scope Z_scope.

(* 0x137d8 (check_as_written returned 0) with rc = 0: beqz a0 (taken); took = count2 - count (0x1380c);
   beqz s4 (taken) to 0x1383c. The rc = 0 arm of EntSegA.ent_segC without its memory premises (no call on this arm),
   so a caller can take it on the real memory (ent_kA) instead of the normalized one. *)
Lemma esp_segC0 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2
                    (Z_to_bv 64 (bv_unsigned s5 - bv_unsigned s3)) (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1383c) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x137d8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P.
  step. if_true. step. step. if_true. apply evt_done. reflexivity.
Qed.

(* 0x1383c (rc = 0) on the #102 ubsan pin (twin 27566683952ebd54...): read_members(&doc) (0x13e94, out of line since
   #102; lib/U/Prog/read_members_c.v), then the argument of check_round_trip(&doc) (0x1408c). The doc is at sp + 0.
   The plain walk of lib/Prog/EntSP_Seg.v (cold/h-rw-pre-4-rw102-ent f3c1596d9c63) at the ubsan addresses. *)
Section D.
Hypothesis HRM : read_members_contract.

Lemma esp_segD : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lblk : Z -> Z -> Prop) (S lo : Z)
    (t : jv) (D : list (Z * Z)),
  RM_K <= S < 2 ^ 64 - 56 -> S mod 16 = 0 ->
  (forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - RM_K) RM_K) ->
  stk rsegs m lo S -> lo <= S - RM_K -> mem_inv rsegs m ->
  pj_node rsegs m lblk S t D ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x1384c) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 S)
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1408c) fc None m' (seg_rom rsegs) /\
      munch [(S - RM_K, S)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S /\
      pj_node rsegs m' lblk S t D)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1383c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lblk S lo t D
    HS H16 HL ST LO MI HN.
  assert (US : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; unfold RM_K, RM_F in *; lia).
  do 2 step.
  eapply evt_cut.
  { eapply (HRM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m lblk S t D lo);
      rewrite ?US; [reflexivity | exact HN | exact HL | exact H16 | exact ST | exact LO | | exact MI].
    cbn [disjoint_from]. split; [left; lia | exact I]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & HN').
  subst ms'. rewrite US in MU, ST'.
  rewrite ret_pc_even by first [lia | reflexivity].
  do 2 step.
  apply evt_done. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | exact HN'].
Qed.

End D.
