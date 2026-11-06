(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 3942 of its 4075 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R10.v, with its module names, addresses and numbers changed; 426 of its 656 lines of code are new or changed and 3845 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R10F.v, with its module names, addresses and numbers changed; 70 of its 152 lines of code are new or changed and 574 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R9.v r9_st (:74, no call), r9_call (:107, call reac_ctrl_parse) at
     a working branch 3803efccea0 (blob 9c72c72c56136cfec6a903ff9d76c16cdd7055b0);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r9_st_of_F (evtF_evt + rng_all) re-derives the source r9_st statement, and r9_st_same
     compiles that it IS R9.r9_st's statement (`ltac:(let T := type of R9.r9_st in exact T)`); r9_call is
     split at its single call into r9_call_pre_F (stop at reac_ctrl_parse entry 0x83e04, ra = 0x817a4) and
     r9_call_post_F (from the return pc 0x817a4, which is the run's exit, 0 further steps). Bridge inputs
     only to a Theorem Labs lane's cgif-form walk.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R9.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* Store hook: StepF.mem_after_store_opt with the register-byte branch of R9.v's fix_lit_store added
   (the engine's cell_of_bytes does not know le1 of a register; le1 v is [Z_to_bv 8 (bv_unsigned v)] by
   conversion), on evtF goals. *)
Ltac r9f_store :=
  try (lazymatch goal with
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => idtac
       | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
           change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
       end);
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= r9f_store.

(* ---- footprint twin of r9_st: the run of the six metadata stores 0x8177c-0x81790 ---- *)
Lemma r9_st_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    rw_cells rsegs m (bv_unsigned s3 + 296) [CB 5 junk] ->
    mem_inv rsegs m ->
    rng RNG (bv_unsigned s3 + 296) 5 ->
    evtF rsegs RNG
      (fun ms' => exists (s5' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81794) fc None m1 (seg_rom rsegs) /\ s5' = Z_to_bv 64 4 /\
         munch [(bv_unsigned s3 + 296, bv_unsigned s3 + 301)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 296) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8177c) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk HC HMI Rsh.
  pose proof (munch_refl [(bv_unsigned s3 + 296, bv_unsigned s3 + 301)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  do 6 step.
  apply evtF_done. do 2 eexists. do 5 eexists.
  split; [reflexivity|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|].
  split.
  { destruct HC as ((_ & Hb) & _). cbn [cells_bytes cbytes app] in Hb. exact Hb. }
  repeat split; vm_compute; reflexivity.
Qed.

(* Compare lemma: re-derives the source r9_st statement verbatim at RNG_all. *)
Lemma r9_st_of_F :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    rw_cells rsegs m (bv_unsigned s3 + 296) [CB 5 junk] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (s5' : word) (m1 : word -> option byte) (b0 b1 b2 b3 b4 : byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5' s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81794) fc None m1 (seg_rom rsegs) /\ s5' = Z_to_bv 64 4 /\
         munch [(bv_unsigned s3 + 296, bv_unsigned s3 + 301)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         bytes_at rsegs m1 (bv_unsigned s3 + 296) [b0; b1; b2; b3; b4] /\
         bv_signed b0 = 0 /\ bv_signed b1 = 0 /\ bv_signed b2 = 0 /\ bv_signed b3 = 0 /\ bv_signed b4 = 4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8177c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk HC HMI.
  pose proof (bv_unsigned_in_range 64 s3) as R3. change (bv_modulus 64) with (2 ^ 64) in R3.
  pose proof (rw_cells_bound _ _ _ _ HC) as HB. cbn [cells_size csize Nat.add] in HB.
  apply (evtF_evt rsegs RNG_all).
  apply (r9_st_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m junk HC HMI).
  apply rng_all; lia.
Qed.

(* The source statement itself: this type-checks only if r9_st_of_F has R9.r9_st's type. *)
Definition r9_st_same : ltac:(let T := type of R9.r9_st in exact T) := r9_st_of_F.

(* ---- r9_call split at its single call (reac_ctrl_parse @ 0x83e04) ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Module RFP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.

(* 0x81794 mv a0,s4 ; 0x81798 mv a1,s2 ; 0x8179c ld a2,184(s1) ; 0x817a0 jal reac_ctrl_parse: stops AT the
   callee entry (pc = 0x83e04, ra = 0x817a4). The only data access is the 8-byte load of [s1 + 184] = o. *)
Lemma r9_call_pre_F : forall (RNG : footprint)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o : Z),
  0 <= o < 2 ^ 64 ->
  ro_cells rsegs m (bv_unsigned s1 + 184) [C8 (Z_to_bv 64 o)] ->
  rng RNG (bv_unsigned s1 + 184) 8 ->
  evtF rsegs RNG
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x817a4) sp gp tp t0 t1 t2 s0 s1 s4 s2 (Z_to_bv 64 o)
                             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x83e04) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81794) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o Ho RO Rld.
  step. step. step. step.
  apply evtF_done. reflexivity.
Qed.

(* From the return pc 0x817a4 (= the run's exit cut): 0 further steps; the callee post facts the proved run
   used, stated over the post-call state, give the run's exit Q. *)
Lemma r9_call_post_F : forall (RNG : footprint)
    (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (R : bvmap 5 word)
    (spv phi N o FS : Z) (fr50 : list byte),
  getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
  getr R 19 = s3 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 26 = s10 ->
  getr R 10 = Z_to_bv 64 (fst (RP.ctrlparse N fr50)) -> getr R 20 = s4 -> getr R 21 = s5 ->
  getr R 25 = s9 -> getr R 18 = s2 -> getr R 27 = s11 ->
  munch (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
         [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (spv - PC.REAC_CTRL_PARSE_K) spv ->
  asan_cells m' -> shadow_rw m' ->
  rw_cells rsegs m' o [CB 36 (snd (RP.ctrlparse N fr50))] ->
  addressable m' (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K ->
  RFP.fp [1%nat] m' (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
    (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o) ->
  evtF rsegs RNG
    (fun ms' => exists (R0 : bvmap 5 word) (m0 : word -> option byte),
       ms' = MS R0 F (Z_to_bv 64 0x817a4) fc None m0 (seg_rom rsegs) /\
       getr R0 2 = sp /\ getr R0 3 = gp /\ getr R0 4 = tp /\ getr R0 8 = s0 /\ getr R0 9 = s1 /\
       getr R0 19 = s3 /\ getr R0 22 = s6 /\ getr R0 23 = s7 /\ getr R0 24 = s8 /\ getr R0 26 = s10 /\
       getr R0 10 = Z_to_bv 64 (fst (RP.ctrlparse N fr50)) /\ getr R0 20 = s4 /\ getr R0 21 = s5 /\
       getr R0 25 = s9 /\ getr R0 18 = s2 /\ getr R0 27 = s11 /\
       munch (PC.reac_ctrl_parse_fp o spv ++ RFP.fp_w [1%nat] FS ++
              [(shadow_addr (spv - PC.REAC_CTRL_PARSE_K), shadow_addr spv)]) m m0 /\
       wmono rsegs m m0 /\ mem_inv rsegs m0 /\
       stk rsegs m0 (spv - PC.REAC_CTRL_PARSE_K) spv /\
       asan_cells m0 /\ shadow_rw m0 /\
       rw_cells rsegs m0 o [CB 36 (snd (RP.ctrlparse N fr50))] /\
       addressable m0 (spv - PC.REAC_CTRL_PARSE_K) PC.REAC_CTRL_PARSE_K /\
       RFP.fp [1%nat] m0 (bv_unsigned tp) FS (spv - PC.REAC_CTRL_PARSE_K) spv
         (PC.reac_ctrl_parse_W o spv) (PC.reac_ctrl_parse_D phi N o))
    (MS R F (Z_to_bv 64 0x817a4) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' R spv phi N o FS fr50
    G2 G3 G4 G8 G9 G19 G22 G23 G24 G26 G10 G20 G21 G25 G18 G27
    MU WM MI ST AC SW RW AD FP.
  apply evtF_done. exists R, m'.
  split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.
