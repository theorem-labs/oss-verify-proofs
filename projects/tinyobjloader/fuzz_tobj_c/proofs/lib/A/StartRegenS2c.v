(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up states of A/fl.v (Start6States), A/fm.v, A/g0.v and A/g1.v (Start6Run0-7), A/fq.v (Start6JStates), A/fs.v (Start6Aux, Start6bStates): segment 6's states computed in the build per CONFIG_RSEQ from segment 5's computed exit (A/StartRegenS2b.v), each run's leaf by the run from the computed state before it and each other state by the recorded module's own rule. *)
(* Segment 6 of the start-up chain (A/Start6.v), made per CONFIG_RSEQ.  A/fl.v (Start6States),
   A/fm.v, A/g0.v, A/g1.v (Start6Run0-7), A/fq.v (Start6JStates) and A/fs.v (Start6Aux,
   Start6bStates) compute segment 6's states in the build from A/ec.v's recorded exit of segment 5
   ([S_s15ok]).  At LPS 727298f3 that exit depends on the flag (A/StartRegenS2b.v
   [Start5R.S_s15ok r]), so each of those states is made again here from [S_s15ok r], by the same
   definition:
   - a state the recorded module computes ([Eval vm_compute]: a run's leaf, the memset call's
     frame and import, an object move, the join's canonical state) is computed for [r = false]
     ([X_0]) and [r = true] ([X_1]), [X r] selecting between them; a run's leaf is the run from
     the computed state before it;
   - a state the recorded module writes as a term of earlier states (the memset class states
     [R16r], [R16m], [R16c], the class selectors [X_of], [F17n], [canon17], [S_s17ok], the class
     facts [pack16]) is that term over the computed ones.
   The eight memset classes of A/fm.v, A/g0.v and A/g1.v are [X_k r] (k = 0..7), [X_k_0] and
   [X_k_1] their two values.  Every state here is reached by a run or a fixed rule from the start
   state, so no recorded cut or exit state is relaunched (Lib/Relaunch.v is not needed).  The
   definitions that do not depend on the start state (addresses, fact lists, class constants,
   [classes16], [O_ss], [O_lowpg], [o21m], [CF16], [DX16], the memset contract, [leaf1],
   [fail_state], ...) are the recorded modules' own; A/StartRegen2c.v proves the runs, call checks
   and facts per value. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts e2 StartDefsA e8 Start4States fl Str_memcpy fi fq fs StartRegenS2b.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fl.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.StartMemsetZ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fs.Start6bStates.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module Start6R.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS2b.Start5R.

(* A/fl.v Start6States, from [S_s15ok r]. *)
Definition R16pre_0 : axst := Eval vm_compute in
  leaf1 (S_s15ok false) (sym_runA segsA 2000%nat [SITE16] (S_s15ok false) true).
Definition R16pre_1 : axst := Eval vm_compute in
  leaf1 (S_s15ok true) (sym_runA segsA 2000%nat [SITE16] (S_s15ok true) true).
Definition R16pre (r : bool) : axst := if r then R16pre_1 else R16pre_0.
Definition R16b_0 : sstate := Eval vm_compute in
  (let St := ax_S (R16pre false) in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 81%positive (ss_lenient St)).
Definition R16b_1 : sstate := Eval vm_compute in
  (let St := ax_S (R16pre true) in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 81%positive (ss_lenient St)).
Definition R16b (r : bool) : sstate := if r then R16b_1 else R16b_0.
Definition R16r (r : bool) (t : Z) : sstate :=
  mkSS (ss_pc (R16b r)) (list_set (ss_regs (R16b r)) 10 (SAlu ALU_ADD (SVar 79%positive) (SLit (c1 t))))
       (ss_fregs (R16b r)) (ss_fcsr (R16b r)) (ss_resv (R16b r)) (ss_objs (R16b r)) ((F16c t) ++ ss_facts (R16b r)) 81%positive (ss_lenient (R16b r)).
Definition R16m (r : bool) (t : Z) : sstate :=
  replace_obj_at (R16r r t) 21 o21m.
Definition R16c (r : bool) (t : Z) : axst :=
  mkAX (mkSS (ss_pc (R16b r)) (ss_regs (R16r r t)) (ss_fregs (R16b r)) (ss_fcsr (R16b r)) (ss_resv (R16b r))
             ((ss_objs (R16m r t)) ++ [O_lowpg; O_ss t]) (ss_facts (R16r r t)) 81%positive (ss_lenient (R16b r))) [] (SLit SHB).

(* A/fm.v, A/g0.v and A/g1.v Start6Run0-7: the memset call of class [k] at [R16c r k] and the run
   to the mmap after it. *)
(* Class 0. *)
Definition M16_0_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 0)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 0)) true).
Definition M16_0_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 0)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 0)) true).
Definition M16_0 (r : bool) : axst := if r then M16_0_1 else M16_0_0.
Definition s16_0_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_0 false)) (ax_S Pre_mszA).
Definition s16_0_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_0 true)) (ax_S Pre_mszA).
Definition s16_0 (r : bool) : wsub := if r then s16_0_1 else s16_0_0.
Definition R16_0_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_0 false) Pre_mszA (s16_0 false) with Some R => R | None => [] end).
Definition R16_0_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_0 true) Pre_mszA (s16_0 true) with Some R => R | None => [] end).
Definition R16_0 (r : bool) : list sobj := if r then R16_0_1 else R16_0_0.
Definition IP16_0_0 : axst := Eval vm_compute in
  import_postA (s16_0 false) Pre_mszA (liftA P_msz) (M16_0 false) (R16_0 false).
Definition IP16_0_1 : axst := Eval vm_compute in
  import_postA (s16_0 true) Pre_mszA (liftA P_msz) (M16_0 true) (R16_0 true).
Definition IP16_0 (r : bool) : axst := if r then IP16_0_1 else IP16_0_0.
Definition IPm_0_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_0 false)) 0.
Definition IPm_0_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_0 true)) 0.
Definition IPm_0 (r : bool) : sstate := if r then IPm_0_1 else IPm_0_0.
Definition IPr_0_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_0 false) (set_objs (IPm_0 false) (R16_0 false))) (ss_facts (ax_S (M16_0 false))).
Definition IPr_0_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_0 true) (set_objs (IPm_0 true) (R16_0 true))) (ss_facts (ax_S (M16_0 true))).
Definition IPr_0 (r : bool) : axst := if r then IPr_0_1 else IPr_0_0.
Definition F17_0_0 : axst := Eval vm_compute in
  leaf1 (IPr_0 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_0 false) true).
Definition F17_0_1 : axst := Eval vm_compute in
  leaf1 (IPr_0 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_0 true) true).
Definition F17_0 (r : bool) : axst := if r then F17_0_1 else F17_0_0.

(* Class 1. *)
Definition M16_1_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 1)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 1)) true).
Definition M16_1_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 1)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 1)) true).
Definition M16_1 (r : bool) : axst := if r then M16_1_1 else M16_1_0.
Definition s16_1_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_1 false)) (ax_S Pre_mszA).
Definition s16_1_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_1 true)) (ax_S Pre_mszA).
Definition s16_1 (r : bool) : wsub := if r then s16_1_1 else s16_1_0.
Definition R16_1_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_1 false) Pre_mszA (s16_1 false) with Some R => R | None => [] end).
Definition R16_1_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_1 true) Pre_mszA (s16_1 true) with Some R => R | None => [] end).
Definition R16_1 (r : bool) : list sobj := if r then R16_1_1 else R16_1_0.
Definition IP16_1_0 : axst := Eval vm_compute in
  import_postA (s16_1 false) Pre_mszA (liftA P_msz) (M16_1 false) (R16_1 false).
Definition IP16_1_1 : axst := Eval vm_compute in
  import_postA (s16_1 true) Pre_mszA (liftA P_msz) (M16_1 true) (R16_1 true).
Definition IP16_1 (r : bool) : axst := if r then IP16_1_1 else IP16_1_0.
Definition IPm_1_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_1 false)) 0.
Definition IPm_1_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_1 true)) 0.
Definition IPm_1 (r : bool) : sstate := if r then IPm_1_1 else IPm_1_0.
Definition IPr_1_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_1 false) (set_objs (IPm_1 false) (R16_1 false))) (ss_facts (ax_S (M16_1 false))).
Definition IPr_1_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_1 true) (set_objs (IPm_1 true) (R16_1 true))) (ss_facts (ax_S (M16_1 true))).
Definition IPr_1 (r : bool) : axst := if r then IPr_1_1 else IPr_1_0.
Definition F17_1_0 : axst := Eval vm_compute in
  leaf1 (IPr_1 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_1 false) true).
Definition F17_1_1 : axst := Eval vm_compute in
  leaf1 (IPr_1 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_1 true) true).
Definition F17_1 (r : bool) : axst := if r then F17_1_1 else F17_1_0.

(* Class 2. *)
Definition M16_2_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 2)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 2)) true).
Definition M16_2_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 2)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 2)) true).
Definition M16_2 (r : bool) : axst := if r then M16_2_1 else M16_2_0.
Definition s16_2_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_2 false)) (ax_S Pre_mszA).
Definition s16_2_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_2 true)) (ax_S Pre_mszA).
Definition s16_2 (r : bool) : wsub := if r then s16_2_1 else s16_2_0.
Definition R16_2_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_2 false) Pre_mszA (s16_2 false) with Some R => R | None => [] end).
Definition R16_2_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_2 true) Pre_mszA (s16_2 true) with Some R => R | None => [] end).
Definition R16_2 (r : bool) : list sobj := if r then R16_2_1 else R16_2_0.
Definition IP16_2_0 : axst := Eval vm_compute in
  import_postA (s16_2 false) Pre_mszA (liftA P_msz) (M16_2 false) (R16_2 false).
Definition IP16_2_1 : axst := Eval vm_compute in
  import_postA (s16_2 true) Pre_mszA (liftA P_msz) (M16_2 true) (R16_2 true).
Definition IP16_2 (r : bool) : axst := if r then IP16_2_1 else IP16_2_0.
Definition IPm_2_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_2 false)) 0.
Definition IPm_2_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_2 true)) 0.
Definition IPm_2 (r : bool) : sstate := if r then IPm_2_1 else IPm_2_0.
Definition IPr_2_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_2 false) (set_objs (IPm_2 false) (R16_2 false))) (ss_facts (ax_S (M16_2 false))).
Definition IPr_2_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_2 true) (set_objs (IPm_2 true) (R16_2 true))) (ss_facts (ax_S (M16_2 true))).
Definition IPr_2 (r : bool) : axst := if r then IPr_2_1 else IPr_2_0.
Definition F17_2_0 : axst := Eval vm_compute in
  leaf1 (IPr_2 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_2 false) true).
Definition F17_2_1 : axst := Eval vm_compute in
  leaf1 (IPr_2 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_2 true) true).
Definition F17_2 (r : bool) : axst := if r then F17_2_1 else F17_2_0.

(* Class 3. *)
Definition M16_3_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 3)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 3)) true).
Definition M16_3_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 3)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 3)) true).
Definition M16_3 (r : bool) : axst := if r then M16_3_1 else M16_3_0.
Definition s16_3_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_3 false)) (ax_S Pre_mszA).
Definition s16_3_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_3 true)) (ax_S Pre_mszA).
Definition s16_3 (r : bool) : wsub := if r then s16_3_1 else s16_3_0.
Definition R16_3_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_3 false) Pre_mszA (s16_3 false) with Some R => R | None => [] end).
Definition R16_3_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_3 true) Pre_mszA (s16_3 true) with Some R => R | None => [] end).
Definition R16_3 (r : bool) : list sobj := if r then R16_3_1 else R16_3_0.
Definition IP16_3_0 : axst := Eval vm_compute in
  import_postA (s16_3 false) Pre_mszA (liftA P_msz) (M16_3 false) (R16_3 false).
Definition IP16_3_1 : axst := Eval vm_compute in
  import_postA (s16_3 true) Pre_mszA (liftA P_msz) (M16_3 true) (R16_3 true).
Definition IP16_3 (r : bool) : axst := if r then IP16_3_1 else IP16_3_0.
Definition IPm_3_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_3 false)) 0.
Definition IPm_3_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_3 true)) 0.
Definition IPm_3 (r : bool) : sstate := if r then IPm_3_1 else IPm_3_0.
Definition IPr_3_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_3 false) (set_objs (IPm_3 false) (R16_3 false))) (ss_facts (ax_S (M16_3 false))).
Definition IPr_3_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_3 true) (set_objs (IPm_3 true) (R16_3 true))) (ss_facts (ax_S (M16_3 true))).
Definition IPr_3 (r : bool) : axst := if r then IPr_3_1 else IPr_3_0.
Definition F17_3_0 : axst := Eval vm_compute in
  leaf1 (IPr_3 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_3 false) true).
Definition F17_3_1 : axst := Eval vm_compute in
  leaf1 (IPr_3 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_3 true) true).
Definition F17_3 (r : bool) : axst := if r then F17_3_1 else F17_3_0.

(* Class 4. *)
Definition M16_4_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 4)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 4)) true).
Definition M16_4_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 4)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 4)) true).
Definition M16_4 (r : bool) : axst := if r then M16_4_1 else M16_4_0.
Definition s16_4_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_4 false)) (ax_S Pre_mszA).
Definition s16_4_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_4 true)) (ax_S Pre_mszA).
Definition s16_4 (r : bool) : wsub := if r then s16_4_1 else s16_4_0.
Definition R16_4_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_4 false) Pre_mszA (s16_4 false) with Some R => R | None => [] end).
Definition R16_4_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_4 true) Pre_mszA (s16_4 true) with Some R => R | None => [] end).
Definition R16_4 (r : bool) : list sobj := if r then R16_4_1 else R16_4_0.
Definition IP16_4_0 : axst := Eval vm_compute in
  import_postA (s16_4 false) Pre_mszA (liftA P_msz) (M16_4 false) (R16_4 false).
Definition IP16_4_1 : axst := Eval vm_compute in
  import_postA (s16_4 true) Pre_mszA (liftA P_msz) (M16_4 true) (R16_4 true).
Definition IP16_4 (r : bool) : axst := if r then IP16_4_1 else IP16_4_0.
Definition IPm_4_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_4 false)) 0.
Definition IPm_4_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_4 true)) 0.
Definition IPm_4 (r : bool) : sstate := if r then IPm_4_1 else IPm_4_0.
Definition IPr_4_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_4 false) (set_objs (IPm_4 false) (R16_4 false))) (ss_facts (ax_S (M16_4 false))).
Definition IPr_4_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_4 true) (set_objs (IPm_4 true) (R16_4 true))) (ss_facts (ax_S (M16_4 true))).
Definition IPr_4 (r : bool) : axst := if r then IPr_4_1 else IPr_4_0.
Definition F17_4_0 : axst := Eval vm_compute in
  leaf1 (IPr_4 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_4 false) true).
Definition F17_4_1 : axst := Eval vm_compute in
  leaf1 (IPr_4 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_4 true) true).
Definition F17_4 (r : bool) : axst := if r then F17_4_1 else F17_4_0.

(* Class 5. *)
Definition M16_5_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 5)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 5)) true).
Definition M16_5_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 5)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 5)) true).
Definition M16_5 (r : bool) : axst := if r then M16_5_1 else M16_5_0.
Definition s16_5_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_5 false)) (ax_S Pre_mszA).
Definition s16_5_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_5 true)) (ax_S Pre_mszA).
Definition s16_5 (r : bool) : wsub := if r then s16_5_1 else s16_5_0.
Definition R16_5_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_5 false) Pre_mszA (s16_5 false) with Some R => R | None => [] end).
Definition R16_5_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_5 true) Pre_mszA (s16_5 true) with Some R => R | None => [] end).
Definition R16_5 (r : bool) : list sobj := if r then R16_5_1 else R16_5_0.
Definition IP16_5_0 : axst := Eval vm_compute in
  import_postA (s16_5 false) Pre_mszA (liftA P_msz) (M16_5 false) (R16_5 false).
Definition IP16_5_1 : axst := Eval vm_compute in
  import_postA (s16_5 true) Pre_mszA (liftA P_msz) (M16_5 true) (R16_5 true).
Definition IP16_5 (r : bool) : axst := if r then IP16_5_1 else IP16_5_0.
Definition IPm_5_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_5 false)) 0.
Definition IPm_5_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_5 true)) 0.
Definition IPm_5 (r : bool) : sstate := if r then IPm_5_1 else IPm_5_0.
Definition IPr_5_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_5 false) (set_objs (IPm_5 false) (R16_5 false))) (ss_facts (ax_S (M16_5 false))).
Definition IPr_5_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_5 true) (set_objs (IPm_5 true) (R16_5 true))) (ss_facts (ax_S (M16_5 true))).
Definition IPr_5 (r : bool) : axst := if r then IPr_5_1 else IPr_5_0.
Definition F17_5_0 : axst := Eval vm_compute in
  leaf1 (IPr_5 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_5 false) true).
Definition F17_5_1 : axst := Eval vm_compute in
  leaf1 (IPr_5 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_5 true) true).
Definition F17_5 (r : bool) : axst := if r then F17_5_1 else F17_5_0.

(* Class 6. *)
Definition M16_6_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 6)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 6)) true).
Definition M16_6_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 6)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 6)) true).
Definition M16_6 (r : bool) : axst := if r then M16_6_1 else M16_6_0.
Definition s16_6_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_6 false)) (ax_S Pre_mszA).
Definition s16_6_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_6 true)) (ax_S Pre_mszA).
Definition s16_6 (r : bool) : wsub := if r then s16_6_1 else s16_6_0.
Definition R16_6_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_6 false) Pre_mszA (s16_6 false) with Some R => R | None => [] end).
Definition R16_6_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_6 true) Pre_mszA (s16_6 true) with Some R => R | None => [] end).
Definition R16_6 (r : bool) : list sobj := if r then R16_6_1 else R16_6_0.
Definition IP16_6_0 : axst := Eval vm_compute in
  import_postA (s16_6 false) Pre_mszA (liftA P_msz) (M16_6 false) (R16_6 false).
Definition IP16_6_1 : axst := Eval vm_compute in
  import_postA (s16_6 true) Pre_mszA (liftA P_msz) (M16_6 true) (R16_6 true).
Definition IP16_6 (r : bool) : axst := if r then IP16_6_1 else IP16_6_0.
Definition IPm_6_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_6 false)) 0.
Definition IPm_6_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_6 true)) 0.
Definition IPm_6 (r : bool) : sstate := if r then IPm_6_1 else IPm_6_0.
Definition IPr_6_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_6 false) (set_objs (IPm_6 false) (R16_6 false))) (ss_facts (ax_S (M16_6 false))).
Definition IPr_6_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_6 true) (set_objs (IPm_6 true) (R16_6 true))) (ss_facts (ax_S (M16_6 true))).
Definition IPr_6 (r : bool) : axst := if r then IPr_6_1 else IPr_6_0.
Definition F17_6_0 : axst := Eval vm_compute in
  leaf1 (IPr_6 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_6 false) true).
Definition F17_6_1 : axst := Eval vm_compute in
  leaf1 (IPr_6 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_6 true) true).
Definition F17_6 (r : bool) : axst := if r then F17_6_1 else F17_6_0.

(* Class 7. *)
Definition M16_7_0 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c false 7)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c false 7)) true).
Definition M16_7_1 : axst := Eval vm_compute in
  leaf1 (withX0 (R16c true 7)) (sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c true 7)) true).
Definition M16_7 (r : bool) : axst := if r then M16_7_1 else M16_7_0.
Definition s16_7_0 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_7 false)) (ax_S Pre_mszA).
Definition s16_7_1 : wsub := Eval vm_compute in
  infer_sub 1 (ax_S (M16_7 true)) (ax_S Pre_mszA).
Definition s16_7 (r : bool) : wsub := if r then s16_7_1 else s16_7_0.
Definition R16_7_0 : list sobj := Eval vm_compute in
  (match entails_frA (M16_7 false) Pre_mszA (s16_7 false) with Some R => R | None => [] end).
Definition R16_7_1 : list sobj := Eval vm_compute in
  (match entails_frA (M16_7 true) Pre_mszA (s16_7 true) with Some R => R | None => [] end).
Definition R16_7 (r : bool) : list sobj := if r then R16_7_1 else R16_7_0.
Definition IP16_7_0 : axst := Eval vm_compute in
  import_postA (s16_7 false) Pre_mszA (liftA P_msz) (M16_7 false) (R16_7 false).
Definition IP16_7_1 : axst := Eval vm_compute in
  import_postA (s16_7 true) Pre_mszA (liftA P_msz) (M16_7 true) (R16_7 true).
Definition IP16_7 (r : bool) : axst := if r then IP16_7_1 else IP16_7_0.
Definition IPm_7_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_7 false)) 0.
Definition IPm_7_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (IP16_7 true)) 0.
Definition IPm_7 (r : bool) : sstate := if r then IPm_7_1 else IPm_7_0.
Definition IPr_7_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_7 false) (set_objs (IPm_7 false) (R16_7 false))) (ss_facts (ax_S (M16_7 false))).
Definition IPr_7_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setS (IP16_7 true) (set_objs (IPm_7 true) (R16_7 true))) (ss_facts (ax_S (M16_7 true))).
Definition IPr_7 (r : bool) : axst := if r then IPr_7_1 else IPr_7_0.
Definition F17_7_0 : axst := Eval vm_compute in
  leaf1 (IPr_7 false) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_7 false) true).
Definition F17_7_1 : axst := Eval vm_compute in
  leaf1 (IPr_7 true) (sym_runA segsA 4000%nat [ECALL_MMAP] (IPr_7 true) true).
Definition F17_7 (r : bool) : axst := if r then F17_7_1 else F17_7_0.

(* A/fq.v Start6JStates: the class selectors (classes 0..6, else 7, as recorded) and the join. *)
Definition M16_of (r : bool) (t : Z) : axst :=
  match t with
  | Z0 => M16_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => M16_7 r | xO p1 => match p1 with xI p2 => M16_7 r | xO p2 => M16_7 r | xH => M16_5 r end | xH => M16_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => M16_7 r | xO p2 => M16_7 r | xH => M16_6 r end | xO p1 => match p1 with xI p2 => M16_7 r | xO p2 => M16_7 r | xH => M16_4 r end | xH => M16_2 r end
              | xH => M16_1 r
              end
  | Zneg p => M16_7 r
  end.
Definition s16_of (r : bool) (t : Z) : wsub :=
  match t with
  | Z0 => s16_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => s16_7 r | xO p1 => match p1 with xI p2 => s16_7 r | xO p2 => s16_7 r | xH => s16_5 r end | xH => s16_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => s16_7 r | xO p2 => s16_7 r | xH => s16_6 r end | xO p1 => match p1 with xI p2 => s16_7 r | xO p2 => s16_7 r | xH => s16_4 r end | xH => s16_2 r end
              | xH => s16_1 r
              end
  | Zneg p => s16_7 r
  end.
Definition R16_of (r : bool) (t : Z) : list sobj :=
  match t with
  | Z0 => R16_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => R16_7 r | xO p1 => match p1 with xI p2 => R16_7 r | xO p2 => R16_7 r | xH => R16_5 r end | xH => R16_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => R16_7 r | xO p2 => R16_7 r | xH => R16_6 r end | xO p1 => match p1 with xI p2 => R16_7 r | xO p2 => R16_7 r | xH => R16_4 r end | xH => R16_2 r end
              | xH => R16_1 r
              end
  | Zneg p => R16_7 r
  end.
Definition IP16_of (r : bool) (t : Z) : axst :=
  match t with
  | Z0 => IP16_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => IP16_7 r | xO p1 => match p1 with xI p2 => IP16_7 r | xO p2 => IP16_7 r | xH => IP16_5 r end | xH => IP16_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => IP16_7 r | xO p2 => IP16_7 r | xH => IP16_6 r end | xO p1 => match p1 with xI p2 => IP16_7 r | xO p2 => IP16_7 r | xH => IP16_4 r end | xH => IP16_2 r end
              | xH => IP16_1 r
              end
  | Zneg p => IP16_7 r
  end.
Definition IPm_of (r : bool) (t : Z) : sstate :=
  match t with
  | Z0 => IPm_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => IPm_7 r | xO p1 => match p1 with xI p2 => IPm_7 r | xO p2 => IPm_7 r | xH => IPm_5 r end | xH => IPm_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => IPm_7 r | xO p2 => IPm_7 r | xH => IPm_6 r end | xO p1 => match p1 with xI p2 => IPm_7 r | xO p2 => IPm_7 r | xH => IPm_4 r end | xH => IPm_2 r end
              | xH => IPm_1 r
              end
  | Zneg p => IPm_7 r
  end.
Definition IPr_of (r : bool) (t : Z) : axst :=
  match t with
  | Z0 => IPr_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => IPr_7 r | xO p1 => match p1 with xI p2 => IPr_7 r | xO p2 => IPr_7 r | xH => IPr_5 r end | xH => IPr_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => IPr_7 r | xO p2 => IPr_7 r | xH => IPr_6 r end | xO p1 => match p1 with xI p2 => IPr_7 r | xO p2 => IPr_7 r | xH => IPr_4 r end | xH => IPr_2 r end
              | xH => IPr_1 r
              end
  | Zneg p => IPr_7 r
  end.
Definition F17_of (r : bool) (t : Z) : axst :=
  match t with
  | Z0 => F17_0 r
  | Zpos p => match p with
              | xI p0 => match p0 with xI p1 => F17_7 r | xO p1 => match p1 with xI p2 => F17_7 r | xO p2 => F17_7 r | xH => F17_5 r end | xH => F17_3 r end
              | xO p0 => match p0 with xI p1 => match p1 with xI p2 => F17_7 r | xO p2 => F17_7 r | xH => F17_6 r end | xO p1 => match p1 with xI p2 => F17_7 r | xO p2 => F17_7 r | xH => F17_4 r end | xH => F17_2 r end
              | xH => F17_1 r
              end
  | Zneg p => F17_7 r
  end.
Definition F17n (r : bool) (t : Z) : sstate :=
  bump_next (ax_S (F17_of r t)) 81%positive.
Definition canon17 (r : bool) (S : sstate) : axst :=
  let S' : sstate := restate_S (DX16 0) S in
  mkAX (mkSS (ss_pc S') (ss_regs S') (ss_fregs S') (ss_fcsr S') (ss_resv S') (ss_objs S') (CF16 ++ ss_facts (R16b r)) 83%positive (ss_lenient S')) [] (SLit SHB).
Definition E_s17_0 : axst := Eval vm_compute in
  canon17 false (F17n false 0).
Definition E_s17_1 : axst := Eval vm_compute in
  canon17 true (F17n true 0).
Definition E_s17 (r : bool) : axst := if r then E_s17_1 else E_s17_0.

(* A/fs.v Start6Aux: the facts one memset class gives, over the per-flag states. *)
Definition pack16 (r : bool) (t : Z) (M : axst) (s : wsub) (R : list sobj) (IP : axst) (IPm : sstate) (IPr F : axst) : Prop :=
  ((sym_runA segsA 6000%nat [MEMSET] (withX0 (R16c r t)) true) = (Some [mkLeafA M RsCut])) /\ (((entails_frA M Pre_mszA s) = (Some R)) /\ (((call_checkA M Pre_mszA s R (map la_state Posts_mszA)) = true) /\ (((import_postA s Pre_mszA (liftA P_msz) M R) = IP) /\ (((ss_next (ax_S M)) = 81%positive) /\ (((ax_X M) = X0) /\ (((move_obj_last (ax_S IP) 0%nat) = IPm) /\ (((same_but_objs (ax_S IP) IPm) = true) /\ (((ss_objs IPm) = (R ++ [O_ss t])) /\ (((length (ss_objs (ax_S IP))) = 26%nat) /\ (((ax_with_facts (ax_setS (ax_setS IP IPm) (set_objs IPm R)) (ss_facts (ax_S M))) = IPr) /\ (((forallb (sprop_below (ss_next (ax_S IP))) (ss_facts (ax_S M))) = true) /\ (((forallb (sprop_below 81%positive) (ss_facts (ax_S M))) = true) /\ (((sym_runA segsA 4000%nat [ECALL_MMAP] IPr true) = (Some [mkLeafA F RsCut])) /\ (((ss_next (ax_S IP)) = 121%positive) /\ (((ax_X IP) = X0) /\ (((ax_X F) = X0) /\ ((ax_base F) = (SLit SHB)))))))))))))))))).

(* A/fs.v Start6bStates: the mmap after the join and the run to malloc's entry. *)
Definition S_s17ok (r : bool) : axst :=
  axA (add_facts F17 (S_after (ax_S (E_s17 r)) (SVar 83%positive) ((ss_objs (ax_S (E_s17 r))) ++ [mmap_obj 83%positive 11571200]) 84%positive)).
Definition E18_0 : axst := Eval vm_compute in
  leaf1 (S_s17ok false) (sym_runA segsA 8000%nat [MALLOC_ENTRY] (S_s17ok false) true).
Definition E18_1 : axst := Eval vm_compute in
  leaf1 (S_s17ok true) (sym_runA segsA 8000%nat [MALLOC_ENTRY] (S_s17ok true) true).
Definition E18 (r : bool) : axst := if r then E18_1 else E18_0.
Definition SPIN17_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_s17 false)) (sym_runA segsA 300%nat [SPIN_MMAPORDIE] (fail_state (E_s17 false)) true).
Definition SPIN17_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_s17 true)) (sym_runA segsA 300%nat [SPIN_MMAPORDIE] (fail_state (E_s17 true)) true).
Definition SPIN17 (r : bool) : axst := if r then SPIN17_1 else SPIN17_0.

End Start6R.
