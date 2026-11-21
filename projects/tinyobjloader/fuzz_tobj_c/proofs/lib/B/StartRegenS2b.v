(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up states of B/ne.v (Start4FailStates), B/ng.v (Start4FailCut), B/nf.v (Start5States), B/n7.v (Start5CallStates) and B/nb.v (Start5bStates): the failed RI mmap's path of the fourth start-up segment and each state of the fifth, computed in the build per CONFIG_RSEQ from the states of B/StartRegenS2.v, by the producer the recorded module applies to its recorded input. *)
(* The failed RI mmap's path of the fourth start-up segment (B/Start4Fail.v) and the fifth start-up
   segment (B/np.v Start5), made per CONFIG_RSEQ, as B/StartRegenS2.v makes the fourth: each state
   for [r = false] ([X_0]) and [r = true] ([X_1]), [X r] selecting between them, by the producer of
   the recorded module that held it (B/ne.v Start4FailStates and B/ng.v Start4FailCut from
   [E_k8x r]; B/nf.v Start5States, B/n7.v Start5CallStates and B/nb.v Start5bStates from
   [E_k12d r]): a run's leaf of the run from the computed state before it, a call's frame, import
   and canonical moves and splits by the recorded rules.  A definition the recorded module writes as
   a term over its states is the same term over the per-flag states.  The recorded modules'
   state-free constants and rules are read from them.  The fail path lives here, not in
   B/StartRegenS2.v, because B/ng.v holds both its rules (Start4FailCut) and the fourth segment's
   proof, which reads B/StartRegenS2.v.  No CFG check of these states has a recorded exit, so none
   is relaunched; each is checked by the run lemmas of B/StartRegen2b.v. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG SymCall SymHeap SymObj SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8 n1 ne ng nf n3 n4 n6 n7 nb StartRegenS2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module Start4FailR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ne.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4FailCut.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2.Start4R.

(* B/ne.v Start4FailStates and B/ng.v Start4FailCut: the failed RI mmap's path, from [E_k8x r]. *)
Definition F0 (r : bool) : axst := fail_state (E_k8x r).
Definition RUN1_0 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL1 [PC_OUT; PC_SPIN] (F0 false) true.
Definition RUN1_1 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL1 [PC_OUT; PC_SPIN] (F0 true) true.
Definition RUN1 (r : bool) : option (list leafA) := if r then RUN1_1 else RUN1_0.
Definition L1a (r : bool) : axst :=
  match RUN1 r with Some (l :: _) => la_state l | _ => F0 r end.
Definition L1b (r : bool) : axst :=
  match RUN1 r with Some (_ :: l :: _) => la_state l | _ => F0 r end.
Definition C2_facts (r : bool) : list sprop :=
  [SPUle (SLit 1) vP; SPUle vP (SLit 12)] ++ ss_facts (ax_S (F0 r)).
Definition C2_objs (r : bool) : list sobj :=
  upd_obj0 (fun o => set_dflt DUnknown (set_cell_val (-592) e_cur (drop_cells (-396) (-376) (drop_cells (-936) (-696) (drop_sym_cells o)))))
    (ss_objs (ax_S (L1a r))).
Definition C2 (r : bool) : axst :=
  axA (mkSS PC_OUT
         (setregs (ss_regs (ax_S (L1a r))) [(11%nat, vP); (13%nat, e_cur); (14%nat, e_nbp); (16%nat, SVar 32%positive); (17%nat, SVar 33%positive)])
         (ss_fregs (ax_S (L1a r))) (ss_fcsr (ax_S (L1a r))) (ss_resv (ax_S (L1a r))) (C2_objs r) (C2_facts r) 34%positive false).
Definition RUN2_0 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL2 [PC_OUT; PC_SPIN] (C2 false) true.
Definition RUN2_1 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL2 [PC_OUT; PC_SPIN] (C2 true) true.
Definition RUN2 (r : bool) : option (list leafA) := if r then RUN2_1 else RUN2_0.
Definition E_spin (r : bool) : axst :=
  match RUN2 r with Some (l :: _) => la_state l | _ => C2 r end.
Definition L2b (r : bool) : axst :=
  match RUN2 r with Some (_ :: l :: _) => la_state l | _ => C2 r end.
Definition L2c (r : bool) : axst :=
  match RUN2 r with Some (_ :: _ :: l :: _) => la_state l | _ => C2 r end.

End Start4FailR.

Module Start5R.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nf.Start5States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Start5CallStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Start5bStates.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS2.Start4R.

(* B/nf.v Start5States, from [E_k12d r]. *)
Definition S_s12ok (r : bool) : axst :=
  axA (add_facts F12 (S_after (ax_S (E_k12d r)) (SVar 36%positive) (ss_objs (ax_S (E_k12d r)) ++ [mmap_obj 36%positive 4096]) 37%positive)).
Definition L12r_0 : axst := Eval vm_compute in
  leaf1 (S_s12ok false) (sym_runA segsA 4000%nat [RIP_ENTRY; ECALL_MMAP] (S_s12ok false) true).
Definition L12r_1 : axst := Eval vm_compute in
  leaf1 (S_s12ok true) (sym_runA segsA 4000%nat [RIP_ENTRY; ECALL_MMAP] (S_s12ok true) true).
Definition L12r (r : bool) : axst := if r then L12r_1 else L12r_0.
Definition SPIN12_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k12d false)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k12d false)) true).
Definition SPIN12_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k12d true)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k12d true)) true).
Definition SPIN12 (r : bool) : axst := if r then SPIN12_1 else SPIN12_0.
Definition L12x_0 : axst := Eval vm_compute in
  mkAX (unknown_obj_at (ax_S (L12r false)) 0) [rX12] (SLit SHB).
Definition L12x_1 : axst := Eval vm_compute in
  mkAX (unknown_obj_at (ax_S (L12r true)) 0) [rX12] (SLit SHB).
Definition L12x (r : bool) : axst := if r then L12x_1 else L12x_0.
Definition C12c_0 : sstate := Eval vm_compute in
  match split_chain (ax_S (L12x false)) splits12 with Some St => St | None => ax_S (L12x false) end.
Definition C12c_1 : sstate := Eval vm_compute in
  match split_chain (ax_S (L12x true)) splits12 with Some St => St | None => ax_S (L12x true) end.
Definition C12c (r : bool) : sstate := if r then C12c_1 else C12c_0.
Definition o12rtc2_0 : sobj := Eval vm_compute in
  nth 13 (ss_objs (C12c false)) (mkObj (SLit 0) (SLit 0) (SLit 0) [] DZero).
Definition o12rtc2_1 : sobj := Eval vm_compute in
  nth 13 (ss_objs (C12c true)) (mkObj (SLit 0) (SLit 0) (SLit 0) [] DZero).
Definition o12rtc2 (r : bool) : sobj := if r then o12rtc2_1 else o12rtc2_0.
Definition o12rtc2a (r : bool) : sobj := add_cell_front (o12rtc2 r) (mkCell (SLit 978352) 8 (SLit 0)).
Definition C12d_0 : sstate := Eval vm_compute in
  replace_obj_at (C12c false) 13 (o12rtc2a false).
Definition C12d_1 : sstate := Eval vm_compute in
  replace_obj_at (C12c true) 13 (o12rtc2a true).
Definition C12d (r : bool) : sstate := if r then C12d_1 else C12d_0.
Definition o12rtc2b (r : bool) : sobj := add_cell_front (o12rtc2a r) (mkCell (SLit 978344) 8 (SLit 0)).
Definition C12e_0 : sstate := Eval vm_compute in
  replace_obj_at (C12d false) 13 (o12rtc2b false).
Definition C12e_1 : sstate := Eval vm_compute in
  replace_obj_at (C12d true) 13 (o12rtc2b true).
Definition C12e (r : bool) : sstate := if r then C12e_1 else C12e_0.
Definition C12 (r : bool) : axst := mkAX (C12e r) [rX12] (SLit SHB).

(* B/n7.v Start5CallStates: the region call at [C12 r], its frame and import, and the canonical
   state after it. *)
Definition myregs12 (r : bool) : list sv := ss_regs (C12e r).
Definition myfregs12 (r : bool) : list sv := ss_fregs (C12e r).
Definition s12 (r : bool) : wsub :=
  [(10%positive, nth 2 (myregs12 r) (SLit 0)); (11%positive, nth 1 (myregs12 r) (SLit 0));
   (14%positive, nth 12 (myregs12 r) (SLit 0)); (15%positive, SAlu ALU_ADD (SVar 1%positive) (SLit (-1048576)));
   (16%positive, SLit (1048576 - 64)); (17%positive, SLit (1048576 - 800)); (18%positive, SLit 304)]
  ++ (map (fun k : nat => (Pos.of_nat (20 + k), nth k (myregs12 r) (SLit 0)))
        (@stdpp.base.filter nat (list nat) _ (fun k : nat => Is_true (negb (existsb (Nat.eqb k) [1; 2; 10; 11; 12]%nat))) _ (seq 0 32))
      ++ map (fun k : nat => (Pos.of_nat (60 + k), nth k (myfregs12 r) (SLit 0))) (seq 0 32)).
Definition R12_0 : list sobj := Eval vm_compute in
  match entails_frA (C12 false) Pre_rip (s12 false) with Some R => R | None => [] end.
Definition R12_1 : list sobj := Eval vm_compute in
  match entails_frA (C12 true) Pre_rip (s12 true) with Some R => R | None => [] end.
Definition R12 (r : bool) : list sobj := if r then R12_1 else R12_0.
Definition IP12_0 : axst := Eval vm_compute in
  import_postA (s12 false) Pre_rip P_ret (C12 false) (R12 false).
Definition IP12_1 : axst := Eval vm_compute in
  import_postA (s12 true) Pre_rip P_ret (C12 true) (R12 true).
Definition IP12 (r : bool) : axst := if r then IP12_1 else IP12_0.
Definition IP12f_0 : axst := Eval vm_compute in
  ax_with_facts (ax_setX (IP12 false) []) (ss_facts (ax_S (IP12 false)) ++ ss_facts (C12e false)).
Definition IP12f_1 : axst := Eval vm_compute in
  ax_with_facts (ax_setX (IP12 true) []) (ss_facts (ax_S (IP12 true)) ++ ss_facts (C12e true)).
Definition IP12f (r : bool) : axst := if r then IP12f_1 else IP12f_0.
Definition E_s13_0 : axst := Eval vm_compute in
  leaf1 (IP12f false) (sym_runA segsA 6000%nat [ECALL_MMAP] (IP12f false) true).
Definition E_s13_1 : axst := Eval vm_compute in
  leaf1 (IP12f true) (sym_runA segsA 6000%nat [ECALL_MMAP] (IP12f true) true).
Definition E_s13 (r : bool) : axst := if r then E_s13_1 else E_s13_0.
Definition T13a_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (E_s13 false)) 0.
Definition T13a_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (E_s13 true)) 0.
Definition T13a (r : bool) : sstate := if r then T13a_1 else T13a_0.
Definition ostk13_0 : sobj := Eval vm_compute in
  last (ss_objs (T13a false)) (mmap_obj 1%positive 0).
Definition ostk13_1 : sobj := Eval vm_compute in
  last (ss_objs (T13a true)) (mmap_obj 1%positive 0).
Definition ostk13 (r : bool) : sobj := if r then ostk13_1 else ostk13_0.
Definition T13b_0 : sstate := Eval vm_compute in
  set_objs (T13a false) (removelast (ss_objs (T13a false))).
Definition T13b_1 : sstate := Eval vm_compute in
  set_objs (T13a true) (removelast (ss_objs (T13a true))).
Definition T13b (r : bool) : sstate := if r then T13b_1 else T13b_0.
Definition T13c_0 : sstate := Eval vm_compute in
  move_obj_last (T13b false) 3.
Definition T13c_1 : sstate := Eval vm_compute in
  move_obj_last (T13b true) 3.
Definition T13c (r : bool) : sstate := if r then T13c_1 else T13c_0.
Definition T13d_0 : sstate := Eval vm_compute in
  mkSS (ss_pc (T13c false)) (ss_regs (T13c false)) (ss_fregs (T13c false)) (ss_fcsr (T13c false)) (ss_resv (T13c false))
    (ss_objs (T13c false) ++ [mstk13]) (ss_facts (T13c false)) (ss_next (T13c false)) (ss_lenient (T13c false)).
Definition T13d_1 : sstate := Eval vm_compute in
  mkSS (ss_pc (T13c true)) (ss_regs (T13c true)) (ss_fregs (T13c true)) (ss_fcsr (T13c true)) (ss_resv (T13c true))
    (ss_objs (T13c true) ++ [mstk13]) (ss_facts (T13c true)) (ss_next (T13c true)) (ss_lenient (T13c true)).
Definition T13d (r : bool) : sstate := if r then T13d_1 else T13d_0.
Definition T13e_0 : sstate := Eval vm_compute in
  match merge_objs_at (T13d false) 23 with Some St => St | None => T13d false end.
Definition T13e_1 : sstate := Eval vm_compute in
  match merge_objs_at (T13d true) 23 with Some St => St | None => T13d true end.
Definition T13e (r : bool) : sstate := if r then T13e_1 else T13e_0.
Definition T13f_0 : sstate := Eval vm_compute in
  move_obj_last (T13e false) 3.
Definition T13f_1 : sstate := Eval vm_compute in
  move_obj_last (T13e true) 3.
Definition T13f (r : bool) : sstate := if r then T13f_1 else T13f_0.
Definition T13g_0 : sstate := Eval vm_compute in
  match merge_objs_at (T13f false) 22 with Some St => St | None => T13f false end.
Definition T13g_1 : sstate := Eval vm_compute in
  match merge_objs_at (T13f true) 22 with Some St => St | None => T13f true end.
Definition T13g (r : bool) : sstate := if r then T13g_1 else T13g_0.
Definition E_s13g (r : bool) : axst := mkAX (T13g r) [] (SLit SHB).

(* B/nb.v Start5bStates: the two mmaps and the munmap after the call. *)
Definition S_s13ok (r : bool) : axst :=
  axA (add_facts F13 (S_after (ax_S (E_s13g r)) (SVar 77%positive) (ss_objs (ax_S (E_s13g r)) ++ [mmap_obj 77%positive 4096]) 78%positive)).
Definition E_s14_0 : axst := Eval vm_compute in
  leaf1 (S_s13ok false) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_s13ok false) true).
Definition E_s14_1 : axst := Eval vm_compute in
  leaf1 (S_s13ok true) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_s13ok true) true).
Definition E_s14 (r : bool) : axst := if r then E_s14_1 else E_s14_0.
Definition SPIN13_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_s13g false)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_s13g false)) true).
Definition SPIN13_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_s13g true)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_s13g true)) true).
Definition SPIN13 (r : bool) : axst := if r then SPIN13_1 else SPIN13_0.
Definition S_s14ok (r : bool) : axst :=
  axA (add_facts F14 (S_after (ax_S (E_s14 r)) (SVar 78%positive) (ss_objs (ax_S (E_s14 r)) ++ [mmap_obj 78%positive 4096]) 79%positive)).
Definition E_s15_0 : axst := Eval vm_compute in
  leaf1 (S_s14ok false) (sym_runA segsA 3000%nat [ECALL_MUNMAP; ECALL_MMAP] (S_s14ok false) true).
Definition E_s15_1 : axst := Eval vm_compute in
  leaf1 (S_s14ok true) (sym_runA segsA 3000%nat [ECALL_MUNMAP; ECALL_MMAP] (S_s14ok true) true).
Definition E_s15 (r : bool) : axst := if r then E_s15_1 else E_s15_0.
Definition SPIN14_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_s14 false)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_s14 false)) true).
Definition SPIN14_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_s14 true)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_s14 true)) true).
Definition SPIN14 (r : bool) : axst := if r then SPIN14_1 else SPIN14_0.
Definition E_s15u_0 : axst := Eval vm_compute in
  drop_last_obj (E_s15 false).
Definition E_s15u_1 : axst := Eval vm_compute in
  drop_last_obj (E_s15 true).
Definition E_s15u (r : bool) : axst := if r then E_s15u_1 else E_s15u_0.
Definition S_s15ok (r : bool) : axst := axA (S_after (ax_S (E_s15u r)) (SLit 0) (ss_objs (ax_S (E_s15u r))) 79%positive).

End Start5R.
