(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtSf1m ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AInv AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocI AMallocA AMallocH ANodeA7 ASecComb ASechs3 ASech8k ASecqib ABudget ASecO1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASech8k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecO1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB.ASecFin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecr69.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecr69 ASecten.

Module ASeciga.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtSf1m ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AInv AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMallocI AMallocA AMallocH ANodeA7 ASecComb ASechs3 ASech8k ASecqib ABudget ASecO1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASech8k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecO1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB.ASecFin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecFinB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecr69.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASecr69.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB.ASecFin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecr69.ASecgji OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecr69.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SplitAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].

Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.
(* [comment removed for export] *)
Ltac thin := repeat match goal with
  | H : boxed _ |- _ => clear H | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : wr_at _ _ _ _ |- _ => clear H | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
  | H : poison_consts _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : NoDup _ |- _ => clear H end.
Ltac stk_fix := lazymatch goal with |- stk _ ?mm ?l ?hi => match goal with H : stk _ mm l ?hi' |- _ => replace hi with hi' by (thin; lia); exact H end end.
Ltac sides1c := first [ eassumption | eqrefl | lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | stk_fix | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | stk_fix | lia | modtac]
                      | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sides
  | |- _ /\ _ => first [eassumption | split; sides]
  | |- _ => sides1 end.
Ltac slia ::= thin; split_all;
  lazymatch goal with
  | |- True => exact I
  | |- ~ (?lo <= ?a < ?hi) =>
      (* [comment removed for export] *)
      repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end;
      first [ assumption
            | multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
                apply (notin_mono a lo hi lo' hi' H); repeat match goal with H' : ~ _ |- _ => clear H' end; lia end
            | repeat match goal with H' : ~ _ |- _ => clear H' end; lia ]
  | |- _ => first [ lia
                  | multimatch goal with H : apart _ _ _ _ |- _ =>
                      (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ]
  end.
Tactic Notation "callx" uconstr(SPEC) "cleaning" tactic(CLEAN) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | CLEAN; post_call_z segs m ]
  end.
Tactic Notation "callx" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | post_call_z segs m ]
  end.
Ltac unfa := unfold ASecComb.LMA, ASecComb.LSTAT, ASecComb.lma_entry, ASecComb.comb_entry, ASecComb.comb_sec_ret,
                    ARtSf1m.LMA, ARtSf1m.LSTAT, ARtSf1m.lma_entry, ARtSf1m.lma_mapret, ARtSf1m.lma_name, ARtSf1m.lma_estest,
                    ARtSf1m.lma_tail, ARtSf1m.lma_espost, ARtSf1m.mapordie_entry,
                    ARtSf1m.mmapordie_entry, ANodeA7.mmapordie_entry, ANodeA7.CF, ANodeA7.PSC, ANodeA7.mmap_ecall_pc, ANodeA7.mmap_after_pc,
                    ANodeA7.mmapordie_resume, AMallocI.TP, AMallocI.alloc_entry, AMallocI.malloc_icpt_entry, AMallocI.malloc_epi_entry,
                    off_th_unwinding, off_th_stats in *.
Ltac kpost MUc WMc :=
  lazymatch type of MUc with munch _ ?mo ?mn =>
    rewrite ?unsigned_lit in MUc by lia;
    transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mo |- _ => clear H end; try clear mo end.

(* [comment removed for export] *)
Ltac cell_fix := lazymatch goal with
  | |- ro_cells _ ?mm ?a ?cs => match goal with H : ro_cells _ mm ?a' cs |- _ => replace a with a' by (thin; lia); exact H
                                               | H : rw_cells _ mm ?a' cs |- _ => replace a with a' by (thin; lia); exact (proj1 H) end
  | |- rw_cells _ ?mm ?a ?cs => match goal with H : rw_cells _ mm ?a' cs |- _ => replace a with a' by (thin; lia); exact H end
  | |- bytes_at _ ?mm ?a ?bs => match goal with H : bytes_at _ mm ?a' bs |- _ => replace a with a' by (thin; lia); exact H end
  | |- u8arr _ ?mm ?a ?bs => match goal with H : u8arr _ mm ?a' bs |- _ => replace a with a' by (thin; lia); exact H end
  end.
Ltac thinc := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : wr_at _ _ _ _ |- _ => clear H | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
  | H : poison_consts _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : NoDup _ |- _ => clear H end.
Ltac sides1 ::= first [ eassumption | eqrefl | stk_fix | cell_fix | thin; lia | unfold boxed in *; thinc; kung; lia | unfold boxed in *; thinc; modtac
                      | rewrite ?unsigned_lit by (thin; lia); first [eassumption | eqrefl | stk_fix | cell_fix | thin; lia | unfold boxed in *; thinc; modtac]
                      | thin; multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ].


(* [comment removed for export] *)

(* [comment removed for export] *)
Section PS4sA8.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr AB q d e ru : Z) (oldp : byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Definition sec_seg4_a8_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s6' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6' (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x376e8) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1)] m m1 /\
    wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -128) /\
    (e <> 0 -> rw_cells rsegs m1 (q + 256 + d + kShadowOffset) [C1 (Z_to_bv 8 e)]).
  #[using="SHP AF2 AF1 PCo RU8 ABR ABQ THR ER NDE NR ST MI oldp Clg"] Lemma sec_seg4_a8_spec : evt rsegs sec_seg4_a8_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37654) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. destruct (Z.eq_dec e 0) as [E0|E0].
    - eapply evt_cut; [eapply (sec_seg4_z_a8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n d); [exact NR| rewrite E0 in NDE; exact NDE] |].
      intros ms' ->. apply evt_done. unfold sec_seg4_a8_post.
      hot_eexists_all. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. intros X; exfalso; exact (X E0).
    - eapply evt_cut; [eapply (sec_seg4_nz_a8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo n stkobj thr AB q d e ru oldp); try eassumption; try lia |].
      { exact (SHP E0). }
      intros ms' PO. unfold sec_seg4_nz_a8_post in PO. (first [ dex17 PO as m1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15; dand6 PO as -> MU WM MI1 ST1 SH1 | dand23 PO as m1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> MU WM MI1 ST1 SH1 | destruct PO as (m1 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & -> & MU & WM & MI1 & ST1 & SH1) ]).
      apply evt_done. unfold sec_seg4_a8_post. hot_eexists_all. split; [reflexivity|].
      split; [replace (Z.min e 1) with 1 by lia; exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. intros _; exact SH1.
  Qed.
End PS4sA8.

(* [comment removed for export] *)
Definition sec_finB_Wc (lo sa thr AB q d e : Z) : list (Z * Z) :=
  [(sa - 1024, sa + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1);
   (thr + 2800, thr + 2824); (thr + 2904, thr + 2912); (AB + 2048, AB + 2048 + 4096);
   (AB + 2032, AB + 2034); (AB, AB + 16)].

Section FinBA8.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (rac spa gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (raA : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr mb q d e ru b1v id : Z).
  Variables (junk0 : list byte) (key : list Z) (v0 v1 v2 vl j0 j1 : word) (b0w : byte) (uj : list byte) (oldp : byte).

  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (sa + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= sa - 1024.
  Hypothesis SPA : sa mod 16 = 0.
  Hypothesis SPH : sa + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis IDR : 0 <= id < 2^32.
  (* [comment removed for export] *)
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  (* [comment removed for export] *)
  Hypothesis MBR : aobj mb (map_size n) /\ mb + map_size n <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SEP_thr : apart mb (map_size n) thr 4096.
  Hypothesis SEP_ctx : apart mb (map_size n) ctx 0x10000.
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (wz 0); C4 (wz n); C8 (wz id)].
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  (* [comment removed for export] *)
  Hypothesis FRA : rw_cells rsegs m (sa + -128)
         (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0).

  Definition sec_finB_a8_postc : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word) (m' : word -> option byte),
    st = MS (mkR rac spa gp tp t0' t1' t2' s0 s1 (wz (AB + 2048)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc rac) fc None m' (seg_rom rsegs)
    /\ munch (sec_finB_Wc lo sa thr AB q d e) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo sa
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0'; C8 v1'; C8 v2']
    /\ rw_cells rsegs m' (thr + 2904) [C8 (wz (bv_unsigned vl + 1))]
    /\ rw_cells rsegs m' (AB + 2032)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (wz 0); C4 (wz n); C8 (wz id)]
    /\ rw_cells rsegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (AB + 2032))]
    /\ rw_cells rsegs m' (AB + 2048) [CB 4096%nat (fill_result canfill uj 4096%nat)]
    /\ rw_cells rsegs m' (q + 256 + d + kShadowOffset) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))].

  #[using="FRA SHP USR ABH HDR SEP_ctx SEP_thr RU8 ABQ MBA MBR STL STS SEP_tc TPL TSDL CTR THR TC HK LS2 LS1 AF52 AF44 AF2 AF1 PCo TSS B1R CF ER NDE NR SPH SPA LO ST MI oldp b0w j1 j0 v2 v1 v0 junk0 ctx tsd Clg"] Lemma sec_finB_a8_c : evt rsegs sec_finB_a8_postc
    (MS (mkR raA (Z_to_bv 64 (sa + -128)) gp tp t0 t1 t2 (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
             (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x37654) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof alloc_ceiling_val as CV. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold kMaxPrimaryUser in NR. unfa.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as RUF.
    assert (MSE : map_size n = 8 * ru + 4096) by (unfold map_size, kPageSize; lia).
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kMaxSize, kStackStoreBlockFrames in *.
    assert (KSO : kShadowOffset = 2147450880) by reflexivity.
    assert (USP : sa = sa) by reflexivity.
    assert (QR : 1024 <= q /\ q + ru <= 17592184995840) by (try (generalize alloc_ceiling_val); clear - AMBR MSE ABQ; lia).   (* [comment removed for export] *)
    assert (RUB : 65536 <= 8 * ru <= 2^32) by (try (generalize alloc_ceiling_val); clear - RU8 RUF NS2 RGE RLT NR; lia).
    assert (DRU : d + 512 <= ru) by (clear - NDE ER RU8 RUF NS2 RGE; lia).   (* [comment removed for export] *)
    assert (RAA : bv_unsigned (Z_to_bv 64 0x3716c) mod 2 = 0) by (rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    assert (SEPthr5 : thr + 4096 <= AB \/ AB + 8 * ru <= thr) by (clear - SEP_thr MSE; destruct SEP_thr; [right|left]; lia).
    assert (SEPctx5 : ctx + 0x10000 <= AB \/ AB + 8 * ru <= ctx) by (clear - SEP_ctx MSE; destruct SEP_ctx; [right|left]; lia).
    assert (SEPtc5 : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx) by (clear - SEP_tc; exact SEP_tc).
    assert (ABR3 : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling) by (split; [replace (AB - 4096) with mb by (clear; lia); replace (4096 + 8 * ru) with (map_size n) by (clear - MSE; lia); exact (proj1 MBR) | try (generalize alloc_ceiling_val); clear - MBR MSE RUF RU8; lia]).   (* [comment removed for export] *)
    assert (TSD5 : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000) by (clear - TSDL; lia).   (* [comment removed for export] *)
    assert (TP5 : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000) by (clear - TPL; lia).   (* [comment removed for export] *)
    assert (TP6 : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000) by (clear - TPL; lia).   (* [comment removed for export] *)
    assert (SPA2 : sa mod 16 = 0) by exact SPA.
    assert (SPR2 : sa + 65536 < 2^64) by (try (generalize alloc_ceiling_val); clear - LO SPH; lia).
    assert (LO2 : alloc_ceiling <= lo /\ lo <= sa - 1024) by (try (generalize alloc_ceiling_val); clear - LO; lia).
    assert (ABA2 : (mb + 4096) mod 4096 = 0) by (try (generalize alloc_ceiling_val); clear - MBA; rewrite Z.add_mod, MBA by lia; reflexivity).
    assert (NR3 : 64513 <= n < 2^31) by (try (generalize alloc_ceiling_val); clear - NR; lia).
    assert (CF1 : 0 <= 1 <= 1) by (clear; lia).
    (* [comment removed for export] *)
    box SPA. box SPH. box RU8. box RUF. box RGE. box RLT. box NS2. box B1R. box IDR.
    box Btsd0. box Btsd1. box Bctx0. box Bctx1. box Bthr. box Bthr1. box Btp. box Bctx. box THRA. box MBA. box RAA.
    box SEPthr5. box SEPctx5. box SEPtc5. box ABR3. box TSD5. box TP5. box TP6. box SPA2. box SPR2. box LO2. box ABA2. box NR3. box CF1.
    Ltac refresh H M WMH H' :=
      pose proof H as H'; unfold boxed in H';
      lazymatch type of M with munch ?W ?mi ?mc =>
      lazymatch type of H' with
      | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs W mi mc A cs) in H'; [ | exact M | cbn [disjoint_from]; simpl_sizes; slia ]
      | bytes_at _ _ ?A ?bs => apply (bytes_at_transport rsegs W mi mc A bs) in H'; [ | exact M | cbn [disjoint_from]; simpl_sizes; slia ]
      | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H'; [ | exact M | exact WMH | cbn [disjoint_from]; simpl_sizes; slia ]
      | u8arr _ _ ?A ?bs => apply (u8arr_transport rsegs W mi mc A bs) in H'; [ | exact M | exact WMH | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
      end end.
    box Cini. box Ckey. box Ctsd. box Cctx. box Cthr2. box Ccan. box Cgotcf. box Cthr. box Cgotsh. box Cshoff. box Cgotmid. box Cgotmide. box Cgothi.
    box Chivars. box Cgotms. box Creal. box Cgotps. box Cps. box AF1. box AF2. box AF44. box AF52. box LS1. box LS2. box HK.
    box STS. box STL. box USR. box HDR. box ABH.
    clear PCo TC.
    pose proof (munch_refl (sec_finB_Wc lo sa thr AB q d e) m) as MU. unfold sec_finB_Wc in MU. unfa.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sa - 1024, sa + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1)] m) as M0_5.
    pose proof (munch_refl [(sa - 1024, sa + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1);
                            (thr + 2800, thr + 2824); (thr + 2904, thr + 2912); (AB + 2048, AB + 2048 + 4096)] m) as M0_6.
    (* [comment removed for export] *)
    refresh AF1 MU WM AF1x. refresh AF2 MU WM AF2x.
    refresh Ccan MU WM Ccan1. refresh Cgotcf MU WM Cgotcf1. refresh Cthr MU WM Cthr1. refresh Cgotsh MU WM Cgotsh1. refresh Cshoff MU WM Cshoff1.
    refresh Cgotmid MU WM Cgotmid1. refresh Cgotmide MU WM Cgotmide1. refresh Cgothi MU WM Cgothi1. refresh Chivars MU WM Chivars1.
    refresh Cgotms MU WM Cgotms1. refresh Creal MU WM Creal1. refresh Cgotps MU WM Cgotps1. refresh Cps MU WM Cps1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (PCo4 : poison_consts mc) by (unfold poison_consts; repeat (split; [assumption|]); assumption) end.
    clear Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1.
    callx (sec_seg4_a8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj thr AB q d e ru oldp) cleaning (clear AF1x AF2x PCo4 SHP).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with H : _ -> rw_cells rsegs mc _ _ |- _ => rename H into SHE4;
      assert (SHX : rw_cells rsegs mc (q + 256 + d + kShadowOffset) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))]);
      [ destruct (Z.eq_dec e 0) as [E0|E0];
        [ rewrite E0; replace (Z.to_nat (Z.min 0 1)) with 0%nat by reflexivity; cbn [repeat]; apply rw_cells_CB0; thin; lia
        | replace (Z.to_nat (Z.min e 1)) with 1%nat by lia; cbn [repeat];
          apply (rwc_rebytes _ _ [C1 (Z_to_bv 8 e)] [CB 1%nat [Z_to_bv 8 e]] ltac:(rsplit; reflexivity) ltac:(reflexivity) (SHE4 E0)) ]
      | clear SHE4 ] end end.
    (* [comment removed for export] *)
    refresh Cini MU WM Cini5. refresh Ckey MU WM Ckey5. refresh Ctsd MU WM Ctsd5. refresh Cctx MU WM Cctx5. refresh Cthr2 MU WM Cthr5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TC5 : thread_cells mc tp tsd ctx thr) by (unfold thread_cells; repeat (split; [assumption|]); first [assumption | apply aobjK_e; assumption | unfold boxed in *; kung; lia]) end.
    clear Cini5 Ckey5 Ctsd5 Cctx5 Cthr5.
    refresh AF1 MU WM AF1y. refresh AF44 MU WM AF44y. refresh AF52 MU WM AF52y.
    refresh Ccan MU WM Ccan1. refresh Cgotcf MU WM Cgotcf1. refresh Cthr MU WM Cthr1. refresh Cgotsh MU WM Cgotsh1. refresh Cshoff MU WM Cshoff1.
    refresh Cgotmid MU WM Cgotmid1. refresh Cgotmide MU WM Cgotmide1. refresh Cgothi MU WM Cgothi1. refresh Chivars MU WM Chivars1.
    refresh Cgotms MU WM Cgotms1. refresh Creal MU WM Creal1. refresh Cgotps MU WM Cgotps1. refresh Cps MU WM Cps1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (PCo5 : poison_consts mc) by (unfold poison_consts; repeat (split; [assumption|]); assumption) end.
    clear Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1.
    refresh STS M0_5 WM STS5. refresh STL M0_5 WM STL5. refresh USR M0_5 WM USR5. clear M0_5.
    callx (sec_seg5_a8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj canfill tsd ctx thr AB ru)
      cleaning (clear TC5 AF1y AF44y AF52y PCo5 STS5 STL5 USR5).
    (* [comment removed for export] *)
    refresh LS1 MU WM LS1x. refresh LS2 MU WM LS2x. refresh HK MU WM HKx. refresh HDR M0_6 WM HDR6i. refresh ABH M0_6 WM ABH6i. clear M0_6.
    callx (sec_seg6_a8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj canfill thr AB ru b1v id)
      cleaning (clear LS1x LS2x HKx HDR6i ABH6i).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      match goal with H : rw_cells rsegs mc (AB + 2032) _ |- _ => rename H into HDR6; box HDR6 end;
      match goal with H : rw_cells rsegs mc AB _ |- _ => rename H into ABH6; box ABH6 end end.
    (* [comment removed for export] *)
    apply evt_done. unfold sec_finB_a8_postc, sec_finB_Wc. unfa. rewrite ?Z_to_bv_bv_unsigned. unfold boxed in *.
    hot_eexists_all.
    split; [reflexivity|].
    split_all; eassumption.
  Qed.
End FinBA8.
End ASeciga.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecFinB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecr69.ASecgji OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecr69 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecten OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASeclv2.ASeciga.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SplitAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hot_apart_f :=
  lazymatch goal with |- ?x + ?n <= ?lo \/ ?hi <= ?x =>
    multimatch goal with
    | H : apart ?a _ ?b _ |- _ => lazymatch x with context [a] => idtac end; lazymatch lo with context [b] => idtac end; eapply (apart_gl _ _ _ _ H); lia
    | H : apart ?a _ ?b _ |- _ => lazymatch x with context [b] => idtac end; lazymatch lo with context [a] => idtac end; eapply (apart_gr _ _ _ _ H); lia
    end
  end.
Ltac hot_base t := lazymatch t with ?x + _ => hot_base x | ?x - _ => hot_base x | _ => t end.
Ltac hot_closed t := lazymatch t with ?x + ?y => hot_closed x; hot_closed y | ?x - ?y => hot_closed x; hot_closed y | ?x * ?y => hot_closed x; hot_closed y | Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac hot_same_base t1 t2 := let b1 := hot_base t1 in let b2 := hot_base t2 in first [ constr_eq b1 b2 | (hot_closed b1; hot_closed b2) ].
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].

Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.
(* [comment removed for export] *)
Ltac thin := repeat match goal with
  | H : boxed _ |- _ => clear H | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : wr_at _ _ _ _ |- _ => clear H | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
  | H : poison_consts _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : NoDup _ |- _ => clear H end.
Ltac stk_fix := lazymatch goal with |- stk _ ?mm ?l ?hi => match goal with H : stk _ mm l ?hi' |- _ => replace hi with hi' by (thin; lia); exact H end end.
Ltac sides1c := first [ eassumption | eqrefl | lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | stk_fix | hot_apart_f | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | stk_fix | lia | modtac]
                      | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sides
  | |- _ /\ _ => first [eassumption | split; sides]
  | |- _ => sides1 end.
Ltac slia ::= thin;
  (* [comment removed for export] *)
  lazymatch goal with
  | |- ~ (_ <= ?a < _) /\ _ => repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end
  | |- _ => idtac
  end;
  split_all;
  lazymatch goal with
  | |- True => exact I
  | |- ~ (?lo <= ?a < ?hi) =>
      (* [comment removed for export] *)
      repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end;
      first [ assumption
            | multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ => hot_same_base lo lo'; apply (notin_mono a lo hi lo' hi' H); repeat match goal with H' : ~ _ |- _ => clear H' end; lia end
            | multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
                apply (notin_mono a lo hi lo' hi' H); repeat match goal with H' : ~ _ |- _ => clear H' end; lia end
            | repeat match goal with H' : ~ _ |- _ => clear H' end; lia ]
  | |- _ => first [ hot_apart_f | lia
                  | multimatch goal with H : apart _ _ _ _ |- _ =>
                      (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ]
  end.
Tactic Notation "callx" uconstr(SPEC) "cleaning" tactic(CLEAN) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | CLEAN; post_call_z segs m ]
  end.
Tactic Notation "callx" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | post_call_z segs m ]
  end.
Ltac unfa := unfold ASecComb.LMA, ASecComb.LSTAT, ASecComb.lma_entry, ASecComb.comb_entry, ASecComb.comb_sec_ret,
                    ARtSf1m.LMA, ARtSf1m.LSTAT, ARtSf1m.lma_entry, ARtSf1m.lma_mapret, ARtSf1m.lma_name, ARtSf1m.lma_estest,
                    ARtSf1m.lma_tail, ARtSf1m.lma_espost, ARtSf1m.mapordie_entry,
                    ARtSf1m.mmapordie_entry, ANodeA7.mmapordie_entry, ANodeA7.CF, ANodeA7.PSC, ANodeA7.mmap_ecall_pc, ANodeA7.mmap_after_pc,
                    ANodeA7.mmapordie_resume, AMallocI.TP, AMallocI.alloc_entry, AMallocI.malloc_icpt_entry, AMallocI.malloc_epi_entry,
                    off_th_unwinding, off_th_stats in *.
Ltac kpost MUc WMc :=
  lazymatch type of MUc with munch _ ?mo ?mn =>
    rewrite ?unsigned_lit in MUc by lia;
    transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mo |- _ => clear H end; try clear mo end.

(* [comment removed for export] *)
Ltac cell_fix := lazymatch goal with
  | |- ro_cells _ ?mm ?a ?cs => match goal with H : ro_cells _ mm ?a' cs |- _ => replace a with a' by (thin; lia); exact H
                                               | H : rw_cells _ mm ?a' cs |- _ => replace a with a' by (thin; lia); exact (proj1 H) end
  | |- rw_cells _ ?mm ?a ?cs => match goal with H : rw_cells _ mm ?a' cs |- _ => replace a with a' by (thin; lia); exact H end
  | |- bytes_at _ ?mm ?a ?bs => match goal with H : bytes_at _ mm ?a' bs |- _ => replace a with a' by (thin; lia); exact H end
  | |- u8arr _ ?mm ?a ?bs => match goal with H : u8arr _ mm ?a' bs |- _ => replace a with a' by (thin; lia); exact H end
  end.
Ltac thinc := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H | H : u8arr _ _ _ _ |- _ => clear H | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : wr_at _ _ _ _ |- _ => clear H | H : _ -> rw_cells _ _ _ _ |- _ => clear H | H : Forall _ _ |- _ => clear H
  | H : poison_consts _ |- _ => clear H | H : thread_cells _ _ _ _ _ |- _ => clear H | H : NoDup _ |- _ => clear H end.
Ltac sides1 ::= first [ eassumption | eqrefl | stk_fix | cell_fix | thin; hot_apart_f | thin; lia | unfold boxed in *; thinc; kung; lia | unfold boxed in *; thinc; modtac
                      | rewrite ?unsigned_lit by (thin; lia); first [eassumption | eqrefl | stk_fix | cell_fix | thin; lia | unfold boxed in *; thinc; modtac]
                      | thin; multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ].

(* [comment removed for export] *)
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TPL : bv_unsigned ?tp = ?V |- _ => tf_closed V; pose proof (I : regn (bv_unsigned tp) 65536 6266880) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac tf_apart B lo ::= multimatch goal with
  | H : apart B _ ?b _ |- _ => lazymatch lo with context [b] => idtac end; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ B _ |- _ => lazymatch lo with context [a] => idtac end; eapply (apart_gr _ _ _ _ H) end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_skip a ::= lazymatch a with context [kShadowOffset] => idtac | context [sh _] => idtac end.
Local Ltac tf_sizes ::= simpl_sizes; rewrite ?repeat_length, ?Z2Nat.id by (thin; lia).
Local Ltac tf_threshold ::= constr:(4%nat).   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
Ltac cell_or_ea := lazymatch goal with
  | |- rw_cells _ ?mm ?a _ => first [ match goal with H : rw_cells _ mm a _ |- _ => exact H end | eassumption ]
  | |- ro_cells _ ?mm ?a _ => first [ match goal with H : ro_cells _ mm a _ |- _ => exact H | H : rw_cells _ mm a _ |- _ => exact (proj1 H) end | eassumption ]
  | |- bytes_at _ ?mm ?a _ => first [ match goal with H : bytes_at _ mm a _ |- _ => exact H end | eassumption ]
  | |- u8arr _ ?mm ?a _ => first [ match goal with H : u8arr _ mm a _ |- _ => exact H end | eassumption ]
  | |- _ => eassumption end.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_finA_Wc (lo sa thr mb AB q d e dc ru pa nch n0 f0 : Z) : list (Z * Z) :=
  [(sa - 1024, sa + -128);
   (LMA + 48, LMA + 65); (LMA + 72, LMA + 616); (LMA + 616, LMA + 617); (mb + 24, mb + 32); (pa + 8 * nch, pa + 8 * nch + 8); (LSTAT + 16, LSTAT + 32);
   (AB + 2032, AB + 2048);
   (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
   (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc)); (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)].

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@ABQ; @ACTR; @ADF0; @ADN0; @AMBR; @APAR; @ATHR; @CE0; @CTR; @DCM; @DF0; @DN0; @DRU; @ER; @KSO; @LO; @MBR; @MSE; @NCH; @NDE; @NR; @PAR; @RUB; @SBR; @SOA; @THR])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hot_slow_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@LO; @SBR; @SOA; @AMBR; @ABQ; @KSO; @MSE; @NR; @NDE; @ER; @NCH; @MBR; @RUB; @PAR; @DCM; @DN0; @DF0; @APAR; @DRU; @ATHR; @CE0; @ADN0; @ADF0; @NE])).
Ltac hot_slow_full := slia.
Ltac hot_slow_all_full := slia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_slow ::= first [ solve [ hot_slow_cut; hot_slow_full ] | hot_slow_full ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_slow_all ::= first [ solve [ hot_slow_cut; hot_slow_all_full ] | hot_slow_all_full ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@AMBR; @LO; @ABQ; @KSO; @SBR; @MSE; @NR; @NDE; @ER; @SOA; @NCH; @DCM; @Ha; @MBR; @RUB; @RU8; @RUF; @NS2; @RGE; @ADN0; @ADF0; @APAR; @H; @ATHR; @DRU; @PAR; @THR; @ACTR; @DN0; @DF0; @OL; @e0; @CE0; @n; @RLT; @TPL; @NE; @MSG; @DTOT; @TSDL; @SPH; @CTR; @DLEN])).
Ltac hot_lia_full := Zify.zify; xlia zchecker.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
Section FinA8c.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (rac spa gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (raT s4T s6T s7T : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr sb mb q d e dc ru pa nch nres lz n0 f0 : Z).
  Variables (junk0 scrL : list byte) (key : list Z) (lk1 lk2 : Z) (cs : byte)
            (na nf ca mx cidx pan sta stm v0 v1 v2 vl h2 w4 d8 j0 j1 : word) (b0w b1w : byte) (bsl : list word)
            (D : list (list Z)) (olds oll olt uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).
  #[warnings="-notation-for-abbreviation"] Local Notation KEY := (key).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (sa + -128 + -48 + -96).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= sa - 1024.
  Hypothesis SPA : sa mod 16 = 0.
  Hypothesis SPH : sa + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis CF : 0 <= canfill <= 1.
  (* [comment removed for export] *)
  Hypothesis SOA : sa <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  (* [comment removed for export] *)
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m LMA [C8 (Z_to_bv 64 4096)].
  Hypothesis LPA8 : ro_cells rsegs m (LMA + 8) [C8 (wz pa)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  (* [comment removed for export] *)
  Hypothesis MBR : aobj mb ms /\ mb + ms <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_sb : apart mb ms sb (2^37).
  Hypothesis SEP_thr : apart mb ms thr 4096.
  Hypothesis SEP_ctx : apart mb ms ctx 0x10000.
  Hypothesis SEP_n0 : apart mb ms n0 kDepotNodesBlock.
  Hypothesis SEP_f0 : apart mb ms f0 kStackStoreBlockBytes.
  Hypothesis SEP_pa : apart mb ms pa (8 * nres).
  Hypothesis SEP_pat : apart pa (8 * nres) thr 4096.
  Hypothesis SEP_pac : apart pa (8 * nres) ctx 0x10000.
  Hypothesis SEP_pan : apart pa (8 * nres) n0 kDepotNodesBlock.
  Hypothesis SEP_paf : apart pa (8 * nres) f0 kStackStoreBlockBytes.
  Hypothesis HSZ : ro_cells rsegs m (mb + 16) [C8 (Z_to_bv 64 (needed_size2 n))].
  Hypothesis CIDX : rw_cells rsegs m (mb + 24) [C8 cidx].
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Hypothesis SHT : rw_cells rsegs m (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt].
  (* [comment removed for export] *)
  Hypothesis NCH : 0 <= nch < nres /\ nres < 2^20.
  Hypothesis PAR : aobj pa (8 * nres) /\ pa + 8 * nres <= alloc_ceiling /\ pa mod 8 = 0.   (* [comment removed for export] *)
  Hypothesis LZ : lz = lma_lz ms.
  Hypothesis LBSL : length bsl = 64%nat.
  Hypothesis LK : 0 <= lk1 < 256 /\ 0 <= lk2 < 2^15.
  Hypothesis LREG : rw_cells rsegs m (LMA + 48) [C8 (wz nres); C8 (wz nch); C1 cs].
  Hypothesis LSTA : rw_cells rsegs m (LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)].
  Hypothesis LMTX : rw_cells rsegs m (LMA + 616) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 lk1); C2 (wz lk2)].
  Hypothesis PAN : rw_cells rsegs m (pa + 8 * nch) [C8 pan].
  Hypothesis GST : rw_cells rsegs m (LSTAT + 16) [C8 sta; C8 stm].
  (* [comment removed for export] *)
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length key) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pasan rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pasan n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pasan rsegs D' n0 f0 m2.
  (* [comment removed for export] *)
  Hypothesis FRA : rw_cells rsegs m (sa + -128)
         (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0).
  Hypothesis FRC : rw_cells rsegs m (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3743c)).
  Hypothesis FRL : rw_cells rsegs m (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).

  (* [comment removed for export] *)
  Definition sec_finA_a8_postc : machine_state -> Prop := fun st =>
    exists (raA t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' : word) (m' md : word -> option byte),
    st = MS (mkR raA (Z_to_bv 64 (sa + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37654) fc None m' (seg_rom rsegs)
    /\ munch (sec_finA_Wc lo sa thr mb AB q d e dc ru pa nch n0 f0) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (sa + -128)
    /\ rw_cells rsegs m' (LMA + 48) [C8 (wz nres); C8 (wz (nch + 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (LMA + 72) [C8 (wz (bv_unsigned na + 1)); C8 nf; C8 ca'; C8 mx';
                                     CB 512 (u64s (upd bsl (Z.to_nat (Z.lxor lz 63)) (wz (bv_unsigned (nth (Z.to_nat (Z.lxor lz 63)) bsl (wz 0)) + 1))))]
    /\ rw_cells rsegs m' (LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 lk1); C2 (wz lk2)]
    /\ rw_cells rsegs m' (mb + 24) [C8 (wz nch)]
    /\ rw_cells rsegs m' (pa + 8 * nch) [C8 (wz mb)]
    /\ rw_cells rsegs m' (LSTAT + 16) [C8 sta'; C8 stm']
    /\ rw_cells rsegs m' (AB + 2032)
         [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (wz 0); C4 (wz n); C8 (wz (snd (depot_putC D KEY)))]
    /\ bytes_at rsegs m' (q + kShadowOffset) (repeat (Z_to_bv 8 250) 256)
    /\ bytes_at rsegs m' (q + 256 + dc + kShadowOffset) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc)))
    /\ bytes_at rsegs m' (q + 256 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))
    /\ wr_at rsegs m' (q + 256 + kShadowOffset) d
    /\ dr AL_pasan rsegs (fst (depot_putC D KEY)) n0 f0 md
    /\ munch (sec_fin_W2 lo sa thr AB q d e dc ru) md m' /\ wmono rsegs md m'.

  #[using="FRL FRC FRA DRF SEP_f0c SEP_n0c SEP_f0t SEP_n0t DF0 DN0 DTOT DLEN DND DR GST PAN LMTX LSTA LREG LBSL LZ PAR NCH SHT OL SHU SHL HDR ABH CIDX HSZ SEP_paf SEP_pan SEP_pac SEP_pat SEP_pa SEP_f0 SEP_n0 SEP_ctx SEP_thr SEP_sb SBR RU8 ABQ MBA MBR SEP_tc TPL TSDL CTR THR CT8 TH0 TC LPA8 PGS SBc PCo DPS PS LTAIL KR KL TRB TRC SOA DC ER NDE NR SPH SPA LO ST MI olt oll olds j1 j0 d8 w4 h2 stm sta pan cidx mx ca cs scrL junk0 sb ctx tsd canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac Clg"] Lemma sec_finA_a8_c : evt rsegs sec_finA_a8_postc
    (MS (mkR raT (wz (sa + -128 + -48 + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA)
             (wz (mb + 4096)) a1 a2 (wz nch) a4 a5 a6 a7
             (wz ms) (wz lz) s4T (wz mb) s6T s7T (wz 7) (wz (mb + 4096)) (wz thr) (wz 1) t3 t4 t5 t6)
        F (wz lma_tail) fc None m (seg_rom rsegs)).
  Proof. try clear CF. try clear TSS. try clear SHP.   (* [comment removed for export] *)
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof alloc_ceiling_val as CV. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold kMaxPrimaryUser in NR. unfa.
    (* [comment removed for export] *)
    pose proof (rz_size_large n ltac:(lia)) as RSL.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as RUF.
    pose proof (map_size_ge n ltac:(lia)) as MSG. pose proof (map_size_le n ltac:(lia)) as MSL.
    assert (MSE : ms = 8 * ru + 4096) by (unfold map_size, kPageSize; lia).
    pose proof (lma_lz_range ms ltac:(lia)) as LZR. rewrite <- LZ in LZR.
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kMaxSize, kStackStoreBlockFrames in *.
    assert (KSO : kShadowOffset = 2147450880) by reflexivity.
    assert (USP : sa = sa) by reflexivity.
    assert (SPC16 : (sa + -128 + -48) mod 16 = 0)
      by (replace (sa + -128 + -48) with (sa + 16 * (-11)) by lia; rewrite Z.add_mod, Z.mul_mod, SPA by lia; reflexivity).
    pose proof (munch_refl (sec_finA_Wc lo sa thr mb AB q d e dc ru pa nch n0 f0) m) as MU. unfold sec_finA_Wc in MU. unfa.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    assert (DTOT' : depot_total D + 1 + Z.of_nat (length KEY) < 2^20) by (try (generalize alloc_ceiling_val); clear - DTOT; lia).
    pose proof (b1_mid_range (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as B1R.
    assert (DCM : dc = d + Z.min e 1) by (try (generalize alloc_ceiling_val); clear - DC ER; rewrite DC; destruct (Z.eqb_spec e 0); lia).
    assert (QR : 1024 <= q /\ q + ru <= 17592184995840) by (try (generalize alloc_ceiling_val); clear - AMBR MSE ABQ; lia).   (* [comment removed for export] *)
    assert (RUB : 65536 <= 8 * ru <= 2^32) by (try (generalize alloc_ceiling_val); clear - RU8 RUF NS2 RGE RLT NR; lia).
    assert (DRU : d + 512 <= ru) by (clear - NDE ER RU8 RUF NS2 RGE; lia).   (* [comment removed for export] *)
    assert (SO : 0 < stkobj /\ stkobj + 2064 <= 2^47) by (try (generalize alloc_ceiling_val); clear - LO SOA; lia).
    assert (RAA : bv_unsigned (Z_to_bv 64 0x3716c) mod 2 = 0) by (rewrite unsigned_lit by lia; reflexivity).
    assert (CSR : bv_unsigned (Z_to_bv 64 comb_sec_ret) mod 2 = 0) by (unfold comb_sec_ret; rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    assert (SEPthr2 : thr + 4096 <= AB \/ AB + needed_size2 n <= thr) by (clear - SEP_thr MSE RUF RU8; destruct SEP_thr; [right|left]; lia).
    assert (SEPctx2 : ctx + 0x10000 <= AB \/ AB + needed_size2 n <= ctx) by (clear - SEP_ctx MSE RUF RU8; destruct SEP_ctx; [right|left]; lia).
    assert (SEPsb3 : AB + 8 * ru <= sb \/ sb + 2^37 <= AB) by (clear - SEP_sb MSE; destruct SEP_sb; [left|right]; lia).
    assert (SEPn03 : n0 + 1048576 <= AB - 4096 \/ AB + 8 * ru <= n0) by (clear - SEP_n0 MSE; destruct SEP_n0; [right|left]; lia).
    assert (SEPf03 : f0 + 8388608 <= AB - 4096 \/ AB + 8 * ru <= f0) by (clear - SEP_f0 MSE; destruct SEP_f0; [right|left]; lia).
    assert (SEPthr5 : thr + 4096 <= AB \/ AB + 8 * ru <= thr) by (clear - SEP_thr MSE; destruct SEP_thr; [right|left]; lia).
    assert (SEPctx5 : ctx + 0x10000 <= AB \/ AB + 8 * ru <= ctx) by (clear - SEP_ctx MSE; destruct SEP_ctx; [right|left]; lia).
    assert (ABR3 : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling) by (split; [replace (AB - 4096) with mb by (clear; lia); replace (4096 + 8 * ru) with ms by (clear - MSE; lia); exact (proj1 MBR) | try (generalize alloc_ceiling_val); clear - MBR MSE RUF RU8; lia]).   (* [comment removed for export] *)
    assert (ABR2 : aobj AB (needed_size2 n) /\ AB + needed_size2 n <= alloc_ceiling) by (split; [apply (aobj_sub _ _ _ _ (proj1 MBR)); clear - MSE RUF RU8 NS2 RGE; lia | try (generalize alloc_ceiling_val); clear - MBR MSE RUF RU8; lia]).   (* [comment removed for export] *)
    assert (TSD5 : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000) by (clear - TSDL; lia).   (* [comment removed for export] *)
    assert (TP5 : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000) by (clear - TPL; lia).   (* [comment removed for export] *)
    assert (TP6 : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000) by (clear - TPL; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (SPA2 : sa mod 16 = 0) by exact SPA.
    assert (SPR2 : sa + 65536 < 2^64) by (try (generalize alloc_ceiling_val); clear - LO SPH; lia).
    assert (LO2 : alloc_ceiling <= lo /\ lo <= sa - 1024) by (try (generalize alloc_ceiling_val); clear - LO; lia).
    assert (SOA2 : sa <= stkobj) by (clear - SOA; lia).
    assert (ABA2 : (mb + 4096) mod 4096 = 0) by (try (generalize alloc_ceiling_val); clear - MBA; rewrite Z.add_mod, MBA by lia; reflexivity).
    assert (NR2 : 64513 <= n < 2^32) by (try (generalize alloc_ceiling_val); clear - NR; lia). assert (NR3 : 64513 <= n < 2^31) by (try (generalize alloc_ceiling_val); clear - NR; lia).
    assert (CF1 : 0 <= 1 <= 1) by (clear; lia).
    (* [comment removed for export] *)
    box SPA. box SPH. box RU8. box RUF. box RGE. box RLT. box NS2. box RSL. box MSG. box MSL.
    box LZR. box LK. box LBSL. box B1R. box KL. box KR. box DTOT. box DTOT'. box DLEN. box DND. box SPC16. box DC.
    box Btsd0. box Btsd1. box Bctx0. box Bctx1. box Bthr. box Bthr1. box Btp. box Bctx. box THRA. box MBA. box SO. box RAA. box CSR. box LZ.
    box SEPthr2. box SEPctx2. box SEPsb3. box SEPn03. box SEPf03. box SEPthr5. box SEPctx5. box ABR3. box ABR2. box TSD5. box TP5. box TP6.
    box SPA2. box SPR2. box LO2. box SOA2. box ABA2. box NR2. box NR3. box CF1.
    (* [comment removed for export] *)
    Ltac refresh H M WMH H' :=
      pose proof H as H'; unfold boxed in H';
      lazymatch type of M with munch ?W ?mi ?mc =>
      lazymatch type of H' with
      | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs W mi mc A cs) in H'; [ | exact M | cbn [disjoint_from]; simpl_sizes; slia ]
      | bytes_at _ _ ?A ?bs => apply (bytes_at_transport rsegs W mi mc A bs) in H'; [ | exact M | cbn [disjoint_from]; simpl_sizes; slia ]
      | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H'; [ | exact M | exact WMH | cbn [disjoint_from]; simpl_sizes; slia ]
      | u8arr _ _ ?A ?bs => apply (u8arr_transport rsegs W mi mc A bs) in H'; [ | exact M | exact WMH | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
      end end.
    box Cini. box Ckey. box Ctsd. box Cctx. box Cthr2. box Ccan. box Cgotcf. box Cthr. box Cgotsh. box Cshoff. box Cgotmid. box Cgotmide. box Cgothi.
    box Chivars. box Cgotms. box Creal. box Cgotps. box Cps. box AF1. box AF2. box AF44. box AF52. box LS1. box LS2. box HK. box SBc. box PGS.
    box TH0. box CT8. box HSZ. box STS. box STL. box USR. box DR.
    clear PCo TC.
    (* [comment removed for export] *)
    pose proof (munch_refl
      [(sa - 1024, sa + -128); (728472 + 48, 728472 + 65); (728472 + 72, 728472 + 616); (728472 + 616, 728472 + 617); (mb + 24, mb + 32); (pa + 8 * nch, pa + 8 * nch + 8); (729096 + 16, 729096 + 32);
       (AB + 2032, AB + 2048)] m) as M0_3.
    (* [comment removed for export] *)
    callx (LTAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (sa + -128 + -48) lo mb ms nch nres lz pa)
      cleaning (unfa; clear FRL LREG LSTA LMTX CIDX PAN GST LPA8).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    callx (comb_sec_post_ok raT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (sa + -128) lo) cleaning (clear FRC).
    (* [comment removed for export] *)
    refresh TH0 MU WM TH01. refresh CT8 MU WM CT81.
    callx (sec_seg2_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj canfill ctx thr AB) cleaning (clear TH01 CT81 HDR).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with H : rw_cells rsegs mc (AB + 2032) _ |- _ => rename H into HDR2 end end.
    (* [comment removed for export] *)
    refresh HSZ MU WM HSZ1. refresh SBc MU WM SBc1. refresh PGS MU WM PGS1.
    refresh Ccan MU WM Ccan1. refresh Cgotcf MU WM Cgotcf1. refresh Cthr MU WM Cthr1. refresh Cgotsh MU WM Cgotsh1. refresh Cshoff MU WM Cshoff1.
    refresh Cgotmid MU WM Cgotmid1. refresh Cgotmide MU WM Cgotmide1. refresh Cgothi MU WM Cgothi1. refresh Chivars MU WM Chivars1.
    refresh Cgotms MU WM Cgotms1. refresh Creal MU WM Creal1. refresh Cgotps MU WM Cgotps1. refresh Cps MU WM Cps1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (PCo3 : poison_consts mc) by (unfold poison_consts; repeat (split; [assumption|]); assumption) end.
    clear Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1.
    lazymatch type of M0_3 with munch ?W3 m ?mc =>
      assert (DR3 : dr AL_pasan rsegs D n0 f0 mc) by
        (eapply (DRF D m mc DR); intros a Ha; apply (M0_3 (Z_to_bv 64 a));
         unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha;
         rewrite unsigned_lit by lia; cbn [outside]; clear - Ha ADF0 ADN0 AMBR APAR DF0 DN0 LO MSE NCH RUB SBR SEP_f0 SEP_n0 SEP_paf SEP_pan; destruct Ha as [Ha|[Ha|Ha]]; rsplit; apply outside_of_disj; slia)   (* [comment removed for export] *) end.
    clear M0_3.
    callx (sec_seg3_a8_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj thr sb AB q d e dc ru n0 f0 _ (b1_mid (bv_unsigned b1w)) _ D KEY olds oll olt dr)
      cleaning (clear HSZ1 SBc1 PGS1 PCo3 DR3 HDR2 SHL SHU SHT).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      match goal with H : dr _ _ _ n0 f0 ?mdx |- _ => rename H into DRd; box DRd;
        match goal with H2 : munch ?Wd mdx mc |- _ =>
          apply (munch_weaken Wd (sec_fin_W2 lo sa thr AB q d e dc ru)) in H2;
          [ rename H2 into MUd; unfold sec_fin_W2 in MUd | unfold sub_fp, sec_fin_W2; cbn [outside]; intros a Ho; slia ] end end;
      match goal with H : rw_cells rsegs mc (AB + 2032) _ |- _ => rename H into HDR3; cbv zeta in HDR3; box HDR3 end;
      match goal with H : bytes_at rsegs mc (q + kShadowOffset) _ |- _ => rename H into SHL3; box SHL3 end;
      match goal with H : bytes_at rsegs mc (q + 256 + dc + kShadowOffset) _ |- _ => rename H into SHT3; box SHT3 end;
      match goal with H : bytes_at rsegs mc (q + 256 + kShadowOffset) _ |- _ => rename H into SHZ3; box SHZ3 end;
      match goal with H : wr_at rsegs mc (q + 256 + kShadowOffset) _ |- _ => rename H into SHW3; box SHW3 end end.
    (* [comment removed for export] *)
    apply evt_done. unfold sec_finA_a8_postc, sec_finA_Wc. unfa. unfold boxed in *.
    hot_eexists_all.
    split; [reflexivity|].
    split_all; eassumption.
  Qed.
End FinA8c.

Section FinA8.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (rac spa gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (raT s4T s6T s7T : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr sb mb q d e dc ru pa nch nres lz n0 f0 : Z).
  Variables (junk0 scrL : list byte) (key : list Z) (lk1 lk2 : Z) (cs : byte)
            (na nf ca mx cidx pan sta stm v0 v1 v2 vl h2 w4 d8 j0 j1 : word) (b0w b1w : byte) (bsl : list word)
            (D : list (list Z)) (olds oll olt uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  #[warnings="-notation-for-abbreviation"] Local Notation sa := (bv_unsigned spa).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).
  #[warnings="-notation-for-abbreviation"] Local Notation KEY := (key).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (sa + -128 + -48 + -96).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= sa - 1024.
  Hypothesis SPA : sa mod 16 = 0.
  Hypothesis SPH : sa + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis CF : 0 <= canfill <= 1.
  (* [comment removed for export] *)
  Hypothesis SOA : sa <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis KL : (1 <= length key <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  (* [comment removed for export] *)
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m LMA [C8 (Z_to_bv 64 4096)].
  Hypothesis LPA8 : ro_cells rsegs m (LMA + 8) [C8 (wz pa)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  (* [comment removed for export] *)
  Hypothesis MBR : aobj mb ms /\ mb + ms <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_sb : apart mb ms sb (2^37).
  Hypothesis SEP_thr : apart mb ms thr 4096.
  Hypothesis SEP_ctx : apart mb ms ctx 0x10000.
  Hypothesis SEP_n0 : apart mb ms n0 kDepotNodesBlock.
  Hypothesis SEP_f0 : apart mb ms f0 kStackStoreBlockBytes.
  Hypothesis SEP_pa : apart mb ms pa (8 * nres).
  Hypothesis SEP_pat : apart pa (8 * nres) thr 4096.
  Hypothesis SEP_pac : apart pa (8 * nres) ctx 0x10000.
  Hypothesis SEP_pan : apart pa (8 * nres) n0 kDepotNodesBlock.
  Hypothesis SEP_paf : apart pa (8 * nres) f0 kStackStoreBlockBytes.
  Hypothesis HSZ : ro_cells rsegs m (mb + 16) [C8 (Z_to_bv 64 (needed_size2 n))].
  Hypothesis CIDX : rw_cells rsegs m (mb + 24) [C8 cidx].
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Hypothesis SHT : rw_cells rsegs m (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt].
  (* [comment removed for export] *)
  Hypothesis NCH : 0 <= nch < nres /\ nres < 2^20.
  Hypothesis PAR : aobj pa (8 * nres) /\ pa + 8 * nres <= alloc_ceiling /\ pa mod 8 = 0.   (* [comment removed for export] *)
  Hypothesis LZ : lz = lma_lz ms.
  Hypothesis LBSL : length bsl = 64%nat.
  Hypothesis LK : 0 <= lk1 < 256 /\ 0 <= lk2 < 2^15.
  Hypothesis LREG : rw_cells rsegs m (LMA + 48) [C8 (wz nres); C8 (wz nch); C1 cs].
  Hypothesis LSTA : rw_cells rsegs m (LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)].
  Hypothesis LMTX : rw_cells rsegs m (LMA + 616) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 lk1); C2 (wz lk2)].
  Hypothesis PAN : rw_cells rsegs m (pa + 8 * nch) [C8 pan].
  Hypothesis GST : rw_cells rsegs m (LSTAT + 16) [C8 sta; C8 stm].
  (* [comment removed for export] *)
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length key) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pasan rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pasan n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pasan rsegs D' n0 f0 m2.
  (* [comment removed for export] *)
  Hypothesis FRA : rw_cells rsegs m (sa + -128)
         (alloc_s1a_frame spa canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 rac junk0).
  Hypothesis FRC : rw_cells rsegs m (sa + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3743c)).
  Hypothesis FRL : rw_cells rsegs m (sa + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz stkobj) (wz 0xb1d58) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).

  Definition sec_fin_a8_postc : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' v0' v1' v2' : word) (m' md : word -> option byte),
    st = MS (mkR rac spa gp tp t0' t1' t2' s0 s1 (wz (AB + 2048)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc rac) fc None m' (seg_rom rsegs)
    /\ munch (sec_fin_W lo sa thr mb AB q d e dc ru pa nch n0 f0) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo sa
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (LMA + 48) [C8 (wz nres); C8 (wz (nch + 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (LMA + 72) [C8 (wz (bv_unsigned na + 1)); C8 nf; C8 ca'; C8 mx';
                                     CB 512 (u64s (upd bsl (Z.to_nat (Z.lxor lz 63)) (wz (bv_unsigned (nth (Z.to_nat (Z.lxor lz 63)) bsl (wz 0)) + 1))))]
    /\ rw_cells rsegs m' (LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 lk1); C2 (wz lk2)]
    /\ rw_cells rsegs m' (mb + 24) [C8 (wz nch)]
    /\ rw_cells rsegs m' (pa + 8 * nch) [C8 (wz mb)]
    /\ rw_cells rsegs m' (LSTAT + 16) [C8 sta'; C8 stm']
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0'; C8 v1'; C8 v2']
    /\ rw_cells rsegs m' (thr + 2904) [C8 (wz (bv_unsigned vl + 1))]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (AB + 2032)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land (b1_mid (bv_unsigned b1w)) 243) 0));
          C2 (wz 0); C4 (wz n); C8 (wz (snd (depot_putC D KEY)))]
    /\ rw_cells rsegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (AB + 2032))]
    /\ rw_cells rsegs m' (AB + 2048) [CB 4096%nat (fill_result canfill uj 4096%nat)]
    /\ bytes_at rsegs m' (q + kShadowOffset) (repeat (Z_to_bv 8 250) 256)
    /\ bytes_at rsegs m' (q + 256 + dc + kShadowOffset) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc)))
    /\ bytes_at rsegs m' (q + 256 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))
    /\ wr_at rsegs m' (q + 256 + kShadowOffset) d
    /\ rw_cells rsegs m' (q + 256 + d + kShadowOffset) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))]
    (* [comment removed for export] *)
    /\ dr AL_pasan rsegs (fst (depot_putC D KEY)) n0 f0 md
    /\ munch (sec_fin_W2 lo sa thr AB q d e dc ru) md m' /\ wmono rsegs md m'.

  #[using="FRL FRC FRA DRF SEP_f0c SEP_n0c SEP_f0t SEP_n0t DF0 DN0 DTOT DLEN DND DR GST PAN LMTX LSTA LREG LBSL LZ PAR NCH SHT SHP OL SHU SHL USR HDR ABH CIDX HSZ SEP_paf SEP_pan SEP_pac SEP_pat SEP_pa SEP_f0 SEP_n0 SEP_ctx SEP_thr SEP_sb SBR RU8 ABQ MBA MBR STL STS SEP_tc TPL TSDL CTR THR CT8 TH0 TC LPA8 PGS SBc HK LS2 LS1 AF52 AF44 AF2 AF1 PCo DPS PS TSS LTAIL KR KL TRB TRC SOA CF DC ER NDE NR SPH SPA LO ST MI oldp olt oll olds b0w j1 j0 d8 w4 h2 v2 v1 v0 stm sta pan cidx mx ca cs scrL junk0 sb ctx tsd stkobj Clg"] Lemma sec_fin_a8_c : evt rsegs sec_fin_a8_postc
    (MS (mkR raT (wz (sa + -128 + -48 + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA)
             (wz (mb + 4096)) a1 a2 (wz nch) a4 a5 a6 a7
             (wz ms) (wz lz) s4T (wz mb) s6T s7T (wz 7) (wz (mb + 4096)) (wz thr) (wz 1) t3 t4 t5 t6)
        F (wz lma_tail) fc None m (seg_rom rsegs)).
  Proof. try clear THRA. try clear LK.   (* [comment removed for export] *) (* [comment removed for export] *) change 4096%nat with (Z.to_nat 4096) in USR. (* [comment removed for export] *) box KL. box LBSL.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof alloc_ceiling_val as CV. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold kMaxPrimaryUser in NR.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as RUF.
    assert (MSE : ms = 8 * ru + 4096) by (unfold map_size, kPageSize; lia).
    assert (KSO : kShadowOffset = 2147450880) by reflexivity.
    assert (DCM : dc = d + Z.min e 1) by (try (generalize alloc_ceiling_val); clear - DC ER; rewrite DC; destruct (Z.eqb_spec e 0); lia).
    assert (QR : 1024 <= q /\ q + ru <= 17592184995840) by (try (generalize alloc_ceiling_val); clear - AMBR MSE ABQ; lia).   (* [comment removed for export] *)
    assert (RUB : 65536 <= 8 * ru <= 2^32) by (try (generalize alloc_ceiling_val); clear - RU8 RUF NS2 RGE RLT NR; lia).
    assert (DRU : d + 512 <= ru) by (clear - NDE ER RU8 RUF NS2 RGE; lia).   (* [comment removed for export] *)
    pose proof (b1_mid_range (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as B1R.
    assert (IDR : 0 <= snd (depot_putC D KEY) < 2^32) by (pose proof (depot_putC_id_range D KEY); lia).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kMaxSize, kStackStoreBlockFrames, kChunksBlockCount in *.
    box RU8. box RUF. box RGE. box RLT. box NS2. box DC. box Btsd0. box Btsd1. box Bctx0. box Bctx1. box Bthr. box Bthr1. box Btp. box Bctx.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply sec_finA_a8_c; try cell_or_ea. }
    intros st PO. unfold sec_finA_a8_postc in PO.
    (first [ dex22 PO as raA t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' mA md; dand19 PO as -> MUA WMA MIA STA LREG' LSTA' LMTX' CIDX' PAN' GST' HDR3 SHL3 SHT3 SHZ3 SHW3 DRd MUd WMd | dand36 PO as raA t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' mA md -> MUA WMA MIA STA LREG' LSTA' LMTX' CIDX' PAN' GST' HDR3 SHL3 dR_PO_t0; dand6 dR_PO_t0 as SHT3 SHZ3 SHW3 DRd MUd WMd | destruct PO as (raA & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ca' & mx' & sta' & stm' & mA & md & -> &
                    MUA & WMA & MIA & STA & LREG' & LSTA' & LMTX' & CIDX' & PAN' & GST' & HDR3 & SHL3 & SHT3 & SHZ3 & SHW3 & DRd & MUd & WMd) ]).
    unfold sec_finA_Wc in MUA. unfa.
    (* [comment removed for export] *)
    Ltac xfer H M WMH := tf_xfer H M WMH.
    tf_open rsegs MUA.
    xfer Cini MUA WMA. xfer Ckey MUA WMA. xfer Ctsd MUA WMA. xfer Cctx MUA WMA. xfer Cthr2 MUA WMA.
    xfer Ccan MUA WMA. xfer Cgotcf MUA WMA. xfer Cthr MUA WMA. xfer Cgotsh MUA WMA. xfer Cshoff MUA WMA. xfer Cgotmid MUA WMA.
    xfer Cgotmide MUA WMA. xfer Cgothi MUA WMA. xfer Chivars MUA WMA. xfer Cgotms MUA WMA. xfer Creal MUA WMA. xfer Cgotps MUA WMA. xfer Cps MUA WMA.
    xfer AF1 MUA WMA. xfer AF2 MUA WMA. xfer AF44 MUA WMA. xfer AF52 MUA WMA. xfer LS1 MUA WMA. xfer LS2 MUA WMA. xfer HK MUA WMA.
    xfer STS MUA WMA. xfer STL MUA WMA. xfer USR MUA WMA. xfer ABH MUA WMA. xfer FRA MUA WMA.
    assert (SHPA : e <> 0 -> rw_cells rsegs mA (q + 256 + d + kShadowOffset) [C1 oldp]).
    { intros NE. pose proof (SHP NE) as SHP'. assert (DCE : dc = d + 1) by (try (generalize alloc_ceiling_val); clear - DC NE; unfold boxed in DC; rewrite DC; destruct (Z.eqb_spec e 0); lia).
      xfer SHP' MUA WMA. exact SHP'. }
    tf_close.
    assert (TCA : thread_cells mA tp tsd ctx thr) by (unfold thread_cells; repeat (split; [assumption|]); first [assumption | apply aobjK_e; assumption | unfold boxed in *; kung; lia]).
    assert (PCA : poison_consts mA) by (unfold poison_consts; repeat (split; [assumption|]); assumption).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (sec_finB_a8_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ raA F fc mA lo n stkobj canfill tsd ctx thr mb q d e ru
                (b1_mid (bv_unsigned b1w)) (snd (depot_putC D KEY))); try cell_or_ea; unfold boxed in *; try lia. }
    intros st' PO'. unfold sec_finB_a8_postc in PO'.
    (first [ dex18 PO' as t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f v0f v1f v2f mF; dand11 PO' as -> MUB WMB MIB STB STS' STL' HDR6 ABH6 USR' SHX | dand29 PO' as t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f v0f v1f v2f mF -> MUB WMB MIB STB STS' STL' HDR6 ABH6 USR' SHX | destruct PO' as (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & v0f & v1f & v2f & mF & -> &
                     MUB & WMB & MIB & STB & STS' & STL' & HDR6 & ABH6 & USR' & SHX) ]).
    unfold sec_finB_Wc in MUB. unfa.
    (* [comment removed for export] *)
    tf_open rsegs MUB.
    xfer LREG' MUB WMB. xfer LSTA' MUB WMB. xfer LMTX' MUB WMB. xfer CIDX' MUB WMB. xfer PAN' MUB WMB. xfer GST' MUB WMB.
    xfer SHL3 MUB WMB. xfer SHT3 MUB WMB. xfer SHZ3 MUB WMB.
    tf_close.
    apply (wr_at_transport rsegs mA mF _ _) in SHW3; [| exact WMB].
    (* [comment removed for export] *)
    apply evt_done. unfold sec_fin_a8_postc, sec_fin_W. unfa. unfold boxed in *.
    hot_eexists_all.
    split; [reflexivity|].
    split.
    { (* [comment removed for export] *)
      apply (munch_trans _ m mA mF).
      - eapply munch_weaken; [| exact MUA]. unfold sub_fp. cbn [outside]. intros x Hx. slia.
      - eapply munch_weaken; [| exact MUB]. unfold sub_fp. cbn [outside]. intros x Hx. slia. }
    split; [exact (wmono_trans rsegs m mA mF WMA WMB)|].
    split_all; try eassumption.
    - (* [comment removed for export] *)
      unfold sec_fin_W2 in MUd |- *. apply (munch_trans _ md mA mF MUd). eapply munch_weaken; [| exact MUB]. unfold sub_fp. cbn [outside]. intros x Hx. slia.
    - exact (wmono_trans rsegs md mA mF WMd WMB).
  Qed.
End FinA8.

