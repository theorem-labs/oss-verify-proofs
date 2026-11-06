(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocI ANodeA7 ASecComb ASechs3 ASecqib ABudget.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
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
Ltac sides1c := first [ eassumption | eqrefl | lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | lia | modtac] ].
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

(* [comment removed for export] *)
Ltac unfa := unfold ASecComb.LMA, ASecComb.LSTAT, ASecComb.lma_entry, ASecComb.comb_entry, ASecComb.comb_sec_ret,
                    ARtSf1m.LMA, ARtSf1m.LSTAT, ARtSf1m.lma_entry, ARtSf1m.lma_mapret, ARtSf1m.lma_name, ARtSf1m.lma_estest,
                    ARtSf1m.mmapordie_entry, ANodeA7.mmapordie_entry, ANodeA7.CF, ANodeA7.PSC, ANodeA7.mmap_ecall_pc, ANodeA7.mmap_after_pc,
                    ANodeA7.mmapordie_resume, AMallocI.TP, AMallocI.alloc_entry, AMallocI.malloc_icpt_entry, off_th_unwinding in *.

(* [comment removed for export] *)
Definition lma_consts (m : word -> option byte) (pn : Z) : Prop :=
     ro_cells rsegs m LMA [C8 (wz 4096)]                                   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b58 [C8 (wz pn)] /\ ro_cells rsegs m pn [C8 (wz lma_name)] /\ 0x10000 <= pn /\ pn + 8 <= 0x60a000   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b60 [C8 (wz CF)] /\ ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ ro_cells rsegs m (CF + 144) [C8 (wz 0)].                             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dep_w8 (top bot fp : Z) : Z := if unwind_depth2 top bot fp then 2 else 1.
Definition dep_b16 (top bot fp : Z) (ra : word) (jb1 : list byte) : list byte := if unwind_depth2 top bot fp then le8 ra else jb1.
(* [comment removed for export] *)

Section O1.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n tsd ctx thr top bot pn : Z).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 3168.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58af4.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  (* [comment removed for export] *)
  Hypothesis UNW : unwind_stmt.
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis LPRE : lma_pre_stmt.
  (* [comment removed for export] *)
  Hypothesis INI : ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x136e22 [C1 (Z_to_bv 8 0)].
  Hypothesis RZm : ro_cells rsegs m 0xb2380 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis MUM : ro_cells rsegs m 0xb2378 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis PCo : poison_consts m.
  Hypothesis CMCS : ro_cells rsegs m 0xb58bc [C4 (Z_to_bv 64 30)].                 (* [comment removed for export] *)
  Hypothesis CFU : ro_cells rsegs m (0x1466e8 + 34) [C1 (Z_to_bv 8 1)].             (* [comment removed for export] *)
  Hypothesis LC : lma_consts m pn.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).

  (* [comment removed for export] *)
  Definition sec_o1_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (pad jb1 jrest junk0 scrL scrM : list byte) (m1 : word -> option byte),
    st = MSsvc (mkR (wz mmapordie_resume) (wz (fp + -2144 + -128 + -48 + -96 + -48)) gp tp t0' t1' t2' (wz lma_name) (wz ms)
                    (wz 0) (wz ms) (wz 3) (wz 34) (wz (-1)) (wz 0) a6' (wz 222)
                    (wz PSC) (wz (needed_size2 n)) (wz (rz_size n)) (wz 8) (wz 0xb1558) (wz (fp + -2128)) (wz 7) (wz 7) (wz thr) (wz 1)
                    t3' t4' t5' t6')
               F (wz mmap_ecall_pc) (wz 222) fc None m1 (seg_rom rsegs)
    /\ munch [(lo, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m m1
    /\ wmono rsegs m m1 /\ mem_inv rsegs m1
    /\ stk rsegs m1 lo (fp + -2144 + -128 + -48 + -96 + -48)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (fp + -2128) [C8 (wz (fp + -2128 + 16))]
    /\ rw_cells rsegs m1 (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))]
    /\ rw_cells rsegs m1 (fp + -2128 + 16) [C8 (wz 0x58af4); CB 8 (dep_b16 top bot fp ra jb1)]
    /\ rw_cells rsegs m1 (fp + -2128 + 12) [C4 (wz 0)]
    /\ rw_cells rsegs m1 (fp + -2128 + 32) [CB 2024 jrest]
    /\ rw_cells rsegs m1 (fp + -2128 + 2056) [C8 (wz fp)]
    /\ rw_cells rsegs m1 (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells rsegs m1 (fp + -2144) [C8 sp; C8 (wz 0x58b60)]
    /\ rw_cells rsegs m1 (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m1 (thr + 8) [C8 (wz top); C8 (wz bot)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (fp + -2144 + -128)
         (alloc_s1a_frame (wz (fp + -2144)) 1 s11 s10 s9 s8 s7 s6 (wz (fp + -81)) (wz (fp + -2128)) (wz 1) (wz 0x58af4) (wz n) sp (wz 0x3704c) junk0)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (fp + -2144 + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3731c))
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (fp + -2144 + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz (fp + -2128)) (wz 0xb1558) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret))
    (* [comment removed for export] *)
    /\ rw_cells rsegs m1 (fp + -2144 + -128 + -48 + -96 + -48) [CB 12 scrM; C4 (wz 34); C8 (wz ms); C8 (wz LMA); C8 (wz LSTAT); C8 (wz lma_mapret)].

  (* [comment removed for export] *)
End O1.
