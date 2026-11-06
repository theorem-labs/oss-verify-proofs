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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AInv AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocI AMallocA AMallocH ANodeA7 ASecComb ASechs3 ASech8k ASecqib ABudget ASecO1.

Module ASecFin.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AInv AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocI AMallocA AMallocH ANodeA7 ASecComb ASechs3 ASech8k ASecqib ABudget ASecO1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASech8k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecO1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
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
Ltac slia ::= thin; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

Section PS4s.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr AB q d e ru : Z) (oldp : byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Definition sec_seg4_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s6' : word),
    ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6' (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x375c8) fc None m1 (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1)] m m1 /\
    wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -128) /\
    (e <> 0 -> rw_cells rsegs m1 (q + 256 + d + kShadowOffset) [C1 (Z_to_bv 8 e)]).
  (* [comment removed for export] *)
End PS4s.

(* [comment removed for export] *)
Definition sec_fin_W (lo fp thr mb AB q d e dc ru pa nch n0 f0 : Z) : list (Z * Z) :=
  [(lo, fp);
   (LMA + 48, LMA + 65); (LMA + 72, LMA + 616); (LMA + 616, LMA + 617); (mb + 24, mb + 32); (pa + 8 * nch, pa + 8 * nch + 8); (LSTAT + 16, LSTAT + 32);
   (AB + 2032, AB + 2048);
   (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
   (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc)); (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d);
   (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1);
   (thr + 2800, thr + 2824); (thr + 2904, thr + 2912); (AB + 2048, AB + 2048 + 4096);
   (AB + 2032, AB + 2034); (AB, AB + 16)].
(* [comment removed for export] *)
Definition sec_fin_W2 (lo fp thr AB q d e dc ru : Z) : list (Z * Z) :=
  [(lo, fp); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
   (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc)); (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d);
   (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1);
   (thr + 2800, thr + 2824); (thr + 2904, thr + 2912); (AB + 2048, AB + 2048 + 4096);
   (AB + 2032, AB + 2034); (AB, AB + 16)].

(* [comment removed for export] *)
Definition sec_finA_W (lo fp thr mb AB q d e dc ru pa nch n0 f0 : Z) : list (Z * Z) :=
  [(fp + -2144 - 1024, fp + -2144 + -128);
   (LMA + 48, LMA + 65); (LMA + 72, LMA + 616); (LMA + 616, LMA + 617); (mb + 24, mb + 32); (pa + 8 * nch, pa + 8 * nch + 8); (LSTAT + 16, LSTAT + 32);
   (AB + 2032, AB + 2048);
   (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
   (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc)); (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)].

Section FinA.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (raT s4T s6T s7T : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n tsd ctx thr top bot sb mb q d e dc ru pa nch nres lz n0 f0 : Z).
  Variables (pad jb1 jrest junk0 scrL : list byte) (lk1 lk2 : Z) (cs : byte)
            (na nf ca mx cidx pan sta stm v0 v1 v2 vl h2 w4 d8 j0 j1 : word) (b0w b1w : byte) (bsl : list word)
            (D : list (list Z)) (olds oll olt uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).
  #[warnings="-notation-for-abbreviation"] Local Notation KEY := (malloc_key top bot fp ra).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (fp + -2144 + -128 + -48 + -96).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 3168.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis NR : kMaxPrimaryUser < n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RA4 : bv_unsigned ra mod 4 = 0.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  (* [comment removed for export] *)
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m LMA [C8 (Z_to_bv 64 4096)].
  Hypothesis LPA8 : ro_cells rsegs m (LMA + 8) [C8 (wz pa)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
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
  Hypothesis DR : dr AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pboth rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pboth n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pboth rsegs D' n0 f0 m2.
  (* [comment removed for export] *)
  Hypothesis O0 : rw_cells rsegs m (fp + -2128) [C8 (wz (fp + -2128 + 16))].
  Hypothesis D8 : rw_cells rsegs m (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))].
  Hypothesis D16 : rw_cells rsegs m (fp + -2128 + 16) [C8 (wz 0x58af4); CB 8 (dep_b16 top bot fp ra jb1)].
  Hypothesis O12 : rw_cells rsegs m (fp + -2128 + 12) [C4 (wz 0)].
  Hypothesis O32 : rw_cells rsegs m (fp + -2128 + 32) [CB 2024 jrest].
  Hypothesis PC1 : rw_cells rsegs m (fp + -2128 + 2056) [C8 (wz fp)].
  Hypothesis FR : rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis AMF : rw_cells rsegs m (fp + -2144) [C8 sp; C8 (wz 0x58b60)].
  Hypothesis FRA : rw_cells rsegs m (fp + -2144 + -128)
         (alloc_s1a_frame (wz (fp + -2144)) 1 s11 s10 s9 s8 s7 s6 (wz (fp + -81)) (wz (fp + -2128)) (wz 1) (wz 0x58af4) (wz n) sp (wz 0x3704c) junk0).
  Hypothesis FRC : rw_cells rsegs m (fp + -2144 + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3731c)).
  Hypothesis FRL : rw_cells rsegs m (fp + -2144 + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz (fp + -2128)) (wz 0xb1558) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).

  (* [comment removed for export] *)
  Definition sec_finA_post : machine_state -> Prop := fun st =>
    exists (raA t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' : word) (m' md : word -> option byte),
    st = MS (mkR raA (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (fp + -2144)) + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 (fp + -2128)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37534) fc None m' (seg_rom rsegs)
    /\ munch (sec_finA_W lo fp thr mb AB q d e dc ru pa nch n0 f0) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (fp + -2144 + -128)
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
    /\ dr AL_pboth rsegs (fst (depot_putC D KEY)) n0 f0 md
    /\ munch (sec_fin_W2 lo fp thr AB q d e dc ru) md m' /\ wmono rsegs md m'.

  (* [comment removed for export] *)
End FinA.
End ASecFin.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASech8k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecqib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecO1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecFinB.ASecFin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
Ltac slia ::= thin; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
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
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cell_or_ea := lazymatch goal with
  | |- rw_cells _ ?mm ?a _ => first [ match goal with H : rw_cells _ mm a _ |- _ => exact H end | eassumption ]
  | |- ro_cells _ ?mm ?a _ => first [ match goal with H : ro_cells _ mm a _ |- _ => exact H | H : rw_cells _ mm a _ |- _ => exact (proj1 H) end | eassumption ]
  | |- bytes_at _ ?mm ?a _ => first [ match goal with H : bytes_at _ mm a _ |- _ => exact H end | eassumption ]
  | |- u8arr _ ?mm ?a _ => first [ match goal with H : u8arr _ mm a _ |- _ => exact H end | eassumption ]
  | |- _ => eassumption end.



(* [comment removed for export] *)
Definition sec_finB_W (lo fp thr AB q d e : Z) : list (Z * Z) :=
  [(fp + -2144 - 1024, fp + -2144 + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + Z.min e 1);
   (thr + 2800, thr + 2824); (thr + 2904, thr + 2912); (AB + 2048, AB + 2048 + 4096);
   (AB + 2032, AB + 2034); (AB, AB + 16)].

(* [comment removed for export] *)
Lemma rw_cells_CB0 : forall (m : word -> option byte) a, 0 <= a -> a <= 2^64 -> rw_cells rsegs m a [CB 0%nat []].
Proof.
  intros m a H0 H1. split; [split; [cbn; split; [reflexivity| exact I]|]|].
  - cbn. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section FinB.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (raA : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n tsd ctx thr top bot mb q d e ru b1v id : Z).
  Variables (pad jb1 jrest junk0 : list byte) (v0 v1 v2 vl j0 j1 : word) (b0w : byte) (uj : list byte) (oldp : byte).

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (fp + -2144 + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 3168.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis NR : kMaxPrimaryUser < n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RA4 : bv_unsigned ra mod 4 = 0.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis IDR : 0 <= id < 2^32.
  (* [comment removed for export] *)
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
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
  Hypothesis O0 : rw_cells rsegs m (fp + -2128) [C8 (wz (fp + -2128 + 16))].
  Hypothesis D8 : rw_cells rsegs m (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))].
  Hypothesis D16 : rw_cells rsegs m (fp + -2128 + 16) [C8 (wz 0x58af4); CB 8 (dep_b16 top bot fp ra jb1)].
  Hypothesis O12 : rw_cells rsegs m (fp + -2128 + 12) [C4 (wz 0)].
  Hypothesis O32 : rw_cells rsegs m (fp + -2128 + 32) [CB 2024 jrest].
  Hypothesis PC1 : rw_cells rsegs m (fp + -2128 + 2056) [C8 (wz fp)].
  Hypothesis FR : rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis AMF : rw_cells rsegs m (fp + -2144) [C8 sp; C8 (wz 0x58b60)].
  Hypothesis FRA : rw_cells rsegs m (fp + -2144 + -128)
         (alloc_s1a_frame (wz (fp + -2144)) 1 s11 s10 s9 s8 s7 s6 (wz (fp + -81)) (wz (fp + -2128)) (wz 1) (wz 0x58af4) (wz n) sp (wz 0x3704c) junk0).

  Definition sec_finB_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word) (m' : word -> option byte),
    st = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (AB + 2048)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (sec_finB_W lo fp thr AB q d e) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo fp
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0'; C8 v1'; C8 v2']
    /\ rw_cells rsegs m' (thr + 2904) [C8 (wz (bv_unsigned vl + 1))]
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)]
    /\ rw_cells rsegs m' (AB + 2032)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (wz 0); C4 (wz n); C8 (wz id)]
    /\ rw_cells rsegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (AB + 2032))]
    /\ rw_cells rsegs m' (AB + 2048) [CB 4096%nat (fill_result 1 uj 4096%nat)]
    /\ rw_cells rsegs m' (q + 256 + d + kShadowOffset) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))].

  (* [comment removed for export] *)
End FinB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fin.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (raT s4T s6T s7T : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n tsd ctx thr top bot sb mb q d e dc ru pa nch nres lz n0 f0 : Z).
  Variables (pad jb1 jrest junk0 scrL : list byte) (lk1 lk2 : Z) (cs : byte)
            (na nf ca mx cidx pan sta stm v0 v1 v2 vl h2 w4 d8 j0 j1 : word) (b0w b1w : byte) (bsl : list word)
            (D : list (list Z)) (olds oll olt uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation ms := (map_size n).
  #[warnings="-notation-for-abbreviation"] Local Notation AB := (mb + 4096).
  #[warnings="-notation-for-abbreviation"] Local Notation KEY := (malloc_key top bot fp ra).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (fp + -2144 + -128 + -48 + -96).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 3168.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis NR : kMaxPrimaryUser < n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RA4 : bv_unsigned ra mod 4 = 0.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  (* [comment removed for export] *)
  Hypothesis LTAIL : lma_tail_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m LMA [C8 (Z_to_bv 64 4096)].
  Hypothesis LPA8 : ro_cells rsegs m (LMA + 8) [C8 (wz pa)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
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
  Hypothesis DR : dr AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pboth rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pboth n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pboth rsegs D' n0 f0 m2.
  (* [comment removed for export] *)
  Hypothesis O0 : rw_cells rsegs m (fp + -2128) [C8 (wz (fp + -2128 + 16))].
  Hypothesis D8 : rw_cells rsegs m (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))].
  Hypothesis D16 : rw_cells rsegs m (fp + -2128 + 16) [C8 (wz 0x58af4); CB 8 (dep_b16 top bot fp ra jb1)].
  Hypothesis O12 : rw_cells rsegs m (fp + -2128 + 12) [C4 (wz 0)].
  Hypothesis O32 : rw_cells rsegs m (fp + -2128 + 32) [CB 2024 jrest].
  Hypothesis PC1 : rw_cells rsegs m (fp + -2128 + 2056) [C8 (wz fp)].
  Hypothesis FR : rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis AMF : rw_cells rsegs m (fp + -2144) [C8 sp; C8 (wz 0x58b60)].
  Hypothesis FRA : rw_cells rsegs m (fp + -2144 + -128)
         (alloc_s1a_frame (wz (fp + -2144)) 1 s11 s10 s9 s8 s7 s6 (wz (fp + -81)) (wz (fp + -2128)) (wz 1) (wz 0x58af4) (wz n) sp (wz 0x3704c) junk0).
  Hypothesis FRC : rw_cells rsegs m (fp + -2144 + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3731c)).
  Hypothesis FRL : rw_cells rsegs m (fp + -2144 + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz (fp + -2128)) (wz 0xb1558) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).

  Definition sec_fin_post : machine_state -> Prop := fun st =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' v0' v1' v2' : word) (m' md : word -> option byte),
    st = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (AB + 2048)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (sec_fin_W lo fp thr mb AB q d e dc ru pa nch n0 f0) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo fp
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
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (AB + 2032)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land (b1_mid (bv_unsigned b1w)) 243) 0));
          C2 (wz 0); C4 (wz n); C8 (wz (snd (depot_putC D KEY)))]
    /\ rw_cells rsegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (AB + 2032))]
    /\ rw_cells rsegs m' (AB + 2048) [CB 4096%nat (fill_result 1 uj 4096%nat)]
    /\ bytes_at rsegs m' (q + kShadowOffset) (repeat (Z_to_bv 8 250) 256)
    /\ bytes_at rsegs m' (q + 256 + dc + kShadowOffset) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc)))
    /\ bytes_at rsegs m' (q + 256 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))
    /\ wr_at rsegs m' (q + 256 + kShadowOffset) d
    /\ rw_cells rsegs m' (q + 256 + d + kShadowOffset) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))]
    (* [comment removed for export] *)
    /\ dr AL_pboth rsegs (fst (depot_putC D KEY)) n0 f0 md
    /\ munch (sec_fin_W2 lo fp thr AB q d e dc ru) md m' /\ wmono rsegs md m'.

  (* [comment removed for export] *)
End Fin.
