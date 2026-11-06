(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall5lv Mallj6y Malllim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall5lv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_mdx7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_m8yt RF_mdx7.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mdx7.RF_m8qy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mdx7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3 RF_egfy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc RF_m8yt RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_mdx7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_mdx7 Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_myiv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mdx7.RF_m8qy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_mdx7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallzvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_myiv.RF_ms87.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I Malleon.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_myiv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_myiv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_am_P.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_myiv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RF_myiv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malleon OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_myiv.Malllub OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_myiv.RF_a0ii OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_M4.RF_m79e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_am_P OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_myiv.RF_a7dr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_myiv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep MRepAux RAlllfc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
Notation AREACH := (AREACH_from p0_reserved).
Notation MFACTS := (@MFACTS_g p0_reserved).

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Definition hz0 (a : Z) : Prop := a < alloc_ceiling /\ ~ (0x10000 <= a < 0x63000).

(* [comment removed for export] *)
Lemma malloc_fp_where st st' lo sp m m' a :
  mrep st m -> mrep st' m' -> mrel st st' -> malloc_fp st st' lo sp a -> alloc_ceiling <= lo ->
  lo <= a < sp \/ CTX <= a < CTX + 928 \/ PERRNO <= a < PERRNO + 4 \/ hz0 a.
Proof.
  intros MR MR' EL FP CLO.
  destruct (malloc_fp_cases st st' lo sp m m' a MR MR' FP) as [W|AC]; [left; exact W|].
  destruct (Z_lt_le_dec a 0x10000) as [L1|L1]; [right; right; right; split; [exact AC| lia]|].
  destruct (Z_lt_le_dec a 0x63000) as [L2|L2]; [| right; right; right; split; [exact AC| lia]].
  (* [comment removed for export] *)
  destruct (Z_lt_le_dec a 0x30000) as [L3|L3].
  - exfalso. pose proof MR as (WF & _). pose proof MR' as (WF' & _). (first [ pose proof (WF) as dR_1; dand3 dR_1 as RS WR _ | pose proof WF as (RS & WR & _) ]). (first [ pose proof (WF') as dR_2; dand3 dR_2 as RS' WR' _ | pose proof WF' as (RS' & WR' & _) ]).
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    destruct FP as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold CTX in H. lia.
    + (first [ pose proof ((WR' _ _ Hr)) as dR_3; dand5 dR_3 as _ _ _ _ RF | destruct (WR' _ _ Hr) as (_ & _ & _ & _ & RF) ]). pose proof (reserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + (first [ pose proof ((WR' _ _ Hr)) as dR_4; dand5 dR_4 as _ _ _ _ RF | destruct (WR' _ _ Hr) as (_ & _ & _ & _ & RF) ]). pose proof (reserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
    + (first [ pose proof ((WR _ _ Hr)) as dR_5; dand5 dR_5 as _ _ _ _ RF | destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]). pose proof (reserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + (first [ pose proof ((WR _ _ Hr)) as dR_6; dand5 dR_6 as _ _ _ _ RF | destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]). pose proof (reserved_disjoint _ _ RF) as (?&?&?&?). lia.
    + pose proof (fresh_image st a (conj FC FR) RS). lia.
  - destruct (malloc_fp_image (Clg:=Clg) st st' lo sp m m' a MR MR' FP CLO ltac:(lia)) as [X|X]; [right; left; exact X| right; right; left; unfold PERRNO; exact X].
Qed.

(* [comment removed for export] *)
Lemma fpF_unchanged st st' LB lo sp m m' :
  MFACTS st LB -> mrep st m -> mrep st' m' -> mrel st st' ->
  pres_except (malloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
  forall a, 0 <= a < 2^64 -> ~ (lo <= a < sp) -> ~ (CTX <= a < CTX + 928) -> ~ (PERRNO <= a < PERRNO + 4) ->
  (hz0 a -> exists blk, In blk LB /\ blk_addr blk <= a < blk_addr blk + blk_size blk) ->
  m' (wa a) = m (wa a).
Proof.
  intros MF MR MR' EL PE CLO LS a Ha N1 N2 N3 HB.
  destruct (Classical_Prop.classic (hz0 a)) as [HZ|NHZ].
  - (first [ pose proof ((HB HZ)) as dR_7; dex1 dR_7 as blk; destruct dR_7 as [Hin Hab] | pose proof ((HB HZ)) as dR_7; dand3 dR_7 as blk Hin Hab | destruct (HB HZ) as (blk & Hin & Hab) ]).
    exact (proj1 (heap_pres_of_fp (Clg:=Clg) st st' LB lo sp m m' MF MR MR' EL PE CLO LS a Ha ltac:(right; right; exists blk; split; [exact Hin| exact Hab]))).
  - apply PE; [exact Ha|]. intros Hfp.
    destruct (malloc_fp_where st st' lo sp m m' a MR MR' EL Hfp CLO) as [X|[X|[X|X]]]; tauto.
Qed.

(* [comment removed for export] *)
Definition malloc_postF (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ (forall a, 0 <= a < 2^64 ->
          ~ (lo <= a < bv_unsigned sp) -> ~ (CTX <= a < CTX + 928) -> ~ (PERRNO <= a < PERRNO + 4) ->
          (hz0 a -> exists blk, In blk LB /\ blk_addr blk <= a < blk_addr blk + blk_size blk) ->
          m' (wa a) = m (wa a))
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ HEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ block_range A n
           /\ HEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
           (* [comment removed for export] *)
           /\ (MMAP_THRESHOLD <= n \/ exists g idx sc', (s_slots (ps_m s')) !! (fst p) = Some (g, idx)
                                    /\ active (ps_m s') sc' = Some g /\ 0 <= sc' <= Z.lor (size_to_class n) 1)
       end.

Definition malloc_stmtF : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo : Z) (errv : word),
  HEAP s LB m ->
  auxv_okd (c_init_done (ctx (ps_m s))) m (bv_unsigned sp) ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - MALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 PTP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM rsegs (raw_malloc n) s
        (malloc_postF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_SYM) fc None m (seg_rom rsegs)).

End CEIL.

Section TOPLEVEL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : big_stmt.

#[using="RBIG AS_PRE RAS as_inv as_pre"] Theorem malloc_specF : malloc_stmtF.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo errv.
  intros HEAP AUXB ST CLO LO ERR MI TP HA N. unfold MALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  (first [ dex1 HEAP as st; dand5 HEAP as LB0 HPERM Hst MR [BLK AR] | dand6 HEAP as st LB0 HPERM Hst MR [BLK AR] | destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]) ]). rename LB into LBc. rename LB0 into LB.
  assert (ECTX : ctx (ps_m s) = ctx st) by (rewrite <- Hst; reflexivity).
  rewrite ECTX in AUXB. pose proof AUXB as AUX.
  pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt rsegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 malloc_entry) fc None m (seg_rom rsegs))).
  { unfold MALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. }
  (intros s0' s1' ms1; (first [ intro dR_18; dand3 dR_18 as -> -> -> | intros (-> & -> & ->) ])). cbv beta.
  eapply (implM_bind rsegs _ _ _ (midQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (implM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ coreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (membed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold implT in |- *.
          pose proof (malloc_core_implT (Clg:=Clg) as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold implT in X. exact X.
      + (intros [cst2 r'] s' ms''; (first [ intro dR_19; dand6 dR_19 as [o1 [st2 r]] ans F1 F2 HC CQ | intros ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ) ])). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - (intros [cst2 r'] s' ms''; (first [ intro dR_20; dex4 dR_20 as st2 r ans o1; dand4 dR_20 as E F1 F2 CQ | intro dR_20; dand8 dR_20 as st2 r ans o1 E F1 F2 CQ | intros (st2 & r & ans & o1 & E & F1 & F2 & CQ) ])). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold midQ. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  (first [ dex4 MQ as st2 r ans o1; dand5 MQ as Ecs Ec F1 F2 CQ | dand9 MQ as st2 r ans o1 Ecs Ec F1 F2 CQ | destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ) ]). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [coreQ] in CQ.
    (first [ dex21 CQ as b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra'; dand20 CQ as -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO SCL MREL BL2 PSM PSF PSO | dand36 CQ as b rg m1 errv1 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' u3 u4 u5 u6 ra' -> MR2 TK2 UA2 MI2 ST2 FR2 ERR2 AUX2 PE2 SPANFP CTR2 SO EXPO dR_CQ_t0; dand6 dR_CQ_t0 as SCL MREL BL2 PSM PSF PSO | destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & SCL & MREL & BL2 & PSM & PSF & PSO) ]).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    (first [ pose proof ((region_addr_facts st2 m1 (fst b) rg MR2 Hr)) as dR_11; dand4 dR_11 as R4 RAL RC RI1 | pose proof (region_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1) ]).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold MALLOC_STACK in LO.
    pose proof (renf_implT (Clg:=Clg) sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia) ltac:(lia) FR2 (pres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (implT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold enf_post in EP.
    (first [ dex17 EP as st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m'; dand8 EP as ER -> MI' ST' MR' TK' PE' LEAF | dand25 EP as st' p w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' ER -> MI' ST' MR' TK' PE' LEAF | destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF) ]).
    (first [ dex1 LEAF as off; dand6 LEAF as OFF0 FIT Ep Est' Ep2 Eoff | dand7 LEAF as off OFF0 FIT Ep Est' Ep2 Eoff | destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff) ]).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    (first [ pose proof ((strip_eq_proj _ _ SE)) as dR_14; dand8 dR_14 as Ec Er En Em _ _ Esl Es | pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es) ]).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some (Clg:=Clg) st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (user_chunk (Clg:=Clg) st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold malloc_postF. do 15 eexists. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply pres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold PTP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - lia. }
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : pres_except (malloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply pres_except_mono.
      + eapply pres_except_trans; [exact PE2|].
        eapply pres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply malloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia. }
    pose proof (heap_pres_of_fp (Clg:=Clg) st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split; [exact PSF|]. split; [exact PSO|].
    split. { intros a Ha N1 N2 N3 HB. eapply (fpF_unchanged st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia) a Ha N1 N2 N3).
             intros HZ. (first [ pose proof ((HB HZ)) as dR_15; dex1 dR_15 as bb; destruct dR_15 as [Hbb Hab] | pose proof ((HB HZ)) as dR_15; dand3 dR_15 as bb Hbb Hab | destruct (HB HZ) as (bb & Hbb & Hab) ]). exists bb. split; [apply HIN; exact Hbb| exact Hab]. }
    exists A, ujunk.
    split; [reflexivity|].
    split. { (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold block_range. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    destruct SCL as [BIGn|(sc' & ACT' & SCR)]; [left; exact BIGn| right].
    exists g, idx, sc'. cbn [ps_m set_m fst s_slots strip].
    split; [| split; [| exact SCR]].
    + unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
      replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + get_stride (get_meta_rec st2 g) * idx) by (unfold UNIT; lia).
      exact SSL.
    + unfold active, ctx in *. cbn [s_ctx strip]. exact ACT'.
  - (* [comment removed for export] *)
    cbn [coreQ] in CQ.
    (first [ dex16 CQ as m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6; dand13 CQ as -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO | dand29 CQ as m1 errv1 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 -> MR2 TK2 MI2 ST2 ERR2 AUX2 PE2 MREL BL2 PSM PSF PSO | destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO) ]).
    apply evt_done. unfold malloc_postF. do 15 eexists. exists m1, errv1.
    pose proof (heap_pres_of_fp (Clg:=Clg) st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split; [exact PSF|]. split; [exact PSO|].
    split. { intros a Ha N1 N2 N3 HB. eapply (fpF_unchanged st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia) a Ha N1 N2 N3).
             intros HZ. (first [ pose proof ((HB HZ)) as dR_17; dex1 dR_17 as bb; destruct dR_17 as [Hbb Hab] | pose proof ((HB HZ)) as dR_17; dand3 dR_17 as bb Hbb Hab | destruct (HB HZ) as (bb & Hbb & Hab) ]). exists bb. split; [apply HIN; exact Hbb| exact Hab]. }
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none (Clg:=Clg) st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL.

Section CEIL2.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Theorem p0_malloc_implM : malloc_stmtF.
Proof.
  exact (malloc_specF as_pre2 as_inv2 alloc_slot_spec as_pre2_intro (big_spec am_pre alloc_meta_spec ramp_big)).
Qed.

End CEIL2.
