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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided1 x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided1 x y
          end ].
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PS2T.
Context {Clg : Ceiling}.
  Variables (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr c sb AB : Z) (b0w b1w : byte) (h2 w4 d8 trace sztag : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].

  Definition alloc_seg2T_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 ((AB + rz_size n) + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37424) fc None m1 (seg_rom rsegs)) /\
    munch [(AB + rz_size n + -16, AB + rz_size n)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].

  #[using="TRC CTR CT8 TH0 HDR SOA SEP_ctx SEP_thr ABR ABA SBR THR HC FR NR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 w4 h2 sb c ctx canfill Clg"] Lemma alloc_seg2T_spec : evt rsegs alloc_seg2T_post
        (MS (mkR (Z_to_bv 64 0x3731c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3731c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. aobjL THR. aobjL CTR.
    pose proof (munch_refl [(AB + rz_size n + -16, AB + rz_size n)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR. unfold kMaxSize in CSR. unfold kHighMemBeg in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (needed_size_mod8 n) as NS8.
    (* [comment removed for export] *)
    assert (SEP_tAB : apart thr 4096 AB (class_size c)) by (generalize SEP_thr ABR; unfold apart; clear; intros; lia).
    assert (SEP_cAB : apart ctx 0x10000 AB (class_size c)) by (generalize SEP_ctx ABR; unfold apart; clear; intros; lia).
    pose proof alloc_ceiling_val as CV. unfold alloc_s1a_frame in FR.
    amz. amz. br_not_taken. amz. amz.
    replace (Z.land (AB + rz_size n) 7) with 0.
    2:{ symmetry. apply land7_of_mod8; [lia|]. apply mod_add_lit; [lia| |].
        - apply (mod0_down AB 32 8); [exists 4; reflexivity| exact ABA].
        - apply (mod0_down (rz_size n) 16 8); [exists 2; reflexivity| apply rz_size_mod16]. }
    amz. amz. br_taken. amz. amz. br_not_taken.
    (* [comment removed for export] *)
    amz. amz. amz. amz.
    amz. replace (Z.shiftr n 32) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. replace (Z.shiftr n 48) with 0 by (rewrite Z.shiftr_div_pow2, Z.div_small by lia; lia).
    amz. sb_done. amz. amz. amz. if_false. amz. amz. amz. amz. amz. sb_done.
    (* [comment removed for export] *)
    amz. br_not_taken. amz. amz. amz. amz. amz. amz.
    apply evt_done. unfold alloc_seg2T_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS2T.
