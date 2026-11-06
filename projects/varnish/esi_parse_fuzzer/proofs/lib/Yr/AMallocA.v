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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j AInv ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.

Module AMalrao.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
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
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

Section PS1a.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 128.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj < 2^64.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis INI : ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)].
    Definition alloc_seg1a_post : machine_state -> Prop := fun ms' =>
    exists (r : Z) (m1 : word -> option byte) (junk0 : list byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s4' s8' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 r) s4' (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) s8' (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37308) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    r = rz_log n /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra junk0).

  #[using="RSS INI SO NR LO ST MI Clg"] Lemma alloc_seg1a_spec : evt rsegs alloc_seg1a_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 stkobj) (Z_to_bv 64 1) (Z_to_bv 64 canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3719c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg1a; try eassumption. intros. subst. apply evt_done. unfold alloc_seg1a_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS1a.

Section PS1b.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis RZm : ro_cells rsegs m 0xb2b80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis RZL : rzlog_stmt.
    Definition alloc_seg1b_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37350) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128).

  #[using="RZL FR RZm NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 Clg"] Lemma alloc_seg1b_spec : evt rsegs alloc_seg1b_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) s8 (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37308) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg1b; try eassumption. intros. subst. apply evt_done. unfold alloc_seg1b_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS1b.

Section PS1c.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj tsd ctx thr : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis MUM : ro_cells rsegs m 0xb2b78 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis GT : get_thread_stmt.
    Definition alloc_seg1c_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37438) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128).

  #[using="GT TC MUM NR SPR LO ST MI ctx tsd Clg"] Lemma alloc_seg1c_spec : evt rsegs alloc_seg1c_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37350) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg1c; try eassumption. intros. subst. apply evt_done. unfold alloc_seg1c_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS1c.

Section PS2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr c cnt maxc sb AB : Z) (ks : list word) (b0w b1w : byte) (kw statv h2 w4 d8 trace sztag : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PC : rw_cells rsegs m (thr + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis CNT : 1 <= cnt <= 16.
  Hypothesis KW : nth_error ks (Z.to_nat (cnt - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis STA : rw_cells rsegs m ((thr + 208) + 2576) [C8 statv].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : thr + 4096 <= sb \/ sb + 2^37 <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= sb \/ sb + 2^37 <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].
    Definition alloc_seg2_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 ((AB + rz_size n) + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37544) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); ((thr + 208 + 80 * c), (thr + 208 + 80 * c) + 4); ((thr + 208) + 2576, (thr + 208) + 2584); (AB + rz_size n + -16, (AB + rz_size n))] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)] /\
    rw_cells rsegs m1 ((thr + 208) + 2576) [C8 statv'] /\
    rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].

  #[using="TRC CTR CT8 TH0 HDR SOA SEP_tc SEP_ctx SEP_thr ABR ABA ABE SBR THRA THR STA KWR KW CNT LKS PC SBc BLK HC FR NR SPR SPA LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 w4 h2 statv kw sb ctx canfill Clg"] Lemma alloc_seg2_spec : evt rsegs alloc_seg2_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 8) a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37438) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg2; try eassumption. intros. subst. apply evt_done. unfold alloc_seg2_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS2.

Section PS3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr c sb AB q r8 d e n0 f0 : Z) (b0w : byte) (b1v : Z) (d8 : word)
            (D : list (list Z)) (k : list Z) (olds : list byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis SOA : bv_unsigned sp <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis PCo : poison_consts m.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : n0 + kDepotNodesBlock <= sb \/ sb + 2^37 <= n0.
  Hypothesis SEP_f0 : f0 + kStackStoreBlockBytes <= sb \/ sb + 2^37 <= f0.
  Hypothesis KL : (1 <= length k <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) k.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (Z_to_bv 64 (stkobj + 16)); C8 (Z_to_bv 64 (Z.of_nat (length k)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) k)).
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].
  Hypothesis SHA : ro_cells rsegs m (q + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)].
  Hypothesis SHU : u8arr rsegs m (q + r8 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
    Definition alloc_seg3_post : machine_state -> Prop := fun ms' =>
    exists (m1 md : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    let id := snd (depot_putC D k) in
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37654) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + rz_size n + -8, AB + rz_size n); (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    dr AL_pasan rsegs (fst (depot_putC D k)) n0 f0 md /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -8, AB + rz_size n);
             (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] md m1 /\
    wmono rsegs md m1 /\
    rw_cells rsegs m1 (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] /\
    bytes_at rsegs m1 (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d)) /\
    wr_at rsegs m1 (q + r8 + kShadowOffset) d.

  #[using="OL SHU SHA HDR TRB TRC KR KL SEP_f0 SEP_n0 DF0 DN0 DTOT DLEN DND DR DPS PS PCo RZ8 ABR ABQ SBR THR HC SOA ER NDE NR SPR LO ST MI olds d8 e sb c Clg"] Lemma alloc_seg3_spec : evt rsegs alloc_seg3_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 (Z_to_bv 64 (stkobj + 16)) (Z_to_bv 64 (Z.of_nat (length k))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37544) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg3; try eassumption. intros. subst. apply evt_done. unfold alloc_seg3_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS3.

Section PS4.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr c sb AB q r8 d e : Z) (oldp : byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 < e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis CR1 : 1 <= c <= 30.
  Hypothesis FIT : needed_size n <= class_size c.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].  (* [comment removed for export] *)
  Hypothesis SHP : rw_cells rsegs m (q + r8 + d + kShadowOffset) [C1 oldp].
    Definition alloc_seg4_nz_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (AB + rz_size n + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x376e8) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + 1)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)].

  #[using="SHP AF2 AF1 PCo RZ8 FIT CR1 ABR ABQ SBR THR ER NDE NR ST MI oldp sb c Clg"] Lemma alloc_seg4_nz_spec : evt rsegs alloc_seg4_nz_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37654) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg4_nz; try eassumption. intros. subst. apply evt_done. unfold alloc_seg4_nz_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS4.

Section PS4z.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (n d : Z).
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + 0.
    Definition alloc_seg4_z_post : machine_state -> Prop := fun ms' => ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x376e8) fc None m (seg_rom rsegs)).

  #[using="NDE NR Clg"] Lemma alloc_seg4_z_spec : evt rsegs alloc_seg4_z_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37654) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg4_z; try eassumption. intros. subst. apply evt_done. unfold alloc_seg4_z_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS4z.

Section PS5.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr c sb AB : Z) (v0 v1 v2 : word) (vs : list word) (uj : list byte).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis SEP_thr : thr + 4096 <= sb \/ sb + 2^37 <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= sb \/ sb + 2^37 <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TSDL : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].   (* [comment removed for export] *)
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].  (* [comment removed for export] *)
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STA2 : u64arr rsegs m (thr + 2912) vs.
  Hypothesis LVS : length vs = 32%nat.
  Hypothesis USR : rw_cells rsegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
    Definition alloc_seg5_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' vc' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3787c) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8);
             (AB + rz_size n, AB + rz_size n + Z.min n 4096)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] /\
    u64arr rsegs m1 (thr + 2912) (upd vs (Z.to_nat c) vc') /\
    rw_cells rsegs m1 (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) (fill_result canfill uj (Z.to_nat (Z.min n 4096)))].

  #[using="USR LVS STA2 STS AF52 AF44 AF1 PCo TPL TSDL SEP_tc SEP_ctx SEP_thr ABR SBR BLK2 TSS TC HC FR CF NR SPR LO ST MI junk0 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 v2 v1 v0 sb ctx tsd Clg"] Lemma alloc_seg5_spec : evt rsegs alloc_seg5_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x376e8) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg5; try eassumption. intros. subst. apply evt_done. unfold alloc_seg5_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS5.

Section PS6.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill thr c sb AB b1v id : Z) (b0w : byte) (j0 j1 : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis ABH : rz_size n <> 16 -> rw_cells rsegs m AB [C8 j0; C8 j1].
    Definition alloc_seg6_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 (AB + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp) /\
    rw_cells rsegs m1 (AB + rz_size n + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] /\
    (rz_size n <> 16 -> rw_cells rsegs m1 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + rz_size n + -16))]).

  #[using="ABH B1R HDR HK LS2 LS1 ABR SBR THR TPL HC FR NR SPR LO ST MI junk0 j1 j0 b0w sb c canfill Clg"] Lemma alloc_seg6_spec : evt rsegs alloc_seg6_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3787c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. eapply alloc_seg6; try eassumption. intros. subst. apply evt_done. unfold alloc_seg6_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PS6.

End AMalrao.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA.AMalrao.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LVS; @OL; @ABR; @SBR; @RGE; @NS; @ABQ; @CGE; @NDE; @ER; @RZ8; @LO; @RSR; @CE0; @CR1; @NR; @KSO; @HB'; @ATHR; @Ha; @HA'; @CSR; @Bthr; @TPL; @H0; @H2; @H; @H1; @ADN0; @ADF0; @DN0; @DF0; @SOA; @TSDL; @Bthr1; @LKS; @KL; @H6; @A; @H3; @H4; @E0; @NSB; @X1; @X2; @X3; @Bctx; @H5; @RZ32'; @RZ32; @NZ; @Hl; @Hx; @LA; @X4; @ACTR; @X; @KLz; @KLz__])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
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

(* [comment removed for export] *)
Definition apart (a s b t : Z) : Prop := a + s <= b \/ b + t <= a.

Lemma lt256_of_log2 : forall a, 0 <= a -> Z.log2 a <= 7 -> a < 256.
Proof.
  intros a Ha Hl. destruct (Z.eq_dec a 0) as [->|NZ]; [lia|].
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; lia.
Qed.
Lemma b1_mid_range : forall x, 0 <= x -> 0 <= b1_mid x < 256.
Proof.
  intros x Hx. unfold b1_mid.
  set (y := Z.lor (Z.land x 18446744073709551612) 1).
  assert (Y : 0 <= y) by (unfold y; apply Z.lor_nonneg; split; [apply Z.land_nonneg; left; lia| lia]).
  set (a := Z.land y 143).
  assert (A : 0 <= a) by (unfold a; apply Z.land_nonneg; right; lia).
  assert (LA : Z.log2 a <= 7).
  { unfold a. pose proof (Z.log2_land y 143 Y ltac:(lia)). change (Z.log2 143) with 7 in H. lia. }
  split; [apply Z.lor_nonneg; lia|].
  apply lt256_of_log2; [apply Z.lor_nonneg; lia|].
  rewrite Z.log2_lor by lia. change (Z.log2 16) with 4. lia.
Qed.
Lemma notin_mono : forall a lo hi lo' hi', ~ (lo' <= a < hi') -> lo' <= lo -> hi <= hi' -> ~ (lo <= a < hi).
Proof. intros; lia. Qed.
Lemma outside_of_disj : forall a lo hi, a + 1 <= lo \/ hi <= a -> ~ (lo <= a < hi).
Proof. intros; lia. Qed.

(* [comment removed for export] *)
Lemma apart_gl : forall a s b t, apart a s b t -> forall x n lo hi,
  a <= x -> x + n <= a + s -> b <= lo -> hi <= b + t -> x + n <= lo \/ hi <= x.
Proof. intros a s b t [H|H] x n lo hi H1 H2 H3 H4; [left|right]; lia. Qed.
Lemma apart_gr : forall a s b t, apart a s b t -> forall x n lo hi,
  b <= x -> x + n <= b + t -> a <= lo -> hi <= a + s -> x + n <= lo \/ hi <= x.
Proof. intros a s b t [H|H] x n lo hi H1 H2 H3 H4; [right|left]; lia. Qed.
Definition boxed (P : Prop) : Prop := P.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module HotBulk. Import Ltac2.
Ltac2 clear_boxed () :=
  let ids := List.map_filter (fun h => let (id, _, ty) := h in
               lazy_match! ty with boxed _ => Some id | _ => None end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac2 clear_negs () :=
  let ids := List.map_filter (fun h => let (id, _, ty) := h in
               lazy_match! ty with not _ => Some id | _ => None end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
End HotBulk.
Ltac box H := lazymatch type of H with ?T => change T with (boxed T) in H end.
Ltac box_places := repeat match goal with H : 0 <= _ <= 1 /\ 0 <= _ <= 1 /\ _ |- _ => box H end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unbox_places := repeat match goal with H : boxed (0 <= _ <= 1 /\ 0 <= _ <= 1 /\ _) |- _ => unfold boxed in H end.
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | multimatch goal with H : apart _ _ _ _ |- _ =>
            (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia
        | unbox_places; first [ lia
            | multimatch goal with H : apart _ _ _ _ |- _ =>
                (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ] ].
(* [comment removed for export] *)

Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sides1c := first [ eassumption | eqrefl | lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | lia | modtac]
                      | unbox_places; kung; lia ].
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

(* [comment removed for export] *)
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
Section PS4u.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr c sb AB q r8 d e : Z) (oldp : byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis CR1 : 1 <= c <= 30.
  Hypothesis FIT : needed_size n <= class_size c.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + r8 + d + kShadowOffset) [C1 oldp].
  Definition alloc_seg4_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 s6' (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x376e8) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1)] m m1 /\
    wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -128) /\
    (e <> 0 -> rw_cells rsegs m1 (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)]).
  #[using="SHP AF2 AF1 PCo RZ8 FIT CR1 ABR ABQ SBR THR ER NDE NR ST MI oldp sb c Clg"] Lemma alloc_seg4_spec : evt rsegs alloc_seg4_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                 a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37654) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. destruct (Z.eq_dec e 0) as [E0|E0].
    - eapply evt_cut; [eapply (alloc_seg4_z_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m n d); [exact NR| rewrite E0, Z.add_0_r in NDE; rewrite NDE; lia] |].
      intros ms' ->. apply evt_done. unfold alloc_seg4_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|]. intros X; exfalso; exact (X E0).
    - eapply evt_cut; [eapply (alloc_seg4_nz_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo n stkobj thr c sb AB q r8 d e oldp); try eassumption; try lia |].
      { exact (SHP E0). }
      intros ms' PO. unfold alloc_seg4_nz_post in PO. (first [ dex17 PO as m1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15; dand6 PO as -> MU WM MI1 ST1 SH1 | dand23 PO as m1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 -> MU WM MI1 ST1 SH1 | destruct PO as (m1 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & -> & MU & WM & MI1 & ST1 & SH1) ]).
      apply evt_done. unfold alloc_seg4_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [replace (Z.min e 1) with 1 by lia; exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|]. intros _; exact SH1.
  Qed.
End PS4u.

(* [comment removed for export] *)
Definition alloc_hit_W (sp : word) (thr c AB n q r8 d e n0 f0 : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 128, bv_unsigned sp);
   (bv_unsigned sp - 1024, bv_unsigned sp + -128);
   (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (thr + 208 + 2576, thr + 208 + 2584); (AB + rz_size n + -16, AB + rz_size n);
   (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
   (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
   (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
   (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096);
   (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)].
(* [comment removed for export] *)
Definition alloc_hit_W2 (sp : word) (thr c AB n q r8 d e : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 128, bv_unsigned sp);
   (bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + rz_size n + -8, AB + rz_size n);
   (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
   (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
   (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096);
   (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)].
(* [comment removed for export] *)
Definition alloc_hit_Wc (sp : word) (thr AB n q r8 d n0 f0 : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 1024, bv_unsigned sp); (thr + 208, thr + 3168); (AB, AB + rz_size n + Z.min n 4096);
   (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (q + r8 + 2147450880, q + r8 + 2147450880 + d + 1)].

Section AllocHit.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr c cnt maxc sb AB q r8 d e n0 f0 : Z).
  Variables (ks : list word) (b0w b1w : byte) (kw statv h2 w4 d8 j0 j1 v0 v1 v2 : word) (vs : list word)
            (D : list (list Z)) (k : list Z) (olds uj : list byte) (oldp : byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis SOA : bv_unsigned sp <= stkobj /\ stkobj + 2064 <= 2^47.
  (* [comment removed for export] *)
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.
  (* [comment removed for export] *)
  Hypothesis INI : ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)].
  Hypothesis RZm : ro_cells rsegs m 0xb2b80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis MUM : ro_cells rsegs m 0xb2b78 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e83d8.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  (* [comment removed for export] *)
  Hypothesis HC : c = size_class (needed_size n).
  Hypothesis PC : rw_cells rsegs m (thr + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis CNT : 1 <= cnt <= 16.
  Hypothesis KW : nth_error ks (Z.to_nat (cnt - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis STA : rw_cells rsegs m (thr + 208 + 2576) [C8 statv].
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STA2 : u64arr rsegs m (thr + 2912) vs.
  Hypothesis LVS : length vs = 32%nat.
  (* [comment removed for export] *)
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis ABH : rz_size n <> 16 -> rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis SHA : ro_cells rsegs m (q + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)].
  Hypothesis SHU : u8arr rsegs m (q + r8 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + r8 + d + kShadowOffset) [C1 oldp].
  Hypothesis USR : rw_cells rsegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
  (* [comment removed for export] *)
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : apart n0 kDepotNodesBlock sb (2^37).
  Hypothesis SEP_f0 : apart f0 kStackStoreBlockBytes sb (2^37).
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  (* [comment removed for export] *)
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pasan rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pasan n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pasan rsegs D' n0 f0 m2.
  Hypothesis KL : (1 <= length k <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) k.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (Z_to_bv 64 (stkobj + 16)); C8 (Z_to_bv 64 (Z.of_nat (length k)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) k)).

  Definition alloc_hit_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' : word) (m' md : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (AB + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (alloc_hit_W sp thr c AB n q r8 d e n0 f0) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 maxc); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)]
    /\ rw_cells rsegs m' (thr + 208 + 2576) [C8 statv']
    /\ rw_cells rsegs m' (thr + 2800) [C8 v0'; C8 v1'; C8 v2']
    /\ u64arr rsegs m' (thr + 2912) (upd vs (Z.to_nat c) vc')
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (AB + rz_size n + -16)
         [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land (b1_mid (bv_unsigned b1w)) 243) 0));
          C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 (snd (depot_putC D k)))]
    /\ (rz_size n <> 16 -> rw_cells rsegs m' AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + rz_size n + -16))])
    (* [comment removed for export] *)
    /\ bytes_at rsegs m' (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))
    /\ wr_at rsegs m' (q + r8 + kShadowOffset) d
    /\ (e <> 0 -> rw_cells rsegs m' (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)])
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) (fill_result canfill uj (Z.to_nat (Z.min n 4096)))]
    (* [comment removed for export] *)
    /\ dr AL_pasan rsegs (fst (depot_putC D k)) n0 f0 md
    /\ munch (alloc_hit_W2 sp thr c AB n q r8 d e) md m' /\ wmono rsegs md m'.

  #[using="TRB TRC KR KL DRF SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_f0 SEP_n0 DF0 DN0 DTOT DLEN DND DR USR SHP OL SHU SHA ABH HDR RZ8 ABR ABQ ABA ABE LVS STA2 STS STA KWR KW CNT LKS PC HC SEP_tc SEP_ctx SEP_thr SBR TPL TSDL CTR THRA THR CT8 TH0 TC SBc HK LS2 LS1 AF52 AF44 AF2 AF1 PCo MUM RZm RSS INI BLK2 BLK DPS PS TSS GT RZL SOA CF ER NDE NR SPR SPA LO ST MI oldp olds v2 v1 v0 j1 j0 d8 w4 h2 statv kw b0w sb ctx tsd Clg"] Lemma alloc_hit : evt rsegs alloc_hit_post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 stkobj) (Z_to_bv 64 1) (Z_to_bv 64 canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3719c) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. (* [comment removed for export] *)
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]). pose proof Bnds as Bnds_; (first [ dand8 Bnds_ as Btsd0 Btsd1 Bctx0 Bctx1 Bthr Bthr1 Btp Bctx | destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx) ]). aobj_lin1 Bthr. aobj_lin1 Bctx. kun.
    unfold kMallocFillByte, kAsanHeapLeftRedzoneMagic, kAllocBegMagic, CHUNK_ALLOCATED in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (KSO : kShadowOffset = 2147450880) by reflexivity.
    pose proof alloc_ceiling_val as CV.
    clear PCo TC.
    (* [comment removed for export] *)
    box_places. box SPA. box THRA. box ABA. box KWR. box ABE. box DLEN. box DTOT. box RA. box CF. box NSB. box RLT. box CNT. box HC. box LKS.
    box Bnds. box CV. box LO0. box KL. box KR. box DND.
    (* [comment removed for export] *)
    box INI. box RSS. box RZm. box MUM. box Ccan. box Cgotcf. box Cthr. box Cgotsh. box Cshoff. box Cgotmid. box Cgotmide. box Cgothi. box Chivars.
    box Cgotms. box Creal. box Cgotps. box Cps. box AF1. box AF2. box AF44. box AF52. box LS1. box LS2. box HK. box SBc.
    box Cini. box Ckey. box Ctsd. box Cctx. box Cthr2. box TH0. box CT8. box TRC. box TRB. box SHA.
    box PC. box STA. box STS. box STA2. box HDR. box SHU. box USR.
    (* [comment removed for export] *)
    Ltac small_ctx := first [ ltac2:(Ltac2.Control.enter HotBulk.clear_boxed) | repeat match goal with H : boxed _ |- _ => clear H end ].   (* [comment removed for export] *)   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac cls X := lazymatch X with
      | context [stkobj] => constr:(1%nat) | context [bv_unsigned sp] => constr:(1%nat)
      | context [thr] => constr:(2%nat) | context [ctx] => constr:(3%nat) | context [AB] => constr:(4%nat)
      | context [q] => constr:(5%nat) | context [n0] => constr:(6%nat) | context [f0] => constr:(7%nat)
      | _ => match goal with
             | Hr : ?alo <= X < _ |- _ => cls alo
             | Hr : ?alo <= X <= _ |- _ => cls alo
             | Hr : ?alo <= X |- _ => lazymatch alo with context [bv_unsigned sp] => constr:(1%nat) | context [thr] => constr:(2%nat) | context [ctx] => constr:(3%nat) | context [q] => constr:(5%nat) | context [AB] => constr:(4%nat) | _ => fail end   (* [comment removed for export] *)
             | _ => constr:(0%nat) end
      end.
    Ltac agl H := eapply (apart_gl _ _ _ _ H); small_ctx; lia.
    Ltac agr H := eapply (apart_gr _ _ _ _ H); small_ctx; lia.
    Ltac ubl := unbox_places; small_ctx; lia.
    Ltac sbl := small_ctx; lia.
    Ltac ivl := lazymatch goal with |- ?A + _ <= ?lo \/ _ <= _ =>
      let a := cls A in let l := cls lo in
      lazymatch a with
      | 1%nat => sbl
      | 2%nat => lazymatch l with 3%nat => agr SEP_tc | 4%nat => agl SEP_thr | 5%nat => ubl | 6%nat => agr SEP_n0t | 7%nat => agr SEP_f0t | 0%nat => ubl | _ => sbl end
      | 3%nat => lazymatch l with 2%nat => agl SEP_tc | 4%nat => agl SEP_ctx | 5%nat => ubl | 6%nat => agr SEP_n0c | 7%nat => agr SEP_f0c | 0%nat => ubl | _ => sbl end
      | 4%nat => lazymatch l with 2%nat => agr SEP_thr | 3%nat => agr SEP_ctx | 6%nat => agr SEP_n0 | 7%nat => agr SEP_f0 | _ => sbl end
      | 5%nat => lazymatch l with 2%nat => ubl | 3%nat => ubl | 6%nat => ubl | 7%nat => ubl | _ => sbl end
      | 6%nat => lazymatch l with 2%nat => agl SEP_n0t | 3%nat => agl SEP_n0c | 4%nat => agl SEP_n0 | 5%nat => ubl | 0%nat => ubl | _ => sbl end
      | 7%nat => lazymatch l with 2%nat => agl SEP_f0t | 3%nat => agl SEP_f0c | 4%nat => agl SEP_f0 | 5%nat => ubl | 0%nat => ubl | _ => sbl end
      | _ => lazymatch l with 2%nat => ubl | 3%nat => ubl | 6%nat => ubl | 7%nat => ubl | _ => sbl end
      end end.
    Ltac slia ::=
      (* [comment removed for export] *)
      lazymatch goal with
      | |- ~ (_ <= ?a < _) /\ _ => repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end
      | |- _ => idtac
      end;
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      lazymatch goal with
      | |- True => exact I
      | |- ~ (?lo <= ?a < ?hi) =>
          (* [comment removed for export] *)
          repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end;
          first [ assumption
                | apply outside_of_disj; ivl
                | multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
                    apply (notin_mono a lo hi lo' hi' H); repeat match goal with H' : ~ _ |- _ => clear H' end; lia end
                | repeat match goal with H' : ~ _ |- _ => clear H' end; lia
                | unbox_places; repeat match goal with H' : ~ _ |- _ => clear H' end; lia ]
      | |- _ => first [ ivl
                      | small_ctx; lia
                      | multimatch goal with H : apart _ _ _ _ |- _ =>
                          (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; small_ctx; lia
                      | unbox_places; small_ctx; first [ lia
                          | multimatch goal with H : apart _ _ _ _ |- _ =>
                              (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ] ]
      end.
    (* [comment removed for export] *)
    Ltac sarr := rewrite ?u32s_length, ?u64s_length, ?upd_length.
    Ltac disj := cbn [disjoint_from]; simpl_sizes; sarr; slia.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac useD lo := match goal with D : forall A k, 0 <= k -> lo <= A -> _ |- _ => apply D end; simpl_sizes; sarr; lia.
    Ltac disjA A := lazymatch A with
      | context [stkobj] => useD (bv_unsigned sp)
      | context [thr] => first [ useD thr | useD (thr + 2800) ]   (* [comment removed for export] *)
      | context [ctx] => useD ctx
      | context [q] => useD (q + 2147450880)
      | context [AB] => useD (AB + rz_size n)
      | _ => useD 0x10000
      end.
    (* [comment removed for export] *)
    Ltac slia_big := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      first [ exact I | ivl | lia
            | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia
            | unbox_places; first [ lia
                | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ] ].
    Ltac refresh H M WMH H' :=
      lazymatch type of M with munch ?W ?mi ?mc =>
      lazymatch type of H with
      | boxed (ro_cells _ _ ?A ?cs) => assert (H' : ro_cells rsegs mc A cs); [apply (ro_cells_transport rsegs W mi mc A cs H M); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (bytes_at _ _ ?A ?bs) => assert (H' : bytes_at rsegs mc A bs); [apply (bytes_at_transport rsegs W mi mc A bs H M); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (rw_cells _ _ ?A ?cs) => assert (H' : rw_cells rsegs mc A cs); [apply (rw_cells_transport rsegs W mi mc A cs H M WMH); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (u8arr _ _ ?A ?bs) => assert (H' : u8arr rsegs mc A bs); [apply (u8arr_transport rsegs W mi mc A bs H M WMH); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (u64arr _ _ ?A ?ws) => assert (H' : u64arr rsegs mc A ws); [apply (u64arr_transport rsegs W mi mc A ws H M WMH); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      end end.
    (* [comment removed for export] *)
    pose proof (munch_refl (alloc_hit_W sp thr c AB n q r8 d e n0 f0) m) as MU. unfold alloc_hit_W in MU.
    pose proof (munch_refl (alloc_hit_Wc sp thr AB n q r8 d n0 f0) m) as MUc. unfold alloc_hit_Wc in MUc.
    (* [comment removed for export] *)
    lazymatch type of MUc with munch ?Wc m m =>
      assert (Dsh : forall A k, 0 <= k -> q + 2147450880 <= A -> A + k <= q + r8 + 2147450880 -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; unbox_places; small_ctx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia);
      assert (Dstk : forall A k, 0 <= k -> bv_unsigned sp <= A -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA'; cbn [disjoint_from]; unbox_places; small_ctx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia);
      assert (Dthr : forall A k, 0 <= k -> thr <= A -> A + k <= thr + 208 -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; unbox_places; small_ctx;
            pose proof SEP_thr as X1; pose proof SEP_n0t as X2; pose proof SEP_f0t as X3;
            unfold apart in X1, X2, X3; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia);
      assert (Dctx : forall A k, 0 <= k -> ctx <= A -> A + k <= ctx + 0x10000 -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; unbox_places; small_ctx;
            pose proof SEP_ctx as X1; pose proof SEP_tc as X2; pose proof SEP_n0c as X3; pose proof SEP_f0c as X4;
            unfold apart in X1, X2, X3, X4; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia);
      assert (Dimg : forall A k, 0 <= k -> 0x10000 <= A -> (A + k <= 0x187288 \/ (0x5d72a8 <= A /\ A + k <= 0x60a000)) -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; unbox_places; small_ctx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia)
    end.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128)] m) as M0_1.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (thr + 208 + 2576, thr + 208 + 2584); (AB + rz_size n + -16, AB + rz_size n)] m) as M0_2.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (thr + 208 + 2576, thr + 208 + 2584); (AB + rz_size n + -16, AB + rz_size n);
                            (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                            (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] m) as M0_3.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (thr + 208 + 2576, thr + 208 + 2584); (AB + rz_size n + -16, AB + rz_size n);
                            (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                            (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
                            (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1)] m) as M0_4.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (thr + 208 + 2576, thr + 208 + 2584); (AB + rz_size n + -16, AB + rz_size n);
                            (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                            (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
                            (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                            (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096)] m) as M0_5.
    (* [comment removed for export] *)
    unfold boxed in INI, RSS.
    callx alloc_seg1a_spec.
    match goal with H : ?x = rz_log n |- _ => subst x end.
    try clear INI; try clear RSS.
    refresh RZm MUc WM RZm1.
    callx alloc_seg1b_spec cleaning (clear RZm1).
    refresh MUM MUc WM MUM1. refresh Cini MUc WM Cini1. refresh Ckey MUc WM Ckey1. refresh Ctsd MUc WM Ctsd1. refresh Cctx MUc WM Cctx1. refresh Cthr2 MUc WM Cthr1.
    callx alloc_seg1c_spec cleaning (clear MUM1 Cini1 Ckey1 Ctsd1 Cctx1 Cthr1).
    (* [comment removed for export] *)
    refresh SBc MUc WM SBc1. refresh TH0 MUc WM TH01. refresh CT8 MUc WM CT81. refresh TRC MUc WM TRC1.
    refresh PC M0_1 WM PC0. refresh STA M0_1 WM STA0. refresh HDR M0_1 WM HDR0. clear PC STA HDR M0_1.
    callx (alloc_seg2_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj canfill ctx thr c cnt maxc sb AB ks) cleaning (clear SBc1 TH01 CT81 TRC1 PC0 STA0 HDR0).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128);
                              (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                              (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
                              (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                              (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096);
                              (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] mc) as M2_6;
      pose proof (wmono_refl rsegs mc) as WM2;
      lazymatch goal with H : rw_cells rsegs mc (thr + 208 + 80 * c) _ |- _ => rename H into PC2; box PC2 end;
      lazymatch goal with H : rw_cells rsegs mc (thr + 208 + 2576) _ |- _ => rename H into STA2'; box STA2' end end.
    (* [comment removed for export] *)
    refresh TRC MUc WM TRC1. refresh TRB MUc WM TRB1. refresh SHA MUc WM SHA1.
    refresh Ccan MUc WM Ccan1. refresh Cgotcf MUc WM Cgotcf1. refresh Cthr MUc WM Cthr1. refresh Cgotsh MUc WM Cgotsh1. refresh Cshoff MUc WM Cshoff1.
    refresh Cgotmid MUc WM Cgotmid1. refresh Cgotmide MUc WM Cgotmide1. refresh Cgothi MUc WM Cgothi1. refresh Chivars MUc WM Chivars1.
    refresh Cgotms MUc WM Cgotms1. refresh Creal MUc WM Creal1. refresh Cgotps MUc WM Cgotps1. refresh Cps MUc WM Cps1.
    refresh SHU M0_2 WM SHU0. clear SHU.
    (* [comment removed for export] *)
    lazymatch type of M0_2 with munch ?W2 m ?mc =>
      assert (DR1 : dr AL_pasan rsegs D n0 f0 mc) by
        (eapply (DRF D m mc DR); intros a Ha; apply (M0_2 (Z_to_bv 64 a)); rewrite unsigned_lit;
         [| unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha; unbox_places; lia];
         unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha;
         cbn [outside]; destruct Ha as [Ha|[Ha|Ha]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply outside_of_disj; slia_big) end.
    clear M0_2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with H : rw_cells rsegs mc (AB + rz_size n + -16) _ |- _ => rename H into HDR2 end end.
    callx (alloc_seg3_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj thr c sb AB q r8 d e n0 f0 _ _ _ D k olds dr)
      cleaning (clear TRC1 TRB1 SHA1 Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1 DR1 HDR2 SHU0).
    (* [comment removed for export] *)
    lazymatch goal with H : dr _ _ _ n0 f0 ?mdx |- _ => rename H into DRd;
      lazymatch goal with H2 : munch ?Wd mdx ?mc |- _ =>
        apply (munch_weaken Wd (alloc_hit_W2 sp thr c AB n q r8 d e)) in H2;
        [ rename H2 into MUd; unfold alloc_hit_W2 in MUd
        | unfold sub_fp, alloc_hit_W2; cbn [outside]; intros a Ho; slia ] end end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                              (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096)] mc) as M3_5;
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                              (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096);
                              (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] mc) as M3_6;
      pose proof (wmono_refl rsegs mc) as WM3;
      lazymatch goal with H : rw_cells rsegs mc (AB + rz_size n + -16) _ |- _ => rename H into HDR3; cbv zeta in HDR3; box HDR3 end;
      lazymatch goal with H : bytes_at rsegs mc (q + r8 + kShadowOffset) _ |- _ => rename H into SHZ3; box SHZ3 end;
      lazymatch goal with H : wr_at rsegs mc (q + r8 + kShadowOffset) _ |- _ => rename H into SHW3; box SHW3 end end.
    (* [comment removed for export] *)
    refresh AF1 MUc WM AF1x. refresh AF2 MUc WM AF2x.
    refresh Ccan MUc WM Ccan1. refresh Cgotcf MUc WM Cgotcf1. refresh Cthr MUc WM Cthr1. refresh Cgotsh MUc WM Cgotsh1. refresh Cshoff MUc WM Cshoff1.
    refresh Cgotmid MUc WM Cgotmid1. refresh Cgotmide MUc WM Cgotmide1. refresh Cgothi MUc WM Cgothi1. refresh Chivars MUc WM Chivars1.
    refresh Cgotms MUc WM Cgotms1. refresh Creal MUc WM Creal1. refresh Cgotps MUc WM Cgotps1. refresh Cps MUc WM Cps1.
    lazymatch type of M0_3 with munch ?W3 m ?mc =>
      assert (SHP3 : e <> 0 -> rw_cells rsegs mc (q + r8 + d + kShadowOffset) [C1 oldp]) by
        (intros NE; apply (rw_cells_transport rsegs W3 m mc _ _ (SHP NE) M0_3 WM); disj) end.
    clear M0_3.
    callx (alloc_seg4_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj thr c sb AB q r8 d e oldp)
      cleaning (clear AF1x AF2x Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1 SHP3).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8);
                              (AB + rz_size n, AB + rz_size n + Z.min n 4096); (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] mc) as M4_6;
      pose proof (wmono_refl rsegs mc) as WM4;
      lazymatch goal with H : e <> 0 -> rw_cells rsegs mc _ _ |- _ => rename H into SHE4 end end.
    (* [comment removed for export] *)
    refresh AF1 MUc WM AF1y. refresh AF44 MUc WM AF44y. refresh AF52 MUc WM AF52y.
    refresh Cini MUc WM Cini1. refresh Ckey MUc WM Ckey1. refresh Ctsd MUc WM Ctsd1. refresh Cctx MUc WM Cctx1. refresh Cthr2 MUc WM Cthr1x.
    refresh Ccan MUc WM Ccan1. refresh Cgotcf MUc WM Cgotcf1. refresh Cthr MUc WM Cthr1. refresh Cgotsh MUc WM Cgotsh1. refresh Cshoff MUc WM Cshoff1.
    refresh Cgotmid MUc WM Cgotmid1. refresh Cgotmide MUc WM Cgotmide1. refresh Cgothi MUc WM Cgothi1. refresh Chivars MUc WM Chivars1.
    refresh Cgotms MUc WM Cgotms1. refresh Creal MUc WM Creal1. refresh Cgotps MUc WM Cgotps1. refresh Cps MUc WM Cps1.
    (* [comment removed for export] *)
    lazymatch type of M0_4 with munch ?W04 _ _ =>
      first [ assert (D4thr : forall A k, 0 <= k -> thr + 2800 <= A -> A + k <= thr + 4096 -> disjoint_from W04 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D4thr not proved" ];
      first [ assert (D4ab : forall A k, 0 <= k -> AB + rz_size n <= A -> A + k <= sb + 2^37 -> disjoint_from W04 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D4ab not proved" ] end.
    refresh STS M0_4 WM STS0. refresh STA2 M0_4 WM STA20. refresh USR M0_4 WM USR0. clear STS STA2 USR M0_4. try clear D4thr. try clear D4ab.
    callx (alloc_seg5_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj canfill tsd ctx thr c sb AB)
      cleaning (clear AF1y AF44y AF52y Cini1 Ckey1 Ctsd1 Cctx1 Cthr1x Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1 STS0 STA20 USR0).
    (* [comment removed for export] *)
    refresh LS1 MUc WM LS1x. refresh LS2 MUc WM LS2x. refresh HK MUc WM HKx.
    assert (RZ32 : rz_size n <> 16 -> 32 <= rz_size n) by (pose proof (rz_size_cases n) as X; clear - X; lia).   (* [comment removed for export] *)
    lazymatch type of M0_5 with munch ?W5 m ?mc =>
      assert (ABH5 : rz_size n <> 16 -> rw_cells rsegs mc AB [C8 j0; C8 j1]) by
        (intros NE; pose proof (RZ32 NE) as RZ32'; apply (rw_cells_transport rsegs W5 m mc _ _ (ABH NE) M0_5 WM); disj) end.
    clear M0_5.
    refresh HDR3 M3_5 WM3 HDR5. clear HDR3 M3_5.
    pose proof (b1_mid_range (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as B1MR.
    callx (alloc_seg6_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj canfill thr c sb AB (b1_mid (bv_unsigned b1w)) (snd (depot_putC D k)))
      cleaning (clear LS1x LS2x HKx ABH5 HDR5).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of M2_6 with munch ?W26 _ _ =>
      first [ assert (D26thr : forall A k, 0 <= k -> thr <= A -> A + k <= thr + 2800 -> disjoint_from W26 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D26thr not proved" ] end.
    refresh PC2 M2_6 WM2 PCf. refresh STA2' M2_6 WM2 STAf.
    lazymatch type of M3_6 with munch ?W36 ?m3 ?mc =>
      assert (SHZf : bytes_at rsegs mc (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))) by
        (unfold boxed in SHZ3; apply (bytes_at_transport rsegs W36 m3 mc _ _ SHZ3 M3_6); cbn [disjoint_from]; rewrite repeat_length, Z2Nat.id by lia; slia) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (SHWf : wr_at rsegs mc (q + r8 + kShadowOffset) d) by (unfold boxed in SHW3; exact (wr_at_transport rsegs _ mc _ _ SHW3 WM3));
      assert (SHEf : e <> 0 -> rw_cells rsegs mc (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)]) by
        (intros NE; lazymatch type of M4_6 with munch ?W46 ?m4 mc =>
           apply (rw_cells_transport rsegs W46 m4 mc _ _ (SHE4 NE) M4_6 WM4); disj end) end.
    apply evt_done. unfold alloc_hit_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split; [exact MU|].
    split; [exact WM|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    all: first [eassumption | rewrite <- ?KSO; eassumption].
  Qed.
End AllocHit.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
