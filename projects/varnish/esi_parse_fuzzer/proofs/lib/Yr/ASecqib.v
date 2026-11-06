(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASechs3 ASech8k.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASech8k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section PT1a.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 128.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis SO : 0 < stkobj < 2^64.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis INI : ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)].
  Hypothesis RSS : ro_cells rsegs m 0x137622 [C1 (Z_to_bv 8 0)].
    Definition sec_seg1a_post : machine_state -> Prop := fun ms' =>
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

  Lemma sec_seg1a_spec : evt rsegs sec_seg1a_post
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 stkobj) (Z_to_bv 64 1) (Z_to_bv 64 canfill) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3719c) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg1a; try eassumption. intros. subst. apply evt_done. unfold sec_seg1a_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT1a.

Section PT1b.

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
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis RZm : ro_cells rsegs m 0xb2b80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis RZL : rzlog_stmt.
    Definition sec_seg1b_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37350) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128).

  Lemma sec_seg1b_spec : evt rsegs sec_seg1b_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 canfill) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) s8 (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37308) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg1b; try eassumption. intros. subst. apply evt_done. unfold sec_seg1b_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT1b.

Section PT1c.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj tsd ctx thr : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis MUM : ro_cells rsegs m 0xb2b78 [C8 (Z_to_bv 64 (2^40))].
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis GT : get_thread_stmt.
    Definition sec_seg1c_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR (Z_to_bv 64 0x3743c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 8) a4' a5' a6' a7'
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3b91c) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128).

  Lemma sec_seg1c_spec : evt rsegs sec_seg1c_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (rz_log n)) (Z_to_bv 64 0x10000) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xffff) (Z_to_bv 64 7) (Z_to_bv 64 (0xb1d58 + 2047)) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37350) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg1c; try eassumption. intros. subst. apply evt_done. unfold sec_seg1c_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT1c.

Section PT2.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill ctx thr AB : Z) (b0w b1w : byte) (h2 w4 d8 trace sztag : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^32.
  Hypothesis SO : 0 < stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj AB (needed_size2 n) /\ AB + needed_size2 n <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_thr : thr + 4096 <= AB \/ AB + needed_size2 n <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= AB \/ AB + needed_size2 n <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis SOA : bv_unsigned sp <= stkobj.
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 trace; C8 sztag].
    Definition sec_seg2_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 n)
                 trace sztag a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032)) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37544) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2048)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 (b1_mid (bv_unsigned b1w))); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].

  Lemma sec_seg2_spec : evt rsegs sec_seg2_post
        (MS (mkR (Z_to_bv 64 0x3743c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj)
                 (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3743c) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg2; try eassumption. intros. subst. apply evt_done. unfold sec_seg2_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT2.

Section PT3.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr sb AB q d e dc ru n0 f0 : Z) (b0w : byte) (b1v : Z) (d8 : word)
            (D : list (list Z)) (k : list Z) (olds oll olt : list byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis SOA : bv_unsigned sp <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_sb : AB + 8 * ru <= sb \/ sb + 2^37 <= AB.
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : n0 + kDepotNodesBlock <= AB - 4096 \/ AB + 8 * ru <= n0.
  Hypothesis SEP_f0 : f0 + kStackStoreBlockBytes <= AB - 4096 \/ AB + 8 * ru <= f0.
  Hypothesis KL : (1 <= length k <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) k.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (Z_to_bv 64 (stkobj + 16)); C8 (Z_to_bv 64 (Z.of_nat (length k)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) k)).
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m 0xb1d98 [C8 (Z_to_bv 64 4096)].
  Hypothesis HSZ : ro_cells rsegs m (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed_size2 n))].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHT : rw_cells rsegs m (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt].
    Definition sec_seg3_post : machine_state -> Prop := fun ms' =>
    exists (m1 md : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    let id := snd (depot_putC D k) in
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37654) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    dr AL_pasan rsegs (fst (depot_putC D k)) n0 f0 md /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] md m1 /\
    wmono rsegs md m1 /\
    rw_cells rsegs m1 (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] /\
    bytes_at rsegs m1 (q + kShadowOffset) (repeat (Z_to_bv 8 250) 256) /\
    bytes_at rsegs m1 (q + 256 + dc + kShadowOffset) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc))) /\
    bytes_at rsegs m1 (q + 256 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d)) /\
    wr_at rsegs m1 (q + 256 + kShadowOffset) d.

  (* [comment removed for export] *)
End PT3.

Section PT4.

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
  Hypothesis ER : 0 < e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb2c0d [C1 (Z_to_bv 8 1)].  (* [comment removed for export] *)
  Hypothesis SHP : rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
    Definition sec_seg4_nz_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (AB + 2048 + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x376e8) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + 1)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (q + 256 + d + kShadowOffset) [C1 (Z_to_bv 8 e)].

  (* [comment removed for export] *)
End PT4.

Section PT4z.

  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (n d : Z).
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis NDE : n = 8 * d + 0.
    Definition sec_seg4_z_post : machine_state -> Prop := fun ms' => ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x376e8) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
End PT4z.

Section PT5.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr AB ru : Z) (v0 v1 v2 vl : word) (uj : list byte).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SEP_thr : thr + 4096 <= AB \/ AB + 8 * ru <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= AB \/ AB + 8 * ru <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TSDL : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Hypothesis AF44 : ro_cells rsegs m 0xb2be4 [C4 (Z_to_bv 64 4096)].   (* [comment removed for export] *)
  Hypothesis AF52 : ro_cells rsegs m 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].  (* [comment removed for export] *)
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
    Definition sec_seg5_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word),
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3787c) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2904, thr + 2912);
             (AB + 2048, AB + 2048 + 4096)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    rw_cells rsegs m1 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] /\
    rw_cells rsegs m1 (thr + 2904) [C8 (Z_to_bv 64 (bv_unsigned vl + 1))] /\
    rw_cells rsegs m1 (AB + 2048) [CB 4096%nat (fill_result canfill uj 4096%nat)].

  (* [comment removed for export] *)
End PT5.

Section PT6.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill thr AB ru b1v id : Z) (b0w : byte) (j0 j1 : word).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis LS1 : ro_cells rsegs m 0xa9df0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146e80 [C8 (Z_to_bv 64 0)].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
    Definition sec_seg6_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 (AB + 2048)) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2034); (AB, AB + 16)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp) /\
    rw_cells rsegs m1 (AB + 2032) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] /\
    rw_cells rsegs m1 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + 2032))].

  (* [comment removed for export] *)
End PT6.

Section PTnull.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s1 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo canfill : Z) (oomb : byte).
  Variables (sp : word) (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis OOM : rw_cells rsegs m 0x137620 [C1 oomb].
  Hypothesis MRN : ro_cells rsegs m 0x137621 [C1 (Z_to_bv 8 1)].
    Definition sec_null_post : machine_state -> Prop := fun ms' =>
    exists (m1 : word -> option byte) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x137620, 0x137621)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp) /\
    rw_cells rsegs m1 0x137620 [C1 (Z_to_bv 8 1)].

  (* [comment removed for export] *)
End PTnull.

