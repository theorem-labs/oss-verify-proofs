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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Export ARt_swar.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition lma_entry : Z := 0x3bad4.
Definition lma_mapret : Z := 0x3bb90.
Definition lma_estest : Z := 0x3bd34.
Definition lma_tail : Z := 0x3bd38.
Definition lma_espost : Z := 0x3bf30.
Definition mmapordie_entry : Z := 0x6c23c.
Definition mapordie_entry : Z := 0x74a0c.
Definition LMA : Z := 0xb1598.
Definition LSTAT : Z := 0xb1808.
Definition lma_name : Z := 0x1981a.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lma_frame (scr : list byte) (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 scr; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition poison0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size value lo : Z) (old : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz addr -> a1 = wz size -> a2 = wz value ->
    addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> pz0_in addr size -> addr + size + 8 <= 2^47 ->
    0 <= value < 256 -> (value = 0 -> size / 8 < 2^45) ->
    poison_consts m ->
    rw_cells rsegs m (sh addr) [CB (Z.to_nat (size / 8)) old] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size value lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz poison_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lma_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo size pn : Z) (Q : machine_state -> Prop),
    let ms := round_up size 4096 + 4096 in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> alloc_ceiling <= lo ->
    a1 = wz LSTAT -> a2 = wz size -> a3 = wz 8 ->
    1 <= size <= 2^40 -> size mod 8 = 0 ->
    ro_cells rsegs m LMA [C8 (wz 4096)] -> ro_cells rsegs m 0xa8b58 [C8 (wz pn)] -> ro_cells rsegs m pn [C8 (wz lma_name)] ->
    0 <= pn -> pn + 8 <= kHighMemBeg ->
    (forall (a2' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -96) (lma_frame scr s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 96) ->
        evt rsegs Q (MS (mkR (wz lma_mapret) (wz (bv_unsigned sp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA)
                            (wz ms) (wz lma_name) a2' (wz 8) a4 a5 a6 a7
                            (wz ms) (wz size) s4 (wz 8) s6 s7 (wz 7) s9 s10 s11 t3 t4 t5 t6)
                        F (wz mmapordie_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz LMA) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz lma_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition lma_null_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (scr : list byte)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp - 96) -> lo <= usp - 96 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    rw_cells rsegs m (usp + -96) (lma_frame scr s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 0) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 96, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp)
        (MS (mkR ra (wz (usp + -96)) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz lma_mapret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lma_mid_stmt : Prop :=
  poison_stmt -> poison0_stmt -> thread_stats_stmt ->
  forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo size mb k tsd ctx thr nch nres : Z) (scr old1 old2 : list byte) (j0 j1 j2 mm72 mm80 : word) (lk1 lk2 : Z)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    let ms := 4096 * k in let ue := mb + 4096 + size in let tl := ms - 4096 - size in
    mem_inv rsegs m -> stk rsegs m lo (usp - 96) -> lo <= usp - 96 - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    1 <= size -> size mod 8 = 0 -> 0 <= tl < 4096 -> 2 <= k <= 2^19 + 16 ->
    aobj mb ms -> mb + ms <= alloc_ceiling -> mb mod 4096 = 0 ->
    0 <= nch < 2^20 -> 0 <= nres < 2^64 -> 0 <= lk1 < 256 -> 0 <= lk2 < 2^15 ->
    poison_consts m -> thread_cells m tp tsd ctx thr -> bv_unsigned tp <= kShadowOffset -> tsd + 8 <= kShadowOffset ->
    (mb + ms <= thr \/ thr + 4096 <= mb) ->
    rw_cells rsegs m (usp + -96) (lma_frame scr s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    ro_cells rsegs m LMA [C8 (wz 4096)] ->
    rw_cells rsegs m mb [C8 j0; C8 j1; C8 j2] ->
    rw_cells rsegs m (sh mb) [CB 512 old1] -> rw_cells rsegs m (sh ue) [CB (Z.to_nat (tl / 8)) old2] ->
    rw_cells rsegs m (thr + off_th_stats + 72) [C8 mm72; C8 mm80] ->
    rw_cells rsegs m (LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 lk1); C2 (wz lk2)] ->
    rw_cells rsegs m (LMA + 48) [C8 (wz nres); C8 (wz nch)] ->
    (forall (ra' t0' t1' t2' a1' a2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        0 <= lma_lz ms < 64 ->
        rw_cells rsegs m' (usp + -96) (lma_frame scr s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' mb [C8 (wz mb); C8 (wz ms); C8 (wz size)] ->
        bytes_at rsegs m' (sh mb) (repeat (Z_to_bv 8 250) 512) -> bytes_at rsegs m' (sh ue) (repeat (Z_to_bv 8 250) (Z.to_nat (tl / 8))) ->
        rw_cells rsegs m' (thr + off_th_stats + 72) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + ms))] ->
        rw_cells rsegs m' (LMA + 616) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 lk1); C2 (wz lk2)] ->
        rw_cells rsegs m' (LMA + 48) [C8 (wz nres); C8 (wz nch)] ->
        munch [(usp - 96 - 64, usp - 96); (sh mb, sh mb + 512); (sh ue, sh ue + tl / 8); (mb, mb + 24);
               (thr + off_th_stats + 72, thr + off_th_stats + 88); (LMA + 616, LMA + 620)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp - 96) ->
        evt rsegs Q (MS (mkR ra' (wz (usp + -96)) gp tp t0' t1' t2' (wz LSTAT) (wz LMA)
                            (wz (mb + 4096)) a1' a2' (wz nch) (wz nres) a5' a6' a7'
                            (wz ms) (wz (lma_lz ms)) (wz mb) (wz mb) (wz (mb + ms)) (wz ue) (wz 7) (wz (mb + 4096)) s10 s11 t3' t4' t5' t6')
                        F (wz lma_estest) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA) (wz mb) a1 a2 a3 a4 a5 a6 a7
                        (wz ms) (wz size) s4 (wz 8) s6 s7 (wz 7) s9 s10 s11 t3 t4 t5 t6)
                    F (wz lma_mapret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lma_esp_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp n pa res : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> 0 <= n < 2^20 -> 0 <= pa -> pa + 8 * n + 8 <= 2^47 -> 0 <= res < 2^64 ->
    ro_cells rsegs m (LMA + 16) [C8 (wz pa)] ->
    evt rsegs Q (MS (mkR (wz lma_espost) (wz (usp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA)
                        (wz (LMA + 16)) (wz (pa + 8 * n)) (wz 0x20000) (wz 0) (wz (LMA + 16)) a5 a6 a7
                        s2 s3 (wz res) s5 s6 s7 s8 (wz res) s10 s11 t3 t4 t5 t6)
                    F (wz mapordie_entry) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA) (wz res) a1 a2 (wz n) (wz n) a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 (wz res) s10 s11 t3 t4 t5 t6)
                    F (wz lma_estest) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition lma_espost_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp n res : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> 0 <= n < 2^20 -> 0 <= res < 2^64 ->
    rw_cells rsegs m (LMA + 48) [C8 (wz n); C8 (wz n)] ->
    (forall (a1' a2' : word) (m' : word -> option byte),
        rw_cells rsegs m' (LMA + 48) [C8 (wz (n + 0x4000)); C8 (wz n)] ->
        munch [(LMA + 48, LMA + 56)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        evt rsegs Q (MS (mkR ra (wz (usp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA)
                            (wz res) a1' a2' (wz n) a4 a5 a6 a7
                            s2 s3 (wz res) s5 s6 s7 s8 (wz res) s10 s11 t3 t4 t5 t6)
                        F (wz lma_tail) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA) a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 (wz res) s5 s6 s7 s8 (wz res) s10 s11 t3 t4 t5 t6)
                    F (wz lma_espost) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lma_tail_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo mb ms n nres lz pa : Z) (na nf ca mx cidx pan sta stm : word) (bsl : list word) (scr : list byte) (lk1 lk2 : Z) (cs : byte)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    let idx := Z.lxor lz 63 in
    mem_inv rsegs m -> stk rsegs m lo (usp - 96) -> lo <= usp - 96 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    0 <= lz < 64 -> 0 <= n < nres -> nres < 2^20 -> aobj pa (8 * nres) -> pa + 8 * nres <= alloc_ceiling -> pa mod 8 = 0 ->
    aobj mb ms -> mb + ms <= alloc_ceiling -> mb mod 4096 = 0 -> 8192 <= ms < 2^40 -> length bsl = 64%nat ->
    (mb + ms <= pa \/ pa + 8 * nres <= mb) ->
    rw_cells rsegs m (usp + -96) (lma_frame scr s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    ro_cells rsegs m (LMA + 8) [C8 (wz pa)] ->
    rw_cells rsegs m (LMA + 48) [C8 (wz nres); C8 (wz n); C1 cs] ->
    rw_cells rsegs m (LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)] ->
    rw_cells rsegs m (LMA + 616) [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 lk1); C2 (wz lk2)] ->
    rw_cells rsegs m (mb + 24) [C8 cidx] ->
    rw_cells rsegs m (pa + 8 * n) [C8 pan] ->
    rw_cells rsegs m (LSTAT + 16) [C8 sta; C8 stm] ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ca' mx' sta' stm' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz (mb + 4096)) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 96, usp); (LMA + 48, LMA + 65); (LMA + 72, LMA + 616); (LMA + 616, LMA + 617);
                           (mb + 24, mb + 32); (pa + 8 * n, pa + 8 * n + 8); (LSTAT + 16, LSTAT + 32)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' (LMA + 48) [C8 (wz nres); C8 (wz (n + 1)); C1 (Z_to_bv 8 0)]
                 /\ rw_cells rsegs m' (LMA + 72) [C8 (wz (bv_unsigned na + 1)); C8 nf; C8 ca'; C8 mx';
                                                  CB 512 (u64s (upd bsl (Z.to_nat idx) (wz (bv_unsigned (nth (Z.to_nat idx) bsl (wz 0)) + 1))))]
                 /\ rw_cells rsegs m' (LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 lk1); C2 (wz lk2)]
                 /\ rw_cells rsegs m' (mb + 24) [C8 (wz n)]
                 /\ rw_cells rsegs m' (pa + 8 * n) [C8 (wz mb)]
                 /\ rw_cells rsegs m' (LSTAT + 16) [C8 sta'; C8 stm'])
        (MS (mkR ra (wz (usp + -96)) gp tp t0 t1 t2 (wz LSTAT) (wz LMA) (wz (mb + 4096)) a1 a2 (wz n) a4 a5 a6 a7
                 (wz ms) (wz lz) s4 (wz mb) s6 s7 (wz 7) (wz (mb + 4096)) s10 s11 t3 t4 t5 t6)
            F (wz lma_tail) fc None m (seg_rom rsegs)).

End CEIL.
