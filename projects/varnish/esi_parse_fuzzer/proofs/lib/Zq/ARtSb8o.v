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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtS4t2 ARtSoqz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition pop_mapret : Z := 0x3c474.
Definition pop_efasret : Z := 0x3c4e8.
Definition mapcb_entry : Z := 0x748c0.
Definition pop_name : Z := 0x172eb.     (* [comment removed for export] *)
Definition kUserMap : Z := 0x40000.

(* [comment removed for export] *)
Definition pop_frame (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition carved (au size nc : Z) : list word :=
  map (fun j => Z_to_bv 64 ((au + (nc - 1 - Z.of_nat j) * size) / 16)) (seq 0 (Z.to_nat nc)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition pop_fit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo R sb c req stat nf au mu : Z) (Q : machine_state -> Prop),
    let size := class_size c in let nc := (mu - au) / size in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a1 = wz stat -> a2 = wz c -> a3 = wz R -> a4 = wz req ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    1 <= c <= 30 -> kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling ->
    0 <= stat < 2^64 -> 1 <= req <= 8 -> 0 <= nf < 2^27 -> 0 <= au -> au + req * size <= mu -> mu <= 2^32 ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 32) [C8 (wz au)] -> rw_cells rsegs m (R + 48) [C8 (wz mu)] ->
    (forall (a5' a6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 64) ->
        evt rsegs Q (MS (mkR (wz pop_efasret) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + nc))
                            (wz 0xb1558) (wz R) (wz (sb + c * 4294967296)) (wz (nf + nc)) (wz req) a5' a6' a7
                            (wz (sb + c * 4294967296)) (wz nc) (wz (mu - au)) (wz size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz efas_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1558) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz pop_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_map_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo R sb c req stat nf au mu : Z) (Q : machine_state -> Prop),
    let size := class_size c in let ums := round_up (au + req * size - mu) kUserMap in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a1 = wz stat -> a2 = wz c -> a3 = wz R -> a4 = wz req ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] -> ro_cells rsegs m 0xb1580 [C4 (wz 4294967295)] -> ro_cells rsegs m 0xb1590 [C1 (Z_to_bv 8 0)] ->
    1 <= c <= 30 -> kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling ->
    0 <= stat < 2^64 -> 1 <= req <= 8 -> 0 <= nf < 2^27 -> 0 <= au <= mu -> mu < au + req * size -> mu mod kUserMap = 0 ->
    mu + ums <= 3758096384 ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 32) [C8 (wz au)] -> rw_cells rsegs m (R + 48) [C8 (wz mu)] ->
    rw_cells rsegs m (R + 56) [C8 (wz 0)] ->
    (forall (a5' a6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -64) (pop_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
        munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 64) ->
        evt rsegs Q (MS (mkR (wz pop_mapret) (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz stat)
                            (wz 0xb1558) (wz (sb + c * 4294967296 + mu)) (wz ums) (wz pop_name) (wz req) a5' a6' a7
                            (wz (sb + c * 4294967296)) (wz ums) (wz (sb + c * 4294967296 + mu)) (wz size) (wz 0xb1558) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz mapcb_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0xb1558) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz pop_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_mapped_stmt : Prop :=
  poison_stmt -> thread_stats_stmt ->
  forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo R sb c req stat nf au mu ums tsd ctx thr : Z) (old : list byte) (statm mm72 mm80 : word)
         (s6v s5v s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    let size := class_size c in let beg := sb + c * 4294967296 + mu in let mu' := mu + ums in let nc := (mu' - au) / size in
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    1 <= c <= 30 -> kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 ->
    aobj stat 32 -> stat + 32 <= alloc_ceiling -> (stat + 24) mod 8 = 0 ->
    1 <= req <= 8 -> 0 <= nf < 2^27 -> 0 <= au <= mu -> beg mod 8 = 0 -> kUserMap <= ums -> ums mod 8 = 0 ->
    mu + ums <= 3758096384 -> au + req * size <= mu' ->
    poison_consts m -> thread_cells m tp tsd ctx thr -> bv_unsigned tp <= kShadowOffset -> tsd + 8 <= kShadowOffset ->
    (R + 128 <= thr \/ thr + 4096 <= R) -> (stat + 32 <= thr + off_th_stats + 72 \/ thr + off_th_stats + 88 <= stat) ->
    (R + 128 <= stat \/ stat + 32 <= R) ->
    rw_cells rsegs m (usp + -64) (pop_frame s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 32) [C8 (wz au)] -> rw_cells rsegs m (R + 48) [C8 (wz mu)] ->
    rw_cells rsegs m (sh beg) [CB (Z.to_nat (ums / 8)) old] ->
    rw_cells rsegs m (thr + off_th_stats + 72) [C8 mm72; C8 mm80] ->
    rw_cells rsegs m (stat + 24) [C8 statm] ->
    (forall (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -64) (pop_frame s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (R + 16) [C8 (wz nf)] -> rw_cells rsegs m' (R + 32) [C8 (wz au)] -> rw_cells rsegs m' (R + 48) [C8 (wz mu')] ->
        bytes_at rsegs m' (sh beg) (repeat (Z_to_bv 8 250) (Z.to_nat (ums / 8))) ->
        rw_cells rsegs m' (thr + off_th_stats + 72) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + ums))] ->
        (exists statm', rw_cells rsegs m' (stat + 24) [C8 statm']) ->
        munch [(usp - 64 - 64, usp - 64); (sh beg, sh beg + ums / 8); (thr + off_th_stats + 72, thr + off_th_stats + 88);
               (stat + 24, stat + 32); (R + 48, R + 56)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp - 64) ->
        evt rsegs Q (MS (mkR (wz pop_efasret) (wz (usp + -64)) gp tp t0' t1' t2' (wz R) (wz (nf + nc))
                            (wz 0xb1558) (wz R) (wz (sb + c * 4294967296)) (wz (nf + nc)) a4' a5' a6' a7'
                            (wz (sb + c * 4294967296)) (wz nc) (wz (mu' - au)) (wz size) (wz 0xb1558) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz efas_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz pop_mapret) (wz (usp + -64)) gp tp t0 t1 t2 (wz R) (wz stat)
                        (wz beg) a1 a2 a3 a4 a5 a6 a7
                        (wz (sb + c * 4294967296)) (wz ums) (wz beg) (wz size) (wz 0xb1558) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz pop_mapret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_carve_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo R sb c nf au ma r : Z) (junk : list word) (ex : byte)
         (s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    let size := class_size c in let nc := ma / size in let fa := free_array_of sb c in
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    1 <= c <= 30 -> kHighMemBeg <= R -> R + 128 <= alloc_ceiling -> kHighMemBeg <= sb -> sb + 2^37 <= alloc_ceiling -> sb mod 4096 = 0 ->
    0 <= nf -> nf + nc < 2^27 -> 0 <= au -> 0 <= ma -> au + ma <= 3758096384 -> au mod 16 = 0 -> r <> 0 -> 0 <= r < 2^64 ->
    length junk = Z.to_nat nc ->
    (R + 128 <= sb \/ sb + 2^37 <= R) ->
    rw_cells rsegs m (usp + -64) (pop_frame s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 32) [C8 (wz au); C8 (wz 0); C8 (wz (au + ma)); C8 (wz 0)] ->
    rw_cells rsegs m (R + 68) [C1 ex] ->
    u32arr rsegs m (fa + 4 * nf) junk ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 1) a1' a2' a3' a4' a5' a6' a7'
                              s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 64, usp); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69); (fa + 4 * nf, fa + 4 * nf + 4 * nc)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
                 /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf + nc))]
                 /\ rw_cells rsegs m' (R + 32) [C8 (wz (au + nc * size)); C8 (wz 0); C8 (wz (au + ma)); C8 (wz 0)]
                 /\ rw_cells rsegs m' (R + 68) [C1 (Z_to_bv 8 0)]
                 /\ u32arr rsegs m' (fa + 4 * nf) (carved au size nc))
        (MS (mkR ra (wz (usp + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + nc)) (wz r) a1 a2 a3 a4 a5 a6 a7
                 (wz (sb + c * 4294967296)) (wz nc) (wz ma) (wz size) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz pop_efasret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_fail_post (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (usp lo : Z)
    (s7 s8 s9 s10 s11 : word) (s6v s5v s4v s3v s2v s1v s0v ra0 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
     ms' = MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz 0) a1' a2' a3' a4' a5' a6' a7'
                  s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra0) fc None m' (seg_rom rsegs)
     /\ munch [(usp - 64, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp.
Definition pop_fail64_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    rw_cells rsegs m (usp + -64) (pop_frame s6v s5v s4v s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (pop_fail_post gp tp F fc usp lo s7 s8 s9 s10 s11 s6v s5v s4v s3v s2v s1v s0v ra0 m)
        (MS (mkR ra (wz (usp + -64)) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz pop_mapret) fc None m (seg_rom rsegs)).
Definition pop_faild8_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo : Z) (s6v s5v s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp - 64) -> lo <= usp - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    rw_cells rsegs m (usp + -64) (pop_frame s6v s5v s4v s3v s2v s1v s0v ra0) -> bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (pop_fail_post gp tp F fc usp lo s7 s8 s9 s10 s11 s6v s5v s4v s3v s2v s1v s0v ra0 m)
        (MS (mkR ra (wz (usp + -64)) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz pop_efasret) fc None m (seg_rom rsegs)).

End CEIL.
