(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_depot_defs R_depot_put R_asan_defs R_deallocate.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma qchunk_spec_L : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (M n b1 B TCX T lo : Z) (ctx w : word) (D : depot) (BK : list Z) (DNB SSB : Z)
    (ws rest : list word),
  (0x6e0000 <= M)%Z -> (M + 24 <= lo)%Z -> (1 <= n < 2^32)%Z -> (0 <= b1 < 256)%Z ->
  rw_cells bsegs m M [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  rw_cells bsegs m (M + 16) [C8 w] ->
  thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= lo)%Z -> (0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x6e0000 <= T)%Z ->
  (T + 4096 <= lo)%Z ->
  rw_cells bsegs m T [C8 (Z_to_bv 64 TCX)] -> rw_cells bsegs m (TCX + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m B [C8 (Z_to_bv 64 (B + 16)); C8 (Z_to_bv 64 (Z.of_nat (length ws)))] ->
  u64arr bsegs m (B + 16) (ws ++ rest) -> length (ws ++ rest) = 255%nat -> (1 <= Z.of_nat (length ws) <= 254)%Z ->
  depot_ok D DNB SSB lo -> depot_rep D BK DNB SSB m -> (d_tot D + Z.of_nat (length ws) + 1 < 2^20)%Z ->
  In (bkt (depot_hash (map bv_unsigned ws))) BK -> (d_n D + 2 < 2^16)%Z ->
  (M + 24 <= DNB \/ DNB + 2 ^ 20 <= M)%Z -> (M + 24 <= SSB \/ SSB + 2 ^ 23 <= M)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 272)%Z -> (bv_unsigned sp <= B)%Z -> (B + 2064 <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (qchunk_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc M n B T D BK DNB SSB ws rest lo m)
    (MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 INST) (Z_to_bv 64 M) (Z_to_bv 64 (M + 16)) (Z_to_bv 64 B)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 qchunk_entry') fc None m (seg_rom bsegs)).
Proof.
  intros until rest. intros HM HMl Hn Hb1 HD UW TC HTCX HTCXl HT HTi HTl TC0 TC8 BC TB HL255 Hsz OK REP Hroom HBK Hn2 HMD HMS
    ST HLO HB HB2 MI.
  unfold qchunk_entry', kHighShadowEnd, INST, g_instance in *.
  destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
  move KI at bottom. move K0 at bottom. move TS at bottom. move T0 at bottom.
  apply box in REP.
  pose proof OK as (_ & _ & _ & HD1 & HD2 & HS1 & HS2 & _).
  pose proof (munch_refl [(M + 16, M + 24); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20); (s_total, s_total + 8);
             (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MUh.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 zstep.
  do 3 zstep. zstep. ifF.
  do 3 zstep.
  sp_facts.
  call (get_current_thread_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  all: rewrite ?Esp in *; try lia; try eassumption.
  all: lazymatch goal with
       | |- thread_cells _ _ _ =>
           unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
           split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
       | |- evt _ _ _ => idtac
       end.
  zstep. ifF.
  do 6 zstep.
  zstep.
  let mm := amem in
  pose proof (depot_rep_frame D BK DNB SSB lo _ m mm (unbox _ REP) OK MUh WM ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)
                ltac:(cbn [disjoint_from]; lia) ltac:(cbn [disjoint_from]; lia)) as REPm.
  clear MUh REP.
  call (depot_put_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ D BK DNB SSB (B + 16)%Z lo ws rest).
  all: rewrite ?Esp in *; try lia; try eassumption.
  let mm := amem in
  pose proof (munch_refl [(M + 16, M + 24)]%Z mm) as MUd; pose proof (wmono_refl bsegs mm) as WMd.
  assert (RID : (0 <= snd (depot_put D (map bv_unsigned ws)) < 2^16)%Z).
  { pose proof (depot_put_id D (map bv_unsigned ws)) as P. pose proof (depot_put_n D (map bv_unsigned ws)) as P2.
    destruct (depot_put D (map bv_unsigned ws)) as [D' id] eqn:E. cbn [fst snd] in *. unfold d_n in *. lia. }
  assert (EZ : Z.shiftr (Z.land (Z.shiftl (snd (depot_put D (map bv_unsigned ws))) 32) 18446744073709551615) 32
               = snd (depot_put D (map bv_unsigned ws))).
  { rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones, Z.mod_small by lia.
    rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }
  assert (EZ2 : Z.land (snd (depot_put D (map bv_unsigned ws))) 4294967295 = snd (depot_put D (map bv_unsigned ws))).
  { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity. }
  do 3 zstep. fold_reg 19%Z. rewrite ?EZ, ?EZ2.
  zstep. rewrite ?Z.lor_0_l, ?EZ2.
  zstep.
  do 10 zstep.
  change (Z.land (Z.shiftl (bv_unsigned (zx16 (Z_to_bv 64 0))) 32) 18446744073709551615) with 0%Z.
  rewrite Z.lor_0_l, zx32_small, unsigned_lit by lia.
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : stk bsegs mm _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
  zstep. zstep.
  finish.
  lazymatch goal with H : depot_rep _ BK DNB SSB ?m2 |- depot_rep _ BK DNB SSB ?mm =>
    apply (depot_rep_frame _ BK DNB SSB lo _ m2 mm H
             (qc_depot_ok_put_ok D (map bv_unsigned ws) DNB SSB lo OK Hn2 ltac:(rewrite map_length; lia)) MUd WMd);
      cbn [disjoint_from]; lia end.
Qed.
