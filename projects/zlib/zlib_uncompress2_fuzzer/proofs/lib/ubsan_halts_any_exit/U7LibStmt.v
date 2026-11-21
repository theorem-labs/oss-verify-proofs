(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* uncompress's U9LibStmt (itself the plain 1.4 S9LibStmt moved by tools/gen_u9libstmt14.py) moved to uncompress2 by tools/reloc_u9u7.py, with uncompress2_z's s0 / s1 pointing at the uncompress2 frame's destLen / sourceLen copies (u+176 / u+168):
   U7 names, the 1.4 UBSan addresses, zfree in a3 at inflateEnd, and za's entry registers s2 = strm, s1 = 7176, s3 = len, s4 = left. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_halts_any_exit Require Export ZlibStmtBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

#[local] Abbreviation RSEGS := Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.

Definition U7_BUF    : Z := 0x341a0.
Definition U7_BUF_N  : Z := 0x40000.
Definition U7_INFL_N : Z := 7176.
Definition U7_WIN_N  : Z := 32768.
Definition U7_FRA    : Z := 1024.
Definition U7_ZWD    : Z := 320.
Definition U7_RO_LO  : Z := 0x10000.
Definition U7_RO_HI  : Z := 0x22000.
Definition U7_IMG_TOP : Z := 0x95000.
Definition U7_ZCALLOC : Z := 0x17d88.
Definition U7_ZCFREE  : Z := 0x17d98.
Definition U7_ZA     : Z := 0x151dc.
Definition U7_RA_II  : Z := 0x14e64.
Definition U7_T_ZW   : Z := 0x17b84.
Definition U7_ZB     : Z := 0x17b88.
Definition U7_T_ZE1  : Z := 0x17d50.
Definition U7_T_ZE2  : Z := 0x17d68.
Definition U7_ZC     : Z := 0x17d6c.
Definition U7_RA2    : Z := 0x14f24.   (* uncompress2_z after jal inflateEnd *)
Definition U7_HARN_RA : Z := 0x14fc0.
Definition U7_T_RET  : Z := 0x14c64.

Definition WA_U7 (u p : Z) : list (word * Z) :=
  [(Z_to_bv 64 (u - U7_FRA), U7_FRA + 112); (Z_to_bv 64 (u + 168), 8); (Z_to_bv 64 (u + 176), 8);
   (Z_to_bv 64 p, U7_INFL_N); (Z_to_bv 64 U7_BUF, U7_BUF_N)].

Definition in_fpw_U7 (u p q n : Z) (a : word) : Prop :=
  let x := bv_unsigned a in
  (u - U7_ZWD <= x < u + 208) \/ (p <= x < p + U7_INFL_N) \/ (U7_BUF <= x < U7_BUF + U7_BUF_N) \/ (q <= x < q + n).

Definition zw_local_stmt_U7 (zw_inv : ZWINV) : Prop :=
  forall u p q n zc sE sW (M M' : word -> option byte),
    (forall a, in_fpw_U7 u p q n a -> M' a = M a) -> zw_inv u p q n zc sE sW M -> zw_inv u p q n zc sE sW M'.

Definition lib_layout_U7 {RCa1 : RunCtx}  (zc : Z) (mem : word -> option byte) (u p q n : Z) : Prop :=
  u mod 16 = 0 /\ zc + U7_FRA <= u /\ u + 208 <= 2 ^ 47 /\ U7_IMG_TOP <= zc /\
  p mod 16 = 0 /\ 0 < p /\ p + U7_INFL_N <= zc /\
  (U7_BUF + U7_BUF_N <= p \/ p + U7_INFL_N <= U7_BUF) /\
  0 <= n < 2 ^ 26 /\ 1 <= q /\ q + n <= zc /\
  (q + n <= U7_BUF \/ U7_BUF + U7_BUF_N <= q) /\ (q + n <= p \/ p + U7_INFL_N <= q) /\
  (forall i, 0 <= i < n -> exists b, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (q + i)) 1 = Some [b]) /\
  (forall i, U7_RO_LO <= i < U7_RO_HI -> mem (Z_to_bv 64 i) = None) /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - U7_FRA)) (Z.to_nat (U7_FRA + 208)) = true /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 p) (Z.to_nat U7_INFL_N) = true /\
  (p + U7_INFL_N <= 0x10000 \/ U7_IMG_TOP <= p) /\
  (n = 0 \/ q + n <= 0x10000 \/ U7_IMG_TOP <= q).

Definition end_cells_U7 {RCa1 : RunCtx}  (mem : word -> option byte) (u p : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 U7_RA2) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 56)) 8 = Some (Z_to_le_bytes 8 p) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 U7_ZCFREE) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0).

(* uncompress2_z does not save s5, so the caller's s5 is carried with s6 .. s11 *) Definition S_ENTRY5 : list reg := [21]%bv ++ S_ENTRY. Definition end_regs_U7 (regs regs' : bvmap 5 word) (u blk : Z) (sE : list Z) : Prop :=
  getr regs' 13 = Z_to_bv 64 U7_ZCFREE /\   (* inflateEnd loads zfree into a3 *)
  getr regs' 11 = Z_to_bv 64 blk /\ getr regs' 10 = Z_to_bv 64 0 /\
  getr regs' 8 = Z_to_bv 64 (u) /\ getr regs' 2 = Z_to_bv 64 (u - 16) /\
  getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  sregs regs' S_ENTRY5 = sE.

Section CONTRACTS.
Context {RCa1 : RunCtx}.
Variable zw_inv : ZWINV.

Definition za_stmt_U7 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n zc : Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  getr regs 2 = Z_to_bv 64 (u - 32) -> getr regs 18 = Z_to_bv 64 (u) -> getr regs 9 = Z_to_bv 64 7176 -> getr regs 10 = pw ->
  getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 U7_BUF_N ->
  lib_layout_U7 zc mem u p q n ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 32)) 8 = Some (Z_to_le_bytes 8 U7_BUF) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 24)) 8 = Some (Z_to_le_bytes 8 (u + 168)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) 8 = Some (Z_to_le_bytes 8 (u + 176)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 U7_RA_II) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u)) 8 = Some (word_to_le_bytes 8 qw) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 64)) 8 = Some (Z_to_le_bytes 8 U7_ZCALLOC) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 U7_ZCFREE) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0) ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte) (pc' : Z),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U7_ZA) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_U7 u p)
    /\ (
           (pc' = U7_T_ZE2 /\ end_regs_U7 regs regs' u p (sregs regs S_ENTRY5) /\ end_cells_U7 mem' u p)
        \/
           (pc' = U7_T_ZW /\
            getr regs' 13 = Z_to_bv 64 U7_ZCALLOC /\ getr regs' 10 = Z_to_bv 64 0 /\
            getr regs' 11 = Z_to_bv 64 U7_WIN_N /\ getr regs' 12 = Z_to_bv 64 1 /\
            getr regs' 2 = Z_to_bv 64 (u - U7_ZWD) /\
            getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
            zw_inv u p q n zc (sregs regs S_ENTRY5) (sregs regs' S_ALL) mem')).

Definition zb_stmt_U7 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw ww : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  let w := bv_unsigned ww in
  getr regs 2 = Z_to_bv 64 (u - U7_ZWD) -> getr regs 10 = ww -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_U7 zc mem u p q n ->
  w mod 16 = 0 -> 0 < w -> w + U7_WIN_N <= zc ->
  (U7_BUF + U7_BUF_N <= w \/ w + U7_WIN_N <= U7_BUF) -> (p + U7_INFL_N <= w \/ w + U7_WIN_N <= p) ->
  (q + n <= w \/ w + U7_WIN_N <= q) ->
  (w + U7_WIN_N <= 0x10000 \/ U7_IMG_TOP <= w) ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem ww (Z.to_nat U7_WIN_N) = true ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U7_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 U7_T_ZE1) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_U7 u p ++ [(ww, U7_WIN_N)])
    /\ end_regs_U7 regs regs' u w sE /\ end_cells_U7 mem' u p.

Definition zb0_stmt_U7 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  getr regs 2 = Z_to_bv 64 (u - U7_ZWD) -> getr regs 10 = Z_to_bv 64 0 -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_U7 zc mem u p q n ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U7_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 U7_T_ZE2) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_U7 u p)
    /\ end_regs_U7 regs regs' u p sE /\ end_cells_U7 mem' u p.

End CONTRACTS.

Definition zc_stmt_U7 {RCa1 : RunCtx}  : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (v0 v1 v2 v3 v4 v5 : word),
  getr regs 2 = Z_to_bv 64 (u - 16) -> getr regs 8 = Z_to_bv 64 (u) ->
  u mod 16 = 0 -> U7_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) (Z.to_nat 224) = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 U7_RA2) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 152)) 8 = Some (Z_to_le_bytes 8 U7_HARN_RA) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 144)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 136)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 128)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 120)) 8 = Some (word_to_le_bytes 8 v3) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 112)) 8 = Some (word_to_le_bytes 8 v4) ->
  (* uncompress2_z saves ra and s0..s4 only (frame 160); v5 is kept, unused, so the arity is unchanged *)
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U7_ZC) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 U7_HARN_RA) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' [(Z_to_bv 64 (u + 56), 8)]
    /\ getr regs' 2 = Z_to_bv 64 (u + 160)
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2
    /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, In r ([3; 4]%bv ++ S_ENTRY) -> getr regs' r = getr regs r).

Record zlib_u2_contract_U7 {RCa1 : RunCtx}  : Type := ZU2C_U7 {
  zw_inv_U7   : ZWINV;
  zw_local_U7 : zw_local_stmt_U7 zw_inv_U7;
  run_za_U7   : za_stmt_U7 zw_inv_U7;
  run_zb_U7   : zb_stmt_U7 zw_inv_U7;
  run_zb0_U7  : zb0_stmt_U7 zw_inv_U7;
  run_zc_U7   : zc_stmt_U7 }.
Arguments ZU2C_U7 {RCa1}.
