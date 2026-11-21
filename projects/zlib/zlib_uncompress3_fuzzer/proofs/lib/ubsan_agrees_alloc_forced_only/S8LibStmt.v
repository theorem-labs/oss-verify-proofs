(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Export ZlibStmtBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

#[local] Abbreviation RSEGS := Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments.

Definition S8_BUF    : Z := 0x32f10.
Definition S8_BUF_N  : Z := 0x40000.
Definition S8_INFL_N : Z := 7176.
Definition S8_WIN_N  : Z := 32768.
Definition S8_FRA    : Z := 1024.
Definition S8_ZWD    : Z := 272.
Definition S8_RO_LO  : Z := 0x10000.
Definition S8_RO_HI  : Z := 0x21000.
Definition S8_IMG_TOP : Z := 0x94000.
Definition S8_ZCALLOC : Z := 0x17280.
Definition S8_ZCFREE  : Z := 0x17290.
Definition S8_ZA     : Z := 0x151d4.
Definition S8_RA_II  : Z := 0x14e8c.
Definition S8_T_ZW   : Z := 0x170d4.
Definition S8_ZB     : Z := 0x170d8.
Definition S8_T_ZE1  : Z := 0x1724c.
Definition S8_T_ZE2  : Z := 0x17264.
Definition S8_ZC     : Z := 0x17268.
Definition S8_RA2    : Z := 0x14f4c.   (* uncompress2_z after jal inflateEnd *)
Definition S8_HARN_RA : Z := 0x14fcc. (* the uncompress2 wrapper after jal uncompress2_z *)
Definition S8_T_RET  : Z := 0x14c3c.

(* uncompress2_z keeps dest (the harness buffer) and left = *destLen as they are; only dest == NULL with
   left = 0 would switch dest, which the harness never passes. So the destLen = 0 case (zm) has dest = S8_BUF and
   left = 0, and both cases leave through the one inflateEnd call (S8_RA2). za_dest_S8 is S8_BUF in both cases,
   written in the shape of I8S's ob (if zm then BUF + 0 * u else BUF) so the two stay convertible. *)
Definition za_dest_S8 (zm : bool) (u : Z) : Z := if zm then S8_BUF + 0 * u else S8_BUF.
Definition za_left_S8 (zm : bool) (left : Z) : Prop := if zm then left = 0 else 1 <= left <= S8_BUF_N.
Definition ra2_S8 (zm : bool) : Z := S8_RA2.

Definition WA_S8 (u p : Z) : list (word * Z) :=
  [(Z_to_bv 64 (u - S8_FRA), S8_FRA + 112); (Z_to_bv 64 (u + 168), 8); (Z_to_bv 64 (u + 176), 8);
   (Z_to_bv 64 p, S8_INFL_N); (Z_to_bv 64 S8_BUF, S8_BUF_N)].

Definition in_fpw_S8 (u p q n : Z) (a : word) : Prop :=
  let x := bv_unsigned a in
  (u - S8_ZWD <= x < u + 208) \/ (p <= x < p + S8_INFL_N) \/ (S8_BUF <= x < S8_BUF + S8_BUF_N) \/ (q <= x < q + n).

Definition zw_local_stmt_S8 (zw_inv : ZWINV) : Prop :=
  forall u p q n zc sE sW (M M' : word -> option byte),
    (forall a, in_fpw_S8 u p q n a -> M' a = M a) -> zw_inv u p q n zc sE sW M -> zw_inv u p q n zc sE sW M'.

Definition lib_layout_S8 {RCa1 : RunCtx}  (zc : Z) (mem : word -> option byte) (u p q n : Z) : Prop :=
  u mod 16 = 0 /\ zc + S8_FRA <= u /\ u + 208 <= 2 ^ 47 /\ S8_IMG_TOP <= zc /\
  p mod 16 = 0 /\ 0 < p /\ p + S8_INFL_N <= zc /\
  (S8_BUF + S8_BUF_N <= p \/ p + S8_INFL_N <= S8_BUF) /\
  0 <= n < 2 ^ 26 /\ 1 <= q /\ q + n <= zc /\
  (q + n <= S8_BUF \/ S8_BUF + S8_BUF_N <= q) /\ (q + n <= p \/ p + S8_INFL_N <= q) /\
  (forall i, 0 <= i < n -> exists b, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (q + i)) 1 = Some [b]) /\
  (forall i, S8_RO_LO <= i < S8_RO_HI -> mem (Z_to_bv 64 i) = None) /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - S8_FRA)) (Z.to_nat (S8_FRA + 208)) = true /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 p) (Z.to_nat S8_INFL_N) = true /\
  (p + S8_INFL_N <= 0x10000 \/ S8_IMG_TOP <= p) /\
  (n = 0 \/ q + n <= 0x10000 \/ S8_IMG_TOP <= q).

Definition end_cells_S8 {RCa1 : RunCtx}  (zm : bool) (mem : word -> option byte) (u p : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 (ra2_S8 zm)) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 56)) 8 = Some (Z_to_le_bytes 8 p) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 S8_ZCFREE) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0).

(* uncompress2_z does not save s5, so the caller's s5 is carried with s6 .. s11 *) Definition S_ENTRY5 : list reg := [21]%bv ++ S_ENTRY. Definition end_regs_S8 (regs regs' : bvmap 5 word) (u blk : Z) (sE : list Z) : Prop :=
  getr regs' 14 = Z_to_bv 64 S8_ZCFREE /\ getr regs' 11 = Z_to_bv 64 blk /\ getr regs' 10 = Z_to_bv 64 0 /\
  getr regs' 8 = Z_to_bv 64 (u) /\ getr regs' 2 = Z_to_bv 64 (u - 16) /\
  getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  sregs regs' S_ENTRY5 = sE.

Section CONTRACTS.
Context {RCa1 : RunCtx}.
Variable zw_tok : bool -> ZWINV.
Variable zm : bool.
#[local] Notation zw_inv := (zw_tok zm).

Definition za_stmt_S8 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n left zc : Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  getr regs 2 = Z_to_bv 64 (u - 32) -> getr regs 9 = Z_to_bv 64 (u) -> getr regs 10 = pw ->
  getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 left ->
  za_left_S8 zm left ->
  lib_layout_S8 zc mem u p q n ->
  (* inflateInit_'s saves: s2 = dest, s1 = &sourceLen and s0 = &destLen (the wrapper's copies, u + 168
     and u + 176), ra *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 32)) 8 = Some (Z_to_le_bytes 8 (za_dest_S8 zm u)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 24)) 8 = Some (Z_to_le_bytes 8 (u + 168)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) 8 = Some (Z_to_le_bytes 8 (u + 176)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 S8_RA_II) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u)) 8 = Some (word_to_le_bytes 8 qw) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 64)) 8 = Some (Z_to_le_bytes 8 S8_ZCALLOC) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 S8_ZCFREE) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0) ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte) (pc' : Z),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S8_ZA) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_S8 u p)
    /\ (
           (pc' = S8_T_ZE2 /\ end_regs_S8 regs regs' u p (sregs regs S_ENTRY5) /\ end_cells_S8 zm mem' u p)
        \/
           (pc' = S8_T_ZW /\
            getr regs' 13 = Z_to_bv 64 S8_ZCALLOC /\ getr regs' 10 = Z_to_bv 64 0 /\
            getr regs' 11 = Z_to_bv 64 S8_WIN_N /\ getr regs' 12 = Z_to_bv 64 1 /\
            getr regs' 2 = Z_to_bv 64 (u - S8_ZWD) /\
            getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
            zw_inv u p q n zc (sregs regs S_ENTRY5) (sregs regs' S_ALL) mem')).

Definition zb_stmt_S8 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw ww : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  let w := bv_unsigned ww in
  getr regs 2 = Z_to_bv 64 (u - S8_ZWD) -> getr regs 10 = ww -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_S8 zc mem u p q n ->
  w mod 16 = 0 -> 0 < w -> w + S8_WIN_N <= zc ->
  (S8_BUF + S8_BUF_N <= w \/ w + S8_WIN_N <= S8_BUF) -> (p + S8_INFL_N <= w \/ w + S8_WIN_N <= p) ->
  (q + n <= w \/ w + S8_WIN_N <= q) ->
  (w + S8_WIN_N <= 0x10000 \/ S8_IMG_TOP <= w) ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem ww (Z.to_nat S8_WIN_N) = true ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S8_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 S8_T_ZE1) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_S8 u p ++ [(ww, S8_WIN_N)])
    /\ end_regs_S8 regs regs' u w sE /\ end_cells_S8 zm mem' u p.

Definition zb0_stmt_S8 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  getr regs 2 = Z_to_bv 64 (u - S8_ZWD) -> getr regs 10 = Z_to_bv 64 0 -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_S8 zc mem u p q n ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S8_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 S8_T_ZE2) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_S8 u p)
    /\ end_regs_S8 regs regs' u p sE /\ end_cells_S8 zm mem' u p.

End CONTRACTS.

Definition zc_stmt_S8 {RCa1 : RunCtx}  (zm : bool) : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (v0 v1 v2 v3 v4 v5 : word),
  getr regs 2 = Z_to_bv 64 (u - 16) -> getr regs 8 = Z_to_bv 64 (u) ->
  u mod 16 = 0 -> S8_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) (Z.to_nat 224) = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 (ra2_S8 zm)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 152)) 8 = Some (Z_to_le_bytes 8 S8_HARN_RA) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 144)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 136)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 128)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 120)) 8 = Some (word_to_le_bytes 8 v3) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 112)) 8 = Some (word_to_le_bytes 8 v4) ->
  (* uncompress2_z saves ra and s0..s4 only (frame 160); v5 is kept, unused, so the arity is unchanged *)
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S8_ZC) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 S8_HARN_RA) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' [(Z_to_bv 64 (u + 56), 8)]
    /\ getr regs' 2 = Z_to_bv 64 (u + 160)
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2
    /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, In r ([3; 4]%bv ++ S_ENTRY) -> getr regs' r = getr regs r).

Record zlib_u2_contract_S8 {RCa1 : RunCtx}  : Type := ZU2C_S8 {
  zw_inv_S8   : bool -> ZWINV;
  zw_local_S8 : forall zm : bool, zw_local_stmt_S8 (zw_inv_S8 zm);
  run_za_S8   : forall zm : bool, za_stmt_S8 zw_inv_S8 zm;
  run_zb_S8   : forall zm : bool, zb_stmt_S8 zw_inv_S8 zm;
  run_zb0_S8  : forall zm : bool, zb0_stmt_S8 zw_inv_S8 zm;
  run_zc_S8   : forall zm : bool, zc_stmt_S8 zm }.
Arguments ZU2C_S8 {RCa1}.
