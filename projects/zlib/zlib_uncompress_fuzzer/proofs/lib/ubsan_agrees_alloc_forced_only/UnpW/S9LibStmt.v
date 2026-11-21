(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Export ZlibStmtBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

#[local] Abbreviation RSEGS := SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition S9_BUF    : Z := 0x32ee0.   (* [comment removed for export] *)
Definition S9_BUF_N  : Z := 0x40000.
Definition S9_INFL_N : Z := 7176.      (* [comment removed for export] *)
Definition S9_WIN_N  : Z := 32768.     (* [comment removed for export] *)
Definition S9_FRA    : Z := 1024.      (* [comment removed for export] *)
Definition S9_ZWD    : Z := 288.  (* a worker 2026-11-17, unpatched, HAND: the stack depth below u at the zcalloc call inside updatewindow (the inflate frame 240 + updatewindow 48) *)       (* [comment removed for export] *)
Definition S9_RO_LO  : Z := 0x10000.   (* [comment removed for export] *)
Definition S9_RO_HI  : Z := 0x21000.
Definition S9_IMG_TOP : Z := 0x94000.  (* [comment removed for export] *)
Definition S9_ZCALLOC : Z := 0x17244. (* [comment removed for export] *)
Definition S9_ZCFREE  : Z := 0x17254. (* [comment removed for export] *)
Definition S9_ZA     : Z := 0x15150.   (* [comment removed for export] *)
Definition S9_RA_II  : Z := 0x14e20.   (* [comment removed for export] *)
Definition S9_T_ZW   : Z := 0x17098.   (* [comment removed for export] *)
Definition S9_ZB     : Z := 0x1709c.   (* [comment removed for export] *)
Definition S9_T_ZE1  : Z := 0x17210.   (* [comment removed for export] *)
Definition S9_T_ZE2  : Z := 0x17228.   (* [comment removed for export] *)
Definition S9_ZC     : Z := 0x1722c.   (* [comment removed for export] *)
Definition S9_RA2    : Z := 0x14ee0.   (* a worker 1.4: uncompress2_z after jal inflateEnd *)
Definition S9_HARN_RA : Z := 0x14f54. (* [comment removed for export] *)
Definition S9_T_RET  : Z := 0x14c34.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition WA_S9 (u p : Z) : list (word * Z) :=
  [(Z_to_bv 64 (u - S9_FRA), S9_FRA + 112); (Z_to_bv 64 (u + 160), 8); (Z_to_bv 64 (u + 168), 8);
   (Z_to_bv 64 p, S9_INFL_N); (Z_to_bv 64 S9_BUF, S9_BUF_N)].

(* [comment removed for export] *)
Definition in_fpw_S9 (u p q n : Z) (a : word) : Prop :=
  let x := bv_unsigned a in
  (u - S9_ZWD <= x < u + 208) \/ (p <= x < p + S9_INFL_N) \/ (S9_BUF <= x < S9_BUF + S9_BUF_N) \/ (q <= x < q + n).

Definition zw_local_stmt_S9 (zw_inv : ZWINV) : Prop :=
  forall u p q n zc sE sW (M M' : word -> option byte),
    (forall a, in_fpw_S9 u p q n a -> M' a = M a) -> zw_inv u p q n zc sE sW M -> zw_inv u p q n zc sE sW M'.

(* [comment removed for export] *)
Definition lib_layout_S9 {RCa1 : RunCtx}  (zc : Z) (mem : word -> option byte) (u p q n : Z) : Prop :=
  u mod 16 = 0 /\ zc + S9_FRA <= u /\ u + 208 <= 2 ^ 47 /\ S9_IMG_TOP <= zc /\
  p mod 16 = 0 /\ 0 < p /\ p + S9_INFL_N <= zc /\
  (S9_BUF + S9_BUF_N <= p \/ p + S9_INFL_N <= S9_BUF) /\
  0 <= n < 2 ^ 26 /\ 1 <= q /\ q + n <= zc /\
  (q + n <= S9_BUF \/ S9_BUF + S9_BUF_N <= q) /\ (q + n <= p \/ p + S9_INFL_N <= q) /\
  (forall i, 0 <= i < n -> exists b, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (q + i)) 1 = Some [b]) /\
  (forall i, S9_RO_LO <= i < S9_RO_HI -> mem (Z_to_bv 64 i) = None) /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - S9_FRA)) (Z.to_nat (S9_FRA + 208)) = true /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 p) (Z.to_nat S9_INFL_N) = true /\
  (* [comment removed for export] *)
  (p + S9_INFL_N <= 0x10000 \/ S9_IMG_TOP <= p) /\
  (n = 0 \/ q + n <= 0x10000 \/ S9_IMG_TOP <= q).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition end_cells_S9 {RCa1 : RunCtx}  (mem : word -> option byte) (u p : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 S9_RA2) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 56)) 8 = Some (Z_to_le_bytes 8 p) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 S9_ZCFREE) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0).

(* [comment removed for export] *)
(* a worker 1.4: uncompress2_z does not save s5, so the caller's s5 is carried with s6 .. s11 *) Definition S_ENTRY5 : list reg := [21]%bv ++ S_ENTRY. Definition end_regs_S9 (regs regs' : bvmap 5 word) (u blk : Z) (sE : list Z) : Prop :=
  getr regs' 14 = Z_to_bv 64 S9_ZCFREE /\ getr regs' 11 = Z_to_bv 64 blk /\ getr regs' 10 = Z_to_bv 64 0 /\
  getr regs' 8 = Z_to_bv 64 (u) /\ getr regs' 2 = Z_to_bv 64 (u - 16) /\
  getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  sregs regs' S_ENTRY5 = sE.

Section CONTRACTS.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variable zw_inv : ZWINV.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition za_stmt_S9 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n zc : Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  (* [comment removed for export] *)
  getr regs 2 = Z_to_bv 64 (u - 32) -> getr regs 9 = Z_to_bv 64 (u) -> getr regs 10 = pw ->
  getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 S9_BUF_N ->
  lib_layout_S9 zc mem u p q n ->
  (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 32)) 8 = Some (Z_to_le_bytes 8 S9_BUF) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 24)) 8 = Some (Z_to_le_bytes 8 (u + 160)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) 8 = Some (Z_to_le_bytes 8 (u + 168)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 S9_RA_II) ->
  (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u)) 8 = Some (word_to_le_bytes 8 qw) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 64)) 8 = Some (Z_to_le_bytes 8 S9_ZCALLOC) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 S9_ZCFREE) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0) ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte) (pc' : Z),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S9_ZA) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_S9 u p)
    /\ (   (* [comment removed for export] *)
           (pc' = S9_T_ZE2 /\ end_regs_S9 regs regs' u p (sregs regs S_ENTRY5) /\ end_cells_S9 mem' u p)
        \/ (* [comment removed for export] *)
           (pc' = S9_T_ZW /\
            getr regs' 13 = Z_to_bv 64 S9_ZCALLOC /\ getr regs' 10 = Z_to_bv 64 0 /\
            getr regs' 11 = Z_to_bv 64 S9_WIN_N /\ getr regs' 12 = Z_to_bv 64 1 /\
            getr regs' 2 = Z_to_bv 64 (u - S9_ZWD) /\
            getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
            zw_inv u p q n zc (sregs regs S_ENTRY5) (sregs regs' S_ALL) mem')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zb_stmt_S9 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw ww : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  let w := bv_unsigned ww in
  getr regs 2 = Z_to_bv 64 (u - S9_ZWD) -> getr regs 10 = ww -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_S9 zc mem u p q n ->
  (* [comment removed for export] *)
  w mod 16 = 0 -> 0 < w -> w + S9_WIN_N <= zc ->
  (S9_BUF + S9_BUF_N <= w \/ w + S9_WIN_N <= S9_BUF) -> (p + S9_INFL_N <= w \/ w + S9_WIN_N <= p) ->
  (q + n <= w \/ w + S9_WIN_N <= q) ->
  (w + S9_WIN_N <= 0x10000 \/ S9_IMG_TOP <= w) ->     (* [comment removed for export] *)
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem ww (Z.to_nat S9_WIN_N) = true ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S9_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 S9_T_ZE1) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_S9 u p ++ [(ww, S9_WIN_N)])
    /\ end_regs_S9 regs regs' u w sE /\ end_cells_S9 mem' u p.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zb0_stmt_S9 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  getr regs 2 = Z_to_bv 64 (u - S9_ZWD) -> getr regs 10 = Z_to_bv 64 0 -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_S9 zc mem u p q n ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S9_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 S9_T_ZE2) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_S9 u p)
    /\ end_regs_S9 regs regs' u p sE /\ end_cells_S9 mem' u p.

End CONTRACTS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zc_stmt_S9 {RCa1 : RunCtx}  : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (v0 v1 v2 v3 v4 v5 : word),
  getr regs 2 = Z_to_bv 64 (u - 16) -> getr regs 8 = Z_to_bv 64 (u) ->
  u mod 16 = 0 -> S9_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->     (* [comment removed for export] *)
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) (Z.to_nat 224) = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 S9_RA2) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 152)) 8 = Some (Z_to_le_bytes 8 S9_HARN_RA) ->
  (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 144)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 136)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 128)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 120)) 8 = Some (word_to_le_bytes 8 v3) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 112)) 8 = Some (word_to_le_bytes 8 v4) ->
  (* a worker 1.4: uncompress2_z saves ra and s0..s4 only (frame 160); v5 is kept, unused, so the arity is unchanged *)
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 S9_ZC) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 S9_HARN_RA) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' [(Z_to_bv 64 (u + 56), 8)]
    /\ getr regs' 2 = Z_to_bv 64 (u + 160)
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2
    /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, In r ([3; 4]%bv ++ S_ENTRY) -> getr regs' r = getr regs r).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record zlib_u2_contract_S9 {RCa1 : RunCtx}  : Type := ZU2C_S9 {
  zw_inv_S9   : ZWINV;
  zw_local_S9 : zw_local_stmt_S9 zw_inv_S9;
  run_za_S9   : za_stmt_S9 zw_inv_S9;
  run_zb_S9   : zb_stmt_S9 zw_inv_S9;
  run_zb0_S9  : zb0_stmt_S9 zw_inv_S9;
  run_zc_S9   : zc_stmt_S9 }.
Arguments ZU2C_S9 {RCa1}.  (* a worker (A1) tool *)
