(* reloc-zl14c *)
(* (uncompress2 1.4 UBSan): uncompress's U9LibStmt (itself the plain 1.4 S9LibStmt moved by tools/gen_u9libstmt14.py) moved to uncompress2 by tools/reloc_u9u7.py, with uncompress2_z's s0 / s1 pointing at the uncompress2 frame's destLen / sourceLen copies (u+176 / u+168):
   U7 names, the 1.4 UBSan addresses, zfree in a3 at inflateEnd, and za's entry registers s2 = strm, s1 = 7176, s3 = len, s4 = left. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim StoreOk Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Export ZlibStmtBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

#[local] Abbreviation RSEGS := TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U8_BUF    : Z := 0x34230.   (* [comment removed for export] *)
Definition U8_BUF_N  : Z := 0x40000.
Definition U8_INFL_N : Z := 7176.      (* [comment removed for export] *)
Definition U8_WIN_N  : Z := 32768.     (* [comment removed for export] *)
Definition U8_FRA    : Z := 1024.      (* [comment removed for export] *)
Definition U8_ZWD    : Z := 320.       (* [comment removed for export] *)
Definition U8_RO_LO  : Z := 0x10000.   (* [comment removed for export] *)
Definition U8_RO_HI  : Z := 0x22000.
Definition U8_IMG_TOP : Z := 0x95000.  (* [comment removed for export] *)
Definition U8_ZCALLOC : Z := 0x17e24. (* [comment removed for export] *)
Definition U8_ZCFREE  : Z := 0x17e34. (* [comment removed for export] *)
Definition U8_ZA     : Z := 0x1526c.   (* [comment removed for export] *)
Definition U8_RA_II  : Z := 0x14ef4.   (* [comment removed for export] *)
Definition U8_T_ZW   : Z := 0x17c20.   (* [comment removed for export] *)
Definition U8_ZB     : Z := 0x17c24.   (* [comment removed for export] *)
Definition U8_T_ZE1  : Z := 0x17dec.   (* [comment removed for export] *)
Definition U8_T_ZE2  : Z := 0x17e04.   (* [comment removed for export] *)
Definition U8_ZC     : Z := 0x17e08.   (* [comment removed for export] *)
Definition U8_RA2    : Z := 0x14fb4.   (* a worker 1.4: uncompress2_z after jal inflateEnd *)
Definition U8_HARN_RA : Z := 0x15050. (* [comment removed for export] *)
Definition U8_T_RET  : Z := 0x14c6c.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* a worker 1.4: uncompress2_z keeps dest (the harness buffer) and left = *destLen as they are; only dest == NULL with
   left = 0 would switch dest, which the harness never passes. So the destLen = 0 case (zm) has dest = U8_BUF and
   left = 0, and both cases leave through the one inflateEnd call (U8_RA2). za_dest_U8 is U8_BUF in both cases,
   written in the shape of I8S's ob (if zm then BUF + 0 * u else BUF) so the two stay convertible. *)
Definition za_dest_U8 (zm : bool) (u : Z) : Z := if zm then U8_BUF + 0 * u else U8_BUF.
Definition za_left_U8 (zm : bool) (left : Z) : Prop := if zm then left = 0 else 1 <= left <= U8_BUF_N.
Definition ra2_U8 (zm : bool) : Z := U8_RA2.

(* [comment removed for export] *)
Definition WA_U8 (u p : Z) : list (word * Z) :=
  [(Z_to_bv 64 (u - U8_FRA), U8_FRA + 112); (Z_to_bv 64 (u + 168), 8); (Z_to_bv 64 (u + 176), 8);
   (Z_to_bv 64 p, U8_INFL_N); (Z_to_bv 64 U8_BUF, U8_BUF_N)].

(* [comment removed for export] *)
Definition in_fpw_U8 (u p q n : Z) (a : word) : Prop :=
  let x := bv_unsigned a in
  (u - U8_ZWD <= x < u + 208) \/ (p <= x < p + U8_INFL_N) \/ (U8_BUF <= x < U8_BUF + U8_BUF_N) \/ (q <= x < q + n).

Definition zw_local_stmt_U8 (zw_inv : ZWINV) : Prop :=
  forall u p q n zc sE sW (M M' : word -> option byte),
    (forall a, in_fpw_U8 u p q n a -> M' a = M a) -> zw_inv u p q n zc sE sW M -> zw_inv u p q n zc sE sW M'.

(* [comment removed for export] *)
Definition lib_layout_U8 {RCa1 : RunCtx}  (zc : Z) (mem : word -> option byte) (u p q n : Z) : Prop :=
  u mod 16 = 0 /\ zc + U8_FRA <= u /\ u + 208 <= 2 ^ 47 /\ U8_IMG_TOP <= zc /\
  p mod 16 = 0 /\ 0 < p /\ p + U8_INFL_N <= zc /\
  (U8_BUF + U8_BUF_N <= p \/ p + U8_INFL_N <= U8_BUF) /\
  0 <= n < 2 ^ 26 /\ 1 <= q /\ q + n <= zc /\
  (q + n <= U8_BUF \/ U8_BUF + U8_BUF_N <= q) /\ (q + n <= p \/ p + U8_INFL_N <= q) /\
  (forall i, 0 <= i < n -> exists b, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (q + i)) 1 = Some [b]) /\
  (forall i, U8_RO_LO <= i < U8_RO_HI -> mem (Z_to_bv 64 i) = None) /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - U8_FRA)) (Z.to_nat (U8_FRA + 208)) = true /\
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 p) (Z.to_nat U8_INFL_N) = true /\
  (* [comment removed for export] *)
  (p + U8_INFL_N <= 0x10000 \/ U8_IMG_TOP <= p) /\
  (n = 0 \/ q + n <= 0x10000 \/ U8_IMG_TOP <= q).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition end_cells_U8 {RCa1 : RunCtx}  (zm : bool) (mem : word -> option byte) (u p : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 (ra2_U8 zm)) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 56)) 8 = Some (Z_to_le_bytes 8 p) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 U8_ZCFREE) /\
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0).

(* [comment removed for export] *)
(* a worker 1.4: uncompress2_z does not save s5, so the caller's s5 is carried with s6 .. s11 *) Definition S_ENTRY5 : list reg := [21]%bv ++ S_ENTRY. Definition end_regs_U8 (regs regs' : bvmap 5 word) (u blk : Z) (sE : list Z) : Prop :=
  getr regs' 13 = Z_to_bv 64 U8_ZCFREE /\   (* a worker 1.4 UBSan: inflateEnd loads zfree into a3 *)
  getr regs' 11 = Z_to_bv 64 blk /\ getr regs' 10 = Z_to_bv 64 0 /\
  getr regs' 8 = Z_to_bv 64 (u) /\ getr regs' 2 = Z_to_bv 64 (u - 16) /\
  getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
  sregs regs' S_ENTRY5 = sE.

Section CONTRACTS.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Variable zw_tok : bool -> ZWINV.   (* [comment removed for export] *)
Variable zm : bool.               (* [comment removed for export] *)
#[local] Notation zw_inv := (zw_tok zm).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition za_stmt_U8 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n left zc : Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  (* [comment removed for export] *)
  getr regs 2 = Z_to_bv 64 (u - 32) -> getr regs 18 = Z_to_bv 64 (u) -> getr regs 9 = Z_to_bv 64 7176 -> getr regs 10 = pw ->
  getr regs 19 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 left ->
  za_left_U8 zm left ->
  lib_layout_U8 zc mem u p q n ->
  (* a worker 1.4: inflateInit_'s saves: s2 = dest, s1 = &sourceLen and s0 = &destLen (the wrapper's copies, u + 168
     and u + 176), ra *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 32)) 8 = Some (Z_to_le_bytes 8 (za_dest_U8 zm u)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 24)) 8 = Some (Z_to_le_bytes 8 (u + 168)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) 8 = Some (Z_to_le_bytes 8 (u + 176)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 U8_RA_II) ->
  (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u)) 8 = Some (word_to_le_bytes 8 qw) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 8)) 4 = Some (Z_to_le_bytes 4 0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 64)) 8 = Some (Z_to_le_bytes 8 U8_ZCALLOC) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 72)) 8 = Some (Z_to_le_bytes 8 U8_ZCFREE) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 80)) 8 = Some (Z_to_le_bytes 8 0) ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte) (pc' : Z),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U8_ZA) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_U8 u p)
    /\ (   (* [comment removed for export] *)
           (pc' = U8_T_ZE2 /\ end_regs_U8 regs regs' u p (sregs regs S_ENTRY5) /\ end_cells_U8 zm mem' u p)
        \/ (* [comment removed for export] *)
           (pc' = U8_T_ZW /\
            getr regs' 13 = Z_to_bv 64 U8_ZCALLOC /\ getr regs' 10 = Z_to_bv 64 0 /\
            getr regs' 11 = Z_to_bv 64 U8_WIN_N /\ getr regs' 12 = Z_to_bv 64 1 /\
            getr regs' 2 = Z_to_bv 64 (u - U8_ZWD) /\
            getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
            zw_inv u p q n zc (sregs regs S_ENTRY5) (sregs regs' S_ALL) mem')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zb_stmt_U8 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw ww : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  let w := bv_unsigned ww in
  getr regs 2 = Z_to_bv 64 (u - U8_ZWD) -> getr regs 10 = ww -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_U8 zc mem u p q n ->
  (* [comment removed for export] *)
  w mod 16 = 0 -> 0 < w -> w + U8_WIN_N <= zc ->
  (U8_BUF + U8_BUF_N <= w \/ w + U8_WIN_N <= U8_BUF) -> (p + U8_INFL_N <= w \/ w + U8_WIN_N <= p) ->
  (q + n <= w \/ w + U8_WIN_N <= q) ->
  (w + U8_WIN_N <= 0x10000 \/ U8_IMG_TOP <= w) ->     (* [comment removed for export] *)
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem ww (Z.to_nat U8_WIN_N) = true ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U8_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 U8_T_ZE1) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_U8 u p ++ [(ww, U8_WIN_N)])
    /\ end_regs_U8 regs regs' u w sE /\ end_cells_U8 zm mem' u p.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zb0_stmt_U8 : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (pw qw : word) (n zc : Z) (sE sW : list Z),
  let p := bv_unsigned pw in
  let q := bv_unsigned qw in
  getr regs 2 = Z_to_bv 64 (u - U8_ZWD) -> getr regs 10 = Z_to_bv 64 0 -> sregs regs S_ALL = sW ->
  zw_inv u p q n zc sE sW mem ->
  lib_layout_U8 zc mem u p q n ->
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U8_ZB) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 U8_T_ZE2) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' (WA_U8 u p)
    /\ end_regs_U8 regs regs' u p sE /\ end_cells_U8 zm mem' u p.

End CONTRACTS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zc_stmt_U8 {RCa1 : RunCtx}  (zm : bool) : Prop :=
  forall (regs : bvmap 5 word) (mem : word -> option byte) (u : Z) (v0 v1 v2 v3 v4 v5 : word),
  getr regs 2 = Z_to_bv 64 (u - 16) -> getr regs 8 = Z_to_bv 64 (u) ->
  u mod 16 = 0 -> U8_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->     (* [comment removed for export] *)
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 16)) (Z.to_nat 224) = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u - 8)) 8 = Some (Z_to_le_bytes 8 (ra2_U8 zm)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 152)) 8 = Some (Z_to_le_bytes 8 U8_HARN_RA) ->
  (* [comment removed for export] *)
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 144)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 136)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 128)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 120)) 8 = Some (word_to_le_bytes 8 v3) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (u + 112)) 8 = Some (word_to_le_bytes 8 v4) ->
  (* a worker 1.4: uncompress2_z saves ra and s0..s4 only (frame 160); v5 is kept, unused, so the arity is unchanged *)
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (Z_to_bv 64 U8_ZC) mem (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb))) (mkst regs' (Z_to_bv 64 U8_HARN_RA) mem' (seg_rom (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)))
    /\ frame_mod mem mem' [(Z_to_bv 64 (u + 56), 8)]
    /\ getr regs' 2 = Z_to_bv 64 (u + 160)
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2
    /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = getr regs 21
    /\ (forall r : reg, In r ([3; 4]%bv ++ S_ENTRY) -> getr regs' r = getr regs r).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record zlib_u2_contract_U8 {RCa1 : RunCtx}  : Type := ZU2C_U8 {
  zw_inv_U8   : bool -> ZWINV;
  zw_local_U8 : forall zm : bool, zw_local_stmt_U8 (zw_inv_U8 zm);
  run_za_U8   : forall zm : bool, za_stmt_U8 zw_inv_U8 zm;
  run_zb_U8   : forall zm : bool, zb_stmt_U8 zw_inv_U8 zm;
  run_zb0_U8  : forall zm : bool, zb0_stmt_U8 zw_inv_U8 zm;
  run_zc_U8   : forall zm : bool, zc_stmt_U8 zm }.
Arguments ZU2C_U8 {RCa1}.  (* a worker (A1) tool *)
