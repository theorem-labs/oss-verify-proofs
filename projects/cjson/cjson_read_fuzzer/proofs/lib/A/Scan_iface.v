(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Notation mem := (word -> option byte).

Definition RSTRTOD : Z := 0x9ae30.
Definition RSSCANF : Z := 0x93cb0.
Definition RFMT_LG : Z := 0x21260.            (* [comment removed for export] *)
Definition RATP : Z := 0x5dd250.               (* [comment removed for export] *)
Definition RERRNO : Z := 0x5dd1ac.             (* [comment removed for export] *)
Definition RGLOBALS_TOP : Z := 0x5ff000.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RSTRTOD_DEPTH : Z := 11232.        (* [comment removed for export] *)
Definition RSSCANF_DEPTH : Z := 9504.         (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rstrtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PE : Z) (txt : list Z) (npre bits used lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (PE, PE + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ reg_get F' 10 = Z_to_bv 64 bits
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' PE [C8 (Z_to_bv 64 (T + used))]
    /\ bytes_at asegs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' RERRNO [C4 ev']
    /\ 0 <= used <= npre.      (* [comment removed for export] *)

Definition rstrtod_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (T PE : Z) (txt pre post : list Z) (bits used : Z) (ejunk : word) (lo : Z) (canary ev : word),
    bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat -> zlength txt <= 2^40 ->
    rw_cells asegs m PE [C8 ejunk] ->
    scan_strtod txt = Some (bits, used) ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
    RGLOBALS_TOP <= T -> (T + zlength txt <= lo \/ bv_unsigned sp <= T) -> T + 2^41 <= 2^63 ->      (* [comment removed for export] *)
    RGLOBALS_TOP <= PE -> (PE + 8 <= lo \/ bv_unsigned sp <= PE) -> PE + 8 <= 2^63 ->
    (PE + 8 <= T \/ T + zlength txt <= PE) ->
    ssp_cells m canary -> rw_cells asegs m RERRNO [C4 ev] ->
    mem_inv asegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 PE ->
    evt asegs (rstrtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PE txt (zlength pre) bits used lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rsscanf_lg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PD : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (RERRNO, RERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
    /\ bytes_at asegs m' T (map (Z_to_bv 8) txt)
    /\ ssp_cells m' canary
    /\ rw_cells asegs m' RERRNO [C4 ev'].

Definition rsscanf_lg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    (T + zlength txt) mod 8 = 0 -> zlength txt <= 256 ->     (* [comment removed for export] *)
    rw_cells asegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSSCANF_DEPTH -> RGLOBALS_TOP <= lo -> bv_unsigned sp < 2^62 ->
    bv_unsigned sp <= T -> T + 2^41 <= 2^63 -> bv_unsigned sp <= PD -> PD + 8 <= 2^63 ->
    (PD + 8 <= T \/ T + zlength txt <= PD) ->
    ssp_cells m canary -> rw_cells asegs m RERRNO [C4 ev] ->
    mem_inv asegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 RFMT_LG -> a2 = Z_to_bv 64 PD ->
    evt asegs (rsscanf_lg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RSSCANF) fc None m (seg_rom asegs)).


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
