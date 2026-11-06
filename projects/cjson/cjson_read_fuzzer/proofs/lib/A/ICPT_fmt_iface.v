(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat FmtFp FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_printf_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_FMT_d : Z := 0x21220.      (* [comment removed for export] *)
Definition A_FMT_g15 : Z := 0x21240.    (* [comment removed for export] *)
Definition A_FMT_lg : Z := 0x21260.     (* [comment removed for export] *)
Definition A_FMT_g17 : Z := 0x21280.    (* [comment removed for export] *)
Definition A_FMT_u04x : Z := 0x212c0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AFMT_STACK : Z := 16384.

(* [comment removed for export] *)
Definition fmt_cells (m : word -> option byte) : Prop :=
  icpt_cells m
  /\ ro_cells asegs m 0x13bdfc [C1 (Z_to_bv 8 1)]               (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3d08 [C8 (Z_to_bv 64 0x9ab0c)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3d00 [C8 (Z_to_bv 64 0x9a964)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3cf8 [C8 (Z_to_bv 64 0x94664)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3ce0 [C8 (Z_to_bv 64 0x9ab20)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3ce8 [C8 (Z_to_bv 64 0x9709c)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3cf0 [C8 (Z_to_bv 64 0x9a948)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3cb8 [C8 (Z_to_bv 64 0x906c4)].      (* [comment removed for export] *)

Definition fmt_cell_ivs : list (Z * Z) := [(0xa3cb8, 0xa3cc0); (0xa3ce0, 0xa3d10); (0x13bdfc, 0x13bdfd)].

(* [comment removed for export] *)
Definition assp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells asegs m AGOT_SSP [C8 (Z_to_bv 64 ASSP)] /\ rw_cells asegs m ASSP [C8 canary].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition asprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ assp_cells m' canary
    /\ rw_cells asegs m' D [CB dn (map (Z_to_bv 8) o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

(* [comment removed for export] *)
Definition asprintf_pre (m : word -> option byte) (sp : word) (D : Z) (dn : nat) (lo : Z) (canary : word) (fc : bv 32) : Prop :=
  fmt_cells m /\ MRT m /\ lowsh_at m /\ mem_inv asegs m /\ frm0 fc /\ assp_cells m canary
  /\ stk asegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo + AFMT_STACK <= bv_unsigned sp
  /\ bv_unsigned sp + 64 <= 2^47 - 1
  /\ (D + Z.of_nat dn <= lo \/ bv_unsigned sp <= D)
  /\ highmem_range D (Z.of_nat dn)
  /\ shadow_ok m D (Z.of_nat dn).

(* [comment removed for export] *)
Definition asprintf_d_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word)
         (i : Z) (o : list Z) (r : Z),
    rw_cells asegs m D [CB dn junkd] ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A_FMT_d ->
    bv_unsigned a2 mod 2^32 = i mod 2^32 -> (-2^31 <= i < 2^31) ->
    fmt_d i = Some (o, r) -> (length o < dn)%nat -> (Z.of_nat dn < 2^31) ->
    asprintf_pre m sp D dn lo canary fc ->
    shadow_ok m A_FMT_d 3 ->
    evt asegs (asprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition asprintf_g_stmt (prec : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word)
         (o : list Z) (r : Z),
    FMT_G_RET -> FMT_G_LEN25 ->
    rw_cells asegs m D [CB dn junkd] ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (if prec =? 15 then A_FMT_g15 else A_FMT_g17) -> (prec = 15 \/ prec = 17) ->
    fmt_g (bv_unsigned a2) prec = Some (o, r) ->
    fmt_fp_facts (f128_of_d (bv_unsigned a2)) 0 prec CHR_g ->
    (length o < dn)%nat -> (Z.of_nat dn < 2^31) ->
    asprintf_pre m sp D dn lo canary fc ->
    shadow_ok m (if prec =? 15 then A_FMT_g15 else A_FMT_g17) 7 ->
    evt asegs (asprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition asprintf_u04x_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : Z) (dn : nat) (junkd : list byte) (lo : Z) (canary : word) (c : Z),
    rw_cells asegs m D [CB dn junkd] ->
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A_FMT_u04x ->
    bv_unsigned a2 mod 2^32 = c -> (0 <= c < 256) ->
    (6 <= dn)%nat -> (Z.of_nat dn < 2^31) ->
    asprintf_pre m sp D dn lo canary fc ->
    shadow_ok m A_FMT_u04x 6 ->
    evt asegs (asprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd 5 (117 :: hex4_lower c) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition asscanf_lg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (T PD : Z) (txt : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary : word) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (ev' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (PD, PD + 8); (AERRNO, AERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ frm0 fc'
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' PD [C8 (match res with Some bits => Z_to_bv 64 bits | None => djunk end)]
    /\ bytes_at asegs m' T (map (Z_to_bv 8) txt)
    /\ assp_cells m' canary
    /\ rw_cells asegs m' AERRNO [C4 ev'].

(* [comment removed for export] *)
Definition asscanf_lg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (T PD : Z) (txt pre post : list Z) (r : Z) (res : option Z) (djunk : word) (lo : Z) (canary ev : word),
    let usp := bv_unsigned sp in
    fmt_cells m -> MRT m -> lowsh_at m -> mem_inv asegs m -> frm0 fc -> assp_cells m canary -> rw_cells asegs m AERRNO [C4 ev] ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 T -> a1 = Z_to_bv 64 A_FMT_lg -> a2 = Z_to_bv 64 PD ->
    bytes_at asegs m T (map (Z_to_bv 8) txt) -> Forall (fun c => 0 <= c < 256) txt ->
    txt = pre ++ 0 :: post -> Forall (fun c => is_numch c = true) pre -> (length pre <= 64)%nat ->
    (T + zlength txt) mod 8 = 0 -> zlength txt <= 256 ->
    rw_cells asegs m PD [C8 djunk] ->
    scan_sscanf_lg txt = Some (r, res) ->
    stk asegs m lo usp -> alloc_ceiling <= lo -> lo + AFMT_STACK <= usp -> usp + 8 <= 2^47 ->
    (T + zlength txt <= lo \/ usp <= T) -> (PD + 8 <= lo \/ usp <= PD) -> (PD + 8 <= T \/ T + zlength txt <= PD) ->
    4096 <= T -> 0x5ff000 <= T -> T + 2^41 <= 2^63 -> KHIGHMEM_BEG <= PD -> PD + 8 <= 2^63 ->
    app_range T (zlength txt) -> shadow_ok m T (zlength pre + 1) -> app_range PD 8 -> shadow_ok m PD 8 ->
    evt asegs (asscanf_lg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F T PD txt r res djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ASSCANF_T) fc None m (seg_rom asegs)).


End CeilWrap.
