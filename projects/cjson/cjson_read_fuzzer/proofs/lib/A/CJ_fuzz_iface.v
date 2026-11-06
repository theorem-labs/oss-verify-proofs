(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Module CJ_print_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AENSURE_ENTRY  : Z := 0x86c50.   (* [comment removed for export] *)
Definition APSTR_ENTRY    : Z := 0x86f44.   (* [comment removed for export] *)
Definition CJPRINT_ENTRY  : Z := 0x839f8.   (* [comment removed for export] *)
Definition CJPRINTU_ENTRY : Z := 0x83b78.   (* [comment removed for export] *)
Definition PBUFD_ENTRY    : Z := 0x83b80.   (* [comment removed for export] *)
Definition PRINT_ENTRY    : Z := 0x83a00.   (* [comment removed for export] *)
Definition PVALUE_ENTRY   : Z := 0x83c3c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition APV_STACK (n : nat) : Z := 272 * Z.of_nat n + 24576.
Definition APRINT_STACK (n : nat) : Z := 128 + APV_STACK n.
Definition PRINT_COST : Z := 7 * 2^33.   (* [comment removed for export] *)
Definition PRINT_NP : Z := 64.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_callee_saved (k : bv 5) : Prop :=
  bv_unsigned k = 8 \/ bv_unsigned k = 9 \/ (18 <= bv_unsigned k <= 27).

(* [comment removed for export] *)
Definition AENSURE_STACK : Z := 80 + AMALLOC_STACK.
(* [comment removed for export] *)
Definition APSTR_STACK : Z := 112 + AFORMAT_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pb_struct (m : word -> option byte) (PB buf len off dep : Z) (fw : word) : Prop :=
  rw_cells asegs m PB [C8 (wz buf); C8 (wz len); C8 (wz off); C8 (wz dep); C4 (wz 0); C4 fw;
                      C8 (wz AMALLOC); C8 (wz AFREE); C8 (wz AREALLOC)].

Definition pb_data (m : word -> option byte) (buf len : Z) (bs : list byte) : Prop :=
  u8arr asegs m buf bs /\ Z.of_nat (length bs) = len.

Definition pb_nums (len off dep : Z) : Prop := 0 <= off <= len /\ len < 2^31 /\ 0 <= dep.

(* [comment removed for export] *)
Definition pb_nul (bs : list byte) (len off : Z) : Prop :=
  exists K, 0 <= K /\ off + K < len /\ nth_error bs (Z.to_nat (off + K)) = Some (wb 0).

(* [comment removed for export] *)
Definition pv_agree (sp0 : Z) (LR : list cblock) (LF : list fframe) (SP PB : Z) (m m' : word -> option byte) : Prop :=
  magree (fun a => cj_client_addr sp0 LR LF SP a /\ ~ (PB <= a < PB + 64)) m m'.

(* [comment removed for export] *)
Definition pb_place (SP PB SPB : Z) : Prop := SP <= PB /\ PB + 64 <= SPB /\ SPB < 2^62.

(* [comment removed for export] *)
Definition pb_below (m : word -> option byte) (PB : Z) : Prop :=
  exists w1 w2 : word, bytes_at asegs m (PB - 16) (le8 w1 ++ le8 w2) /\ bv_unsigned w1 <= PB.

(* [comment removed for export] *)
Definition INT_MAX : Z := 2^31 - 1.
Definition KRE : Z := 69696 + 2^19 + 64 + CL24_TAX.   (* [comment removed for export] *)
Definition pb_pot (len : Z) : Z := 8 * len + KRE * Z.log2 (len + 1) + (if len =? INT_MAX then 2^33 + KRE else 0).
(* [comment removed for export] *)
Definition PB_FAIL : Z := 2^33 + KRE + cost_free.
(* [comment removed for export] *)
Definition pb_allow (len : Z) : Z := PB_FAIL + (pb_pot INT_MAX - pb_pot len).
(* [comment removed for export] *)
Definition pb_npot (len : Z) : Z := Z.log2 (len + 1) + (if len =? INT_MAX then 1 else 0).
Definition pb_npallow (len : Z) : Z := 2 + (pb_npot INT_MAX - pb_npot len).

Section Stmts.
  Variable AI : art_iface.
  Variable TI : trs_iface.

  (* [comment removed for export] *)
  Definition ensure_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np B0 : Z) (PB buf len off dep : Z) (fw : word) (bs : list byte)
      (needed lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word)
                          (LB' : list cblock) (TRS' : list (list Z)) (B' np' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 errv']
      /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m m'
      /\ ART AI sp0 SPB LB' LF TRS' B' m' mo' g' /\ TINV TI np' TRS' /\ gmono g g'
      /\ ( (* [comment removed for export] *)
           (a0 = wz 0 /\ Permutation LR LB' /\ pb_struct m' PB 0 0 off dep fw
            /\ B0 - PB_FAIL <= B' /\ np' <= np + 2)
           (* [comment removed for export] *)
        \/ (a0 = wz 0 /\ Permutation ((buf, len) :: LR) LB' /\ pb_struct m' PB buf len off dep fw /\ pb_data m' buf len bs
            /\ B' = B0 /\ np' = np)
           (* [comment removed for export] *)
        \/ (exists buf' len' bs', a0 = wz (buf' + off) /\ Permutation ((buf', len') :: LR) LB'
              /\ pb_struct m' PB buf' len' off dep fw /\ pb_data m' buf' len' bs'
              /\ needed + off + 1 <= len' /\ len' < 2^31 /\ len <= len'
              /\ B0 - (pb_pot len' - pb_pot len) <= B' /\ np' <= np + (pb_npot len' - pb_npot len)) ).

  Definition ensure_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B0 : Z)
           (PB buf len off dep : Z) (fw : word) (bs : list byte) (needed lo : Z) (errv : word),
      ART AI sp0 SPB LB LF TRS B0 m mo g -> Permutation ((buf, len) :: LR) LB ->
      pb_struct m PB buf len off dep fw -> pb_data m buf len bs -> pb_nums len off dep ->
      pb_place (bv_unsigned sp) PB SPB -> pb_below m PB -> bv_unsigned sp + 16 <= PB -> PB + 80 <= 2^47 ->
      sp0 <= 2^47 -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> ASTACK_BOTTOM sp0 <= lo -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AENSURE_STACK ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
      sh_zero m alloc_ceiling (2^47) ->
      TINV TI np TRS -> np + 2 <= NPMAX TI ->
      pb_allow len <= B0 ->
      a0 = wz PB -> a1 = wz needed -> 0 <= needed < 2^64 ->
      LSCPS asegs (ensure_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LR LF np B0 PB buf len off dep fw bs needed lo m g)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz AENSURE_ENTRY) fc None m (seg_rom asegs)) mo g.

  (* [comment removed for export] *)
  Definition print_outcome (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np BB : Z) (PB len dep : Z) (fw : word) (a0 : word)
      (m' : word -> option byte) (mo' : Model) (g' : lghost) : Prop :=
    exists (LB' : list cblock) (TRS' : list (list Z)) (B' np' : Z) (buf' len' off' : Z),
      ART AI sp0 SPB LB' LF TRS' B' m' mo' g' /\ TINV TI np' TRS'
      /\ ( (a0 = wz 0 /\ (exists dep', pb_struct m' PB buf' len' off' dep' fw)
            /\ ( (buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB') )
            /\ BB - pb_allow len <= B' /\ np' <= np + pb_npallow len)
        \/ (a0 = wz 1 /\ (exists bs', Permutation ((buf', len') :: LR) LB'
              /\ pb_struct m' PB buf' len' off' dep fw /\ pb_data m' buf' len' bs' /\ pb_nums len' off' dep /\ pb_nul bs' len' off')
            /\ len <= len' /\ BB - (pb_pot len' - pb_pot len) <= B' /\ np' <= np + (pb_npot len' - pb_npot len)) ).

  (* [comment removed for export] *)
  Definition pvalue_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (sp0 SPB : Z) (LR B : list cblock) (LF : list fframe) (np BB : Z) (CH : list (Z * Z * Z))
      (n : nat) (p PB len dep : Z) (fw : word) (lo : Z) (m : word -> option byte) (g : lghost)
      : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 errv']
      /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m m'
      /\ cj_chain CJ_PRINTABLE m' n p B
      /\ gmono g g' /\ chain_cells m' CH
      /\ print_outcome sp0 SPB LR LF np BB PB len dep fw a0 m' mo' g'.

  Definition print_value_at (n : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR B : list cblock) (LF : list fframe) (TRS : list (list Z)) (np BB : Z) (CH : list (Z * Z * Z))
           (PB buf len off dep p : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word),
      ART AI sp0 SPB LB LF TRS BB m mo g -> Permutation ((buf, len) :: LR) LB ->
      pb_struct m PB buf len off dep fw -> pb_data m buf len bs -> pb_nums len off dep -> dep + Z.of_nat n <= 2^40 ->
      cj_chain CJ_PRINTABLE m n p B -> p <> 0 -> (forall b, In b B -> In b LR) ->
      pb_place (bv_unsigned sp) PB SPB -> PB mod 8 = 0 -> bv_unsigned sp mod 16 = 0 ->
      sp0 <= 2^47 -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> ASTACK_BOTTOM sp0 <= lo -> PB + 80 <= 2^47 ->
      (* [comment removed for export] *)
      (bv_unsigned sp + 16 <= PB -> pb_below m PB) ->
      (PB = bv_unsigned sp + 8 -> exists w : word, bytes_at asegs m (bv_unsigned sp) (le8 w)) ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - APV_STACK n ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP -> frm0 fc ->
      sh_zero m alloc_ceiling (2^47) ->
      TINV TI np TRS -> np + pb_npallow len <= NPMAX TI ->
      lf_room 1 LF (Z.of_nat n) ->
      (* [comment removed for export] *)
      chain_cells m CH -> chain_ok (bv_unsigned sp + 16) CH (ASTACK_TOP sp0) -> chain_link (bv_unsigned s0) (bv_unsigned sp) CH ->
      Forall (fun x => fr_f x <= PB) CH ->
      (* [comment removed for export] *)
      4096 <= bv_unsigned ra -> bv_unsigned ra < AIMG_HI -> ~ is_pc0 (bv_unsigned ra) ->
      pb_allow len <= BB ->
      a0 = wz p -> a1 = wz PB ->
      LSCPS asegs (pvalue_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np BB CH n p PB len dep fw lo m g)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz PVALUE_ENTRY) fc None m (seg_rom asegs)) mo g.

  Definition print_value_stmt : Prop := forall n, print_value_at n.

  (* [comment removed for export] *)
  Definition pstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (sp0 SPB : Z) (LR : list cblock) (LF : list fframe) (np BB : Z) (PB len dep : Z) (fw : word) (lo : Z)
      (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 errv']
      /\ pv_agree sp0 LR LF (bv_unsigned sp) PB m m'
      /\ gmono g g'
      /\ print_outcome sp0 SPB LR LF np BB PB len dep fw a0 m' mo' g'.

  Definition pstr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR Bv : list cblock) (LF : list fframe) (TRS : list (list Z)) (np BB : Z)
           (PB buf len off dep s : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word),
      ART AI sp0 SPB LB LF TRS BB m mo g -> Permutation ((buf, len) :: LR) LB ->
      pb_struct m PB buf len off dep fw -> pb_data m buf len bs -> pb_nums len off dep ->
      cj_str m s Bv -> (forall b, In b Bv -> In b LR) ->
      pb_place (bv_unsigned sp) PB SPB -> pb_below m PB -> bv_unsigned sp + 16 <= PB -> PB + 80 <= 2^47 ->
      sp0 <= 2^47 -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> ASTACK_BOTTOM sp0 <= lo -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - APSTR_STACK ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP -> frm0 fc ->
      sh_zero m alloc_ceiling (2^47) ->
      TINV TI np TRS -> np + pb_npallow len <= NPMAX TI ->
      4096 <= bv_unsigned ra -> ~ is_pc0 (bv_unsigned ra) ->
      pb_allow len <= BB ->
      a0 = wz s -> a1 = wz PB ->
      LSCPS asegs (pstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR LF np BB PB len dep fw lo m g)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz APSTR_ENTRY) fc None m (seg_rom asegs)) mo g.

  (* [comment removed for export] *)
  Definition print_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (sp0 SPB : Z) (LR B : list cblock) (LF : list fframe) (np B0 : Z) (n : nat) (p : Z) (lo : Z)
      (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word) (LB' : list cblock) (TRS' : list (list Z)) (B' np' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 errv']
      /\ cj_pres sp0 (B ++ LR) LF (bv_unsigned sp) m m'
      /\ cj_chain CJ_PRINTABLE m' n p B
      /\ ART AI sp0 SPB LB' LF TRS' B' m' mo' g'
      /\ TINV TI np' TRS' /\ np <= np' <= np + PRINT_NP
      /\ gmono g g'
      /\ B0 - PRINT_COST <= B'
      /\ ( (a0 = wz 0 /\ Permutation (B ++ LR) LB')
        \/ (exists q k, a0 = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LR) LB') ).

  Definition print_pre_stmt (entry : Z) (ARGS : word -> word -> Prop) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB LR B : list cblock) (LF : list fframe) (TRS : list (list Z)) (np B0 : Z)
           (n : nat) (p : Z) (lo : Z) (errv : word),
      ART AI sp0 SPB LB LF TRS B0 m mo g -> Permutation (B ++ LR) LB ->
      cj_chain CJ_PRINTABLE m n p B -> p <> 0 -> (n <= 1001)%nat ->
      (* [comment removed for export] *)
      bv_unsigned sp <= SPB -> SPB < 2^62 -> bv_unsigned sp mod 16 = 0 ->
      sp0 <= 2^47 -> bv_unsigned sp + 16 < ASTACK_TOP sp0 -> bv_unsigned s0 <= bv_unsigned sp ->
      bv_unsigned sp + 16 <= sp0 ->                            (* [comment removed for export] *)
      4096 <= bv_unsigned ra -> ~ is_pc0 (bv_unsigned ra) ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> ASTACK_BOTTOM sp0 <= lo -> lo <= bv_unsigned sp - APRINT_STACK n ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m -> tp = wz ATP -> frm0 fc ->
      sh_zero m alloc_ceiling (2^47) ->                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      TINV TI np TRS -> np + PRINT_NP <= NPMAX TI -> Forall (STAT TI) S_PRINT_CONST ->
      lf_room 1 LF (Z.of_nat n) ->
      PRINT_COST <= B0 ->
      a0 = wz p -> ARGS a1 a2 ->
      LSCPS asegs (print_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np B0 n p lo m g)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz entry) fc None m (seg_rom asegs)) mo g.

  Definition cjprint_stmt : Prop := print_pre_stmt CJPRINT_ENTRY (fun _ _ => True).          (* [comment removed for export] *)
  Definition cjprintu_stmt : Prop := print_pre_stmt CJPRINTU_ENTRY (fun _ _ => True).        (* [comment removed for export] *)
  Definition pbuffered_stmt : Prop :=                                                         (* [comment removed for export] *)
    print_pre_stmt PBUFD_ENTRY (fun a1 _ => exists pre, a1 = wz pre /\ 0 <= pre < 2^31).
End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; [cbn; lia|]. cbn [bytes_le_to_Z].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range| apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with (2^8) in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as H0.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned.
    lazymatch goal with |- bv_wrap 8 ?x = _ => change (bv_wrap 8 x) with (x mod 2^8) end.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z_mod_mult, Z.lor_0_r. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by lia. rewrite Z.lor_0_l. exact IH.
Qed.

Lemma bytes_le_to_Z_bound : forall bs : list byte, bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. pose proof (bytes_le_to_Z_to_le_bytes (length bs) (bytes_le_to_Z bs) (bytes_le_to_Z_nonneg bs)) as E.
  rewrite Z_to_le_bytes_to_Z in E. rewrite E at 1. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma le8_of_bytes8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2^64) in B.
  pose proof (bytes_le_to_Z_nonneg bs).
  rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Lemma bytes16_words : forall bs : list byte, length bs = 16%nat -> exists w1 w2 : word, bs = le8 w1 ++ le8 w2.
Proof.
  intros bs L. exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (skipn 8 bs)).
  rewrite !le8_of_bytes8 by (rewrite ?length_firstn, ?length_skipn; lia). symmetry. apply firstn_skipn.
Qed.


End CeilWrap.
End CJ_print_iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface CJ_tree AShadow CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
Import CJ_print_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition AFUZZ_ENTRY : Z := 0x82358.

(* [comment removed for export] *)
Definition AFUZZ_STACK : Z := 64 + PARSE_DOC_STACK.
Definition FUZZ_COST (size : Z) : Z := 1024 * size + 2^20 + PRINT_COST.
Definition FUZZ_NP (size : Z) : Z := 128.
(* [comment removed for export] *)

Section Stmt.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Variable S_LIB : list (list Z).     (* [comment removed for export] *)

  Definition llvmfuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B np : Z)
      (D size : Z) (data : list byte) (lo : Z) (m : word -> option byte) (g : lghost)
      : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                             (m' : word -> option byte) (errv' : word) (LB' LX : list cblock) (TRS' : list (list Z)) (B' np' : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ a0 = wz 0
      /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' AERRNO [C4 errv']
      /\ ART AI sp0 SPB LB' [] TRS' B' m' mo' g' /\ Permutation LB' (LB ++ LX)     (* [comment removed for export] *)
      /\ dpres sp0 LB [] (bv_unsigned sp) m m'          (* [comment removed for export] *)
      /\ gmono g g'
      /\ TINV TI np' TRS' /\ np <= np' <= np + FUZZ_NP size
      /\ B - FUZZ_COST size <= B'
      /\ sh_zero m' alloc_ceiling (2^47)
      /\ (size <= 4 \/ bytes_at asegs m' D data).

  Definition llvmfuzz_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B np : Z)
           (D size : Z) (data : list byte) (lo : Z) (errv : word),
      ART AI sp0 SPB LB [] TRS B m mo g ->
      TINV TI np TRS -> np + FUZZ_NP size <= NPMAX TI ->
      (forall tr, In tr S_LIB -> STAT TI tr) ->
      (size <= 4 \/ (In (D, size) LB /\ bytes_at asegs m D data /\ Z.of_nat (length data) = size)) ->
      0 <= size < 2^26 ->
      rw_cells asegs m AERRNO [C4 errv] -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AFUZZ_STACK ->
      bv_unsigned sp <= SPB -> bv_unsigned sp mod 16 = 0 ->
      SPB < 2^62 -> sp0 <= 2^47 -> bv_unsigned sp + 16 <= ASTACK_TOP sp0 -> ASTACK_BOTTOM sp0 <= lo ->   (* [comment removed for export] *)
      bv_unsigned sp + 16 <= sp0 ->                            (* [comment removed for export] *)
      frm0 fc -> tp = wz ATP ->
      a0 = wz D -> a1 = wz size ->
      FUZZ_COST size <= B ->
      sh_zero m alloc_ceiling (2^47) ->                     (* [comment removed for export] *)
      LSCPS asegs (llvmfuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LB TRS B np D size data lo m g)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz AFUZZ_ENTRY) fc None m (seg_rom asegs)) mo g.
End Stmt.


End CeilWrap.
