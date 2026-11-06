(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require CJ_tree.
Module CJ_print_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.CJ_tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ENSURE_ENTRY : Z := 0x143a4.
Definition PSTR_ENTRY   : Z := 0x144dc.
Definition PVALUE_ENTRY : Z := 0x130fc.
Definition PRINT_ENTRY  : Z := 0x12efc.   (* [comment removed for export] *)
Definition CJPRINT_ENTRY : Z := 0x12ef4.  (* [comment removed for export] *)
Definition CJPRINTU_ENTRY : Z := 0x13040. (* [comment removed for export] *)
Definition PBUFD_ENTRY  : Z := 0x13048.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ENSURE_STACK : Z := 32 + RMALLOC_STACK.                 (* [comment removed for export] *)
Definition PSTR_STACK   : Z := 112 + ENSURE_STACK.                 (* [comment removed for export] *)
Definition PV_BASE      : Z := 9504.                               (* [comment removed for export] *)
Definition PV_STACK (n : nat) : Z := 128 * Z.of_nat n + PV_BASE.   (* [comment removed for export] *)
Definition PRINT_STACK (n : nat) : Z := 112 + PV_STACK n.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_callee_saved (k : bv 5) : Prop :=
  bv_unsigned k = 8 \/ bv_unsigned k = 9 \/ (18 <= bv_unsigned k <= 27).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pb_struct (m : word -> option byte) (PB buf len off dep : Z) (fw : word) : Prop :=
  rw_cells psegs m PB [C8 (wz buf); C8 (wz len); C8 (wz off); C8 (wz dep); C4 (wz 0); C4 fw;
                      C8 (wz PMALLOC); C8 (wz PFREE); C8 (wz PREALLOC)].

Definition pb_data (m : word -> option byte) (buf len : Z) (bs : list byte) : Prop :=
  u8arr psegs m buf bs /\ Z.of_nat (length bs) = len.

Definition pb_nums (len off dep : Z) : Prop := 0 <= off <= len /\ len < 2^31 /\ 0 <= dep.

(* [comment removed for export] *)
Definition pb_nul (bs : list byte) (len off : Z) : Prop :=
  exists K, 0 <= K /\ off + K < len /\ nth_error bs (Z.to_nat (off + K)) = Some (wb 0).

(* [comment removed for export] *)
Definition pv_agree (LR : list cblock) (SP PB : Z) (m m' : word -> option byte) : Prop :=
  magree (fun a => cj_client_addr LR SP a /\ ~ (PB <= a < PB + 64)) m m'.

(* [comment removed for export] *)
Definition pb_place (SP PB SPB : Z) : Prop := SP <= PB /\ PB + 64 <= SPB /\ SPB < 2^62.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmts.
  Variable HI : cj_heap_iface.

  (* [comment removed for export] *)
  Definition ensure_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (SPB : Z) (LR : list cblock) (PB buf len off dep : Z) (fw : word) (bs : list byte) (needed lo : Z)
      (m : word -> option byte) : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word) (LB' : list cblock),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom psegs)
      /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' PERRNO [C4 errv']
      /\ pv_agree LR (bv_unsigned sp) PB m m'
      /\ LHEAP HI SPB LB' m' mo'
      /\ ( (* [comment removed for export] *)
           (a0 = wz 0 /\ Permutation LR LB' /\ pb_struct m' PB 0 0 off dep fw)
           (* [comment removed for export] *)
        \/ (a0 = wz 0 /\ Permutation ((buf, len) :: LR) LB' /\ pb_struct m' PB buf len off dep fw /\ pb_data m' buf len bs)
           (* [comment removed for export] *)
        \/ (exists buf' len' bs', a0 = wz (buf' + off) /\ Permutation ((buf', len') :: LR) LB'
              /\ pb_struct m' PB buf' len' off dep fw /\ pb_data m' buf' len' bs'
              /\ needed + off + 1 <= len' /\ len' < 2^31) ).

  Definition ensure_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR : list cblock) (PB buf len off dep : Z) (fw : word) (bs : list byte) (needed lo : Z) (errv : word),
      LHEAP HI SPB LB m mo -> Permutation ((buf, len) :: LR) LB ->
      pb_struct m PB buf len off dep fw -> pb_data m buf len bs -> pb_nums len off dep ->
      pb_place (bv_unsigned sp) PB SPB ->
      stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
      rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP ->
      a0 = wz PB -> a1 = wz needed -> 0 <= needed < 2^64 ->
      SCPS psegs (ensure_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LR PB buf len off dep fw bs needed lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ENSURE_ENTRY) fc None m (seg_rom psegs)) mo.

  (* [comment removed for export] *)
  Definition print_outcome (SPB : Z) (LR : list cblock) (PB dep : Z) (fw : word) (a0 : word)
      (m' : word -> option byte) (mo' : Model) : Prop :=
    exists (LB' : list cblock) (buf' len' off' : Z),
      LHEAP HI SPB LB' m' mo'
      /\ ( (a0 = wz 0 /\ exists dep', pb_struct m' PB buf' len' off' dep' fw
              /\ ( (buf' = 0 /\ Permutation LR LB')
                   \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB') ))
        \/ (a0 = wz 1 /\ exists bs', Permutation ((buf', len') :: LR) LB'
              /\ pb_struct m' PB buf' len' off' dep fw /\ pb_data m' buf' len' bs' /\ pb_nums len' off' dep
              /\ pb_nul bs' len' off') ).

  (* [comment removed for export] *)
  Definition pstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LR : list cblock) (PB dep : Z) (fw : word) (lo : Z) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ mem_inv psegs m' /\ frm0 fc' /\ (forall k : bv 5, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' PERRNO [C4 errv'] /\ CJST m'
      /\ pv_agree LR (bv_unsigned sp) PB m m'
      /\ print_outcome SPB LR PB dep fw a0 m' mo'.

  Definition pstr_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR Bv : list cblock) (PB buf len off dep s : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word),
      LHEAP HI SPB LB m mo -> Permutation ((buf, len) :: LR) LB ->
      pb_struct m PB buf len off dep fw -> pb_data m buf len bs -> pb_nums len off dep ->
      cj_str m s Bv -> (forall b, In b Bv -> In b LR) ->
      CJST m ->
      pb_place (bv_unsigned sp) PB SPB ->
      stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PSTR_STACK ->
      rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> frm0 fc ->
      a0 = wz s -> a1 = wz PB ->
      SCPS psegs (pstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR PB dep fw lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PSTR_ENTRY) fc None m (seg_rom psegs)) mo.

  (* [comment removed for export] *)
  Definition pvalue_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ mem_inv psegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' PERRNO [C4 errv'] /\ CJST m'
      /\ pv_agree LR (bv_unsigned sp) PB m m'
      /\ cj_chain CJ_PRINTABLE m' n p B
      /\ print_outcome SPB LR PB dep fw a0 m' mo'.

  Definition pvalue_spec_at (n : nat) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR B : list cblock) (PB buf len off dep p : Z) (fw : word) (bs : list byte) (lo : Z) (errv : word),
      LHEAP HI SPB LB m mo -> Permutation ((buf, len) :: LR) LB ->
      pb_struct m PB buf len off dep fw -> pb_data m buf len bs -> pb_nums len off dep ->
      dep + Z.of_nat n <= 2^40 ->
      cj_chain CJ_PRINTABLE m n p B -> p <> 0 -> (forall b, In b B -> In b LR) ->
      CJST m ->
      pb_place (bv_unsigned sp) PB SPB -> bv_unsigned sp mod 16 = 0 ->
      stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PV_STACK n ->
      rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> frm0 fc ->
      a0 = wz p -> a1 = wz PB ->
      SCPS psegs (pvalue_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PVALUE_ENTRY) fc None m (seg_rom psegs)) mo.

  (* [comment removed for export] *)
  Definition print_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LR B : list cblock) (n : nat) (p : Z) (lo : Z) (errv : word) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word) (LB' : list cblock),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ mem_inv psegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' PERRNO [C4 errv'] /\ CJST m'
      /\ cj_pres (B ++ LR) (bv_unsigned sp) m m'
      /\ cj_chain CJ_PRINTABLE m' n p B
      /\ LHEAP HI SPB LB' m' mo'
      /\ ( (a0 = wz 0 /\ Permutation (B ++ LR) LB')
        \/ (exists q k, a0 = wz q /\ q <> 0 /\ Permutation ((q, k) :: B ++ LR) LB') ).

  Definition print_pre_stmt (entry : Z) (ARGS : word -> word -> Prop) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (SPB : Z) (LB LR B : list cblock) (n : nat) (p : Z) (lo : Z) (errv : word),
      LHEAP HI SPB LB m mo -> Permutation (B ++ LR) LB ->
      cj_chain CJ_PRINTABLE m n p B -> p <> 0 -> (n <= 1001)%nat ->
      CJST m ->
      bv_unsigned sp <= SPB -> SPB < 2^62 -> bv_unsigned sp mod 16 = 0 ->
      stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PRINT_STACK n ->
      rw_cells psegs m PERRNO [C4 errv] -> mem_inv psegs m -> tp = wz PTP -> frm0 fc ->
      a0 = wz p -> ARGS a1 a2 ->
      SCPS psegs (print_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p lo errv m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz entry) fc None m (seg_rom psegs)) mo.

  Definition print_stmt : Prop := print_pre_stmt PRINT_ENTRY (fun _ _ => True).             (* [comment removed for export] *)
  Definition cjprint_stmt : Prop := print_pre_stmt CJPRINT_ENTRY (fun _ _ => True).         (* [comment removed for export] *)
  Definition cjprintu_stmt : Prop := print_pre_stmt CJPRINTU_ENTRY (fun _ _ => True).       (* [comment removed for export] *)
  Definition pbuffered_stmt : Prop :=                                                        (* [comment removed for export] *)
    print_pre_stmt PBUFD_ENTRY (fun a1 _ => exists pre, a1 = wz pre /\ 0 <= pre < 2^31).
End Stmts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pb_struct_size : cells_size [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0);
                                   C8 (wz PMALLOC); C8 (wz PFREE); C8 (wz PREALLOC)] = 64%nat.
Proof. reflexivity. Qed.

Lemma pv_agree_refl : forall LR SP PB m, pv_agree LR SP PB m m.
Proof. intros. apply magree_refl. Qed.

Lemma pv_agree_trans : forall LR SP PB m1 m2 m3,
  pv_agree LR SP PB m1 m2 -> pv_agree LR SP PB m2 m3 -> pv_agree LR SP PB m1 m3.
Proof. intros. eapply magree_trans; eauto. Qed.

(* [comment removed for export] *)
Lemma pv_agree_weaken : forall LR LR' SP SP' PB m m',
  pv_agree LR SP PB m m' -> SP <= SP' -> (forall b, In b LR' -> In b LR) -> pv_agree LR' SP' PB m m'.
Proof.
  intros LR LR' SP SP' PB m m' H HS HL. eapply magree_mono; [exact H|]. cbv beta.
  intros a [Hc Hn]. split; [|exact Hn].
  destruct Hc as [Hc|[Hc|(A & n & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists A, n. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma pv_agree_of_cj_pres : forall LR SP PB m m', cj_pres LR SP m m' -> pv_agree LR SP PB m m'.
Proof. intros LR SP PB m m' H a Ha [Hc _]. apply H; assumption. Qed.

(* [comment removed for export] *)
Lemma cj_pres_of_pv_agree : forall LR SP PB m m' SP',
  pv_agree LR SP PB m m' -> PIMG_HI <= SP -> SP <= PB -> PB + 64 <= SP' ->
  (forall A n, In (A, n) LR -> A + n <= SP) ->
  cj_pres LR SP' m m'.
Proof.
  intros LR SP PB m m' SP' H H0 H1 H2 HB a Ha Hc. apply H; [exact Ha|]. split.
  - destruct Hc as [Hs|[Hd|Hb]]; [left; lia| right; left; exact Hd| right; right; exact Hb].
  - destruct Hc as [Hs|[[Hd _]|(A & n & Hin & Hr)]]; [lia| unfold PDATA_LO, PIMG_HI in *; lia|].
    pose proof (HB _ _ Hin). lia.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg CJ_iface CJ_tree.
Import CJ_print_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition esc_extra (c : Z) : Z :=
  if (c =? 34) || (c =? 92) || (c =? 8) || (c =? 12) || (c =? 10) || (c =? 13) || (c =? 9) then 1
  else if c <? 32 then 5 else 0.

Fixpoint esc_count (s : list byte) : Z :=
  match s with [] => 0 | b :: s' => esc_extra (bv_unsigned b) + esc_count s' end.

Lemma esc_extra_range : forall c, 0 <= esc_extra c <= 5.
Proof. intros c. unfold esc_extra. destruct (_ || _); [lia|]. destruct (c <? 32); lia. Qed.

Lemma esc_count_app : forall a b, esc_count (a ++ b) = esc_count a + esc_count b.
Proof. induction a as [|x a IH]; intros b; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma esc_count_range : forall s, 0 <= esc_count s <= 5 * Z.of_nat (length s).
Proof. induction s as [|b s IH]; cbn; [lia|]. pose proof (esc_extra_range (bv_unsigned b)). lia. Qed.

Lemma esc_count_firstn_le : forall s i, esc_count (firstn i s) <= esc_count s.
Proof.
  intros s i. rewrite <- (firstn_skipn i s) at 2. rewrite esc_count_app. pose proof (esc_count_range (skipn i s)). lia.
Qed.

Lemma firstn_S_snoc : forall {A} (pre post : list A) (b : A), firstn (S (length pre)) (pre ++ b :: post) = pre ++ [b].
Proof. intros A pre post b. induction pre as [|x pre IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma firstn_len_app : forall {A} (pre post : list A), firstn (length pre) (pre ++ post) = pre.
Proof. intros A pre post. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma esc_count_firstn_S : forall s i b, nth_error s i = Some b ->
  esc_count (firstn (S i) s) = esc_count (firstn i s) + esc_extra (bv_unsigned b).
Proof.
  intros s i b H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen). subst i.
  rewrite firstn_S_snoc, firstn_len_app, esc_count_app. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition RMASK : Z := 0x400003700.
Definition resc1b (c : Z) : bool := (c =? 8) || (c =? 9) || (c =? 10) || (c =? 12) || (c =? 13) || (c =? 34).

Lemma rmask_bit : forall c, 0 <= c <= 34 ->
  Z.land (Z.shiftr RMASK (Z.land c 63)) 1 = if resc1b c then 1 else 0.
Proof.
  intros c Hc.
  assert (G : forall n : nat, (n <= 34)%nat -> Z.land (Z.shiftr RMASK (Z.land (Z.of_nat n) 63)) 1 = if resc1b (Z.of_nat n) then 1 else 0).
  { intros n Hn. do 35 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  specialize (G (Z.to_nat c) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.

Lemma rmask_bit' : forall c, 0 <= c <= 34 ->
  Z.land (Z.shiftr RMASK c) 1 = if resc1b c then 1 else 0.
Proof.
  intros c Hc.
  assert (G : forall n : nat, (n <= 34)%nat -> Z.land (Z.shiftr RMASK (Z.of_nat n)) 1 = if resc1b (Z.of_nat n) then 1 else 0).
  { intros n Hn. do 35 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  specialize (G (Z.to_nat c) ltac:(lia)). rewrite Z2Nat.id in G by lia. exact G.
Qed.

Lemma resc1b_extra : forall c, 0 < c <= 34 -> esc_extra c = if resc1b c then 1 else if c <? 32 then 5 else 0.
Proof.
  intros c Hc. unfold esc_extra, resc1b.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try reflexivity; try lia.
Qed.

Lemma esc_extra_gt34 : forall c, 34 < c -> esc_extra c = if c =? 92 then 1 else 0.
Proof.
  intros c Hc. unfold esc_extra.
  destruct (Z.eqb_spec c 34), (Z.eqb_spec c 92), (Z.eqb_spec c 8), (Z.eqb_spec c 12), (Z.eqb_spec c 10), (Z.eqb_spec c 13), (Z.eqb_spec c 9); cbn [orb]; try reflexivity; try lia.
  destruct (Z.ltb_spec c 32); [lia| reflexivity].
Qed.

Lemma unsigned_lit8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact Hc. Qed.

Lemma neg_flag5 : forall b, Z.land (bv_swrap 32 (0 - Z.b2z b) mod 18446744073709551616) 5 = if b then 5 else 0.
Proof. intros [|]; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Str.
  Variables (S : Z) (str tail : list byte).
  Hypothesis NONUL : ~ In (wb 0) str.

  Notation full := (str ++ wb 0 :: tail).
  Notation L := (Z.of_nat (length str)).
  Notation E := (esc_count str).

  Lemma full_nth_lt : forall i, 0 <= i < L ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ nth_error str (Z.to_nat i) = Some b /\ 0 < bv_unsigned b < 256.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:EQ.
    - exists b. split. { rewrite nth_error_app1 by lia. exact EQ. } split; [reflexivity|].
      pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
      enough (bv_unsigned b <> 0) by lia.
      intros Hb. apply NONUL. replace (wb 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in EQ. lia.
  Qed.

  Lemma full_nth_len : nth_error full (Z.to_nat L) = Some (wb 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition chb (i : Z) : byte := nth (Z.to_nat i) full (wb 0).
  Notation ch i := (bv_unsigned (chb i)).

  Lemma chb_nth : forall i, 0 <= i <= L -> nth_error full (Z.to_nat i) = Some (chb i).
  Proof.
    intros i Hi. unfold chb. destruct (nth_error full (Z.to_nat i)) as [b|] eqn:EQ.
    - f_equal. symmetry. apply nth_error_nth. exact EQ.
    - apply nth_error_None in EQ. rewrite length_app in EQ. cbn [length] in EQ. lia.
  Qed.

  Lemma ch_L : ch L = 0.
  Proof. pose proof (chb_nth L ltac:(lia)) as H. rewrite full_nth_len in H. injection H as <-. reflexivity. Qed.

  Lemma ch_lt : forall i, 0 <= i < L -> nth_error str (Z.to_nat i) = Some (chb i) /\ 0 < ch i < 256.
  Proof.
    intros i Hi. destruct (full_nth_lt i Hi) as (b & H1 & H2 & H3).
    rewrite (chb_nth i ltac:(lia)) in H1. injection H1 as ->. auto.
  Qed.

  Lemma ch_range : forall i, 0 <= i <= L -> 0 <= ch i < 256 /\ (ch i = 0 <-> i = L).
  Proof.
    intros i Hi. destruct (Z.eq_dec i L) as [->|NE].
    - rewrite ch_L. lia.
    - destruct (ch_lt i ltac:(lia)) as [_ H]. lia.
  Qed.

  Lemma ch_read : forall m i, bytes_at psegs m S full -> 0 <= i <= L -> ov_read_bytes psegs m (wa (S + i)) 1 = Some [chb i].
  Proof. intros m i STR Hi. eapply u8ro_read; [exact STR| apply chb_nth; exact Hi| lia| reflexivity]. Qed.

  Lemma esc_step : forall i, 0 <= i < L -> esc_count (firstn (Z.to_nat (i + 1)) str) = esc_count (firstn (Z.to_nat i) str) + esc_extra (ch i).
  Proof.
    intros i Hi. destruct (ch_lt i Hi) as [H2 _].
    replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. apply esc_count_firstn_S. exact H2.
  Qed.

  (* [comment removed for export] *)
  Definition pos (i : Z) : Z := i + esc_count (firstn (Z.to_nat i) str).

  Lemma pos_0 : pos 0 = 0.
  Proof. reflexivity. Qed.

  Lemma pos_step : forall i, 0 <= i < L -> pos (i + 1) = pos i + 1 + esc_extra (ch i).
  Proof. intros i Hi. unfold pos. rewrite esc_step by exact Hi. lia. Qed.

  Lemma pos_bound : forall i, 0 <= i <= L -> i <= pos i /\ pos i + (L - i) <= L + E.
  Proof.
    intros i Hi. unfold pos. pose proof (esc_count_range (firstn (Z.to_nat i) str)) as R1.
    pose proof (esc_count_firstn_le str (Z.to_nat i)) as R2. lia.
  Qed.

  Lemma pos_next_bound : forall i, 0 <= i < L -> pos i + 1 + esc_extra (ch i) + (L - i - 1) <= L + E.
  Proof. intros i Hi. rewrite <- pos_step by exact Hi. pose proof (pos_bound (i + 1) ltac:(lia)). lia. Qed.

  Lemma pos_L : pos L = L + E.
  Proof. unfold pos. rewrite Nat2Z.id, firstn_all. reflexivity. Qed.

 Section Count.
  Variables (m : word -> option byte).
  Hypothesis STR : bytes_at psegs m S full.
  Hypothesis MI : mem_inv psegs m.

  Lemma S_bound : 0 <= S /\ S + L + 1 + Z.of_nat (length tail) <= 2^64.
  Proof. pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite length_app in B. cbn [length] in B. lia. Qed.

  (* [comment removed for export] *)
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x11 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation CST pc i e c x15 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S) (Z_to_bv 64 34) x11 (Z_to_bv 64 92) (Z_to_bv 64 17179883264) (Z_to_bv 64 c) x15 x16 x17
             x18 (Z_to_bv 64 i) (Z_to_bv 64 e) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
  Definition count_end : machine_state -> Prop :=
    fun ms' => exists c x15, ms' = CST 0x14598 L E c x15.

  Definition P38 (i : Z) : Prop := forall x15, ch i <= 34 ->
    evt psegs count_end (CST 0x14568 i (esc_count (firstn (Z.to_nat i) str)) (ch i) x15).
  Definition P60 (i : Z) : Prop := forall x15, (34 < ch i \/ (ch i <> 0 /\ resc1b (ch i) = false)) ->
    evt psegs count_end (CST 0x14590 i (esc_count (firstn (Z.to_nat i) str)) (ch i) x15).

  Lemma count_both : forall (k : nat) (i : Z), Z.of_nat k = L - i -> 0 <= i <= L -> P38 i /\ P60 i.
  Proof.
    induction k as [|k IH]; intros i Hk Hi; unfold P38, P60.
    - assert (Ei : i = L) by lia. subst i. rewrite !ch_L. split; intros x15 Hc.
      + pose proof S_bound as SB.
        zstep. zstep. zstep. if_true. zstep. if_true.
        apply evt_done. unfold count_end. rewrite firstn_all2 by lia. do 2 eexists. reflexivity.
      + exfalso. lia.
    - assert (Hi' : 0 <= i < L) by lia.
      destruct (IH (i+1) ltac:(lia) ltac:(lia)) as [IH38 IH60]. unfold P38, P60 in IH38, IH60.
      pose proof (ch_read m (i+1) STR ltac:(lia)) as RD1. destruct (ch_range (i+1) ltac:(lia)) as [CR1 CZ1].
      destruct (ch_lt i Hi') as [_ CR].
      pose proof (esc_step i Hi') as ES.
      pose proof S_bound as SB.
      (* [comment removed for export] *)
      assert (D54 : forall x15, evt psegs count_end (CST 0x14584 (i + 1) (esc_count (firstn (Z.to_nat (i + 1)) str)) (ch (i + 1)) x15)).
      { intros x15. zstep. if_cases K; zify_cond K.
        - apply IH38. lia.
        - zstep. apply IH60. lia. }
      assert (D34 : forall x15, evt psegs count_end (CST 0x14564 (i + 1) (esc_count (firstn (Z.to_nat (i + 1)) str)) (ch (i + 1)) x15)).
      { intros x15. zstep. if_cases K; zify_cond K.
        - apply IH60. lia.
        - apply IH38. lia. }
      (* [comment removed for export] *)
      assert (B44 : forall x15, esc_extra (ch i) = 1 -> evt psegs count_end (CST 0x14574 i (esc_count (firstn (Z.to_nat i) str)) (ch i) x15)).
      { intros x15 HE. zstep. zstep. replace (S + (i + 1)) with (S + i + 1) in RD1 by lia. zstep. zstep. cbv beta.
        replace (esc_count (firstn (Z.to_nat i) str) + 1) with (esc_count (firstn (Z.to_nat (i + 1)) str)) by lia.
        apply D54. }
      (* [comment removed for export] *)
      assert (B18 : forall x15, esc_extra (ch i) = (if ch i <? 32 then 5 else 0) ->
                evt psegs count_end (CST 0x14548 i (esc_count (firstn (Z.to_nat i) str)) (ch i) x15)).
      { intros x15 HE. zstep. zstep. zstep. rewrite neg_flag5. rewrite <- HE.
        zstep. zstep. replace (S + (i + 1)) with (S + i + 1) in RD1 by lia. zstep. zstep. cbv beta.
        rewrite <- ES. apply D34. }
      split; intros x15 Hc.
      + (* [comment removed for export] *)
        zstep. zstep. rewrite (Z.mod_small (ch i) 64) by lia. unfold RMASK in *. rewrite rmask_bit' by lia.
        destruct (resc1b (ch i)) eqn:RB.
        * zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. apply B44. rewrite resc1b_extra, RB by lia. reflexivity.
        * zstep. if_cases K; zify_cond K; [| exfalso; lia]. clear K.
          zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
          zstep. apply B18. rewrite resc1b_extra, RB by lia. reflexivity.
      + (* [comment removed for export] *)
        zstep. if_cases K; zify_cond K.
        * apply B44. rewrite esc_extra_gt34, K by lia. reflexivity.
        * zstep. apply B18. destruct (Z_lt_le_dec 34 (ch i)) as [Hgt|Hle].
          -- rewrite esc_extra_gt34 by lia. replace (ch i =? 92) with false by (symmetry; apply Z.eqb_neq; lia).
             replace (ch i <? 32) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
          -- destruct Hc as [Hc|[Hz RB]]; [exfalso; lia|]. rewrite resc1b_extra, RB by lia. reflexivity.
  Qed.

  Lemma count_loop : forall (a4 : word) x15, evt psegs count_end (CST 0x14538 0 0 (bv_unsigned a4) x15).
  Proof.
    intros a4 x15. pose proof S_bound as SB.
    pose proof (ch_read m 0 STR ltac:(lia)) as RD0. destruct (ch_range 0 ltac:(lia)) as [CR0 CZ0]. rewrite Z.add_0_r in RD0.
    destruct (count_both (Z.to_nat L) 0 ltac:(lia) ltac:(lia)) as [H38 H60]. unfold P38, P60 in H38, H60. cbn [Z.to_nat firstn esc_count] in H38, H60.
    zstep. zstep. cbv beta.
    zstep. if_cases K; zify_cond K.
    - apply H38. lia.
    - zstep. apply H60. lia.
  Qed.

 End Count.
End Str.
