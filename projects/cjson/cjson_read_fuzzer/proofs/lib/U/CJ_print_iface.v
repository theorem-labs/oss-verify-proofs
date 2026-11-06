(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ENSURE_ENTRY : Z := 0x15564.
Definition PSTR_ENTRY   : Z := 0x156ac.
Definition PVALUE_ENTRY : Z := 0x14370.
Definition PRINT_ENTRY  : Z := 0x1415c.   (* [comment removed for export] *)
Definition CJPRINT_ENTRY : Z := 0x14154.  (* [comment removed for export] *)
Definition CJPRINTU_ENTRY : Z := 0x142b4. (* [comment removed for export] *)
Definition PBUFD_ENTRY  : Z := 0x142bc.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ENSURE_STACK : Z := 32 + RMALLOC_STACK.                 (* [comment removed for export] *)
Definition PSTR_STACK   : Z := 128 + ENSURE_STACK.                 (* [comment removed for export] *)
Definition PV_BASE      : Z := 9504.                               (* [comment removed for export] *)
Definition PV_STACK (n : nat) : Z := 128 * Z.of_nat n + PV_BASE.   (* [comment removed for export] *)
Definition PRINT_STACK (n : nat) : Z := 112 + PV_STACK n.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_callee_saved (k : bv 5) : Prop :=
  bv_unsigned k = 8 \/ bv_unsigned k = 9 \/ (18 <= bv_unsigned k <= 27).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pb_struct (m : word -> option byte) (PB buf len off dep : Z) (fw : word) : Prop :=
  rw_cells usegs m PB [C8 (wz buf); C8 (wz len); C8 (wz off); C8 (wz dep); C4 (wz 0); C4 fw;
                      C8 (wz PMALLOC); C8 (wz PFREE); C8 (wz PREALLOC)].

Definition pb_data (m : word -> option byte) (buf len : Z) (bs : list byte) : Prop :=
  u8arr usegs m buf bs /\ Z.of_nat (length bs) = len.

Definition pb_nums (len off dep : Z) : Prop := 0 <= off <= len /\ len < 2^31 /\ 0 <= dep.

(* [comment removed for export] *)
Definition pb_nul (bs : list byte) (len off : Z) : Prop :=
  exists K, 0 <= K /\ off + K < len /\ nth_error bs (Z.to_nat (off + K)) = Some (wb 0).

(* [comment removed for export] *)
Definition pv_agree (LR : list cblock) (SP PB : Z) (m m' : word -> option byte) : Prop :=
  magree (fun a => cj_client_addr LR SP a /\ ~ (PB <= a < PB + 64)) m m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pb_place (SP PB SPB : Z) : Prop := SP <= PB /\ PB + 64 <= SPB /\ SPB < 2^62 /\ PB mod 8 = 0.

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
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' PERRNO [C4 errv']
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
      stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ENSURE_STACK ->
      rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m -> tp = wz PTP ->
      a0 = wz PB -> a1 = wz needed -> 0 <= needed < 2^64 ->
      SCPS usegs (ensure_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LR PB buf len off dep fw bs needed lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ENSURE_ENTRY) fc None m (seg_rom usegs)) mo.

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
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ frm0 fc' /\ (forall k : bv 5, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' PERRNO [C4 errv'] /\ CJST m'
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
      stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PSTR_STACK ->
      rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m -> tp = wz PTP -> frm0 fc ->
      a0 = wz s -> a1 = wz PB ->
      SCPS usegs (pstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR PB dep fw lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PSTR_ENTRY) fc None m (seg_rom usegs)) mo.

  (* [comment removed for export] *)
  Definition pvalue_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' PERRNO [C4 errv'] /\ CJST m'
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
      stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PV_STACK n ->
      rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m -> tp = wz PTP -> frm0 fc ->
      a0 = wz p -> a1 = wz PB ->
      SCPS usegs (pvalue_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p PB dep fw lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PVALUE_ENTRY) fc None m (seg_rom usegs)) mo.

  (* [comment removed for export] *)
  Definition print_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (SPB : Z) (LR B : list cblock) (n : nat) (p : Z) (lo : Z) (errv : word) (m : word -> option byte)
      : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                          (m' : word -> option byte) (errv' : word) (LB' : list cblock),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ frm0 fc' /\ (forall k : bv 5, fp_callee_saved k -> reg_get F' k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' PERRNO [C4 errv'] /\ CJST m'
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
      stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PRINT_STACK n ->
      rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m -> tp = wz PTP -> frm0 fc ->
      a0 = wz p -> ARGS a1 a2 ->
      SCPS usegs (print_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F SPB LR B n p lo errv m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz entry) fc None m (seg_rom usegs)) mo.

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
