(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition OUT_DEPTH : Z := 1024.        (* [comment removed for export] *)
Definition FMT_FP_DEPTH : Z := 4640.     (* [comment removed for export] *)
Definition PC_DEPTH : Z := 5184.         (* [comment removed for export] *)
Definition VF_DEPTH : Z := 5552.         (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SFILE_LO : Z := 0x31c470.      Definition SFILE_HI : Z := 0x3509a8.
(* [comment removed for export] *)
Definition SBUF_LO : Z := 0x3509b0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sink.
  Context {St : Type}.
  Variables (Fp B BS : Z).
  Variable SINK : mem -> St -> Prop.
  Variable TOPOK : Z -> Prop.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.

  (* [comment removed for export] *)
  Definition SR : list (Z * Z) := [(Fp, Fp + 232); (B, B + BS)].

  (* [comment removed for export] *)
  Definition sink_frame_stmt : Prop :=
    forall (W : list (Z * Z)) (m m' : mem) (st : St),
      SINK m st -> munch W m m' -> wmono usegs m m' ->
      Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv) W ->
      Forall (fun iv => snd iv <= B \/ B + BS <= fst iv) W ->
      SINK m' st.

  (* [comment removed for export] *)
  Definition sink_flags_stmt : Prop :=
    forall m st, SINK m st -> exists fl : byte, rw_cells usegs m Fp [CB 1 [fl]] /\ Z.land (bv_unsigned fl) 32 = 0.

  Definition topok_stmt : Prop := forall a b, a <= b -> TOPOK b -> TOPOK a.

  (* [comment removed for export] *)
  Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (S : Z) (bs : list Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at usegs m' S (zb bs).

  Definition out_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (bs : list Z) (lo : Z) (canary : word),
      SINK m st ->
      bytes_at usegs m (bv_unsigned a0) (zb bs) ->
      Forall (fun c => 0 <= c < 256) bs -> zlength bs < 2^31 ->
      a1 = Z_to_bv 64 (zlength bs) ->
      a2 = Z_to_bv 64 Fp ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary ->
      mem_inv usegs m ->
      (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
      (bv_unsigned a0 + zlength bs <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength bs <= Fp \/ Fp + 232 <= bv_unsigned a0) ->
      (bv_unsigned a0 + zlength bs <= B \/ B + BS <= bv_unsigned a0) ->
      implM usegs (OUT bs) st
            (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) bs lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x2b4c9c) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition fpcall_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch ((lo, bv_unsigned sp) :: SR) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary.
  (* [comment removed for export] *)

  Definition fpcall_stmt (c : Z * Z * Z * Z * Z) : Prop :=
    let '(y, w, p, fl, t) := c in
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      SINK m st ->
      y = bv_unsigned a1 + 2^64 * bv_unsigned a2 ->
      a0 = Z_to_bv 64 Fp -> a3 = Z_to_bv 64 w -> a4 = Z_to_bv 64 p -> a5 = Z_to_bv 64 fl -> a6 = Z_to_bv 64 t ->
      bv_unsigned a7 <> 5 ->
      (-2^31 <= w <= 1) -> (-2^31 <= p < 2^20) -> (0 <= fl < 2^32) -> (0 <= t < 256) -> Z.lor t 32 <> 97 ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FMT_FP_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary ->
      mem_inv usegs m -> frm0 fc ->
      (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (B + BS <= lo \/ bv_unsigned sp <= B) ->
      implM usegs (OUTFP y w p fl t) st
            (fpcall_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x2b61f0) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition arg_ok (m : mem) (lo sp ap : Z) (slot : word) (a : parg) : Prop :=
    match a with
    | PA_s s => exists slack : list byte,
        bytes_at usegs m (bv_unsigned slot) (zb s ++ Z_to_bv 8 0 :: slack)
        /\ Forall (fun c => 0 < c < 256) s
        /\ ((- (bv_unsigned slot + zlength s + 1)) mod 8 <= zlength slack)
        /\ 0 < bv_unsigned slot
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= B \/ B + BS <= bv_unsigned slot)
        /\ (bv_unsigned slot + zlength s + 1 + zlength slack <= ap \/ ap + 8 <= bv_unsigned slot)
    | PA_sn => bv_unsigned slot = 0
    | PA_i i => -2^31 <= i < 2^31 /\ bv_unsigned slot mod 2^32 = i mod 2^32
    | PA_u u => 0 <= u < 2^32 /\ bv_unsigned slot mod 2^32 = u
    | PA_z u => bv_unsigned slot = u
    | PA_g d => bv_unsigned slot = d
    end.
  Fixpoint args_ok (m : mem) (lo sp ap : Z) (slots : list word) (args : list parg) : Prop :=
    match args with
    | [] => True
    | a :: args' => match slots with
                    | [] => False
                    | w :: slots' => arg_ok m lo sp ap w a /\ args_ok m lo sp ap slots' args'
                    end
    end.

  Definition printf_core_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (AP lo : Z) (canary : word) (m : mem) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom usegs)
      /\ munch ((lo, bv_unsigned sp) :: (AP, AP + 8) :: SR) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells usegs m' AP [C8 apv]
      /\ (0 <= r <= INT_MAX).

  (* [comment removed for export] *)
  Definition printf_core_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word)
           (fmt : list Z) (VA i : Z) (slots : list word) (args : list parg),
      SINK m st ->
      bytes_at usegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
      a0 = Z_to_bv 64 Fp ->
      rw_cells usegs m (bv_unsigned a2) [C8 (Z_to_bv 64 (VA + 8 * i))] ->
      va_area m VA slots -> 0 <= i -> args_ok m lo (bv_unsigned sp) (bv_unsigned a2) (skipn (Z.to_nat i) slots) args ->
      Forall fpcall_stmt (fp_calls (length fmt) fmt args) ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) -> TOPOK (bv_unsigned sp) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      (* [comment removed for export] *)
      (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) -> (0 <= BS) ->
      ((3261552 <= Fp /\ Fp + 232 <= 3475880) \/ (bv_unsigned a2 + 8 <= Fp /\ Fp + 232 <= VA)) ->
      ((3475888 <= B /\ B + BS <= lo) \/ (bv_unsigned a2 + 8 <= B /\ B + BS <= VA)) ->
      (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
      implM usegs (printf_model OUT OUTFP fmt args) st
            (printf_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (bv_unsigned a2) lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x2b51b8) fc None m (seg_rom usegs)).
End Sink.

(* [comment removed for export] *)
Definition printf_core1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary.

Definition printf_core1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (fmt : list Z),
    bytes_at usegs m (bv_unsigned a1) (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt ->
    pass1_ok fmt = true ->
    a0 = Z_to_bv 64 0 ->
    stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - PC_DEPTH) -> (GLOBALS_TOP <= lo) ->
    (bv_unsigned sp < 2^63) ->
    ssp_cells m canary -> mem_inv usegs m ->
    (bv_unsigned a1 + zlength fmt <= STATIC_SPLIT) ->
    (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + 8 <= 2^64) ->
    evt usegs (printf_core1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2b51b8) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section SnSink.
  (* [comment removed for export] *)
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Definition SN_CAP : Z := 80.

  Definition SINK_sn (m : mem) (o : list Z) : Prop :=
    exists junk : list byte,
      wfile m Fp fl0 j1 j2 lbfw B (zb o) junk
      /\ rw_cells usegs m (Fp + 148) frest /\ Z.of_nat (cells_size frest) = 84
      /\ zlength o + zlength junk = SN_CAP
      /\ (B + SN_CAP <= Fp \/ Fp + 232 <= B)
      /\ TOP <= Fp /\ TOP <= B.
  Definition TOPOK_sn (sp : Z) : Prop := sp <= TOP.

  Definition OUT_sn (bs : list Z) : M (list Z) unit :=
    o <- mget ;; if zlength o + zlength bs <=? SN_CAP then mput (o ++ bs) else munr.

  (* [comment removed for export] *)
  Definition OUTFP_sn (y w p fl t : Z) : M (list Z) Z := munr.
End SnSink.

(* [comment removed for export] *)
Definition TOPOK_none (sp : Z) : Prop := True.

