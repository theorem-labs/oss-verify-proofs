(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_irt F_rip I_printf_lib I_printf_common.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition zb8 (l : list Z) : list byte := map (Z_to_bv 8) l.

(* [comment removed for export] *)
Definition FMT_D : Z := 0x1482c.
Definition FMT_D_chars : list Z := [37; 100; 10]%Z.
(* [comment removed for export] *)
Definition FMT_TOOBIG : Z := 0x198e7.
Definition FMT_TOOBIG_chars : list Z :=
  [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]%Z.

End CANSEC1.
Ltac img_strz A B :=
  intros m MI; apply ro_bytes_at; [exact MI| unfold A; lia| unfold A, B, zb8; cbn; lia|];
  apply ro_bytes_b_sound; vm_compute; reflexivity.
Section CANSEC2. Context {rc : runConstT}.
Lemma fmt_d_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_D (zb8 FMT_D_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_D FMT_D_chars. Qed.
Lemma fmt_toobig_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_TOOBIG (zb8 FMT_TOOBIG_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_TOOBIG FMT_TOOBIG_chars. Qed.

End CANSEC2.
Ltac norm_len CH :=
  unfold zb8, CH; repeat match goal with |- context [Z.of_nat (length ?l)] => let n := eval cbv in (Z.of_nat (length l)) in change (Z.of_nat (length l)) with n end.
Ltac pci A BY CH :=
  lazymatch goal with
  | |- _ = Z_to_bv 64 _ => eassumption
  | |- bytes_at _ _ _ _ => first [apply BY; assumption | eassumption]
  | |- Forall _ _ => first [assumption | unfold zb8, CH; cbn [map app]; noz_tac]
  | |- _ = zb8 _ ++ _ => unfold zb8, CH; cbn [map app]; reflexivity
  | |- shadow_bytes _ _ _ _ => norm_len CH; assumption
  | |- rng _ (shad _) _ => norm_len CH; assumption
  | |- intconv _ => unfold intconv; cbv; first [left; reflexivity | right; reflexivity]
  | |- sconv _ => unfold sconv; cbv; reflexivity
  | |- bv_unsigned _ = _ => cbv; reflexivity
  | |- _ <> [] => discriminate
  | |- rw_cells _ _ _ _ => eassumption
  | |- _ /\ _ => first [eassumption | norm_len CH; unfold A; lia]
  | |- _ => first [assumption | eassumption]
  end.
Ltac pc_inst A BY CH PRE :=
  intros; eapply printf_common_int1 with (pre := zb8 PRE); pci A BY CH.

(* [comment removed for export] *)
Section CANSEC3. Context {rc : runConstT}.
Definition printf_common_int_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).

Theorem printf_common_d_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> a1 = Z_to_bv 64 FMT_D ->
  shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).
Proof. pc_inst FMT_D fmt_d_bytes FMT_D_chars ([] : list Z). Qed.

Theorem printf_common_toobig_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> a1 = Z_to_bv 64 FMT_TOOBIG ->
  shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).
Proof. pc_inst FMT_TOOBIG fmt_toobig_bytes FMT_TOOBIG_chars ([99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32]%Z). Qed.

(* [comment removed for export] *)
Definition FMT_USAGE : Z := 0x158ba.
Definition FMT_USAGE_chars : list Z := [117; 115; 97; 103; 101; 58; 32; 37; 115; 32; 73; 78; 80; 85; 84; 10]%Z.  (* [comment removed for export] *)
Definition FMT_CANTOPEN : Z := 0x1d956.
Definition FMT_CANTOPEN_chars : list Z := [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 37; 115; 10]%Z.  (* [comment removed for export] *)
Definition FMT_READERR : Z := 0x1d96b.
Definition FMT_READERR_chars : list Z := [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10]%Z.  (* [comment removed for export] *)
Lemma fmt_usage_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_USAGE (zb8 FMT_USAGE_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_USAGE FMT_USAGE_chars. Qed.
Lemma fmt_cantopen_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_CANTOPEN (zb8 FMT_CANTOPEN_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_CANTOPEN FMT_CANTOPEN_chars. Qed.
Lemma fmt_readerr_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m FMT_READERR (zb8 FMT_READERR_chars ++ [Z_to_bv 8 0]).
Proof. img_strz FMT_READERR FMT_READERR_chars. Qed.

End CANSEC3.
Ltac pcs_inst A BY CH PRE :=
  intros; eapply printf_common_str1 with (pre := zb8 PRE); pci A BY CH.

(* [comment removed for export] *)
Section CANSEC4. Context {rc : runConstT}.
Definition printf_common_s_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (Sa : Z) (sstr : list byte) (RLO RHI : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2320)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_layout m -> a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  rw_cells bsegs m (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)] ->
  (bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z ->
  bytes_at bsegs m Sa (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
  (Sa + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z ->
  app_blk Sa (Sa + (Z.of_nat (length sstr) + 1)) -> (0 < Sa)%Z ->
  unpoisoned m Sa (Sa + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
  (RLO <= Sa /\ Sa + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  rng RNG (bv_unsigned a2) 8 -> rng RNG Sa (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46ac0) fc None m (seg_rom bsegs)).

Theorem printf_common_usage_spec : printf_common_s_stmt FMT_USAGE 16.
Proof. unfold printf_common_s_stmt. pcs_inst FMT_USAGE fmt_usage_bytes FMT_USAGE_chars ([117; 115; 97; 103; 101; 58; 32]%Z). Qed.
Theorem printf_common_cantopen_spec : printf_common_s_stmt FMT_CANTOPEN 20.
Proof. unfold printf_common_s_stmt. pcs_inst FMT_CANTOPEN fmt_cantopen_bytes FMT_CANTOPEN_chars ([99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]%Z). Qed.
Theorem printf_common_readerr_spec : printf_common_s_stmt FMT_READERR 22.
Proof. unfold printf_common_s_stmt. pcs_inst FMT_READERR fmt_readerr_bytes FMT_READERR_chars ([99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]%Z). Qed.

Corollary printf_common_d_stmt : printf_common_int_stmt FMT_D 3.
Proof. exact printf_common_d_spec. Qed.
Corollary printf_common_toobig_stmt : printf_common_int_stmt FMT_TOOBIG 32.
Proof. exact printf_common_toobig_spec. Qed.
End CANSEC4.
