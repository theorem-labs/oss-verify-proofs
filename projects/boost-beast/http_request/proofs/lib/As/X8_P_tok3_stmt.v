(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AXRep AXRep2 AXPRep X8_P_tok_stmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Definition AEXISTS_STACK : Z := 240 + TOKIT_STACK.

(* [comment removed for export] *)
Definition ex_place (LF : list fframe) (A n : Z) : Prop :=
  fsobj H LF A n /\ (A + n <= ALOWSH_LO \/ AHI_LO <= A) /\ A + n <= AAPP_HI.

Definition ex_W (lo : Z) (sp : word) (ff fp : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)]%Z.

Definition ex_post_v (v : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (TL T SP TP : Z) (sbs tbs : list byte) (tlrest trest : list cell) (LF : list fframe) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ff fp : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (if v then 1 else 0))
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (ex_W lo sp ff fp) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' TL (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest)
    /\ rw_cells asegs m' T (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest)
    /\ bytes_at asegs m' SP sbs /\ bytes_at asegs m' TP tbs
    /\ fresh_frame H LF 1 ff fp /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi                     (* [comment removed for export] *)
    /\ accessible m' TL 16 /\ accessible m' T 16
    /\ accessible m' SP (Z.of_nat (length sbs)) /\ accessible m' TP (Z.of_nat (length tbs)).

Definition token_list_exists_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (TL T SP TP : Z) (sbs tbs : list byte) (tlrest trest : list cell) (LF : list fframe) (lo shi : Z) (m : mem) : machine_state -> Prop :=
  ex_post_v (token_list_exists (zbytes sbs) (zbytes tbs)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    TL T SP TP sbs tbs tlrest trest LF lo shi m.

Definition token_list_exists_stmt : Prop :=
  forall (TL T SP TP : Z) (sbs tbs : list byte) (tlrest trest : list cell) (LF : list fframe) (lo shi : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m TL (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest) ->
  rw_cells asegs m T (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest) ->
  bytes_at asegs m SP sbs -> bytes_at asegs m TP tbs -> SP + Z.of_nat (length sbs) < 2^64 -> TP + Z.of_nat (length tbs) < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo + AEXISTS_STACK <= bv_unsigned sp -> aceil <= lo ->       (* [comment removed for export] *)
  (bv_unsigned sp <= TL \/ TL + Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest)) <= lo) ->
  (bv_unsigned sp <= T \/ T + Z.of_nat (cells_size (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest)) <= lo) ->
  (bv_unsigned sp <= SP \/ SP + Z.of_nat (length sbs) <= lo) ->
  (bv_unsigned sp <= TP \/ TP + Z.of_nat (length tbs) <= lo) ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  bv_unsigned sp mod 16 = 0 -> tp = Z_to_bv 64 ATP -> ACONST m -> athr_cells m ->
  as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->
  accessible m TL 16 -> TL mod 8 = 0 -> accessible m T 16 -> T mod 8 = 0 ->
  accessible m SP (Z.of_nat (length sbs)) -> accessible m TP (Z.of_nat (length tbs)) ->
  ex_place LF TL (Z.of_nat (cells_size (C8 (wz SP) :: C8 (wz (Z.of_nat (length sbs))) :: tlrest))) ->
  ex_place LF T (Z.of_nat (cells_size (C8 (wz TP) :: C8 (wz (Z.of_nat (length tbs))) :: trest))) ->
  ex_place LF SP (Z.of_nat (length sbs)) -> ex_place LF TP (Z.of_nat (length tbs)) ->
  evt asegs (token_list_exists_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc TL T SP TP sbs tbs tlrest trest LF lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz TL) (wz T) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_TOKEN_LIST_EXISTS) fc None m (seg_rom asegs)).

End HCW.
