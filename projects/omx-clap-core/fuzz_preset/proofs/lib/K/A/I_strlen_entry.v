(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Theorem Labs, 2026-10-28: fuzz_preset's program code calls the TRAMPOLINE, not the interceptor body, so the walk
   has to start four bytes earlier than the donor's does. The step is the donor's own: the released lift
   leptonica/fhmtgen_fuzzer K5/A10/I_strcmp_lift.v:66-72 (the same kit family; bzip2's K tree has no
   lift file for strlen) does one `lstep` from the trampoline and then applies the walk. The
   trampoline is one uncompressed instruction, `jal zero, <interceptor>`, measured in fuzz_preset's own images:
     asan        __wrap_strlen 0x42d18 -> __interceptor_strlen 0x42da8 (bytes 6f 00 00 09)
     asan-ubsan  __wrap_strlen 0x42e04 -> __interceptor_strlen 0x42e94 (bytes 6f 00 00 09)
   Nothing else here is new: the statement is I_strlen.v's, with the entry pc replaced. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Spec Require StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.P Require Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Shadow IcptSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Layout R_small R_m2s R_thread I_consts I_qck X_atexit F_strlen D_kit I_ikit I_strnlenw I_strlenw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require I_strlen.
Module TwinB__.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Import Shadow IcptSpec.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.R_small.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.X_atexit.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.F_strlen.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_ikit.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strnlenw.TwinB__ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strlenw.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.I_strlen.TwinB__.

(* __wrap_strlen, measured in fuzz_preset's own image *)
Definition e_wrap_strlen : Z := 0x42e04.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Theorem istrlen_wrap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  a0 = Z_to_bv 64 s ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRLEN_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 < s <= 2^47 -> Z.of_nat (length str) < 2^40 -> s + Z.of_nat (length str) + 1 <= 2^47 ->
  bytes_at bsegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_sn m -> icells_sl m -> mem_inv bsegs m ->
  evt bsegs (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_wrap_strlen) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros.
  pose proof (munch_refl [(bv_unsigned sp - ISTRLEN_DEPTH, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  unfold e_wrap_strlen. lstep.
  eapply (istrlen_spec RIP); eassumption.
Qed.

End WithRIP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require R_isPoisoned.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A.R_isPoisoned.TwinB__.
(* bzip2's own discharge of RIP (K/A/R_isPoisoned.v `rip_proof`, ported here). *)
Definition istrlen_wrap_closed := istrlen_wrap_spec rip_proof.
End TwinB__.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Import Layout Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec F_strlen D_kit I_ikit
  I_strnlenw I_strlenw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Import I_strlen.

(* __wrap_strlen, measured in fuzz_preset's own image *)
Definition e_wrap_strlen : Z := 0x42d18.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Theorem istrlen_wrap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  a0 = Z_to_bv 64 s ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRLEN_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 < s <= 2^47 -> Z.of_nat (length str) < 2^40 -> s + Z.of_nat (length str) + 1 <= 2^47 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  chk_ok m s (Z.of_nat (length str) + 1) -> m2s_cells m -> icells_sn m -> icells_sl m -> mem_inv asegs m ->
  evt asegs (istrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_wrap_strlen) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros.
  pose proof (munch_refl [(bv_unsigned sp - ISTRLEN_DEPTH, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold e_wrap_strlen. lstep.
  eapply (istrlen_spec RIP); eassumption.
Qed.

End WithRIP.

From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.K.A Require Import R_isPoisoned.
(* bzip2's own discharge of RIP (K/A/R_isPoisoned.v `rip_proof`, ported here). *)
Definition istrlen_wrap_closed := istrlen_wrap_spec rip_proof.
