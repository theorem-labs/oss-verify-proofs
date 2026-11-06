(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_memcpy F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Definition pad_entry := 0x18dbc%Z.

(* [comment removed for export] *)
Definition got_ssp := 0x224e8%Z.
Definition ssp_guard := 0x53af8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Definition pad_n (w l fl : Z) : Z :=
  if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
  pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_model | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_model as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_model | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_model | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

(* [comment removed for export] *)
Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.rw_cells_bytes_at' | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.rw_cells_bytes_at' as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.rw_cells_bytes_at' | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.rw_cells_bytes_at' | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.rw_cells_bytes_at' OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 368, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (bv_unsigned sp - 368) (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

(* [comment removed for export] *)
Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

(* [comment removed for export] *)
Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(q - 368, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' (q - 368) q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.
#[export] Instance P_pad_contract : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_contract := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_contract_ok.
#[export] Instance P_pad_call_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_call_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_pad.pad_call_c_ok.
