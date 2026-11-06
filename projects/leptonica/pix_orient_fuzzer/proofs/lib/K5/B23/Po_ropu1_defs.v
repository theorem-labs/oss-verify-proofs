(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface RT_fk D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Po_rows Po_iface Po_ropl_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition X_ropu_arms : Z := e_rasteropUniLow_po + 0x130.   (* [comment removed for export] *)
Definition X_ropu_exit : Z := e_rasteropUniLow_po + 0x8cc.   (* [comment removed for export] *)
Definition X_ropu_wa : Z := e_rasteropUniLow_po + 0x20c.     (* [comment removed for export] *)
Definition X_ropu_gen : Z := e_rasteropUniLow_po + 0x134.    (* [comment removed for export] *)

Section Ropu1Defs.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition ropu1_exit_cont (Σ : rts RT) PMc (QF : config -> Prop) (m0 : mem) (PF : Z -> Prop) (F : bvmap 5 word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) : Prop :=
  forall (mf : mem) (Ff : bvmap 5 word) (fcf : bv 32)
      (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xt3 xt4 xt5 xt6 : word),
    fs_agree F Ff -> ART RT Σ mf -> mem_inv asegs mf -> stk asegs mf lo (usp + -64) -> wmono asegs m0 mf ->
    rw_cells asegs mf (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    agree_on PF m0 mf ->
    cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -64)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          Ff (Z_to_bv 64 X_ropu_exit) fcf None mf (seg_rom asegs)))) QF.

Definition ropu1_arms : Prop :=
  forall (Σ : rts RT) PMc (QF : config -> Prop) (m0 mc : mem) (PF : Z -> Prop) (F Fc : bvmap 5 word) (fc : bv 32)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xra xt4 xt5 xt6 : word)
         (usp lo datad dn dwpl dpixw dpixh DX DY DW DH : Z),
  fdfs_only PMc -> mat_stable PMc ->
  ropu1_exit_cont Σ PMc QF m0 PF F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo ->
  0 <= DX -> 0 < DW -> DX + DW <= dpixw -> 0 <= DY -> 0 < DH -> DY + DH <= dpixh -> 0 < dpixw <= 20000 -> 0 < dpixh <= 20000 ->
  0 < dwpl -> dpixw <= 32 * dwpl -> dn = 4 * (dwpl * dpixh) -> dn <= 0x4000000 ->
  In (datad, dn) (rt_live RT Σ) -> 0 < datad -> datad mod 16 = 0 ->
  (forall a, PF a -> usp <= a \/ a < lo) -> (forall a, PF a -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + dn)] a) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + LSTK 1 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 -> usp <= rt_sp0 RT Σ ->
  Z.of_nat (length (rt_frames RT Σ)) + 0 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length (rt_live RT Σ)) + 0 <= LIVE_MAX -> 0 <= rt_credit RT Σ ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  fs_agree F Fc -> ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -64) -> wmono asegs m0 mc ->
  rw_cells asegs mc (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  agree_on PF m0 mc ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 DX) (Z_to_bv 64 SHB) (Z_to_bv 64 DH) s0 s1
                                        (Z_to_bv 64 datad) (Z_to_bv 64 PIX_CLR) (Z_to_bv 64 (Z.land DX 31)) (Z_to_bv 64 DH) (Z_to_bv 64 dwpl)
                                        (Z_to_bv 64 DW) (Z_to_bv 64 DY) (Z_to_bv 64 DW)
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 DX) xt4 xt5 xt6)
          Fc (Z_to_bv 64 X_ropu_arms) fc None mc (seg_rom asegs)))) QF.

(* [comment removed for export] *)
Definition ropu1_arm_at (X : Z) (RES : Z -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (QF : config -> Prop) (m0 mc : mem) (PF : Z -> Prop) (F Fc : bvmap 5 word) (fc : bv 32)
         (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (xra xt4 xt5 xt6 : word)
         (usp lo datad dn dwpl dpixw dpixh DX DY DW DH : Z),
  RES (DX mod 32) -> fdfs_only PMc -> mat_stable PMc ->
  ropu1_exit_cont Σ PMc QF m0 PF F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo ->
  0 <= DX -> 0 < DW -> DX + DW <= dpixw -> 0 <= DY -> 0 < DH -> DY + DH <= dpixh -> 0 < dpixw <= 20000 -> 0 < dpixh <= 20000 ->
  0 < dwpl -> dpixw <= 32 * dwpl -> dn = 4 * (dwpl * dpixh) -> dn <= 0x4000000 ->
  In (datad, dn) (rt_live RT Σ) -> 0 < datad -> datad mod 16 = 0 ->
  (forall a, PF a -> usp <= a \/ a < lo) -> (forall a, PF a -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + dn)] a) ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + LSTK 1 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 -> usp <= rt_sp0 RT Σ ->
  Z.of_nat (length (rt_frames RT Σ)) + 0 <= Z.of_nat FRAMES_MAX -> Z.of_nat (length (rt_live RT Σ)) + 0 <= LIVE_MAX -> 0 <= rt_credit RT Σ ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  fs_agree F Fc -> ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -64) -> wmono asegs m0 mc ->
  rw_cells asegs mc (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  agree_on PF m0 mc ->
  cps asegs (ASTA RT Σ PMc (eq (MS (mkR xra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 DX) (Z_to_bv 64 SHB) (Z_to_bv 64 DH) s0 s1
                                        (Z_to_bv 64 datad) (Z_to_bv 64 PIX_CLR) (Z_to_bv 64 (Z.land DX 31)) (Z_to_bv 64 DH) (Z_to_bv 64 dwpl)
                                        (Z_to_bv 64 DW) (Z_to_bv 64 DY) (Z_to_bv 64 DW)
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 DX) xt4 xt5 xt6)
          Fc (Z_to_bv 64 X) fc None mc (seg_rom asegs)))) QF.
Definition ropu1_wa : Prop := ropu1_arm_at X_ropu_wa (fun r => r = 0).
Definition ropu1_gen : Prop := ropu1_arm_at X_ropu_gen (fun r => 0 < r).
End Ropu1Defs.
