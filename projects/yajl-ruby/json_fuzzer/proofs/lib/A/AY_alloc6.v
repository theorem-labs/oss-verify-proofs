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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_hand AY_alloc1 AY_alloc2 AY_alloc3 AY_alloc5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AAL_REL : Z := 0x828a4.    (* [comment removed for export] *)
Definition RET_MAGIC : Z := 0x45e0360e.
Definition F5b : byte := Z_to_bv 8 245.
Definition F8b : byte := Z_to_bv 8 248.

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition sh16_f5 : list cell := [C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aal9a_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff PF : Z) (shf : list byte) (w0 : word),
  mem_inv asegs m1 ->
  rw_cells asegs m1 (ff / 8 + 2147450880) [CB 16 shf] ->
  rw_cells asegs m1 ff [C8 w0] -> rw_cells asegs m1 (ff + 120) [C8 (Z_to_bv 64 PF)] ->
  amem ff 128 -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 -> 0 <= PF < 2^64 ->
  pol P ff (ff + 128) -> pol P (ff / 8 + 2147450880) (ff / 8 + 2147450880 + 16) ->
  evtA asegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 PF) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) s3 s4 s5 (Z_to_bv 64 ff) s7 s8 s9 s10 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 AAL_REL) fc None m' (seg_rom asegs)
      /\ munch [(ff / 8 + 2147450880, ff / 8 + 2147450880 + 16); (ff, ff + 8)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (ff / 8 + 2147450880) sh16_f5
      /\ rw_cells asegs m' ff [C8 (Z_to_bv 64 RET_MAGIC)] /\ rw_cells asegs m' (ff + 120) [C8 (Z_to_bv 64 PF)])
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) s3 s4 s5 (Z_to_bv 64 ff) s7 s8 s9 s10 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_EPI) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until w0. intros MI SHC FF0 FFP FF1 FF2 FF3 PFR PFF PFFS.
  unfold pol, AAL_EPI, AAL_REL, sh16_f5, F5b, RET_MAGIC, amem in *.
  assert (LS : length shf = 16%nat) by (destruct SHC as [[WF _] _]; cbn in WF; tauto).
  set (SHF := ff / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF, SHF + 16); (ff, ff + 8)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in SHC; [| reflexivity]. cbn [app mk_CB_cells] in SHC.
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }          (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 16 zstepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists m', MS _ _ _ _ _ ?mx _ = _ /\ _ => exists mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells asegs _ SHF _ |- _ => exact H2 end|].
  split; [lazymatch goal with H2 : rw_cells asegs _ ff _ |- _ => exact H2 end| exact FFP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aal9b_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ PF : Z) (fl : byte),
  mem_inv asegs m1 ->
  rw_cells asegs m1 PF [C1 fl] ->
  rw_cells asegs m1 (bv_unsigned sp + -104) [C8 vs11; C8 vs10; C8 vs9; C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  amem PF 1 -> PF + 1 <= alloc_ceiling -> alloc_ceiling + 160 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  P (Z_to_bv 64 PF, 1%nat) -> pol P (bv_unsigned sp - 160) (bv_unsigned sp) ->
  evtA asegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR vra sp gp tp t0 t1 t2 vs0 vs1 s3 a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch [(PF, PF + 1)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' PF [C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' (bv_unsigned sp + -104) [C8 vs11; C8 vs10; C8 vs9; C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 PF) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_REL) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until fl. intros MI PFC SV PF1 PF2 SPL SPH PPF PSTK.
  unfold pol, AAL_REL, amem in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(PF, PF + 1)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  assert (PPF' : forall a k, PF <= a -> a + Z.of_nat k <= PF + 1 -> (a = PF /\ k = 1%nat) -> P (Z_to_bv 64 a, k)) by (intros a k _ _ [-> ->]; exact PPF).
  zstepA.                                                 (* [comment removed for export] *)
  stepA. stepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 13 zstepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists m', MS _ _ _ _ _ ?mx _ = _ /\ _ => exists mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells asegs _ PF _ |- _ => exact H2 end| lazymatch goal with H2 : rw_cells asegs _ (bv_unsigned sp + -104) _ |- _ => exact H2 end].
Qed.
End RC__2.
