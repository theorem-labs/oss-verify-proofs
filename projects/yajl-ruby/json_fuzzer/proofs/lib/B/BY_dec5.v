(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_globals2 BI_strlen_icp BYajlRep BYajl_iface BY_ubkit BY_hand BY_dec1 BY_dec2 BY_dec3.
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
Definition ADP_RET4' : Z := 0x8b9c4.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_tail : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SQ B S n A lo : Z) (str slack ws : list byte),
  mem_inv bsegs m -> stk bsegs m lo SQ -> alloc_ceiling <= lo -> lo <= SQ - 2160 -> SQ + 240 <= 2^47 ->
  (length str <= 63)%nat -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < A -> A + (Z.of_nat (length str) + 1) + Z.of_nat (length slack) <= lo ->
  bytes_at bsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  icp_globals bsegs m 2147450880 -> icp_globals2 bsegs m ->
  shadow_window bsegs m 2147450880 A (Z.of_nat (length str) + 1) ws -> range_clean 2147450880 A (Z.of_nat (length str) + 1) ws ->
  pol P (shw_lo 2147450880 A) (shw_hi 2147450880 A (Z.of_nat (length str) + 1)) ->
  pol P A (A + (Z.of_nat (length str) + 1) + Z.of_nat (length slack)) ->
  pol P 0x10000 0x603000 -> pol P lo SQ ->
  evtA bsegs P (fun ms' => exists (q0 q1 q2 x3 x4 x5 x6 x7 q3 q4 q5 q6 : word) (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 ADP_RET4') (Z_to_bv 64 SQ) gp tp q0 q1 q2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 B) (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length str))) x3 x4 x5 x6 x7
                      s2 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 A) s8 s9 (Z_to_bv 64 2147450880) s11 q3 q4 q5 q6)
                     F (Z_to_bv 64 AY_BUF_APPEND) fc None m' (seg_rom bsegs)
       /\ munch [(SQ - 2160, SQ)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SQ
       /\ bytes_at bsegs m' A (str ++ Z_to_bv 8 0 :: slack) /\ icp_globals bsegs m' 2147450880 /\ icp_globals2 bsegs m')
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 A) s8 s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_TAIL) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until ws. intros MI ST CEIL LOQ SQH HLEN NONUL PAD A0 AHI STR IG IG2 SHW RC PSH PSTR PIMG PSTK.
  unfold pol, ADP_RET4', ADP_TAIL, AY_BUF_APPEND in *.
  pose proof CEIL as CEIL'. aceil.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(SQ - 2160, SQ)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  stepA.                                                  (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  pose proof (strlen_icp_small_spec) as SL. unfold strlen_icp_post, strlen_icp_entry in SL.
  specialize (SL (Z_to_bv 64 0x8b9b4) (Z_to_bv 64 SQ)). rewrite !USQ in SL.
  call_spA (SL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A 2147450880 str slack ws lo P).
  all: try assumption. all: try lia. all: try reflexivity.
  all: try (intros a k Ha Hk; apply PIMG; lia).
  - intros a k Ha Hk; apply PSTK; lia.
  - cbv beta.
    lazymatch goal with X : stk bsegs ?mx lo _ |- _ => rename X into ST2 end.
    zstepA.                                               (* [comment removed for export] *)
    rewrite ?(unsigned_lit (Z.of_nat (length str))), ?yswrap32_small by lia.
    stepA. stepA. stepA.                                  (* [comment removed for export] *)
    apply evtA_done.
    lazymatch goal with |- exists q0 q1 q2 x3 x4 x5 x6 x7 q3 q4 q5 q6 m', MS _ _ _ _ _ ?mx _ = _ /\ _ =>
        eexists _, _, _, _, _, _, _, _, _, _, _, _, mx end.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
    split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADP_REL : Z := 0x8bbc8.     (* [comment removed for export] *)
Definition DEC_RET_MAGIC : Z := 0x45e0360e.
Definition F5b' : byte := Z_to_bv 8 245.
Definition fsh_f5 : list cell := [C1 F5b'; C1 F5b'; C1 F5b'; C1 F5b'; C1 F5b'; C1 F5b'; C1 F5b'; C1 F5b'].

Lemma adp_epi1 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ FF PF : Z) (w0 : word) (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
  mem_inv bsegs m1 -> alloc_ceiling <= SQ -> SQ + 240 <= 2^47 ->
  rw_cells bsegs m1 (SQ + 80) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ->
  rw_cells bsegs m1 FF [C8 w0] -> rw_cells bsegs m1 (FF + 56) [C8 (Z_to_bv 64 PF)] ->
  rw_cells bsegs m1 (FF / 8 + 2147450880) [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7] ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 -> 0 <= PF < 2^64 ->
  pol P (SQ + 80) (SQ + 96) -> pol P FF (FF + 64) -> pol P (FF / 8 + 2147450880) (FF / 8 + 2147450880 + 8) ->
  evtA bsegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 PF) (Z_to_bv 64 FF) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (FF / 8 + 2147450880)) s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ADP_REL) fc None m' (seg_rom bsegs)
      /\ munch [(FF / 8 + 2147450880, FF / 8 + 2147450880 + 8); (FF, FF + 8)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (FF / 8 + 2147450880) fsh_f5
      /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 DEC_RET_MAGIC)] /\ rw_cells bsegs m' (FF + 56) [C8 (Z_to_bv 64 PF)]
      /\ rw_cells bsegs m' (SQ + 80) [C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)])
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (FF / 8 + 2147450880)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_RET5) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until b7. intros MI SQL SQH L80 FF0 FFP FSH FF1 FF2 FF3 PFR PSQ PFF PFFS.
  unfold pol, ADP_RET5, ADP_REL, fsh_f5, F5b', DEC_RET_MAGIC in *.
  set (SHF := FF / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 8 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF, SHF + 8); (FF, FF + 8)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }          (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 8 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists m', MS _ _ _ _ _ ?mx _ = _ /\ _ => exists mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ SHF _ |- _ => exact H2 end|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ FF _ |- _ => exact H2 end|].
  split; [exact FFP| exact L80].
Qed.

(* [comment removed for export] *)
Lemma adp_epi2 : forall (P : acc -> Prop) (rav sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ PF : Z) (fl : byte),
  mem_inv bsegs m1 ->
  rw_cells bsegs m1 PF [C1 fl] ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) [C8 vs11; C8 vs10; C8 vs9; C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  (6303744 <= PF /\ (PF + 1 <= 2147446784 \/ 17594333495296 <= PF)) -> PF + 1 <= alloc_ceiling -> alloc_ceiling + 256 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  P (Z_to_bv 64 PF, 1%nat) -> pol P (bv_unsigned sp - 256) (bv_unsigned sp) ->
  evtA bsegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR vra sp gp tp t0 t1 t2 vs0 vs1 (Z_to_bv 64 PF) a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(PF, PF + 1)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' PF [C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs m' (bv_unsigned sp + -104) [C8 vs11; C8 vs10; C8 vs9; C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 PF) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_REL) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until fl. intros MI PFC SV PF1 PF2 SPL SPH PPF PSTK.
  unfold pol, ADP_REL in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(PF, PF + 1)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  assert (PPF' : forall a k, PF <= a -> a + Z.of_nat k <= PF + 1 -> (a = PF /\ k = 1%nat) -> P (Z_to_bv 64 a, k)) by (intros a k _ _ [-> ->]; exact PPF).
  zstepA.                                                 (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 13 zstepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  replace (bv_unsigned sp + -224 + 224) with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists m', MS _ _ _ _ _ ?mx _ = _ /\ _ => exists mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ PF _ |- _ => exact H2 end| lazymatch goal with H2 : rw_cells bsegs _ (bv_unsigned sp + -104) _ |- _ => exact H2 end].
Qed.
(* [comment removed for export] *)
End RC__1.
