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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_hand.
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
Definition ADP_RET1 : Z := 0x8ab14.   (* [comment removed for export] *)
Definition ADP_HEAD : Z := 0x8ac3c.   (* [comment removed for export] *)
Definition ADP_EXIT : Z := 0x8afb0.   (* [comment removed for export] *)
Definition ADP_MAGIC : Z := 0x41b58ab3.
Definition ADP_DESCR : Z := 0x19840.
Definition F1b : byte := Z_to_bv 8 241.
Definition F3b : byte := Z_to_bv 8 243.
Definition F8b : byte := Z_to_bv 8 248.

(* [comment removed for export] *)
Definition A_LIT_Q : Z := 0x22000.  Definition A_LIT_CR : Z := 0x22020. Definition A_LIT_LF : Z := 0x22040. Definition A_LIT_BSL : Z := 0x22060.
Definition A_LIT_SL : Z := 0x22080. Definition A_LIT_QT : Z := 0x220a0. Definition A_LIT_FF : Z := 0x220c0. Definition A_LIT_BS : Z := 0x220e0.
Definition A_LIT_TAB : Z := 0x22100.

(* [comment removed for export] *)
Definition dspill (w0 w16 : word) (FF : Z) (sur cp : word) : list cell :=
  [C8 w0; C8 (Z_to_bv 64 (FF + 33)); C8 (Z_to_bv 64 0xffc00); C8 (Z_to_bv 64 (FF + 35)); C8 (Z_to_bv 64 (FF + 36)); C8 (Z_to_bv 64 (FF + 34)); C8 (Z_to_bv 64 (FF + 32));
   C8 (Z_to_bv 64 0xd800); C8 (Z_to_bv 64 A_LIT_BS); C8 (Z_to_bv 64 A_LIT_BSL); C8 (Z_to_bv 64 A_LIT_SL); C8 (Z_to_bv 64 A_LIT_QT); C8 (Z_to_bv 64 A_LIT_CR);
   C8 (Z_to_bv 64 0xfc00); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 w16; C8 (Z_to_bv 64 FF); C4 sur; C4 cp].
(* [comment removed for export] *)
Definition dspill0 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w16 : word) (FF : Z) (sur cp : word) : list cell :=
  [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 w16; C8 (Z_to_bv 64 FF); C4 sur; C4 cp].

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma adp1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (B S n lo : Z),
  stk asegs m1 lo (bv_unsigned sp) -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells asegs m1 674224 [C8 (Z_to_bv 64 711544)] -> rw_cells asegs m1 711544 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells asegs m1 674312 [C8 (Z_to_bv 64 711552)] -> rw_cells asegs m1 711552 [C4 (Z_to_bv 64 1)] ->
  0 <= B < 2^64 -> 0 <= S < 2^64 -> 0 <= n < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 ->
  evtA asegs P (fun ms' => exists (SQ : Z) (jq : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 ADP_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 64) (Z_to_bv 64 711544) (sx32 (Z_to_bv 64 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_STACK_MALLOC_0) fc None m' (seg_rom asegs)
      /\ SQ mod 32 = 0 /\ bv_unsigned sp - 272 <= SQ <= bv_unsigned sp - 256
      /\ munch [(lo, bv_unsigned sp)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SQ
      /\ rw_cells asegs m' SQ [CB 152 jq]
      /\ rw_cells asegs m' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs m' (SQ + 152) (bv_unsigned sp + -104))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_STRING_DECODE) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros ST MI CEIL LOQ SPH SP16 G1 G2 G3 G4 R1 R2 R3 PSTK PIMG. unfold AY_STRING_DECODE, ADP_RET1, AY_STACK_MALLOC_0, pol in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  carve_frame 256%nat ST.
  stepA. apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [8;144;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 14 stepA.                                             (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned sp + -256)) by lia. rewrite (land_align32 (bv_unsigned sp + -256)) by lia.
  remember (bv_unsigned sp + -256 - (bv_unsigned sp + -256) mod 32) as SQ eqn:SQE.
  assert (SQF : SQ mod 32 = 0 /\ bv_unsigned sp - 272 <= SQ <= bv_unsigned sp - 256) by (subst SQ; clear -CEILB SP16; Z.div_mod_to_equations; lia).
  clear SQE.
  match type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    apply (proj1 (ycells_app asegs _ _ [c0; c1] rest)) in FR end.
  destruct FR as [FRlo SV]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV.
  pose proof (stk_release asegs _ _ _ _ ST FRlo ltac:(lia)) as ST'. clear ST FRlo. cbn [cells_size csize Nat.add] in ST'.
  pose proof (proj2 (stk_split asegs _ _ (SQ + 152) _ ST' ltac:(lia))) as GAP.
  destruct (stk_carve_at _ _ _ SQ 152 ST' ltac:(lia) ltac:(cbn; lia)) as [ST [jq FR]]. clear ST'.
  replace (bv_unsigned sp + -256 + Z.of_nat 152) with (bv_unsigned sp + -104) in SV, GAP by lia.
  stepA.                                                   (* [comment removed for export] *)
  stepA. stepA.                                            (* [comment removed for export] *)
  do 4 stepA.                                              (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  stepA. stepA.                                            (* [comment removed for export] *)
  apply evtA_done. cbv beta. eexists SQ, _, _. split; [reflexivity|].
  split; [exact (proj1 SQF)|]. split; [exact (proj2 SQF)|].
  repeat match goal with |- _ /\ _ => split end; try assumption; try exact FR; exact GAP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma adp2_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ FF B S n : Z) (jq fj : list byte) (ffp : word),
  mem_inv asegs m1 -> alloc_ceiling <= SQ -> SQ + 272 <= 2^47 ->
  rw_cells asegs m1 SQ [CB 152 jq] ->
  rw_cells asegs m1 FF [CB 56 fj; C8 ffp] -> rw_cells asegs m1 (2147450880 + FF / 8) [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  (6303744 <= FF /\ (FF + 64 <= 2147446784 \/ 17594333495296 <= FF)) -> FF + 64 <= alloc_ceiling -> FF mod 64 = 0 -> 0 <= n < 2^32 ->
  pol P SQ (SQ + 152) -> pol P FF (FF + 64) -> pol P (2147450880 + FF / 8) (2147450880 + FF / 8 + 8) ->
  evtA asegs P (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (j0 j128 fj' : list byte) (m' : mem),
      munch [(SQ, SQ + 152); (FF, FF + 64); (FF / 8 + 2147450880, FF / 8 + 2147450880 + 8)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' FF [C8 (Z_to_bv 64 ADP_MAGIC); C8 (Z_to_bv 64 ADP_DESCR); C8 (Z_to_bv 64 AY_STRING_DECODE); CB 32 fj'; C8 ffp]
      /\ rw_cells asegs m' (FF / 8 + 2147450880) [C1 F1b; C1 F1b; C1 F1b; C1 F1b; C1 F8b; C1 F3b; C1 F3b; C1 F3b]
      /\ length fj' = 32%nat
      /\ ((n = 0 /\ ms' = MS (mkR (Z_to_bv 64 ADP_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 ADP_EXIT) fc None m' (seg_rom asegs)
           /\ (exists (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w16 sur cp : word), rw_cells asegs m' SQ (dspill0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w16 FF sur cp)))
          \/ (0 < n /\ ms' = MS (mkR (Z_to_bv 64 ADP_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 0) (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) (Z_to_bv 64 92) s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (-8)) (Z_to_bv 64 (FF / 8 + 2147450880)) (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 ADP_HEAD) fc None m' (seg_rom asegs)
           /\ (exists (w0 w16 sur cp : word), rw_cells asegs m' SQ (dspill w0 w16 FF sur cp)))))
    (MS (mkR (Z_to_bv 64 ADP_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 FF) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 n) s6 s7 (Z_to_bv 64 2147450880) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ADP_RET1) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until ffp. intros MI SQL SQH FR FFC FSH FF1 FF2 FF3 NR PSTK PFF PFFS.
  unfold pol, ADP_RET1, ADP_HEAD, ADP_EXIT, AY_STRING_DECODE, ADP_MAGIC, ADP_DESCR, F1b, F3b, F8b, dspill, dspill0, A_LIT_BS, A_LIT_BSL, A_LIT_SL, A_LIT_QT, A_LIT_CR in *.
  assert (LFJ : length fj = 56%nat) by (destruct FFC as [[WF _] _]; cbn in WF; tauto).
  assert (LJQ : length jq = 152%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  set (SHF := FF / 8 + 2147450880) in *. replace (2147450880 + FF / 8) with SHF in FSH, PFFS by lia.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 8 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(SQ, SQ + 152); (FF, FF + 64); (SHF, SHF + 8)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  apply (rw_cells_split_CB asegs _ _ [] 56 _ [_] [8; 8; 8; 32]%nat) in FFC; [| reflexivity]. cbn [app mk_CB_cells] in FFC.
  apply (rw_cells_split_CB asegs _ _ [] 152 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  stepA. stepA.                                           (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 3 zstepA.                                            (* [comment removed for export] *)
  zstepA. shadow_addr.                                    (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA. zstepA.                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. change (FF / 8 + 2147450880) with SHF.          (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.                      (* [comment removed for export] *)
  - (* [comment removed for export] *)
    stepA. stepA.                                         (* [comment removed for export] *)
    apply evtA_done. cbv beta.
    lazymatch goal with H1 : rw_cells asegs ?mx FF [_; _; _; CB 32 ?x; _] |- _ => eexists _, _, _, _, _, _, _, _, [], [], x, mx end.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [lazymatch goal with H : rw_cells asegs _ FF _ |- _ => exact H end|].
    split; [lazymatch goal with H : rw_cells asegs _ SHF _ |- _ => exact H end|].
    split; [rewrite ?length_firstn, ?length_skipn, ?LFJ; lia|].
    left. split; [revert K1; rewrite ?unsigned_lit by lia; intros K1; lia|]. split; [reflexivity|].
    lazymatch goal with H : rw_cells asegs _ SQ _ |- _ => awordify H; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _; exact H end.
  - (* [comment removed for export] *)
    stepA. stepA.                                         (* [comment removed for export] *)
    do 10 zstepA.                                         (* [comment removed for export] *)
    do 2 zstepA.                                          (* [comment removed for export] *)
    do 5 zstepA.                                          (* [comment removed for export] *)
    do 2 zstepA.                                          (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    do 10 zstepA.                                         (* [comment removed for export] *)
    zstepA. zstepA.                                       (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. zstepA.                                       (* [comment removed for export] *)
    apply evtA_done. cbv beta.
    lazymatch goal with H1 : rw_cells asegs ?mx FF [_; _; _; CB 32 ?x; _] |- _ => eexists _, _, _, _, _, _, _, _, [], [], x, mx end.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [lazymatch goal with H : rw_cells asegs _ FF _ |- _ => exact H end|].
    split; [lazymatch goal with H : rw_cells asegs _ SHF _ |- _ => exact H end|].
    split; [rewrite ?length_firstn, ?length_skipn, ?LFJ; lia|].
    right. split; [revert K1; rewrite ?unsigned_lit by lia; intros K1; lia|]. split; [reflexivity|].
    lazymatch goal with H : rw_cells asegs _ SQ _ |- _ => awordify H; eexists _, _, _, _; exact H end.
Qed.
End RC__2.
