(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_KitH ECH_Rep ECH_LibState ECH_C1_stmt ECH_C4_stmt ECH_C5_stmt ECH_C13_stmt ECH_C14_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition DX_HEAD : Z := 0x2b3eb8.    Definition DX_R1 : Z := 0x2b3f54.   Definition DX_R2 : Z := 0x2b3f70.   Definition DX_MALLOC : Z := 0x2b3f80.
Definition DX_R3 : Z := 0x2b3f94.      Definition DX_R4 : Z := 0x2b3fd0.   Definition DX_R5 : Z := 0x2b3fe0.   Definition DX_R6 : Z := 0x2b3ff0.
Definition DX_R7 : Z := 0x2b4000.      Definition DX_R8 : Z := 0x2b4014.   Definition DX_RET1 : Z := 0x2b4028. Definition DX_RA1 : Z := 0x2b4044.
Definition DX_RA2 : Z := 0x2b4060.     Definition DX_RA3 : Z := 0x2b4074.  Definition DX_R9 : Z := 0x2b4098.   Definition DX_R10 : Z := 0x2b40a8.
Definition DX_R11 : Z := 0x2b40b4.     Definition DX_R12 : Z := 0x2b40cc.  Definition DX_EPI : Z := 0x2b40d0.
Definition DX_FAILA : Z := 0x2b403c.   (* [comment removed for export] *)
Definition DX_FILE_PKT : Z := 0x33a29.   (* [comment removed for export] *)
Definition DX_FILE_ECHS : Z := 0x36488.  (* [comment removed for export] *)
Definition DX_FUNC : Z := 0x28d3e.       (* [comment removed for export] *)
Definition DX_THUNK_CMP : Z := 0x2b4158. Definition DX_THUNK_COPY : Z := 0x2b4184. Definition DX_THUNK_FREE : Z := 0x2b3924.
Definition DX_R_INTERNAL : Z := 0xc0103. Definition SSL_R_BAD_ECHCONFIG_EXTENSION : Z := 425. Definition DX_ERR_LIB_SSL : Z := 20.
(* [comment removed for export] *)
Definition dx_frame (j0 : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j0; C8 (wz DX_THUNK_FREE); C8 (wz DX_THUNK_COPY); C8 (wz DX_THUNK_CMP); C8 (wz 0);
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma dx_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo ee pk : Z),
      a0 = Z_to_bv 64 ee -> a1 = Z_to_bv 64 pk -> 0 < ee < 2^64 -> ee mod 8 = 0 -> 0 < pk < 2^64 -> pk mod 8 = 0 ->   (* [comment removed for export] *)
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 j0 (a0' a1' a2' a3' a4' : word),
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0' a1' a2' a3' a4' (Z_to_bv 64 1) (Z_to_bv 64 (-2)) a7
                       (Z_to_bv 64 pk) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 0) s6 s7 s8 s9 s10 (Z_to_bv 64 2) t3 t4 t5 t6)
                   F (Z_to_bv 64 DX_HEAD) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -144, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -144)
          /\ rw_cells usegs m1 (bv_unsigned sp + -144) (dx_frame j0 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m (seg_rom usegs)).
  Proof.
    intros until pk. intros A0 A1 EEP EAL PKP PAL ST CEIL LO MI. subst a0 a1.
    unfold P_ech_decode_echconfig_exts, DX_HEAD, DX_FILE_PKT, DX_FILE_ECHS.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. carve_frame 144%nat ST.
    do 13 st1. step. step. step.
    (* [comment removed for export] *)
    step. ubal_by PAL. step. ubal_by EAL. st1.
    (* [comment removed for export] *)
    step. step. step. do 5 step. step. step. step. st1. step. st1. step. st1.
    apply evt_done. do 7 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
    unfold dx_frame, DX_THUNK_FREE, DX_THUNK_COPY, DX_THUNK_CMP. unfold wz. exact FR.
  Qed.
End S.
Section S2.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  (* [comment removed for export] *)
  Lemma pk_byte : forall m base bs cur i b,
    bytes_at usegs m base bs -> nth_error bs (Z.to_nat (cur - base + i)) = Some b -> base <= cur -> 0 <= i ->
    ov_read_bytes usegs m (wa (cur + i)) 1 = Some [b].
  Proof.
    intros m base bs cur i b BS NTH LE I0. eapply (u8ro_read usegs m base bs (cur - base + i) b); [exact BS| exact NTH| lia|]. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segH :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (pk cur base rem : Z) (bs : list byte),
      rw_cells usegs m pk (pk_cells cur base rem) -> bytes_at usegs m base bs -> pk_in base (zlength bs) cur rem ->
      0 < pk -> pk + 24 < 2^64 -> pk + 24 <= base \/ base + zlength bs <= pk ->
      0 < base -> base + zlength bs + 4 <= 2^64 ->   (* [comment removed for export] *)
      mem_inv usegs m ->
      evt usegs (fun ms' => exists (a0' a1' a2' a3' a4' s6' s7' s10' : word) m' cur' rem',
          munch [(pk, pk + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
          /\ rw_cells usegs m' pk (pk_cells cur' base rem') /\ cur + rem = cur' + rem' /\ 0 <= rem' <= rem /\
         (  (rem = 0 /\ m' = m /\ rem' = rem /\
             ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 (-2)) a7 (Z_to_bv 64 pk) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 0) s6 s7 s8 s9 s10 (Z_to_bv 64 2) t3 t4 t5 t6)
                      F (Z_to_bv 64 DX_EPI) fc None m' (seg_rom usegs))
         \/ (exists line, (line = 206 \/ line = 210) /\ 1 <= rem /\
             ms' = MS (mkR (Z_to_bv 64 DX_RA1) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' (Z_to_bv 64 1) (Z_to_bv 64 (-2)) a7 (Z_to_bv 64 pk) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 0) s6' s7'
                           (Z_to_bv 64 line) s9 s10' (Z_to_bv 64 2) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_ERR_new) fc None m' (seg_rom usegs))
         \/ (exists b0 b1 extlen, 0 <= extlen < 512 /\ cur' = cur + 4 + extlen /\ rem' = rem - 4 - extlen /\ 0 <= b0 < 256 /\ 0 <= b1 < 256 /\
             ms' = MS (mkR (Z_to_bv 64 DX_R1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 518) a3' a4' (Z_to_bv 64 1) (Z_to_bv 64 (-2)) a7 (Z_to_bv 64 pk) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 0) (Z_to_bv 64 b0) (Z_to_bv 64 b1)
                           (Z_to_bv 64 (cur + 4)) s9 (Z_to_bv 64 extlen) (Z_to_bv 64 2) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_CRYPTO_free) fc None m' (seg_rom usegs))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 (-2)) a7 (Z_to_bv 64 pk) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 0) s6 s7 s8 s9 s10 (Z_to_bv 64 2) t3 t4 t5 t6)
            F (Z_to_bv 64 DX_HEAD) fc None m (seg_rom usegs)).
  Proof.
    intros until bs. intros PK BS PIN PKP PKH PKA BP BH MI.
    unfold DX_HEAD, DX_EPI, DX_RA1, DX_R1, P_ERR_new, P_CRYPTO_free, SSL_R_BAD_ECHCONFIG_EXTENSION. unfold pk_cells in PK.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold pk_in, zlength in PIN. unfold zlength in PKA, BH.
    pose proof (munch_refl [(pk, pk + 24)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. if_lit.
    step. unfold wz. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R0 : rem = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. step. step.
      apply evt_done. exists a0, a1, a2, a3, a4, s6, s7, s10, m, cur, rem. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      left. split; [exact R0|]. split; [reflexivity|]. split; [reflexivity|]. reflexivity. }
    assert (R1 : 1 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. if_cases K0; zify_cond K0.
    { step. step.
      apply evt_done. do 8 eexists. exists m, cur, rem. repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      right; left. exists 206. split; [left; reflexivity|]. split; [exact R1|]. reflexivity. }
    assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. unfold wz. step. br. step. step. br. step. br.
    (* [comment removed for export] *)
    destruct (nth_error bs (Z.to_nat (cur - base + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    destruct (nth_error bs (Z.to_nat (cur - base + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (pk_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    pose proof (byte_range c0) as C0R. pose proof (byte_range c1) as C1R.
    step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)).
    (* [comment removed for export] *)
    step. step. st1. st1. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      step. step.
      apply evt_done. do 8 eexists. exists m1, (cur + 2), (rem - 2). repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      right; left. exists 206. split; [left; reflexivity|]. split; [exact R1|]. reflexivity. }
    assert (R4 : 4 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. br. step. br.
    destruct (nth_error bs (Z.to_nat (cur - base + 2))) as [c2|] eqn:N2; [| apply nth_error_None in N2; lia].
    destruct (nth_error bs (Z.to_nat (cur - base + 3))) as [c3|] eqn:N3; [| apply nth_error_None in N3; lia].
    pose proof (pk_byte _ _ _ _ _ _ BS N2 ltac:(lia) ltac:(lia)) as RD2. pose proof (pk_byte _ _ _ _ _ _ BS N3 ltac:(lia) ltac:(lia)) as RD3.
    pose proof (byte_range c2) as C2R. pose proof (byte_range c3) as C3R.
    step. change (zxb c2) with (Z_to_bv 64 (bv_unsigned c2)). step. change (zxb c3) with (Z_to_bv 64 (bv_unsigned c3)).
    (* [comment removed for export] *)
    step. step.
    set (x2 := bv_unsigned c2) in *. set (x3 := bv_unsigned c3) in *.
    rewrite (unsigned_lit x2) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (x2 * 2 ^ 8)) by lia. rewrite (unsigned_lit x3) by lia.
    replace (Z.lor (x2 * 2 ^ 8) x3) with (x3 + 256 * x2) by (rewrite Z.lor_comm; rewrite <- (lor_shiftl8_add x3 x2) by lia; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
    set (extlen := x3 + 256 * x2) in *. assert (XLR : 0 <= extlen < 2^16) by (subst extlen; lia).
    (* [comment removed for export] *)
    step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      step. step.
      apply evt_done. do 8 eexists. exists m1, (cur + 2), (rem - 2). repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      right; left. exists 206. split; [left; reflexivity|]. split; [exact R1|]. reflexivity. }
    assert (RX : 4 + extlen <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. ubnot. step. br.
    step. step. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      do 4 step.
      apply evt_done. do 8 eexists. exists m2, (cur + 4 + extlen), (rem - 4 - extlen). repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      all: try (right; left; exists 210; split; [right; reflexivity|]; split; [exact R1|]; reflexivity).
      all: match goal with |- ?G => idtac "H210-LEFT" G end. }
    assert (X512 : extlen < 512) by (revert K0; rewrite ?unsigned_lit by lia; subst extlen; lia). clear K0.
    do 5 step.
    apply evt_done. do 8 eexists. exists m2, (cur + 4 + extlen), (rem - 4 - extlen). repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    all: try (right; right; exists (bv_unsigned c0), (bv_unsigned c1), extlen; pose proof (byte_range c0); pose proof (byte_range c1); repeat match goal with |- _ /\ _ => split end; try lia; reflexivity).
    all: match goal with |- ?G => idtac "HOK-LEFT" G end.
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S2.
Section S3.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma dx_seg2 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (extlen D : Z),
      0 <= extlen < 512 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
         (extlen = 0 /\
          ms' = MS (mkR (Z_to_bv 64 DX_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 16) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 217) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) s5 s6 s7 (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 extlen) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom usegs))
      \/ (1 <= extlen /\
          ms' = MS (mkR (Z_to_bv 64 DX_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 extlen) (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 527) a4 a5 a6 a7 s2 (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) s5 s6 s7 (Z_to_bv 64 D) s9 (Z_to_bv 64 extlen) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m (seg_rom usegs)))
        (MS (mkR (Z_to_bv 64 DX_R1) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 DX_FILE_PKT) (Z_to_bv 64 DX_FILE_ECHS) s5 s6 s7 (Z_to_bv 64 D) s9 (Z_to_bv 64 extlen) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R1)) fc None m (seg_rom usegs)).
  Proof.
    intros until D. intros XR MI. unfold DX_R1, DX_R2, DX_R3, P_CRYPTO_malloc, P_CRYPTO_memdup, DX_FILE_PKT, DX_FILE_ECHS. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (X0 : extlen = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      do 6 step. apply evt_done. left. split; [exact X0| reflexivity].
    - assert (X1 : 1 <= extlen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      do 6 step. apply evt_done. right. split; [exact X1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma dx_seg3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z),
      0 < A < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R3) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 16) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 217) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 DX_FILE_ECHS) s5 s6 s7 s8 (Z_to_bv 64 A) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 DX_FILE_ECHS) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R2)) fc None m (seg_rom usegs)).
  Proof.
    intros until A. intros AR MI. unfold DX_R2, DX_R3, P_CRYPTO_malloc, DX_FILE_ECHS. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. step. try br. do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_seg4 :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee A val b0 b1 extlen : Z) (E : entrep) pad1 pad2 pad3 pad4 junk
           j0 (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra : word),
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> 0 <= en_exts E < 2^64 ->
      rw_cells usegs m A [CB 16 junk] -> 0 < A -> A + 16 < 2^64 -> (A + 16 <= ee \/ ee + ENTRY_SIZE <= A) ->
      0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= extlen < 512 -> 0 <= val < 2^64 ->
      A mod 8 = 0 ->   (* [comment removed for export] *)
      rw_cells usegs m (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> 144 <= bv_unsigned sp ->
      (bv_unsigned sp <= A \/ A + 16 <= bv_unsigned sp + -144) ->
      mem_inv usegs m ->
      evt usegs (fun ms' => exists m1 jk,
          munch [(A, A + 16)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 A [C2 (wz (256 * b0 + b1)); C2 (wz extlen); CB 4 jk; C8 (wz val)]
          /\ rw_cells usegs m1 (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) /\
         (  (en_exts E = 0 /\
             ms' = MS (mkR (Z_to_bv 64 DX_R4) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (b0 * 2^8)) (Z_to_bv 64 b1) (Z_to_bv 64 A) (Z_to_bv 64 val) (Z_to_bv 64 extlen) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m1 (seg_rom usegs))
         \/ (0 < en_exts E /\
             ms' = MS (mkR (Z_to_bv 64 DX_R8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 (en_exts E)) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (b0 * 2^8)) (Z_to_bv 64 b1) (Z_to_bv 64 A) (Z_to_bv 64 val) (Z_to_bv 64 extlen) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom usegs))))
        (MS (mkR (Z_to_bv 64 DX_R3) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 b0) (Z_to_bv 64 b1) s8 (Z_to_bv 64 val) (Z_to_bv 64 extlen) s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R3)) fc None m (seg_rom usegs)).
  Proof.
    intros until xra. intros EC EEP EEH XR OE AP AH DJ B0 B1 XL VR AAL FR SPL DJF MI.
    unfold DX_R3, DX_R4, DX_R8, P_OPENSSL_sk_new_null, P_OPENSSL_sk_push. unfold entry_cells in EC. unfold ENTRY_SIZE in *.
    unfold dx_frame, DX_THUNK_FREE, DX_THUNK_COPY, DX_THUNK_CMP in FR. retpc.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [(A, A + 16)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. try br. step. step. ubal_by AAL. step. if_lit.
    (* [comment removed for export] *)
    step. step.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit b0) by lia. rewrite (unsigned_lit (b0 * 2^8)) by lia. rewrite (unsigned_lit b1) by lia.
    replace (Z.lor (b0 * 2 ^ 8) b1) with (256 * b0 + b1) by (rewrite Z.lor_comm; replace (b0 * 2 ^ 8) with (Z.shiftl b0 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); rewrite (lor_shiftl8_add b1 b0) by lia; lia).
    st1. st1. st1.
    (* [comment removed for export] *)
    step. unfold wz. step. if_lit.
    (* [comment removed for export] *)
    step. unfold wz. step. if_cases K0; zify_cond K0.
    - assert (XP : 0 < en_exts E) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step. step. apply evt_done. do 2 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
      right. split; [exact XP| reflexivity].
    - assert (X0 : en_exts E = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step. apply evt_done. do 2 eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
      left. split; [exact X0|]. rewrite X0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_seg5 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z)
           j0 (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra : word),
      rw_cells usegs m (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> 144 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R5) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) (Z_to_bv 64 DX_THUNK_CMP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 P) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_cmp_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R4) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R4)) fc None m (seg_rom usegs)).
  Proof.
    intros until xra. intros FR SPL MI.
    unfold DX_R4, DX_R5, P_OPENSSL_sk_set_cmp_thunks, DX_THUNK_CMP. unfold dx_frame, DX_THUNK_FREE, DX_THUNK_COPY, DX_THUNK_CMP in FR. retpc.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. step. unfold wz. step. step. apply evt_done. reflexivity.
  Qed.

  Lemma dx_seg6 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z)
           j0 (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra : word),
      rw_cells usegs m (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> 144 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R6) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) (Z_to_bv 64 DX_THUNK_COPY) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 P) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_copy_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R5) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 P) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R5)) fc None m (seg_rom usegs)).
  Proof.
    intros until xra. intros FR SPL MI.
    unfold DX_R5, DX_R6, P_OPENSSL_sk_set_copy_thunks, DX_THUNK_COPY. unfold dx_frame, DX_THUNK_FREE, DX_THUNK_COPY, DX_THUNK_CMP in FR. retpc.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. step. unfold wz. step. step. apply evt_done. reflexivity.
  Qed.

  Lemma dx_seg7 :
    forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z)
           j0 (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra : word),
      rw_cells usegs m (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> 144 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R7) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 P) (Z_to_bv 64 DX_THUNK_FREE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 P) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R6) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 P) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R6)) fc None m (seg_rom usegs)).
  Proof.
    intros until xra. intros FR SPL MI.
    unfold DX_R6, DX_R7, P_OPENSSL_sk_set_thunks, DX_THUNK_FREE. unfold dx_frame, DX_THUNK_FREE, DX_THUNK_COPY, DX_THUNK_CMP in FR. retpc.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. step. unfold wz. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_seg8 :
    forall (sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee P A : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> 0 < P < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          munch [(ee, ee + ENTRY_SIZE)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) P (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 DX_R8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ee) (Z_to_bv 64 P) (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 A) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R7) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ee) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 A) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R7)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC EEP EEH PR MI. unfold DX_R7, DX_R8, P_OPENSSL_sk_push. unfold entry_cells in EC |- *. cbn [en_version en_pname en_publen en_pub en_nsuites en_suites en_maxname en_cfgid en_exts en_loadtime en_forretry en_enclen en_encoded].
    unfold ENTRY_SIZE in *. retpc.
    pose proof (munch_refl [(ee, ee + 104)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    st1. step. try br. step. step. step. apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption; try reflexivity.
    all: unfold wz in *; exact EC.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_seg9 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (r : Z),
      0 < r < 2^63 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 (-2)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 DX_HEAD) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R8)) fc None m (seg_rom usegs)).
  Proof.
    intros until r. intros RR MI. unfold DX_R8, DX_HEAD. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. step. try br. apply evt_done. reflexivity.
  Qed.
End S3.

Section S4.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma dx_glue1 : forall (line : Z) (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), 0 <= line < 2^31 -> mem_inv usegs m1 ->
      evt usegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 DX_RA2) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 line) (Z_to_bv 64 DX_FUNC) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 line) s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_debug) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_RA1) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 line) s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 DX_RA1)) fc None m1 (seg_rom usegs)).
  Proof.
    intros until m1. intros LR MI. unfold DX_RA1, DX_RA2, P_ERR_set_debug, DX_FILE_ECHS, DX_FUNC. retpc.
    do 7 step. finish.
  Qed.
  Lemma dx_glue2 : forall (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : mem), mem_inv usegs m1 ->
      evt usegs (fun ms' => exists v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6,
                   ms' = MS (mkR (Z_to_bv 64 DX_RA3) sp gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 DX_ERR_LIB_SSL) (Z_to_bv 64 SSL_R_BAD_ECHCONFIG_EXTENSION) (Z_to_bv 64 0) c3 c4 c5 c6 c7
                                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6) F (Z_to_bv 64 P_ERR_set_error) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_RA2) sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (ret_pc (Z_to_bv 64 DX_RA2)) fc None m1 (seg_rom usegs)).
  Proof.
    intros until m1. intros MI. unfold DX_RA2, DX_RA3, P_ERR_set_error, DX_ERR_LIB_SSL, SSL_R_BAD_ECHCONFIG_EXTENSION. retpc.
    do 5 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segF2 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4
           j0 (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra : word),
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> 0 <= en_exts E < 2^64 ->
      rw_cells usegs m (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> 144 <= bv_unsigned sp -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R9) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) (Z_to_bv 64 (en_exts E)) (Z_to_bv 64 DX_THUNK_FREE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0) (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_RA3) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_RA3)) fc None m (seg_rom usegs)).
  Proof.
    intros until xra. intros EC EEP EEH XR FR SPL MI. unfold DX_RA3, DX_R9, P_OPENSSL_sk_set_thunks, DX_THUNK_FREE. unfold entry_cells in EC. unfold ENTRY_SIZE in EEH.
    unfold dx_frame, DX_THUNK_FREE, DX_THUNK_COPY, DX_THUNK_CMP in FR. retpc.
    pose proof (word_range sp) as SPR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    step. step. unfold wz. step. if_lit.
    step. step. unfold wz. do 4 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segF3 :
    forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
      GOT_echfree m -> 0 <= P < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R10) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 P_ossl_echext_free) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R9) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R9)) fc None m (seg_rom usegs)).
  Proof.
    intros until P. intros GE PR MI. unfold DX_R9, DX_R10, P_OPENSSL_sk_pop_free, P_ossl_echext_free. unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free in GE. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. step. unfold wz. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segF4 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z) (E : entrep) pad1 pad2 pad3 pad4,
      rw_cells usegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE < 2^64 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          munch [(ee, ee + ENTRY_SIZE)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ rw_cells usegs m1 ee (entry_cells (mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) 0 (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 DX_R11) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ee) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_echext_free) fc None m1 (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R10) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ee) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 0) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R10)) fc None m (seg_rom usegs)).
  Proof.
    intros until pad4. intros EC EEP EEH MI. unfold DX_R10, DX_R11, P_ossl_echext_free. unfold entry_cells in EC |- *.
    cbn [en_version en_pname en_publen en_pub en_nsuites en_suites en_maxname en_cfgid en_exts en_loadtime en_forretry en_enclen en_encoded]. unfold ENTRY_SIZE in *. retpc.
    pose proof (munch_refl [(ee, ee + 104)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    st1. step. step. apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption; try reflexivity.
    all: unfold wz in *; exact EC.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segF5 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 DX_FILE_ECHS) (Z_to_bv 64 240) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R11) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 0) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R11)) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold DX_R11, DX_R12, P_CRYPTO_free, DX_FILE_ECHS. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    do 6 step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segF6 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
      mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 DX_R12) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 DX_EPI) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 DX_R12) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 DX_R12)) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros MI. unfold DX_R12, DX_EPI. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma dx_segE :
    forall (rax sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (j0 : list byte) (x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 ra : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      rw_cells usegs m (bv_unsigned sp + -144) (dx_frame j0 x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 ra) ->
      stk usegs m lo (bv_unsigned sp + -144) -> hceil <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
      evt usegs (fun ms' =>
          ms' = MS (mkR ra sp gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom usegs)
          /\ stk usegs m lo (bv_unsigned sp))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DX_EPI) fc None m (seg_rom usegs)).
  Proof.
    intros until lo. intros FR ST CEIL LO MI. unfold DX_EPI. unfold dx_frame in FR. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
    do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). apply evt_done. split; [reflexivity| exact ST].
  Qed.
End S4.
