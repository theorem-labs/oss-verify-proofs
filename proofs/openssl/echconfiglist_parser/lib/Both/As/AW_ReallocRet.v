(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocKit AllocRep AllocWalkKit AsDepotInv AW_MallocBase AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section HCW.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Variables (sp ra s0 s1 s2 s3 s4 s5 s6 : word).
  Variables (gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (T : list Z) (rest : list word) (jk jr1 jr2 : list byte) (cfu : word) (P0 size UN : Z).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2576 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis LR  : length rest = (255 - length T)%nat.
  Hypothesis NR  : (1 <= length T <= 30)%nat.
  Hypothesis UNR : 0 < UN < 2^64.

  (* [comment removed for export] *)
  Definition realloc_ret_post (m : mem) : machine_state -> Prop := fun ms' =>
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz UN) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ stk asegs m lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Lemma icpt_frame_releaseR : forall m,
    stk asegs m lo (bv_unsigned sp + -2208) ->
    rw_cells asegs m (bv_unsigned sp + -2208) [C8 cfu; C8 (wz 0x1bf8f0); C8 (wz P0); C8 (wz size); C8 sp; C8 (wz 0x197900)] ->
    rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 jr1; C8 (wz 0x1bf960)] ->
    rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jr2] ->
    rw_cells asegs m (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))] ->
    u64arr asegs m (bv_unsigned sp + -2136 + 16) (map wz T ++ rest) ->
    rw_cells asegs m (bv_unsigned sp + -80) [C8 sp] ->
    rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m lo (bv_unsigned sp).
  Proof.
    intros m ST FRR FRA FP ESO TRB TFB F8.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (stk_of_rw_cells asegs _ _ _ FRR) as K0. pose proof (stk_of_rw_cells asegs _ _ _ FRA) as K1. pose proof (stk_of_rw_cells asegs _ _ _ FP) as K1b.
    pose proof (stk_of_rw_cells asegs _ _ _ ESO) as K2.
    pose proof (stk_of_rw_cells asegs _ _ _ TFB) as K4. pose proof (stk_of_rw_cells asegs _ _ _ F8) as K5.
    pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB))) as K3.
    cbn [cells_size csize Nat.add] in K0, K1, K1b, K2, K3, K4, K5.
    rewrite u64s_length, length_app, length_map, LR in K3.
    eapply stk_merge; [exact ST| |lia].
    eapply stk_merge; [exact K0| |lia]. replace (bv_unsigned sp + -2208 + Z.of_nat 48) with (bv_unsigned sp + -2160) by lia.
    eapply stk_merge; [exact K1| |lia]. replace (bv_unsigned sp + -2160 + Z.of_nat 16) with (bv_unsigned sp + -2144) by lia.
    eapply stk_merge; [exact K1b| |lia]. replace (bv_unsigned sp + -2144 + Z.of_nat 8) with (bv_unsigned sp + -2136) by lia.
    eapply stk_merge; [exact K2| |lia]. replace (bv_unsigned sp + -2136 + Z.of_nat 16) with (bv_unsigned sp + -2136 + 16) by lia.
    eapply stk_merge; [exact K3| |lia].
    replace (bv_unsigned sp + -2136 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -80) by lia.
    eapply stk_merge; [exact K4| |lia]. replace (bv_unsigned sp + -80 + Z.of_nat 8) with (bv_unsigned sp + -72) by lia.
    replace (bv_unsigned sp) with (bv_unsigned sp + -72 + Z.of_nat 72) at 2 by lia. exact K5.
  Qed.

  Theorem realloc_ret : forall (xra t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs5 xs6 t3 t4 t5 t6 : word) (m : mem),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) ->
    rw_cells asegs m (bv_unsigned sp + -2208) [C8 cfu; C8 (wz 0x1bf8f0); C8 (wz P0); C8 (wz size); C8 sp; C8 (wz 0x197900)] ->
    rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 jr1; C8 (wz 0x1bf960)] ->
    rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jr2] ->
    rw_cells asegs m (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))] ->
    u64arr asegs m (bv_unsigned sp + -2136 + 16) (map wz T ++ rest) ->
    rw_cells asegs m (bv_unsigned sp + -80) [C8 sp] ->
    rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    evt asegs (realloc_ret_post m)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 (wz UN) xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x197a10) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI ST FRR FRA FP ESO TRB TFB F8.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR. acb.
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.
    replace (ret_pc (Z_to_bv 64 1669376)) with (Z_to_bv 64 1669376) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step.
    replace (ret_pc (Z_to_bv 64 1833312)) with (Z_to_bv 64 1833312) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    step. do 8 step. step. step.
    apply evt_done. unfold realloc_ret_post. do 14 eexists. split; [reflexivity|].
    eapply icpt_frame_releaseR; eassumption.
  Qed.
  (* [comment removed for export] *)
  Definition rframes (m : mem) : Prop :=
       rw_cells asegs m (bv_unsigned sp + -2208) [C8 cfu; C8 (wz 0x1bf8f0); C8 (wz P0); C8 (wz size); C8 sp; C8 (wz 0x197900)]
    /\ rw_cells asegs m (bv_unsigned sp + -2160) [CB 8 jr1; C8 (wz 0x1bf960)]
    /\ rw_cells asegs m (bv_unsigned sp + -2144) [CB 8 jr2]
    /\ rw_cells asegs m (bv_unsigned sp + -2136) [C8 (wz (bv_unsigned sp + -2136 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m (bv_unsigned sp + -2136 + 16) (map wz T ++ rest)
    /\ rw_cells asegs m (bv_unsigned sp + -80) [C8 sp]
    /\ rw_cells asegs m (bv_unsigned sp + -72) [CB 8 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma rframes_transport : forall W m m', rframes m -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W (bv_unsigned sp + -2208) 2208 -> rframes m'.
  Proof.
    intros W m m' (F1 & F2 & F3 & F4 & F5 & F6 & F7) MU WM D.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    assert (DJ : forall A n, bv_unsigned sp + -2208 <= A -> A + n <= bv_unsigned sp -> 0 <= n -> disjoint_from W A n).
    { intros A n H1 H2 H3. clear - D H1 H2 H3. induction W as [|[u v] W IH]; [exact I|]. cbn [disjoint_from] in D |- *. destruct D as [D1 D2].
      split; [clear IH D2; lia| exact (IH D2)]. }
    assert (LTB : (length (map wz T ++ rest) = 255)%nat) by (rewrite length_app, length_map, LR; clear - NR; lia).
    Ltac trw H MU WM DJ := eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [cells_size csize length Nat.add Nat.mul]; apply DJ; lia].
    trw F1 MU WM DJ. trw F2 MU WM DJ. trw F3 MU WM DJ. trw F4 MU WM DJ. trw F6 MU WM DJ. trw F7 MU WM DJ.
    eapply u64arr_transport in F5; [| exact MU| exact WM| rewrite LTB; apply DJ; lia].
    exact (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 F7)))))).
  Qed.

  Theorem realloc_retF : forall (xra t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs5 xs6 t3 t4 t5 t6 : word) (m : mem),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) -> rframes m ->
    evt asegs (realloc_ret_post m)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 (wz UN) xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x197a10) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI ST (F1 & F2 & F3 & F4 & F5 & F6 & F7). eapply realloc_ret; eassumption.
  Qed.
End HCW.
