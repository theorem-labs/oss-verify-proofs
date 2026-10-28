(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_Populate AW_Gfa.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocTacX.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition lcd_push_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P CA cnt mc cp : Z) (chunks : list Z) (q0 q1 q3 : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 q2 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (P, P + 4); (P + 16 + 4 * cnt, P + 20 + 4 * cnt); (CA + 2576, CA + 2584)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' P [C4 (wz (cnt + 1)); C4 (wz mc)]
    /\ u32arr asegs m' (P + 16) (wlist (rev (cp :: chunks)))
    /\ stk asegs m' (P + 16 + 4 * (cnt + 1)) (P + 80)
    /\ rw_cells asegs m' (CA + CACHE_STATS) [C8 q0; C8 q1; C8 q2; C8 q3].
End HCW2.

Section Push.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp : word) (rax t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (f0 f1 f2 f3 f4 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo sb c CA p cnt mc csz : Z) (chunks : list Z) (q0 q1 q2 q3 : word).
  Let P := CA + PCLASS_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Variable m0 : mem.   (* [comment removed for export] *)
  Hypothesis MI : mem_inv asegs m.
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp); (P, P + 4); (P + 16 + 4 * cnt, P + 20 + 4 * cnt); (CA + 2576, CA + 2584)]%Z m0 m.
  Hypothesis WM : wmono asegs m0 m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -48).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 48 <= bv_unsigned sp.
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -48) [C8 f4; C8 f3; C8 f2; C8 f1; C8 f0; C8 ra].
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize <= aceil.
  Hypothesis PR : rbeg <= p < rbeg + 2^32. Hypothesis PA : p mod 16 = 0.
  Hypothesis Ha4 : a4 = sx32 (wz cnt).
  Hypothesis ISB : rw_cells asegs m (AINST + 32) [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)].
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)].
  Hypothesis PC2 : rw_cells asegs m (P + 8) [C8 (wz csz)]. Hypothesis CSZ : 0 <= csz < 2^64.
  Hypothesis PC3 : u32arr asegs m (P + 16) (wlist (rev chunks)).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis ROOM : 0 <= cnt <= 15.
  Hypothesis PC4 : stk asegs m (P + 16 + 4 * cnt) (P + 80).
  Hypothesis QST : rw_cells asegs m (CA + CACHE_STATS) [C8 q0; C8 q1; C8 q2; C8 q3].

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Lemma lcd_push :
    evt asegs (lcd_push_post ra sp gp tp f0 f1 f2 f3 f4 s5 s6 s7 s8 s9 s10 s11 F fc m0 lo P CA cnt mc (Z.shiftr (p - rbeg) kCompactPtrScale) chunks q0 q1 q3)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz P) s1 (wz CA) (wz AINST) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19965c) fc None m (seg_rom asegs)).
  Proof.
    unfold AINST, PCLASS_SIZE, CACHE_STATS, kSpaceSize, kNumClasses, kCompactPtrScale, AHI_LO in *. subst a4.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    change (6976152 + 32) with 6976184 in ISB.
    assert (PB : CA + 80 <= P /\ P + 80 <= CA + 2560) by (subst P; clear - HC; try acb; lia).
    assert (LEN : Z.of_nat (length (wlist (rev chunks))) = cnt) by (unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; clear - CNT; try acb; lia).
    assert (CPR : 0 <= Z.shiftr (p - rbeg) 4 < 2^28) by (rewrite Z.shiftr_div_pow2 by (clear; aunf; lia); clear - PR; try acb; Z.div_mod_to_equations; aunf; lia).
    rewrite sx32_wz by (clear - ROOM; try acb; lia). unfold wz in *.
    (* [comment removed for export] *)
    do 12 step.
    rewrite ?(unsigned_lit c), ?(unsigned_lit cnt), ?(unsigned_lit p), ?(unsigned_lit sb) by (clear - HC ROOM PR SBR; try acb; subst rbeg; aunf; lia).
    rewrite (shl32_shr30 cnt) by (clear - ROOM; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 32) by (clear; lia).
    rewrite ?(unsigned_lit (c * 2^32)) by (clear - HC; try acb; lia).
    rewrite (unsigned_lit (p - c * 2^32)) by (clear - HC PR SBR; try acb; subst rbeg; aunf; lia).
    rewrite (unsigned_lit (p - c * 2^32 - sb)) by (clear - HC PR SBR; try acb; subst rbeg; aunf; lia).
    replace (p - c * 2^32 - sb) with (p - rbeg) by (subst rbeg; clear; lia).
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (P + 16 + 4 * cnt + 4) _ PC4 ltac:(hci; clear - ROOM; try acb; lia)) as [SK1 SK2]. clear PC4.
    destruct (stk_cells _ _ _ SK1 ltac:(hci; clear; lia)) as [jw JW]. clear SK1.
    replace (P + 16 + 4 * cnt + 4 - (P + 16 + 4 * cnt)) with 4 in JW by (clear; lia). change (Z.to_nat 4) with 4%nat in JW.
    remember (P + 16 + 4 * cnt) as D eqn:ED in JW |- *.
    replace (P + 4 * cnt) with (D + -16) by (subst D; clear; lia).
    (* [comment removed for export] *)
    st1. step. subst D.
    (* [comment removed for export] *)
    step.
    assert (AL8 : (CA + 2576) mod 8 = 0) by (clear - CAR; try acb; destruct CAR as (_ & _ & M); Z.div_mod_to_equations; aunf; lia).
    assert (ALR : 0 <= CA + 2576 < 2^64) by (clear - CAR; try acb; aunf; lia).
    astep.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp).
    assert (ARR' : u32arr asegs m1 (P + 16) (wlist (rev ((Z.shiftr (p - rbeg) 4) :: chunks)))).
    { unfold wlist in *. cbn [rev]. rewrite map_app. cbn [map]. apply u32arr_snoc. split; [exact PC3|].
      rewrite length_map, length_rev. replace (Z.of_nat (length chunks)) with cnt by (unfold zlen in CNT; clear - CNT; try acb; lia). exact JW. }
    apply evt_done. unfold lcd_push_post. do 16 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact PC1|]. split; [exact ARR'|]. split; [replace (P + 16 + 4 * (cnt + 1)) with (P + 16 + 4 * cnt + 4) by (clear; lia); exact SK2| exact QST].
  Qed.
End Push.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lcd_head_nodrain_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P CA c p cnt : Z) : machine_state -> Prop :=
  fun ms' => exists (a5' : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz P) s1 (wz CA) (wz AINST) (wz c) (wz p) (sx32 (wz cnt)) a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19965c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition lcd_head_drain_post (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P CA c p cnt mc : Z) : machine_state -> Prop :=
  fun ms' => exists m' (j8 : list byte),
    let n := mc / 2 in
    ms' = MS (mkR (wz 0x199a10) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (wz P) (wz CA) (wz AINST) (Z_to_bv 64 (bv_unsigned sp + -104)) (wz (CA + 2560))
                  (wz c) (wz (P + 16 + 4 * (cnt - n))) (wz n) (wz (CA + 2560)) a7 (wz AINST) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x199b50) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (P, P + 4)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (bv_unsigned sp + -112) [CB 8 j8; C8 (wz AINST); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0x1997c8)]
    /\ rw_cells asegs m' P [C4 (wz (cnt - n)); C4 (wz mc)].
End HCW2.

Section Head.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo c CA p cnt mc : Z).
  Let P := CA + PCLASS_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 112 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz CA. Hypothesis Ha1 : a1 = wz AINST. Hypothesis Ha2 : a2 = wz c. Hypothesis Ha3 : a3 = wz p.
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis PR : 0 <= p < 2^64.
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)].
  Hypothesis CNT : 0 <= cnt <= mc. Hypothesis MC : 1 <= mc <= 16.

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Ltac head_common :=
    unfold AINST, PCLASS_SIZE, kNumClasses, AHI_LO in *; subst a0 a1 a2 a3;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR; acb;
    assert (PB : CA + 80 <= P /\ P + 80 <= CA + 2560) by (subst P; clear - HC; try acb; lia);
    unfold wz in *;
    (* [comment removed for export] *)
    step; carve_frame 48%nat ST; do 6 step;
    (* [comment removed for export] *)
    step; (let K := fresh "K" in if_cases K; zify_cond K; [deadK K| clear K]);
    step; step; (let K := fresh "K" in if_cases K; zify_cond K; [deadK K| clear K]);
    (* [comment removed for export] *)
    step; step; step; rewrite (unsigned_lit c) by (clear - HC; try acb; lia); replace (CA + c * 80) with P by (subst P; clear; lia);
    step; step; (let K := fresh "K" in if_cases K; zify_cond K; [exfalso; revert K; rewrite sx32_wz, unsigned_lit by (clear - MC; try acb; lia); clear - MC; try acb; intros K; lia| clear K]);
    step; step.

  Lemma lcd_head_nodrain : cnt < mc ->
    evt asegs (lcd_head_nodrain_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P CA c p cnt)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199618) fc None m (seg_rom asegs)).
  Proof.
    intros LT.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    head_common.
    if_cases K; zify_cond K. { exfalso. revert K. rewrite !sx32_wz, !unsigned_lit by (clear - MC CNT; try acb; lia). clear - LT; try acb. intros K. lia. } clear K.
    apply evt_done. unfold lcd_head_nodrain_post. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
  Qed.

  Lemma lcd_head_drain : cnt = mc ->
    evt asegs (lcd_head_drain_post ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P CA c p cnt mc)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199618) fc None m (seg_rom asegs)).
  Proof.
    intros EQ.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (P, P + 4)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    head_common.
    if_cases K; zify_cond K. 2:{ exfalso. apply K. subst cnt. reflexivity. } clear K.
    (* [comment removed for export] *)
    do 8 step.
    (* [comment removed for export] *)
    step. carve_frame 64%nat ST. st1. st1. st1. step. step. st1. st1. st1. st1.
    (* [comment removed for export] *)
    step. step. step.
    rewrite ?sx32_wz, ?zx32_wz by (clear - MC CNT; try acb; lia). unfold wz. rewrite ?(unsigned_lit cnt), ?(unsigned_lit mc) by (clear - MC CNT; try acb; lia).
    rewrite (shl32_val cnt) by (clear - MC CNT; try acb; lia). rewrite !Z.shiftr_div_pow2 by (clear; lia). rewrite (Z.div_mul cnt (2^32)) by (clear; lia).
    change (2^1) with 2.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - MC CNT; try acb; lia). clear - EQ MC; try acb. intros K. Z.div_mod_to_equations. lia. } clear K.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit cnt), ?(unsigned_lit (mc / 2)) by (clear - MC CNT; try acb; Z.div_mod_to_equations; lia).
    step. step. step. step. step.
    rewrite (unsigned_lit (cnt - mc / 2)) by (clear - MC CNT EQ; try acb; Z.div_mod_to_equations; lia). rewrite (Z.shiftl_mul_pow2 (cnt - mc / 2) 2) by (clear; lia). change (2^2) with 4.
    step. step. step. step. step.
    rewrite ?unsigned_lit by (clear - SPR HI LO; try acb; lia).
    replace (P + (cnt - mc / 2) * 4 + 16) with (P + 16 + 4 * (cnt - mc / 2)) by (clear; lia).
    replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by (clear; lia).
    apply evt_done. unfold lcd_head_drain_post. do 2 eexists. cbv zeta.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FR0| assumption].
  Qed.
End Head.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lcd_drain_tail_post (sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo P CA c p cnt : Z) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (wz 0x1997c8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz P) (wz CA) (wz CA) (wz AINST) (wz c) (wz p) (sx32 (wz cnt)) a5 a6 a7
                  (wz AINST) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19965c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp - 112)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48).
End HCW2.

Section DrainTail.
  Context {HCEIL : HeapCeil}.
  Variables (sp gp tp rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo c CA p cnt : Z) (mcw f8 : word) (j8 : list byte).
  Let P := CA + PCLASS_SIZE * c.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -112).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 160 <= bv_unsigned sp.
  Hypothesis HC : 1 <= c < kNumClasses.
  Hypothesis CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0.
  Hypothesis CNT : 0 <= cnt < 2^31.
  Hypothesis FR0 : rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j8; C8 f8; C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0x1997c8)].
  Hypothesis PC1 : rw_cells asegs m P [C4 (wz cnt); C4 mcw].

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Lemma lcd_drain_tail :
    evt asegs (lcd_drain_tail_post sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P CA c p cnt)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (wz P) (wz CA) a0 a1 a2 a3 a4 a5 a6 a7
               (wz AINST) (wz c) (wz p) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x199a10) fc None m (seg_rom asegs)).
  Proof.
    unfold AINST, PCLASS_SIZE, kNumClasses, AHI_LO in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    assert (PB : CA + 80 <= P /\ P + 80 <= CA + 2560) by (subst P; clear - HC; try acb; lia).
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 112)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (E112 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; clear - SPR HI LO; try acb; lia).
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. st1. step. step. st1.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -160) _ |- _ => release_frame H ST (bv_unsigned sp + -112) end.
    (* [comment removed for export] *)
    step. step. step.
    release_frame FR0 ST (bv_unsigned sp + -48).
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    apply evt_done. unfold lcd_drain_tail_post. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.
End DrainTail.

