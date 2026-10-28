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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocKit AllocRep AsAtomics AllocWalkKit AW_IAInit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Ltac litx := repeat match goal with
  | |- context [Z_to_bv 64 (bv_swrap ?n ?x)] => let v := eval vm_compute in (bv_swrap n x) in change (bv_swrap n x) with v
  | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v
  | |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
  | |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v
  | |- context [Z_to_bv 64 (Z.shiftr ?x ?y)] => let v := eval vm_compute in (Z.shiftr x y) in change (Z.shiftr x y) with v
  | |- context [Z_to_bv 64 (Z.shiftl ?x ?y)] => let v := eval vm_compute in (Z.shiftl x y) in change (Z.shiftl x y) with v
  | |- context [Z_to_bv 64 (?x + ?y)] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (x + y) in change (x + y) with v
  end.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Definition drain_W (spv C LG : Z) (ng : Z) : list ivl :=
    [(spv + -48, spv); (AINST + OI_QMUTEX, AINST + OI_QMUTEX + 8); (AINST + OI_GQ, AINST + OI_GQ + 32); (C, C + 32)]
    ++ (if ng =? 0 then [] else [(LG, LG + 8)]).
End HCW.

  Section Drain.
  Context {HCEIL : HeapCeil}.
    Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
    Variables (lo C : Z) (ng fg LG bg gsz gcnt : Z) (nt ft LT bt : Z) (qmax qmin qcache : Z).
    Hypothesis MI : mem_inv asegs m.
    Hypothesis ST : stk asegs m lo (bv_unsigned sp).
    Hypothesis LO : aceil <= lo. Hypothesis HI : lo + 48 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
    Hypothesis CR : akobj C 32 /\ C + 32 <= aceil /\ C mod 8 = 0.   (* [comment removed for export] *)
    Hypothesis NGR : 0 <= ng < 2^63 /\ 0 <= fg < 2^64 /\ 0 <= LG < 2^64 /\ 0 <= bg. Hypothesis NTR : 0 < nt < 2^63 /\ 0 <= ft < 2^64 /\ 0 <= LT < 2^64 /\ 0 <= bt.
    Hypothesis BR : bg + bt < 2^63. Hypothesis QR : 0 <= qmax < 2^64 /\ 0 <= qmin < 2^64.
    Hypothesis GSZ : 0 <= gsz < 2^64 /\ 0 <= gcnt < 2^64.
    (* [comment removed for export] *)
    Hypothesis LGR : ng <> 0 -> AHI_LO <= LG /\ LG + 24 <= aceil /\ LG mod 8 = 0 /\ (LG + 24 <= C \/ C + 32 <= LG).
    Hypothesis QM : rw_cells asegs m (AINST + OI_QMUTEX) [C8 (wz 0)].
    Hypothesis GQ : rw_cells asegs m (AINST + OI_GQ) [C8 (wz ng); C8 (wz fg); C8 (wz LG); C8 (wz bg)].
    Hypothesis GL : ng <> 0 -> rw_cells asegs m LG [C8 (wz 0); C8 (wz gsz); C8 (wz gcnt)].
    Hypothesis TQ : rw_cells asegs m C [C8 (wz nt); C8 (wz ft); C8 (wz LT); C8 (wz bt)].
    Hypothesis QC : rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)].

    Definition drain_mem (m' : mem) (mutex : Z) : Prop :=
         munch (drain_W (bv_unsigned sp) C LG ng) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (AINST + OI_QMUTEX) [C8 (wz mutex)]
      /\ rw_cells asegs m' (AINST + OI_GQ) [C8 (wz (ng + nt)); C8 (wz (if ng =? 0 then ft else fg)); C8 (wz LT); C8 (wz (bg + bt))]
      /\ (ng <> 0 -> rw_cells asegs m' LG [C8 (wz ft); C8 (wz gsz); C8 (wz gcnt)])
      /\ rw_cells asegs m' C [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
      /\ rw_cells asegs m' (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)].

    (* [comment removed for export] *)
    Definition drain_norec_post : machine_state -> Prop := fun ms' =>
      exists (t0' t1' a1' a4' a5' a6' a7' : word) m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz (AINST + OI_Q)) a1' a2 a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ drain_mem m' 0.
    (* [comment removed for export] *)
    Definition drain_rec_post : machine_state -> Prop := fun ms' =>
      exists (t0' t1' a4' a5' a6' a7' : word) m',
        ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz (AINST + OI_Q)) (wz qmin) a2 a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x198d74) fc None m' (seg_rom asegs)
        /\ drain_mem m' 256.

    Let ENTRY := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (AINST + OI_Q)) (wz C) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x198bd0) fc None m (seg_rom asegs).

    (* [comment removed for export] *)
    Definition drain_check_post : machine_state -> Prop := fun ms' =>
      exists (t0' t1' a5' a6' a7' : word) (jk : list byte) m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2 s0 s1 (wz (AINST + OI_Q)) (wz (bg + bt)) a2 a3 (wz qmax) a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x198c9c) fc None m' (seg_rom asegs)
        /\ munch (drain_W (bv_unsigned sp) C LG ng) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -48)
        /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ rw_cells asegs m' (AINST + OI_QMUTEX) [C4 (wz 0); C4 (wz 0)]
        /\ rw_cells asegs m' (AINST + OI_GQ) [C8 (wz (ng + nt)); C8 (wz (if ng =? 0 then ft else fg)); C8 (wz LT); C8 (wz (bg + bt))]
        /\ (ng <> 0 -> rw_cells asegs m' LG [C8 (wz ft); C8 (wz gsz); C8 (wz gcnt)])
        /\ rw_cells asegs m' C [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
        /\ rw_cells asegs m' (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)].

    Lemma drain_to_check : evt asegs drain_check_post ENTRY.
    Proof.
      unfold ENTRY.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof (munch_refl (drain_W (bv_unsigned sp) C LG ng) m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof (akobj_env _ _ (proj1 CR) ltac:(clear; lia)) as CRE. pose proof (akobj_lit _ _ (proj1 CR)) as CRB.
      unfold drain_W, AINST, OI_QMUTEX, OI_GQ, OI_Q, OI_QMAX, AHI_LO, wz in *. acb.
      replace (6976152 + 880) with 6977032 in * by reflexivity. replace (6977032 + 8) with 6977040 in * by reflexivity.
      replace (6976152 + 888) with 6977040 in * by reflexivity. replace (6977040 + 32) with 6977072 in * by reflexivity.
      replace (6976152 + 792) with 6976944 in * by reflexivity. replace (6976152 + 728) with 6976880 in * by reflexivity.
      apply (rw_cells_reshape _ _ _ [C4 (wz 0); C4 (wz 0)]) in QM; [| reflexivity| reflexivity| cbn; exact (conj I (conj I I))]. unfold wz in QM.
      assert (MA : 6977032 mod 4 = 0) by reflexivity. assert (MR : 0 <= 6977032 < 2^64) by (clear; lia).
      destruct (Z.eqb_spec ng 0) as [NG0|NG1]; cbn [app] in MU |- *.
      - (* [comment removed for export] *)
        clear GL LGR.
        (* [comment removed for export] *)
        step. carve_frame 48%nat ST. step. step. step. step. step. step. step. step. step. litx.
        (* [comment removed for export] *)
        astep. step. step. step. step. litx. astep.
        step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
        step. litx. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
        (* [comment removed for export] *)
        step. litx. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - CRE ACEILB; lia). clear - CRE CRB. lia. } clear K.
        step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - NTR; lia). clear - NTR. lia. } clear K.
        step. step. if_cases K; zify_cond K. 2: { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - NGR; lia). clear - NG0. lia. } clear K.
        (* [comment removed for export] *)
        step. step. step. step. step. step.
        (* [comment removed for export] *)
        step; fix_lit_store. step; fix_lit_store. step; fix_lit_store. step. step. step. step. step; fix_lit_store. step.
        (* [comment removed for export] *)
        apply (rw_cells_reshape _ _ _ [C1 (b8 1); C1 (b8 0); C2 (wz 0); C4 (wz 0)]) in QM; [| reflexivity| reflexivity| cbn; repeat split; exact I].
        st1. step. step.
        apply (rw_cells_reshape _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in QM; [| reflexivity| reflexivity| cbn; repeat split; exact I].
        apply evt_done. unfold drain_check_post, drain_W. rewrite (proj2 (Z.eqb_eq ng 0) NG0). cbn [app]. unfold AINST, OI_QMUTEX, OI_GQ, OI_QMAX, OI_Q, wz. rewrite NG0, Z.add_0_l.
        do 7 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact QM|]. split; [exact GQ|].
        split; [intros NE; exfalso; exact (NE eq_refl)|]. split; [exact TQ| exact QC].
      - (* [comment removed for export] *)
        specialize (GL NG1). specialize (LGR NG1).
        step. carve_frame 48%nat ST. step. step. step. step. step. step. step. step. step. litx.
        astep. step. step. step. step. litx. astep.
        step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
        step. litx. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
        step. litx. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - CRE ACEILB; lia). clear - CRE CRB. lia. } clear K.
        step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - NTR; lia). clear - NTR. lia. } clear K.
        step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit, ?land64_id by (clear - NGR; lia). clear - NG1. lia. } clear K.
        (* [comment removed for export] *)
        step. step. step. step. step. step. step. step.
        (* [comment removed for export] *)
        step; fix_lit_store. step; fix_lit_store. step; fix_lit_store. step. step. step. step. step; fix_lit_store. step.
        apply (rw_cells_reshape _ _ _ [C1 (b8 1); C1 (b8 0); C2 (wz 0); C4 (wz 0)]) in QM; [| reflexivity| reflexivity| cbn; repeat split; exact I].
        st1. step. step.
        apply (rw_cells_reshape _ _ _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in QM; [| reflexivity| reflexivity| cbn; repeat split; exact I].
        apply evt_done. unfold drain_check_post, drain_W. rewrite (proj2 (Z.eqb_neq ng 0) NG1). cbn [app]. unfold AINST, OI_QMUTEX, OI_GQ, OI_QMAX, OI_Q, wz.
        do 7 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact QM|]. split; [exact GQ|].
        split; [intros _; exact GL|]. split; [exact TQ| exact QC].
    Qed.

    Theorem drain_norec : bg + bt <= qmax -> evt asegs drain_norec_post ENTRY.
    Proof.
      intros LE. eapply evt_cut; [exact drain_to_check|]. cbv beta. intros ms1 PC.
      destruct PC as (t0' & t1' & a5' & a6' & a7' & jk & m1 & -> & MU & WM & MI1 & ST1 & FR & QM1 & GQ1 & GL1 & TQ1 & QC1). clear QM GQ GL TQ QC MI ST.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof (akobj_env _ _ (proj1 CR) ltac:(clear; lia)) as CRE. pose proof (akobj_lit _ _ (proj1 CR)) as CRB.
      unfold drain_W, AINST, OI_QMUTEX, OI_GQ, OI_Q, OI_QMAX, AHI_LO, wz in *. acb.
      replace (6976152 + 880) with 6977032 in * by reflexivity. replace (6977032 + 8) with 6977040 in * by reflexivity.
      replace (6976152 + 888) with 6977040 in * by reflexivity. replace (6977040 + 32) with 6977072 in * by reflexivity.
      replace (6976152 + 792) with 6976944 in * by reflexivity. replace (6976152 + 728) with 6976880 in * by reflexivity.
      (* [comment removed for export] *)
      step. if_cases K; zify_cond K. 2: { exfalso. revert K. rewrite ?unsigned_lit by (clear - LE QR BR NGR NTR; lia). clear - LE. lia. } clear K.
      step. step. step. step. step. step. step.
      release_frame FR ST1 (bv_unsigned sp).
      apply (rw_cells_reshape _ _ _ [C8 (Z_to_bv 64 0)]) in QM1; [| reflexivity| reflexivity| cbn; repeat split; exact I].
      apply evt_done. unfold drain_norec_post, drain_mem, drain_W. unfold AINST, OI_QMUTEX, OI_GQ, OI_QMAX, OI_Q, wz. do 8 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST1|]. split; [exact QM1|]. split; [exact GQ1|]. split; [exact GL1|]. split; [exact TQ1| exact QC1].
    Qed.

    Theorem drain_rec : qmax < bg + bt -> evt asegs drain_rec_post ENTRY.
    Proof.
      intros GT. eapply evt_cut; [exact drain_to_check|]. cbv beta. intros ms1 PC.
      destruct PC as (t0' & t1' & a5' & a6' & a7' & jk & m1 & -> & MU & WM & MI1 & ST1 & FR & QM1 & GQ1 & GL1 & TQ1 & QC1). clear QM GQ GL TQ QC MI ST.
      pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof (akobj_env _ _ (proj1 CR) ltac:(clear; lia)) as CRE. pose proof (akobj_lit _ _ (proj1 CR)) as CRB.
      unfold drain_W, AINST, OI_QMUTEX, OI_GQ, OI_Q, OI_QMAX, AHI_LO, wz in *. acb.
      replace (6976152 + 880) with 6977032 in * by reflexivity. replace (6977032 + 8) with 6977040 in * by reflexivity.
      replace (6976152 + 888) with 6977040 in * by reflexivity. replace (6977040 + 32) with 6977072 in * by reflexivity.
      replace (6976152 + 792) with 6976944 in * by reflexivity. replace (6976152 + 728) with 6976880 in * by reflexivity.
      assert (MA : 6977032 mod 4 = 0) by reflexivity. assert (MR : 0 <= 6977032 < 2^64) by (clear; lia). cbn [app] in MU.
      (* [comment removed for export] *)
      pose proof (munch_refl [(6977032, 6977032 + 4)]%Z m1) as MUY. pose proof (wmono_refl asegs m1) as WMY.
      all: step; (if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit by (clear - GT QR BR NGR NTR; lia); clear - GT; lia|]; clear K).
      all: step; step; step; step; step; step; step; step; litx.
      all: astep; step; step; step; step; litx; astep.
      all: step; (if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]; clear K).
      all: step; step; litx; step; (if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]; clear K).
      all: step; step; step; step; step; step; step; step.
      all: release_frame FR ST1 (bv_unsigned sp).
      all: apply (rw_cells_reshape _ _ _ [C8 (Z_to_bv 64 256)]) in QM1; [| reflexivity| reflexivity| cbn; repeat split; exact I].
      all: apply evt_done; unfold drain_rec_post, drain_mem, drain_W; unfold AINST, OI_QMUTEX, OI_GQ, OI_QMAX, OI_Q, wz; do 7 eexists; split; [reflexivity|].
      all: split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST1|]; split; [exact QM1|]; split; [exact GQ1|].
      all: split; [intros NE; specialize (GL1 NE); specialize (LGR NE); eapply rw_cells_transport; [exact GL1| exact MUY| exact WMY|];
                   cbn [disjoint_from cells_size csize length Nat.add]; split; [| exact I]; right; clear - LGR; lia|].
      all: split; [exact TQ1| exact QC1].
    Qed.
  End Drain.
