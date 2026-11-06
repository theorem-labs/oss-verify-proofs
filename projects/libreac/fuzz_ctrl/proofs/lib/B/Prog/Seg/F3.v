(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 184 of its 206 lines of code are new or changed and 374 lines of the source are left out. *)
(* Segment F3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan build of libreac v1.9.0, image B), frame-loop turn
   j: from the return point 0x81f78 of F2's checked memcpy to the return point of a reac_ctrl_parse call, 0x81fbc
   (len >= 50, the long-frame parse block 0x81f94) or 0x82048 (len < 50, the short-frame parse block 0x82020).
     0x81f78 li a0,50 / 0x81f7c bltu s4,a0,0x82020    len < 50: to the short parse block
     0x81f80 bnez s2,0x81f88                           Phi <> 0 (HB), so 0x81f84 `j 0x82fa0` (the trap) is not taken
     0x81f88 li a0,-18 / 0x81f8c bltu s2,a0,0x81f94    Phi < 2^64 - 18 (Phi + 50 <= stklo), so 0x81f90 is not taken
     0x81f94-0x81fa8 the five record-shadow stores, 0x81fac-0x81fb8 mv a0,s2 / mv a1,s4 / ld a2,280(s1) / jal
     reac_ctrl_parse, returning to 0x81fbc
   v1.9.0 against the patched image: the same instructions 0x70 bytes later, the trap at 0x82fa0 (was 0x82f3c), and
   the record pointer of the parse call loaded from FLI's spill [A+280] (was `mv a2,s6`; f2_parse_seg).
   The head run 0x81f78 -> 0x81f94 / 0x82020 (f3_head) writes no memory; it is lifted by Tac_slot.sl_run_lib, FRA
   moves by sl_fra_move, ENT by ent_mat and the bundles by F1's moves.  Both parse blocks are F2.f2_parse_seg (the
   record stores and the call on reac_ctrl_parse's contract, a Section hypothesis: a member of SlotLink's
   callee_contracts whose proof file is not in this tree).  Cuts: the official SlotInv.v Inv_B81f78_at (entry, pc
   0x81f78), Inv_B81fbc_at (pc 0x81fbc) and Inv_B82048_at (pc 0x82048) (exits).
   rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

(* ---- the head run 0x81f78 -> 0x82020 (len < 50) / 0x81f94 (len >= 50); no store ---- *)
Lemma f3_head :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (N phi : Z),
    0 <= N < 2 ^ 64 -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
    evt rsegs
      (fun ms' => exists a0' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) s5 s6
                       s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 (if N <? 50 then 0x82020 else 0x81f94)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 phi) s3 (Z_to_bv 64 N) s5 s6 s7 s8 s9
               s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81f78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m N phi
    HN Hphi0 Hphi1.
  (* 0x81f78 li a0,50 ; 0x81f7c bltu s4,a0 *)
  step. step.
  lazymatch goal with
  | |- context [bv_ltu (Z_to_bv 64 N) ?c] =>
      let u := eval vm_compute in (bv_unsigned c) in
      assert (Ec : bv_ltu (Z_to_bv 64 N) c = (N <? u))
        by (unfold bv_ltu; rewrite (MState.unsigned_lit N) by lia; change (bv_unsigned c) with u; reflexivity)
  end.
  rewrite Ec. destruct (Z.ltb_spec N 50) as [Hlt|Hge]; cbv iota.
  - apply evt_done. eexists. reflexivity.
  - (* 0x81f80 bnez s2 (taken) *)
    step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        let E := fresh "E" in
        assert (E : c = true)
          by (rewrite (bv_eqb_lit phi 0) by lia; apply Bool.negb_true_iff, Z.eqb_neq; lia);
        rewrite E; cbv iota; clear E
    end.
    (* 0x81f88 li a0,-18 ; 0x81f8c bltu s2,a0 (taken) *)
    step. step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        lazymatch c with
        | bv_ltu (Z_to_bv 64 phi) ?d =>
            let u := eval vm_compute in (bv_unsigned d) in
            let E := fresh "E" in
            assert (E : c = true)
              by (unfold bv_ltu; rewrite (MState.unsigned_lit phi) by lia; change (bv_unsigned d) with u;
                  apply Z.ltb_lt; lia);
            rewrite E; cbv iota; clear E
        end
    end.
    apply evt_done. eexists. reflexivity.
Qed.

(* ==== the segment ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs F1 F2.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module PC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Open Scope Z_scope.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* reac_ctrl_parse, taken on its lib/B contract (a member of SlotLink.callee_contracts), never on its code. A normal
   callee premise, discharged at the top through callee_contracts_holds by the v1.9 image-B proof
   reac_ctrl_parse_holds (lib/B/Prog/reac_ctrl_parse.v, a file of a working branch, not in this delivery). *)
Hypothesis HPARSE : PC.reac_ctrl_parse_contract.

(* seg_F3 (S_F3): from 0x81f78 (turn j, the copied frame bytes at Phi) through the record stores and the
   reac_ctrl_parse call of the frame's length class to 0x81fbc (len >= 50) or 0x82048 (len < 50). *)
Lemma seg_F3 : forall j : nat,
  Hat B APIf ra (Inv_B81fbc_at B APIf ra) j -> Hat B APIf ra (Inv_B82048_at B APIf ra) j ->
  Hat B APIf ra (Inv_B81f78_at B APIf ra) j.
Proof.
  intros j Hx4c Hxd8 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_B81f78_at, FCUT, FCUTP, CUTST in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hr18 & Hr20 & HFT &
                    HLK & HFC & Hr22 & HFSj & HREC).
  subst c.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  destruct (f2_flen_rng g j) as (HN0 & HNb).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HInblk : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (unfold hb1; cbn [app]; left; reflexivity).
  destruct (f1_lw_blocks (APIf rc) _ mem md phi _ HAH HInblk) as (_ & Hp4096 & Hpstklo & _ & _).
  assert (HL : AC.a_size (flen g j) = Z.max (flen g j) 1) by reflexivity.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81f78) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 (if flen g j <? 50 then 0x82020 else 0x81f94) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 22 = getr regs 22 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\ mem' = mem)
    (Post B APIf ra g)).
  { exact Hhalt. }
  { rewrite f1_mkR_of.
    pose proof Hr18 as R18. pose proof Hr20 as R20. unfold rg in R18, R20.
    rewrite R18, R20.
    eapply evt_mono; [apply f3_head; lia |].
    intros ms' (a0' & ->).
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 12 (split; [reflexivity|]).
    reflexivity. }
  intros R pc' mem1 regs'' md'
    (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K22 & K21 & K26 & K27 & Hm) Hreg Hmat.
  subst pc' mem1.
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact K27).
  (* ---- the frame and the bundles move to the new registers (the memory is the same) ---- *)
  pose proof (sl_fra_move B APIf ra g fr _ regs regs'' mem md md' HFRA E2 E3 E4 E8 E9 E19 E26 Hmat) as HFRA2.
  assert (HENT2 : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
  assert (HLK2 : LK g fr j regs'' mem).
  { apply (f1_lk_move g fr j regs regs'' mem mem A HLK Hr9 ltac:(lia) ltac:(lia) E9 E27).
    - intros x _. reflexivity.
    - intros x _. reflexivity.
    - intros x _. reflexivity.
    - intros x _. split; reflexivity.
    - exact (fra_stk B APIf ra g fr _ regs'' mem md' HFRA2). }
  destruct HFC as (S232 & R21 & R20).
  assert (S232' : spill regs'' mem 232 (t_left (g_in g) j - t_h (g_in g) j))
    by (apply (f1_spill_keep regs regs'' mem mem A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
        [intros x _; reflexivity | exact S232]).
  assert (HFC2 : FC g fr j regs'' mem).
  { split; [exact S232'|].
    split; [unfold rg in *; rewrite E21; exact R21 | unfold rg in *; rewrite E20; exact R20]. }
  assert (HFT2 : FTURN g j phi regs'' mem).
  { destruct HFT as (S224 & S232f & HPHI & HPHIl).
    split; [apply (f1_spill_keep regs regs'' mem mem A 224 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
            [intros x _; reflexivity | exact S224]|].
    split; [apply (f1_spill_keep regs regs'' mem mem A 232 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) E9);
            [intros x _; reflexivity | exact S232f]|].
    split; [exact HPHI | exact HPHIl]. }
  assert (HFSj2 : FSj g fr j regs'' mem).
  { apply (f1_fsj_move g fr j regs regs'' mem mem HFSj); intros x _; reflexivity. }
  assert (Hr182 : rg regs'' 18 phi) by (unfold rg in *; rewrite E18; exact Hr18).
  assert (Hr202 : rg regs'' 20 (flen g j)) by (unfold rg in *; rewrite E20; exact Hr20).
  assert (Hr222 : rg regs'' 22 1) by (unfold rg in *; rewrite E22; exact Hr22).
  assert (HPB : f2_PB g j phi fr regs'' mem).
  { split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact Hr182|].
    split; [exact Hr202|]. split; [exact HFT2|]. split; [exact HLK2|]. split; [exact HFC2|].
    split; [exact Hr222|]. split; [exact HFSj2 | exact HREC]. }
  destruct (Z_lt_le_dec (flen g j) 50) as [Hlt|Hge].
  - (* len < 50: the short parse block 0x82020 -> 0x82048 *)
    replace (if flen g j <? 50 then 0x82020 else 0x81f94) with 0x82020
      by (rewrite (proj2 (Z.ltb_lt _ _) Hlt); reflexivity).
    apply (f2_parse_seg B APIf ra empty FF HPARSE 0x82020 0x82038 0x82048 j g regs'' mem md' fr phi).
    + left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact Hlt].
    + exact HFRA2.
    + exact HENT2.
    + exact HPB.
    + intros regs' mem' md'' HFRA' HENT' HPB' HFPS' Ha0'.
      destruct HPB' as (Hgn' & Hj' & HHB' & Hr18' & Hr20' & HFT' & HLK' & HFC' & Hr22' & HFSj' & HREC').
      rewrite <- SEGS. apply Hxd8.
      unfold Inv_B82048_at, FCUT, FCUTP, CUTST.
      exists phi, regs', mem', md'', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn'|]. split; [exact Hj'|]. split; [exact HHB'|]. split; [exact Hr18'|].
      split; [exact Hr20'|]. split; [exact HFT'|].
      split; [exact HLK'|]. split; [exact Hr22'|]. split; [exact HFSj'|]. split; [exact HREC'|].
      split; [exact HFPS'|]. split; [exact Ha0' | exact Hlt].
  - (* len >= 50: the long parse block 0x81f94 -> 0x81fbc *)
    replace (if flen g j <? 50 then 0x82020 else 0x81f94) with 0x81f94
      by (rewrite (proj2 (Z.ltb_ge _ _) Hge); reflexivity).
    apply (f2_parse_seg B APIf ra empty FF HPARSE 0x81f94 0x81fac 0x81fbc j g regs'' mem md' fr phi).
    + right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact Hge].
    + exact HFRA2.
    + exact HENT2.
    + exact HPB.
    + intros regs' mem' md'' HFRA' HENT' HPB' HFPS' Ha0'.
      destruct HPB' as (Hgn' & Hj' & HHB' & Hr18' & Hr20' & HFT' & HLK' & HFC' & Hr22' & HFSj' & HREC').
      rewrite <- SEGS. apply Hx4c.
      unfold Inv_B81fbc_at, FCUT, FCUTP, CUTST.
      exists phi, regs', mem', md'', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn'|]. split; [exact Hj'|]. split; [exact HHB'|]. split; [exact Hr18'|].
      split; [exact Hr20'|]. split; [exact HFT'|].
      split; [exact HLK'|]. split; [exact HFC'|]. split; [exact Hr22'|]. split; [exact HFSj'|].
      split; [exact HREC'|]. split; [exact HFPS'|]. split; [exact Ha0' | exact Hge].
Qed.

End S.
