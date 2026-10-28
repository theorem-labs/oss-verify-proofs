(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
Ltac mem_after_store_keep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB;
          first [ let sz := eval cbv beta iota delta [cells_size csize Nat.add] in (cells_size cs) in
                  mas_is_nat_lit sz; change (cells_size cs) with sz in HB
                | cbn [cells_size csize Nat.add] in HB ];
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear HB; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Local Ltac mem_after_store_opt ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store_keep
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store_keep
  | _ => idtac
  end.

Section Ret.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Variables (sp ra0 s0v s1v s2v s3v s4v s5v s6v s7v : word).
  (* [comment removed for export] *)
  Variables (q0 q1 q2 q3 q4 : word).
  (* [comment removed for export] *)
  Variables (x1 gp tp x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U MP size : Z) (T : list Z) (rest : list word) (jk : list byte) (pjunk : word).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2544 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis UR : 1 <= U < 2^64. Hypothesis UA : U mod 64 = 0.
  Hypothesis MPR : 0 <= MP /\ MP + 8 <= 2^64 /\ (MP + 8 <= lo \/ bv_unsigned sp <= MP).
  Hypothesis PW  : rw_cells asegs m MP [C8 pjunk].
  Hypothesis ST  : stk asegs m lo (bv_unsigned sp + -2192).
  Hypothesis FR  : rw_cells asegs m (bv_unsigned sp + -2192) [C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 (wz 0x1bfc0c)].
  Hypothesis ESO : rw_cells asegs m (bv_unsigned sp + -2144) [C8 (wz (bv_unsigned sp + -2144 + 16)); C8 (wz (Z.of_nat (length T)))].
  Hypothesis TRB : u64arr asegs m (bv_unsigned sp + -2144 + 16) (map wz T ++ rest).
  Hypothesis LR  : length rest = (255 - length T)%nat.
  Hypothesis NR  : (1 <= length T <= 30)%nat.
  Hypothesis TFB : rw_cells asegs m (bv_unsigned sp + -88) [C8 sp].
  Hypothesis F4  : rw_cells asegs m (bv_unsigned sp + -80) [CB 8 jk; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].

  Definition memalign_ret_post : machine_state -> Prop := fun ms' => exists m',
    ms' = MS (mkR ra0 sp gp tp x5 x6 x7 s0v s1v (wz 0) (wz U) x12 x13 x14 x15 x16 x17 s2v s3v s4v s5v s6v s7v x24 x25 x26 x27 x28 x29 x30 x31)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(MP, MP + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' MP [C8 (wz U)]
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ stk asegs m lo (bv_unsigned sp)      (* [comment removed for export] *)
    /\ m' = write_to_mem m (wa MP) (le8 (wz U)).   (* [comment removed for export] *)

  Theorem memalign_ret :
    evt asegs memalign_ret_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 (wz MP) x9 (wz U) x11 x12 x13 x14 x15 x16 x17 x18 (wz 63) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x197ac4) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (munch_refl [(MP, MP + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    acb. unfold wz in *.
    (* [comment removed for export] *)
    assert (STK0h : hidden (stk asegs m lo (bv_unsigned sp))).
    { constructor.
      pose proof (stk_of_rw_cells asegs _ _ _ FR) as K1. pose proof (stk_of_rw_cells asegs _ _ _ ESO) as K2.
      pose proof (stk_of_rw_cells asegs _ _ _ TFB) as K4. pose proof (stk_of_rw_cells asegs _ _ _ F4) as K5.
      pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB))) as K3.
      cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5.
      rewrite u64s_length, length_app, length_map, LR in K3.
      eapply stk_merge; [exact ST| |lia]. eapply stk_merge; [exact K1| |lia].
      replace (bv_unsigned sp + -2192 + Z.of_nat 48) with (bv_unsigned sp + -2144) by lia.
      eapply stk_merge; [exact K2| |lia]. replace (bv_unsigned sp + -2144 + Z.of_nat 16) with (bv_unsigned sp + -2144 + 16) by lia.
      eapply stk_merge; [exact K3| |lia].
      replace (bv_unsigned sp + -2144 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -88) by lia.
      eapply stk_merge; [exact K4| |lia]. replace (bv_unsigned sp + -88 + Z.of_nat 8) with (bv_unsigned sp + -80) by lia.
      replace (bv_unsigned sp) with (bv_unsigned sp + -80 + Z.of_nat 80) at 2 by lia. exact K5. }
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    { exfalso. clear - K UR; try acb. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    step. step. rewrite (unsigned_lit U) by (clear - UR; lia). change 63 with (Z.ones 6). rewrite Z.land_comm, Z.land_ones by (clear; lia). change (2^6) with 64.
    rewrite UA.
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. do 9 step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [| split; [destruct STK0h as [STK0]; exact STK0| rewrite Heqm; unfold wz; f_equal; f_equal; clear; lia]].
    (* [comment removed for export] *)
    lazymatch goal with FR' : rw_cells asegs ?mm (bv_unsigned sp + -2192) _, ESO' : rw_cells asegs _ (bv_unsigned sp + -2144) _,
                         TFB' : rw_cells asegs _ (bv_unsigned sp + -88) _, F4' : rw_cells asegs _ (bv_unsigned sp + -80) _,
                         TRB' : u64arr asegs _ (bv_unsigned sp + -2144 + 16) _, ST0 : stk asegs _ lo (bv_unsigned sp + -2192) |- _ =>
      pose proof (stk_of_rw_cells asegs _ _ _ FR') as K1; pose proof (stk_of_rw_cells asegs _ _ _ ESO') as K2;
      pose proof (stk_of_rw_cells asegs _ _ _ TFB') as K4; pose proof (stk_of_rw_cells asegs _ _ _ F4') as K5;
      pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB'))) as K3;
      cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5;
      rewrite u64s_length, length_app, length_map, LR in K3;
      eapply stk_merge; [exact ST0| |lia]; eapply stk_merge; [exact K1| |lia] end.
    replace (bv_unsigned sp + -2192 + Z.of_nat 48) with (bv_unsigned sp + -2144) by lia.
    eapply stk_merge; [eassumption| |lia]. replace (bv_unsigned sp + -2144 + Z.of_nat 16) with (bv_unsigned sp + -2144 + 16) by lia.
    eapply stk_merge; [eassumption| |lia].
    replace (bv_unsigned sp + -2144 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -88) by lia.
    eapply stk_merge; [eassumption| |lia]. replace (bv_unsigned sp + -88 + Z.of_nat 8) with (bv_unsigned sp + -80) by lia.
    replace (bv_unsigned sp) with (bv_unsigned sp + -80 + Z.of_nat 80) at 2 by lia. assumption.
  Qed.
End Ret.
