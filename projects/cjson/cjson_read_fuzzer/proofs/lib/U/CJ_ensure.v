(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_utraps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaSplit.
Local Ltac lia ::= lia_cj.
Local Ltac flia ::= flia_cj.
Local Ltac simpl_sizes ::= simpl_sizes_cj.
Local Ltac simpl_arr_sizes ::= simpl_arr_sizes_cj.


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.

Ltac shpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc | |- ?g => idtac "GOAL" g end.
Ltac shh H := let T := type of H in idtac H ":" T.
Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, ENSURE_STACK in *; lia.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section PVA.
  Variable HI : cj_heap_iface.

  (* [comment removed for export] *)
  Lemma pv_agree_stack : forall SPB LBX m mo LR SP PB lo' hi' m1 m2,
    LHEAP HI SPB LBX m mo -> (forall b, In b LR -> In b LBX) ->
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> alloc_ceiling <= lo' -> hi' <= SP ->
    pv_agree LR SP PB m1 m2.
  Proof.
    intros SPB LBX m mo LR SP PB lo' hi' m1 m2 HL HLR MU WM Hlo Hhi. try rewrite alloc_ceiling_eq in Hlo.
    eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [Hc _]. cbn. split; [|exact I].
    destruct Hc as [Hs|[[Hd _]|(A' & n' & Hin & Hr)]].
    - lia.
    - unfold PDATA_LO, PIMG_HI in Hd. lia.
    - pose proof (lh_block_range HI _ _ _ _ _ _ HL (HLR _ Hin)) as (_ & _ & _ & R4 & _). try rewrite alloc_ceiling_eq in R4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pv_agree_hole : forall LR SP PB lo' hi' m1 m2,
    munch [(lo', hi')] m1 m2 -> wmono usegs m1 m2 -> PB <= lo' -> hi' <= PB + 64 ->
    pv_agree LR SP PB m1 m2.
  Proof.
    intros LR SP PB lo' hi' m1 m2 MU WM Hlo Hhi.
    eapply magree_of_munch; [exact MU| exact WM|]. intros a Ha [_ Hn]. cbn. split; [lia|exact I].
  Qed.

  (* [comment removed for export] *)
  Lemma pv_agree_alloc : forall L LR SP SP' PB m1 m2,
    cj_pres L SP' m1 m2 -> SP' <= SP -> (forall b, In b LR -> In b L) -> pv_agree LR SP PB m1 m2.
  Proof.
    intros L LR SP SP' PB m1 m2 H HS HL. apply pv_agree_of_cj_pres. eapply cj_pres_weaken; eauto.
  Qed.
End PVA.

Section S.
  Variable HI : cj_heap_iface.

  Section Call.
    (* [comment removed for export] *)
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
              (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
              (SPB : Z) (LB LR : list cblock) (PB buf len off dep : Z) (fw : word) (bs : list byte) (needed lo : Z) (errv : word).
    Hypothesis HP : Permutation ((buf, len) :: LR) LB.
    Hypothesis PN : pb_nums len off dep.
    Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - ENSURE_STACK.
    Hypothesis TP : tp = wz PTP.
    Hypothesis ND : 0 <= needed < 2^64.
    Hypothesis LEN : Z.of_nat (length bs) = len.
    (* [comment removed for export] *)
    Hypothesis R1 : 0 < buf.
    Hypothesis R4 : buf + len <= alloc_ceiling.
    Hypothesis SPhi : bv_unsigned sp <= 2^64.

    Notation POST := (ensure_post HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPB LR PB buf len off dep fw bs needed lo m).
    Notation SP1 := (bv_unsigned sp + -32).
    Notation FRAME mm := (rw_cells usegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    Notation PBS mm b l := (rw_cells usegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 dep);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 91236); C8 (Z_to_bv 64 90916); C8 (Z_to_bv 64 97488)]).

    Lemma SP1eq : bv_unsigned (Z_to_bv 64 SP1) = SP1.
    Proof. apply unsigned_lit. try rewrite alloc_ceiling_eq in CEIL. unfold ENSURE_STACK, RMALLOC_STACK in LO. lia. Qed.

    Lemma PBS_fold : forall mm b l, PBS mm b l -> pb_struct mm PB b l off dep fw.
    Proof. intros mm b l H. exact H. Qed.

    (* [comment removed for export] *)
    Lemma epi : forall (mm : word -> option byte) (mo' : Model) (LB' : list cblock) (errv' : word)
                       (x1 x5 x6 x7 x8 x9 x10 x11 r x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      LHEAP HI SPB LB' mm mo' ->
      FRAME mm -> stk usegs mm lo SP1 -> mem_inv usegs mm -> rw_cells usegs mm PERRNO [C4 errv'] ->
      pv_agree LR (bv_unsigned sp) PB m mm ->
      ( (r = Z_to_bv 64 0 /\ Permutation LR LB' /\ pb_struct mm PB 0 0 off dep fw)
        \/ (r = Z_to_bv 64 0 /\ Permutation ((buf, len) :: LR) LB' /\ pb_struct mm PB buf len off dep fw /\ pb_data mm buf len bs)
        \/ (exists buf' len' bs', r = Z_to_bv 64 (buf' + off) /\ Permutation ((buf', len') :: LR) LB'
              /\ pb_struct mm PB buf' len' off dep fw /\ pb_data mm buf' len' bs'
              /\ needed + off + 1 <= len' /\ len' < 2^31) ) ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 x8 x9 x10 x11 r x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x155dc) fc None mm (seg_rom usegs)) mo'.
    Proof.
      intros until x31. intros HL' FR ST' MI' ERR' PVA OUT.
      try rewrite alloc_ceiling_eq in CEIL. unfold ENSURE_STACK, RMALLOC_STACK in LO.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL'|].
      step. step. step. step. step. step. step.
      release_frame FR ST' (bv_unsigned sp).
      apply evt_done. apply scps_done. unfold ensure_post.
      do 18 eexists. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact PVA|]. split; [exact HL'|].
      unfold wz. exact OUT.
    Qed.

    (* [comment removed for export] *)
    Lemma u8arr_of_two_CB : forall mm A n1 b1 n2 b2,
      rw_cells usegs mm A [CB n1 b1; CB n2 b2] -> u8arr usegs mm A (b1 ++ b2) /\ length b1 = n1 /\ length b2 = n2.
    Proof.
      intros mm A n1 b1 n2 b2 H.
      pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
      pose proof (rw_cells_merge usegs mm A [] [CB n1 b1; CB n2 b2] [] ltac:(rewrite app_nil_r; exact H)) as M.
      cbn [app cells_size cells_bytes csize cbytes] in M. rewrite app_nil_r, Nat.add_0_r in M.
      split; [| split; [exact L1| exact L2]]. eapply u8arr_of_rw_cells. exact M.
    Qed.

    (* [comment removed for export] *)
    Lemma grow : forall (m1 : word -> option byte) (mo : Model) (ns : Z) (x1 x5 x6 x7 x9 x11 x12 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      LHEAP HI SPB LB m1 mo -> PBS m1 buf len -> u8arr usegs m1 buf bs ->
      FRAME m1 -> stk usegs m1 lo SP1 -> rw_cells usegs m1 PERRNO [C4 errv] -> mem_inv usegs m1 ->
      pv_agree LR (bv_unsigned sp) PB m m1 ->
      needed + off + 1 <= ns < 2^31 -> len < needed + off + 1 ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 (Z_to_bv 64 ns) x9 (Z_to_bv 64 PB) x11 x12 (Z_to_bv 64 buf) x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x15618) fc None m1 (seg_rom usegs)) mo.
    Proof.
      intros until x31. intros HL PBS1 ARR FR ST1 ERR MI1 PVA NS NR.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold ENSURE_STACK, RMALLOC_STACK in LO. pose proof SP1eq as E1.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      destruct PL as (PL1 & PL2 & PL3 & PL4). destruct PN as (PN1 & PN2 & PN3). unfold PERRNO in ERR.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. step. if_cases Kd; zify_cond Kd; [exfalso; lia|]. clear Kd.
      step. step. step. step.
      replace (ret_pc (Z_to_bv 64 97488)) with (wz PREALLOC) by (unfold wz, PREALLOC; symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply evt_done. cbv beta.
      eapply scps_bind.
      { eapply (lh_realloc HI) with (lo := lo) (A := buf) (k := len) (n := ns) (old := bs); rewrite ?E1;
          first [ exact HL | eapply perm_in_head; exact HP | exact (proj1 ARR) | exact ST1 | exact ERR | exact MI1 | exact TP | reflexivity | slv | lia ]. }
      cbv beta. intros ms2 mo2 PO.
      destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2
                      & -> & MI2 & ST2 & ERR2 & RES).
      rewrite E1 in ST2. unfold PERRNO in ERR2.
      replace (ret_pc (Z_to_bv 64 0x15630)) with (Z_to_bv 64 0x15630) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct RES as [(-> & HL2 & PR2) | (B & junk & -> & CR & HB & HL2 & PR2 & BLK)].
      - (* [comment removed for export] *)
        rewrite E1 in PR2. unfold wz.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS1; [| left; lia].
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
        clear PVA PR2 MI1 ST1 ERR HL ARR.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; first [exfalso; apply K0; reflexivity | idtac]. clear K0.
        step. step. step. step.
        replace (ret_pc (Z_to_bv 64 90916)) with (wz PFREE) by (unfold wz, PFREE; symmetry; apply ret_pc_even; [lia| reflexivity]).
        apply evt_done. cbv beta.
        eapply scps_bind.
        { eapply (lh_free HI) with (lo := lo) (A := buf) (n := len); rewrite ?E1;
            first [ exact HL2 | eapply perm_in_head; exact HP | exact ST2 | exact ERR2 | exact MI2 | exact TP | reflexivity | slv | lia ]. }
        cbv beta. intros ms3 mo3 PO.
        destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3
                        & -> & MI3 & ST3 & ERR3 & PR3 & HL3).
        rewrite E1 in ST3, PR3. unfold PERRNO in ERR3.
        replace (ret_pc (Z_to_bv 64 0x15698)) with (Z_to_bv 64 0x15698) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL2)) as HP3.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR3) in PBS1; [| left; lia].
        assert (PVA3 : pv_agree LR (bv_unsigned sp) PB m m3).
        { eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_alloc; [exact PR3| lia|].
          intros b Hb. eapply Permutation_in; [exact HP3| exact Hb]. }
        clear PVA2 PR3 MI2 ST2 ERR2 HL2.
        pose proof (munch_refl [(PB, PB + 16)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL3|].
        step. step. fix_lit_store. step. fix_lit_store. step.
        apply evt_done. cbv beta.
        lazymatch goal with |- SCPS _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m4 end.
        eapply epi; [ | exact FR | exact ST3 | exact MI3 | exact ERR3 | | left].
        + eapply (lh_frame HI); [exact HL3| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia.
        + eapply pv_agree_trans; [exact PVA3|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia].
        + split; [reflexivity|]. split; [exact HP3|]. exact PBS1.
      - (* [comment removed for export] *)
        rewrite E1 in PR2. unfold wz.
        destruct CR as (CR1 & CR2 & CR3 & CR4 & CR5). try rewrite alloc_ceiling_eq in CR4. unfold PIMG_LO, PIMG_HI in CR5.
        pose proof (perm_cb_remove _ _ _ _ HP (lh_nodup HI _ _ _ _ HL)) as HPr.
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in FR; [| left; lia].
        apply (cj_pres_rw_cells _ _ _ _ _ _ PR2) in PBS1; [| left; lia].
        assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
        { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_alloc; [exact PR2| lia|].
          intros b Hb. eapply Permutation_in; [exact HPr| exact Hb]. }
        clear PVA PR2 MI1 ST1 ERR HL ARR.
        rewrite (Z.min_l len ns) in BLK by lia.
        pose proof (munch_refl [(PB, PB + 16)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
        eapply scps_step_evt; [eapply (lh_mok HI); exact HL2|].
        step. if_cases K0; zify_cond K0; first [exfalso; lia | idtac]. clear K0.
        step. zstep. rewrite zb_lxor_ones by lia. step. step.
        (* [comment removed for export] *)
        step. if_cases Kw; zify_cond Kw; first [exfalso; lia | idtac]. clear Kw.
        zstep. step.
        apply evt_done. cbv beta.
        destruct (u8arr_of_two_CB _ _ _ _ _ _ BLK) as (ARR2 & L1 & L2).
        eapply epi; [ | exact FR | exact ST2 | exact MI2 | exact ERR2 | | right; right].
        + eapply (lh_frame HI); [exact HL2| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia.
        + eapply pv_agree_trans; [exact PVA2|]. eapply pv_agree_hole; [exact MU| exact WM| lia| lia].
        + exists B, ns, (firstn (Z.to_nat len) bs ++ junk). split; [reflexivity|]. split.
          { eapply Permutation_trans; [| apply Permutation_refl]. apply perm_skip. exact HPr. }
          split; [exact PBS1|]. split; [| lia]. split; [exact ARR2|]. rewrite length_app, L1, L2. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma body : forall (m1 : word -> option byte) (mo : Model) (x1 x5 x6 x7 x8 x9 x12 x15 x16 x17 x18 x28 x29 x30 x31 : word),
      LHEAP HI SPB LB m1 mo -> PBS m1 buf len -> u8arr usegs m1 buf bs ->
      FRAME m1 -> stk usegs m1 lo SP1 -> rw_cells usegs m1 PERRNO [C4 errv] -> mem_inv usegs m1 ->
      pv_agree LR (bv_unsigned sp) PB m m1 ->
      needed < 2^31 ->
      SCPS usegs POST
        (MS (mkR x1 (Z_to_bv 64 SP1) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 PB) (Z_to_bv 64 needed) x12 (Z_to_bv 64 buf) (Z_to_bv 64 len) x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x155b0) fc None m1 (seg_rom usegs)) mo.
    Proof.
      intros until x31. intros HL PBS0 ARR FR ST ERR MI PVA1 N31.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold ENSURE_STACK, RMALLOC_STACK in LO.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      destruct PL as (PL1 & PL2 & PL3 & PL4). destruct PN as (PN1 & PN2 & PN3). unfold PERRNO in ERR.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      step. zstep. zstep. zstep. if_cases Kroom; zify_cond Kroom.
      - (* [comment removed for export] *)
        zstep. rewrite zb_lxor_ones by lia. step. if_cases Kw; zify_cond Kw; first [exfalso; lia | idtac]. clear Kw.
        zstep. apply evt_done. cbv beta.
        eapply epi; [exact HL| exact FR| exact ST| exact MI| exact ERR| exact PVA1| right; right].
        exists buf, len, bs. split; [reflexivity|]. split; [exact HP|]. split; [exact PBS0|]. split; [split; [exact ARR| exact LEN]|]. lia.
      - step. step. if_cases Kna; zify_cond Kna; first [exfalso; apply Kna; reflexivity | idtac]. clear Kna.
        zstep. step. if_cases K30; zify_cond K30.
        + (* [comment removed for export] *)
          zstep. apply evt_done. cbv beta.
          eapply grow; [exact HL| exact PBS0| exact ARR| exact FR| exact ST| exact ERR| exact MI| exact PVA1| | lia].
          rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 in K30 by lia. lia.
        + zstep. step. if_cases K31; zify_cond K31.
          * (* [comment removed for export] *)
            step. step. apply evt_done. cbv beta.
            eapply epi; [exact HL| exact FR| exact ST| exact MI| exact ERR| exact PVA1| right; left].
            split; [reflexivity|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR| exact LEN].
          * step. step. step. apply evt_done. cbv beta.
            eapply grow; [exact HL| exact PBS0| exact ARR| exact FR| exact ST| exact ERR| exact MI| exact PVA1| | lia].
            rewrite Z.shiftr_div_pow2 in K31 by lia. lia.
    Qed.

    Lemma entry : forall (mo : Model) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      LHEAP HI SPB LB m mo -> PBS m buf len -> u8arr usegs m buf bs ->
      stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m PERRNO [C4 errv] -> mem_inv usegs m ->
      SCPS usegs POST
        (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 PB) (Z_to_bv 64 needed) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x15564) fc None m (seg_rom usegs)) mo.
    Proof.
      intros until x31. intros HL PBS0 ARR ST ERR MI.
      pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL. unfold ENSURE_STACK, RMALLOC_STACK in LO.
      pose proof R4 as R4'. try rewrite alloc_ceiling_eq in R4'.
      pose proof PL as (PL1 & PL2 & PL3 & PL4). destruct PN as (PN1 & PN2 & PN3). unfold PERRNO in ERR.
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
      eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
      carve_frame 32%nat ST.
      step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      assert (HL1 : LHEAP HI SPB LB m1 mo).
      { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. lia. }
      assert (PVA1 : pv_agree LR (bv_unsigned sp) PB m m1).
      { eapply (pv_agree_stack HI); [exact HL| | exact MU| exact WM| slv| lia].
        intros b Hb. eapply Permutation_in; [exact HP| right; exact Hb]. }
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit PB), (align8_land7 PB PL4) by lia. step. if_false.
      step. step. if_cases K0; zify_cond K0; first [exfalso; lia | idtac]. clear K0.
      step. step. if_cases Klen; zify_cond Klen.
      - (* [comment removed for export] *) zstep. step. if_cases Kn; zify_cond Kn.
        + step. step. apply evt_done. cbv beta.
          eapply epi; [exact HL1| exact FR| exact ST| exact MI| exact ERR| exact PVA1| right; left].
          split; [reflexivity|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR| exact LEN].
        + apply evt_done. cbv beta.
          eapply body; [exact HL1| exact PBS0| exact ARR| exact FR| exact ST| exact ERR| exact MI| exact PVA1|].
          rewrite Z.shiftr_div_pow2 in Kn by lia. lia.
      - zstep. step. step. if_cases Kn; zify_cond Kn.
        + apply evt_done. cbv beta.
          eapply epi; [exact HL1| exact FR| exact ST| exact MI| exact ERR| exact PVA1| right; left].
          split; [reflexivity|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR| exact LEN].
        + step. step. if_cases Koff; zify_cond Koff.
          * apply evt_done. cbv beta.
            eapply body; [exact HL1| exact PBS0| exact ARR| exact FR| exact ST| exact ERR| exact MI| exact PVA1|].
            rewrite Z.shiftr_div_pow2 in Kn by lia. lia.
          * step. apply evt_done. cbv beta.
            eapply epi; [exact HL1| exact FR| exact ST| exact MI| exact ERR| exact PVA1| right; left].
            split; [reflexivity|]. split; [exact HP|]. split; [exact PBS0|]. split; [exact ARR| exact LEN].
    Qed.
  End Call.

  Theorem ensure_spec : ensure_stmt HI.
  Proof.
    unfold ensure_stmt. intros until errv. intros HL HP PS PD PN PL ST CEIL LO ERR MI TP A0 A1 ND.
    unfold ENSURE_ENTRY, wz in A0, A1. subst a0 a1. unfold wz, ENSURE_ENTRY.
    pose proof (lh_block_range HI _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as (R1 & _ & _ & R4 & _).
    pose proof ST as STc; destruct STc as (_ & SPhi & _).
    destruct PD as [ARR LEN].
    eapply entry; try eassumption.
  Qed.
End S.

(* [comment removed for export] *)


End CeilWrap.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
      change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
  | _ => idtac
  end.
Ltac shpc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc | |- ?g => idtac "GOAL" g end.
Ltac shh H := let T := type of H in idtac H ":" T.
Ltac slv := rewrite ?alloc_ceiling_eq in *; unfold RMALLOC_STACK, ENSURE_STACK in *; lia.
