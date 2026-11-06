(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_free A_F_free_spec A_MallocKit_AB A_MallocKit_A A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Arith MI_Inv MI_Kit MI_Read MI_Geom MI_Pres2 MI_Cnt MI_WFree MI_WGroup Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog ProgR A_Realloc A_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_free_spec RRealloc_iface RF_realloc_inpl RF_realloc_dec F_memcpy.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section ARM.
Hypothesis HMAL : rmalloc_impl_stmt.
Hypothesis HFREE : rfree_impl_stmt.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
    (s : PState) (LB LB0 : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbs : list byte)
    (st : mstate) (g bg : aptr) (idx : Z) (r : region) (off : Z).
Let c : cptr := fst p.
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let Bg := conc st bg.
Let E := Bg + 16 + stride * (idx + 1) - 4.
Let sp1 := bv_unsigned sp - 64.
Let POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m.

Hypotheses (PERM : Permutation LB0 LB) (Hst : strip st = ps_m s) (RMR : rmrep st m1) (HBL : brk_link st (ps_brk s))
    (AR : AREACH_from ref_reserved st LB0) (Hin0 : In (p, A, old) LB0)
    (SL : s_slots st !! c = Some (g, idx)) (HM : m_mem mr = Some bg) (Hr : s_regions st !! (fst bg) = Some r) (Kr : r_kind r = RKGroup)
    (FC : fst c = fst bg) (Ec : c = (fst bg, snd bg + UNIT + stride * idx)) (CB : Bg = r_base r + snd bg)
    (HA : A = conc st c + UNIT * off) (Hoff : 0 <= off <= 255) (FIT : UNIT * off + old <= stride - IB) (HO : 0 <= old)
    (S16 : UNIT <= stride) (SMOD : stride mod UNIT = 0) (B0 : 0 <= snd bg) (BG16 : snd bg mod UNIT = 0) (Hidx : 0 <= idx <= m_last_idx mr) (LI : m_last_idx mr <= 31)
    (SPAN : snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r)) (RCEIL : r_base r + round_up_pg (r_len r) <= alloc_ceiling) (RB0 : 0 <= r_base r)
    (SSTR : m_sizeclass mr < 48 -> stride < 2 ^ 20) (SC63 : 48 <= m_sizeclass mr -> m_sizeclass mr = 63)
    (K3 : known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5)).

Hypotheses (FR : rw_cells rsegs m1 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (ST1 : stk rsegs m1 lo sp1) (MI1 : mem_inv rsegs m1) (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv])
    (AUX1 : rauxv_ok m1 B) (PRES1 : rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1)
    (OLDB : bytes_at rsegs m A oldbs) (OLEN : Z.of_nat (length oldbs) = old)
    (SB : bv_unsigned sp <= B) (CLO : alloc_ceiling <= lo) (LO : lo <= bv_unsigned sp - RREALLOC_STACK)
    (TP : tp = Z_to_bv 64 RATP) (HN : 0 <= n < 2^48) (EFA : True).

Lemma move_arm : forall (rax t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29 y30 y31 : word),
  implM rsegs (realloc_move p n) s POST
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 A) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
               (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x49d98) fc None m1 (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil. pose proof LO as LOv'.
  assert (ETP : bv_unsigned tp + -164 = 422892) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (SP1 : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; subst sp1; lia).
  assert (HEAP1 : RHEAP s LB m1) by (exists st, LB0; split; [exact PERM|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]).
  assert (HinL : In (p, A, old) LB) by (eapply Permutation_in; [exact PERM| exact Hin0]).
  pose proof (RHEAP_block_range_proof s LB m1 _ HEAP1 HinL) as BRp. cbn [blk_addr blk_size fst snd] in BRp. destruct BRp as (A0 & A16 & _ & ACE & AIMG).
  pose_ceil.
  assert (SK0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SK1 : stride * (idx + 1) = stride * idx + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  rewrite SK1 in SPAN. pose proof (round_up_pg_ge (r_len r)) as RUP.
  assert (OLDhi : old < 2 ^ 48) by (unfold UNIT, IB in *; lia).
  unfold realloc_move.

  eapply implM_bind.
  { eapply implM_evt.
    { step. step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
    cbv beta. intros ms' ->.
    pose proof HMAL as X. unfold rmalloc_impl_stmt, rmalloc_entry in X.
    eapply X with (lo := lo) (B := B) (errv := errv); clear X;
      [exact HEAP1| exact AUX1| rewrite SP1; subst sp1; lia| rewrite SP1; exact ST1| exact CLO| rewrite SP1; subst sp1; unfold RMALLOC_STACK; lia
      | exact ERR1| exact MI1| exact TP| reflexivity| exact HN]. }
  cbv beta. intros r1 s' ms' PO.
  destruct PO as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & AUXC2 & PRES2 & EFA2 & ESO2 & RR).
  rewrite SP1 in ST2, PRES2.
  replace (ret_pc (Z_to_bv 64 0x49da8)) with (Z_to_bv 64 0x49da8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  assert (FR2 : rw_cells rsegs m2 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rheap_pres_rw_cells _ _ _ _ _ _ PRES2) in FR; [exact FR| left; cbn; lia]. }

  assert (PRES01 : rheap_pres LB (bv_unsigned sp) m m1).
  { intros a Ha HC. apply PRES1; [exact Ha|]. cbv beta. intros X.
    destruct HC as [Y|[[Y NS]|(b' & Hb' & Hab)]]; [unfold RERRNO in X; clear - X Y CLOv LOv'; lia| unfold ralloc_static, RERRNO in *; clear - X Y NS CLOv; lia|].
    destruct (RHEAP_block_range_proof s LB m1 b' HEAP1 Hb') as (_ & _ & _ & BC' & BI'). pose_ceil. unfold RERRNO in X. clear - X Hab BC' BI' CLOv. lia. }
  assert (AUXC01 : rauxcell_pres m m1).
  { intros a Ha. apply (proj1 (PRES1 a ltac:(unfold RAUXV_CELL in Ha; lia) ltac:(cbv beta; unfold RAUXV_CELL, RLIBC, RERRNO in *; clear - Ha CLOv; lia))). }
  assert (PRES02 : rheap_pres LB (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [exact PRES01|]. eapply rheap_pres_weaken; [exact PRES2| subst sp1; clear; lia| auto]. }
  assert (AUXC02 : rauxcell_pres m m2) by (eapply rauxcell_pres_trans; [exact AUXC01| exact AUXC2]).
  destruct r1 as [p'|].
  2:{
      destruct RR as [-> HEAP2]. apply implM_ret.
      step. if_true. do 10 step.
      replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; lia); subst sp1; lia).
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold POST, rrealloc_post. do 15 eexists. exists m2, errv2. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact AUXC02|].
      split; [eapply rheap_pres_weaken; [exact PRES02| apply Z.le_refl| intros b' Hb'; unfold lb_remove in Hb'; apply In_filter_b in Hb' as [Hb' _]; exact Hb']|].
      split; [exact EFA2|]. split; [exact ESO2|]. split; [reflexivity|]. split; [exact HEAP2| exact PRES02]. }

  destruct RR as (A' & junk & -> & BR' & HEAP2 & BLK & _).
  pose proof BR' as (A'0 & A'16 & _ & A'CE & A'IMG). pose_ceil.
  assert (NEp : p' <> p).
  { pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI _].
    intros ->. apply NI. change p with (blk_id (p, A, old)). apply in_map. exact HinL. }
  pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p', A', n) (p, A, old) HEAP2 ltac:(left; reflexivity) ltac:(right; exact HinL) ltac:(cbn; exact NEp)) as DISJ.
  cbn [blk_addr blk_size fst snd] in DISJ.
  set (k := Z.min n old).
  assert (HK : 0 <= k <= n /\ k <= old) by (subst k; lia).

  assert (LK : length (firstn (Z.to_nat k) oldbs) = Z.to_nat k) by (rewrite length_firstn; lia).
  assert (OLDk : bytes_at rsegs m2 A (firstn (Z.to_nat k) oldbs)).
  { rewrite <- (firstn_skipn (Z.to_nat k) oldbs) in OLDB. apply bytes_at_app in OLDB as [X _].
    eapply rheap_pres_bytes_at; [exact PRES02| exact X|]. right. right. exists (p, A, old). split; [exact HinL|]. cbn [blk_addr blk_size fst snd]. rewrite LK. lia. }

  assert (DST : rw_cells rsegs m2 A' [Cells.CB (Z.to_nat k) (firstn (Z.to_nat k) junk)] /\ bytes_at rsegs m2 (A' + k) (skipn (Z.to_nat k) junk) /\ length junk = Z.to_nat n).
  { destruct BLK as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as [LJ _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. cbn [cells_size csize] in HW.
    rewrite <- (firstn_skipn (Z.to_nat k) junk) in HB. apply bytes_at_app in HB as [HB1 HB2]. rewrite length_firstn in HB2.
    replace (Z.of_nat (Z.to_nat k `min` length junk)) with k in HB2 by lia.
    split; [| split; [exact HB2| exact LJ]]. split; [split|].
    - cbn. split; [rewrite length_firstn; lia| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB1.
    - cbn [cells_size csize]. eapply wr_at_sub; [exact HW| lia| lia]. }
  destruct DST as (DST & TAILB & LJ).

  cbv iota.
  eapply (implM_evt rsegs _ _ _ (fun ms1 => exists kk, kk = k /\
     ms1 = MS (mkR (Z_to_bv 64 0x49da8) (Z_to_bv 64 sp1) gp tp w0 w1 w2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 A') (Z_to_bv 64 old) (Z_to_bv 64 kk)
                   w6 w7 w8 w9 w10 (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 w11 w12 w13 w14)
              F (Z_to_bv 64 0x49dbc) fc None m2 (seg_rom rsegs))).
  { step. if_cases K0; zify_cond K0. { exfalso. clear - K0 A'0. lia. } clear K0.
    step. rewrite (unsigned_lit A) by lia. replace (A + old + - A) with old by lia. step.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - apply evt_done. exists n. split; [subst k; lia| reflexivity].
    - step. apply evt_done. exists old. split; [subst k; lia| reflexivity]. }
  cbv beta. intros ms1 (kk & -> & ->).
  set (src := firstn (Z.to_nat k) oldbs) in *.

  eapply (implM_bind rsegs _ _ _ (fun u s'' ms'' => exists m3 : mem, rpres_except (fun a => A' <= a < A' + k) m2 m3 /\ rw_cells rsegs m3 A' [Cells.CB (Z.to_nat k) src]
       /\ rfree_post (Z_to_bv 64 0x49dd0) (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 F fc
             s' ((p', A', n) :: LB) p lo B errv2 m3 u s'' ms'')).
  { eapply (implM_evt rsegs _ _ _ (fun ms2 => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m3 : mem),
       munch [(A', A' + k)] m2 m3 /\ wmono rsegs m2 m3 /\ mem_inv rsegs m3 /\ rw_cells rsegs m3 A' [Cells.CB (Z.to_nat k) src]
       /\ ms2 = MS (mkR (Z_to_bv 64 0x49dd0) (Z_to_bv 64 sp1) gp tp x5 x6 x7 (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 rfree_entry) fc None m3 (seg_rom rsegs))).
    {
      step. step. step.
      eapply evt_cut.
      { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 k)).
        - rewrite (unsigned_lit A) by lia. exact OLDk.
        - rewrite (unsigned_lit k) by lia. exact LK.
        - rewrite (unsigned_lit A'), (unsigned_lit k) by lia. exact DST.
        - rewrite (unsigned_lit A), (unsigned_lit A'), (unsigned_lit k) by lia. clear - DISJ HK. lia.
        - exact MI2. }
      cbv beta. intros ms2 (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
      assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - A0 ACE HO; lia).
      assert (UA' : bv_unsigned (Z_to_bv 64 A') = A') by (apply unsigned_lit; clear - A'0 A'CE HN; lia).
      assert (UK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; clear - HK HN; lia).
      rewrite UA', UK in MU3. rewrite UA', UK in DST3. rewrite UA in SRC3. clear UA UA' UK.
      replace (ret_pc (Z_to_bv 64 0x49dc8)) with (Z_to_bv 64 0x49dc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      step. step. apply evt_done. do 14 eexists. exists m3. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact DST3|].
      unfold rfree_entry. reflexivity. }
    cbv beta. intros ms2 (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & MU3 & WM3 & MI3 & DST3 & ->).
    assert (PE23 : rpres_except (fun a => A' <= a < A' + k) m2 m3).
    { eapply rpres_except_of_munch'; [exact MU3| exact WM3|]. intros lo' hi' [EI|[]] x Hx. inversion EI; subst lo' hi'. exact Hx. }
    assert (HEAP3 : RHEAP s' ((p', A', n) :: LB) m3).
    { eapply RHEAP_frame_proof; [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right. right.
      exists (p', A', n). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. clear - HK. lia. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [| constructor]. cbn [fst snd].
      destruct AUX2 as (av & q3 & q4 & q5 & q16 & q6 & q11 & q12 & q23 & rnd & _ & _ & _ & CB' & _). unfold RAUXV_CELL, RLIBC. pose_ceil. clear - CB' A'CE A'IMG HK HN. lia. }
    assert (ST3 : stk rsegs m3 lo sp1) by (eapply rpres_except_stk; [exact PE23| exact ST2| cbv beta; intros; subst sp1; clear - H A'CE CLOv LO; lia]).
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 errv2]).
    { eapply rpres_except_rw_cells; [exact PE23| exact ERR2|]. rewrite ETP. cbn [cells_size csize Z.of_nat Nat.add Pos.of_succ_nat]. cbv beta. intros a Ha. clear - Ha A'IMG HK HN. lia. }
    pose proof HFREE as X. unfold rfree_impl_stmt in X.
    eapply implM_mono.
    { eapply X with (lo := lo) (B := B); clear X;
      [exact HEAP3| right; exact HinL| exact AUX3| rewrite SP1; subst sp1; lia| rewrite SP1; exact ST3| exact CLO
      | rewrite SP1; subst sp1; unfold RFREE_STACK; lia| exact ERR3| exact MI3| exact TP| reflexivity]. }
    cbv beta. intros u s'' ms'' PF. exists m3. split; [exact PE23|]. split; [exact DST3| exact PF]. }
  cbv beta. intros u s'' ms'' (m3 & PE23 & DST3 & PF).
  destruct PF as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & AUXC34 & PRES34 & EFA4 & ESO4 & HEAP4).
  rewrite SP1 in ST4, PRES34.
  replace (ret_pc (Z_to_bv 64 0x49dd0)) with (Z_to_bv 64 0x49dd0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR3 : rw_cells rsegs m3 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE23| exact FR2|]. cbn [cells_size csize Z.of_nat Nat.add Pos.of_succ_nat]. cbv beta. intros a Ha. subst sp1. clear - Ha A'CE CLOv LO HK. lia. }
  assert (FR4 : rw_cells rsegs m4 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rheap_pres_rw_cells _ _ _ _ _ _ PRES34) in FR3; [exact FR3| left; lia]. }
  apply implM_ret.

  step. step. do 10 step.
  replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; lia); subst sp1; lia).
  release_frame FR4 ST4 (bv_unsigned sp).

  assert (ELB : lb_remove p ((p', A', n) :: LB) = (p', A', n) :: lb_remove p LB).
  { assert (Hb : bptr_eqb p' p = false).
    { unfold bptr_eqb. destruct (aptr_eqb_spec (fst p') (fst p)) as [E1|NE1]; [| reflexivity].
      destruct (Z.eqb_spec (snd p') (snd p)) as [E2|NE2]; [| reflexivity]. exfalso. apply NEp. destruct p', p; cbn in E1, E2; congruence. }
    unfold lb_remove. rewrite filter_cons_True; [reflexivity|]. unfold blk_id. cbn [fst]. rewrite Hb. exact I. }
  rewrite ELB in PRES34, HEAP4.

  assert (NC23 : forall a, rclient_addr (lb_remove p LB) (bv_unsigned sp) a -> ~ (A' <= a < A' + k)).
  { intros a [X|[[X NS]|(b' & Hb' & Hab)]] Y; [clear - X Y A'CE CLOv LO HK SPR; lia| clear - X Y A'IMG HK HN; lia|].
    unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' NEQ].
    assert (NEb : blk_id (p', A', n) <> blk_id b').
    { cbn [blk_id fst]. intros E1. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map blk_id fst] in ND.
      apply List.NoDup_cons_iff in ND as [NI _]. apply NI. rewrite E1. apply in_map. exact Hb'. }
    pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p', A', n) b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb') NEb) as D.
    cbn [blk_addr blk_size fst snd] in D. clear - D Hab Y HK. lia. }
  assert (PRES03 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m3).
  { eapply rheap_pres_trans.
    - eapply rheap_pres_weaken; [exact PRES02| apply Z.le_refl| intros b' Hb'; unfold lb_remove in Hb'; apply In_filter_b in Hb' as [Hb' _]; exact Hb'].
    - intros a Ha HC. apply PE23; [exact Ha| exact (NC23 a HC)]. }
  assert (PRES04 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m4).
  { eapply rheap_pres_trans; [exact PRES03|]. eapply rheap_pres_weaken; [exact PRES34| subst sp1; clear; lia| intros b' Hb'; right; exact Hb']. }
  assert (AUXC04 : rauxcell_pres m m4).
  { eapply rauxcell_pres_trans; [exact AUXC02|]. eapply rauxcell_pres_trans; [| exact AUXC34].
    intros a Ha. unfold RAUXV_CELL, RLIBC in Ha. apply (proj1 (PE23 a ltac:(clear - Ha; lia) ltac:(cbv beta; clear - Ha A'IMG HK HN; lia))). }

  assert (TAIL3 : bytes_at rsegs m3 (A' + k) (skipn (Z.to_nat k) junk)).
  { eapply rpres_except_bytes_at; [exact PE23| exact TAILB| cbv beta; intros a Ha; clear - Ha; lia]. }
  assert (BLK3 : rw_cells rsegs m3 A' [Cells.CB (Z.to_nat n) (src ++ skipn (Z.to_nat k) junk)]).
  { destruct DST3 as [[_ HB3] HW3]. cbn [cells_bytes cbytes] in HB3. rewrite app_nil_r in HB3.
    split; [split|].
    - cbn. split; [| exact I]. rewrite length_app, LK, length_skipn, LJ. clear - HK. lia.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB3|]. rewrite LK, Z2Nat.id by lia. exact TAIL3.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. destruct BLK as [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r, Z2Nat.id in HW by lia.
      cbn [cells_size csize] in HW3. rewrite Nat.add_0_r, Z2Nat.id in HW3 by lia.
      assert (HWt : wr_at rsegs m3 (A' + k) (n - k)).
      { eapply rpres_except_wr_at; [exact PE23| eapply wr_at_sub; [exact HW| clear - HK; lia| clear - HK; lia]| cbv beta; intros a Ha; clear - Ha; lia]. }
      destruct HW3 as (W0 & W1 & W3). destruct HWt as (V0 & V1 & Vt). split; [exact W0|]. split; [clear - V1 HK; lia|].
      intros i Hi. destruct (Z.lt_ge_cases i k) as [LT|GE]; [apply W3; clear - Hi LT HK; lia|].
      replace (A' + i) with (A' + k + (i - k)) by lia. apply Vt. clear - Hi GE HK. lia. }
  assert (BLK4 : rw_cells rsegs m4 A' [Cells.CB (Z.to_nat n) (src ++ skipn (Z.to_nat k) junk)]).
  { eapply rheap_pres_rw_cells; [exact PRES34| exact BLK3|]. right. right. exists (p', A', n). split; [left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. clear; lia. }
  apply evt_done. unfold POST, rrealloc_post. do 15 eexists. exists m4, errv2. split; [reflexivity|].
  split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|]. split; [exact AUXC04|].
  split; [exact PRES04|]. split; [rewrite EFA4; exact EFA2|]. split; [rewrite ESO4; exact ESO2|].
  exists A', (skipn (Z.to_nat k) junk). split; [reflexivity|]. split; [exact BR'|]. split; [exact HEAP4|].
  replace (Z.to_nat (Z.min old n)) with (Z.to_nat k) by (subst k; clear; lia). exact BLK4.
Qed.

Lemma arm_ccM : conc st c = r_base r + snd c.
Proof. apply conc_region'. rewrite FC. exact Hr. Qed.

Lemma move_armB : forall (rax t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29 y30 y31 : word),
  move_cond A n E (m_sizeclass mr) ->
  implM rsegs (realloc_body p A n (ps_m s)) s POST
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 A) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
               (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x49d98) fc None m1 (seg_rom rsegs)).
Proof.
  intros. pose proof arm_ccM as CC. destruct H as [NI NR].
  assert (RC : realloc_case (strip st) (fst p) A n = RcMove).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). fold c. rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_end rg_g rg_idx rg_stride rg_start].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    assert (EE : conc st c + stride - IB - A = E - A).
    { subst E Bg. rewrite CB, Z.mul_add_distr_l, Z.mul_1_r, CC, Ec. cbn [snd]. unfold UNIT, IB. clear. lia. }
    rewrite EE.
    destruct (Z.leb_spec n (E - A)); destruct (Z.ltb_spec n MMAP_THRESHOLD); destruct (Z.leb_spec (m_sizeclass mr) (size_to_class n + 1)); cbn [andb];
      try (exfalso; apply NI; clear - H H0 H1; tauto).
    all: destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.leb_spec 48 (m_sizeclass mr)); cbn [andb]; try reflexivity; exfalso; first [apply NR; clear - H2 H3; tauto| clear - H0 H2; lia]. }
  unfold realloc_body. rewrite <- Hst, RC. apply move_arm.
Qed.
End ARM.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_free_spec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Kit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Cnt OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WGroup OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Realloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ProgR OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc2.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_A.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_free_spec.TwinB RRealloc_iface.TwinB RF_realloc_inpl.TwinB RF_realloc_dec.TwinB F_memcpy.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section ARM.
Hypothesis HMAL : rmalloc_impl_stmt.
Hypothesis HFREE : rfree_impl_stmt.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
    (s : PState) (LB LB0 : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbs : list byte)
    (st : mstate) (g bg : aptr) (idx : Z) (r : region) (off : Z).
Let c : cptr := fst p.
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let Bg := conc st bg.
Let E := Bg + 16 + stride * (idx + 1) - 4.
Let sp1 := bv_unsigned sp - 64.
Let POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m.

Hypotheses (PERM : Permutation LB0 LB) (Hst : strip st = ps_m s) (RMR : rmrep st m1) (HBL : brk_link st (ps_brk s))
    (AR : AREACH_from ref_reserved st LB0) (Hin0 : In (p, A, old) LB0)
    (SL : s_slots st !! c = Some (g, idx)) (HM : m_mem mr = Some bg) (Hr : s_regions st !! (fst bg) = Some r) (Kr : r_kind r = RKGroup)
    (FC : fst c = fst bg) (Ec : c = (fst bg, snd bg + UNIT + stride * idx)) (CB : Bg = r_base r + snd bg)
    (HA : A = conc st c + UNIT * off) (Hoff : 0 <= off <= 255) (FIT : UNIT * off + old <= stride - IB) (HO : 0 <= old)
    (S16 : UNIT <= stride) (SMOD : stride mod UNIT = 0) (B0 : 0 <= snd bg) (BG16 : snd bg mod UNIT = 0) (Hidx : 0 <= idx <= m_last_idx mr) (LI : m_last_idx mr <= 31)
    (SPAN : snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r)) (RCEIL : r_base r + round_up_pg (r_len r) <= alloc_ceiling) (RB0 : 0 <= r_base r)
    (SSTR : m_sizeclass mr < 48 -> stride < 2 ^ 20) (SC63 : 48 <= m_sizeclass mr -> m_sizeclass mr = 63)
    (K3 : known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5)).

Hypotheses (FR : rw_cells rsegs m1 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (ST1 : stk rsegs m1 lo sp1) (MI1 : mem_inv rsegs m1) (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv])
    (AUX1 : rauxv_ok m1 B) (PRES1 : rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1)
    (OLDB : bytes_at rsegs m A oldbs) (OLEN : Z.of_nat (length oldbs) = old)
    (SB : bv_unsigned sp <= B) (CLO : alloc_ceiling <= lo) (LO : lo <= bv_unsigned sp - RREALLOC_STACK)
    (TP : tp = Z_to_bv 64 RATP) (HN : 0 <= n < 2^48) (EFA : True).

Lemma move_arm : forall (rax t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29 y30 y31 : word),
  implM rsegs (realloc_move p n) s POST
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 A) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
               (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x4b59c) fc None m1 (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil. pose proof LO as LOv'.
  assert (ETP : bv_unsigned tp + -164 = 429036) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (SP1 : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; subst sp1; lia).
  assert (HEAP1 : RHEAP s LB m1) by (exists st, LB0; split; [exact PERM|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]).
  assert (HinL : In (p, A, old) LB) by (eapply Permutation_in; [exact PERM| exact Hin0]).
  pose proof (RHEAP_block_range_proof s LB m1 _ HEAP1 HinL) as BRp. cbn [blk_addr blk_size fst snd] in BRp. destruct BRp as (A0 & A16 & _ & ACE & AIMG).
  pose_ceil.
  assert (SK0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SK1 : stride * (idx + 1) = stride * idx + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  rewrite SK1 in SPAN. pose proof (round_up_pg_ge (r_len r)) as RUP.
  assert (OLDhi : old < 2 ^ 48) by (unfold UNIT, IB in *; lia).
  unfold realloc_move.

  eapply implM_bind.
  { eapply implM_evt.
    { step. step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
    cbv beta. intros ms' ->.
    pose proof HMAL as X. unfold rmalloc_impl_stmt, rmalloc_entry in X.
    eapply X with (lo := lo) (B := B) (errv := errv); clear X;
      [exact HEAP1| exact AUX1| rewrite SP1; subst sp1; lia| rewrite SP1; exact ST1| exact CLO| rewrite SP1; subst sp1; unfold RMALLOC_STACK; lia
      | exact ERR1| exact MI1| exact TP| reflexivity| exact HN]. }
  cbv beta. intros r1 s' ms' PO.
  destruct PO as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & AUXC2 & PRES2 & EFA2 & ESO2 & RR).
  rewrite SP1 in ST2, PRES2.
  replace (ret_pc (Z_to_bv 64 0x4b5ac)) with (Z_to_bv 64 0x4b5ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  assert (FR2 : rw_cells rsegs m2 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rheap_pres_rw_cells _ _ _ _ _ _ PRES2) in FR; [exact FR| left; cbn; lia]. }

  assert (PRES01 : rheap_pres LB (bv_unsigned sp) m m1).
  { intros a Ha HC. apply PRES1; [exact Ha|]. cbv beta. intros X.
    destruct HC as [Y|[[Y NS]|(b' & Hb' & Hab)]]; [unfold RERRNO in X; clear - X Y CLOv LOv'; lia| unfold ralloc_static, RERRNO in *; clear - X Y NS CLOv; lia|].
    destruct (RHEAP_block_range_proof s LB m1 b' HEAP1 Hb') as (_ & _ & _ & BC' & BI'). pose_ceil. unfold RERRNO in X. clear - X Hab BC' BI' CLOv. lia. }
  assert (AUXC01 : rauxcell_pres m m1).
  { intros a Ha. apply (proj1 (PRES1 a ltac:(unfold RAUXV_CELL in Ha; lia) ltac:(cbv beta; unfold RAUXV_CELL, RLIBC, RERRNO in *; clear - Ha CLOv; lia))). }
  assert (PRES02 : rheap_pres LB (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [exact PRES01|]. eapply rheap_pres_weaken; [exact PRES2| subst sp1; clear; lia| auto]. }
  assert (AUXC02 : rauxcell_pres m m2) by (eapply rauxcell_pres_trans; [exact AUXC01| exact AUXC2]).
  destruct r1 as [p'|].
  2:{
      destruct RR as [-> HEAP2]. apply implM_ret.
      step. if_true. do 10 step.
      replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; lia); subst sp1; lia).
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold POST, rrealloc_post. do 15 eexists. exists m2, errv2. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact AUXC02|].
      split; [eapply rheap_pres_weaken; [exact PRES02| apply Z.le_refl| intros b' Hb'; unfold lb_remove in Hb'; apply In_filter_b in Hb' as [Hb' _]; exact Hb']|].
      split; [exact EFA2|]. split; [exact ESO2|]. split; [reflexivity|]. split; [exact HEAP2| exact PRES02]. }

  destruct RR as (A' & junk & -> & BR' & HEAP2 & BLK & _).
  pose proof BR' as (A'0 & A'16 & _ & A'CE & A'IMG). pose_ceil.
  assert (NEp : p' <> p).
  { pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map blk_id fst] in ND. apply List.NoDup_cons_iff in ND as [NI _].
    intros ->. apply NI. change p with (blk_id (p, A, old)). apply in_map. exact HinL. }
  pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p', A', n) (p, A, old) HEAP2 ltac:(left; reflexivity) ltac:(right; exact HinL) ltac:(cbn; exact NEp)) as DISJ.
  cbn [blk_addr blk_size fst snd] in DISJ.
  set (k := Z.min n old).
  assert (HK : 0 <= k <= n /\ k <= old) by (subst k; lia).

  assert (LK : length (firstn (Z.to_nat k) oldbs) = Z.to_nat k) by (rewrite length_firstn; lia).
  assert (OLDk : bytes_at rsegs m2 A (firstn (Z.to_nat k) oldbs)).
  { rewrite <- (firstn_skipn (Z.to_nat k) oldbs) in OLDB. apply bytes_at_app in OLDB as [X _].
    eapply rheap_pres_bytes_at; [exact PRES02| exact X|]. right. right. exists (p, A, old). split; [exact HinL|]. cbn [blk_addr blk_size fst snd]. rewrite LK. lia. }

  assert (DST : rw_cells rsegs m2 A' [Cells.CB (Z.to_nat k) (firstn (Z.to_nat k) junk)] /\ bytes_at rsegs m2 (A' + k) (skipn (Z.to_nat k) junk) /\ length junk = Z.to_nat n).
  { destruct BLK as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as [LJ _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. cbn [cells_size csize] in HW.
    rewrite <- (firstn_skipn (Z.to_nat k) junk) in HB. apply bytes_at_app in HB as [HB1 HB2]. rewrite length_firstn in HB2.
    replace (Z.of_nat (Z.to_nat k `min` length junk)) with k in HB2 by lia.
    split; [| split; [exact HB2| exact LJ]]. split; [split|].
    - cbn. split; [rewrite length_firstn; lia| exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB1.
    - cbn [cells_size csize]. eapply wr_at_sub; [exact HW| lia| lia]. }
  destruct DST as (DST & TAILB & LJ).

  cbv iota.
  eapply (implM_evt rsegs _ _ _ (fun ms1 => exists kk, kk = k /\
     ms1 = MS (mkR (Z_to_bv 64 0x4b5ac) (Z_to_bv 64 sp1) gp tp w0 w1 w2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 A') (Z_to_bv 64 old) (Z_to_bv 64 kk)
                   w6 w7 w8 w9 w10 (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 w11 w12 w13 w14)
              F (Z_to_bv 64 0x4b5c0) fc None m2 (seg_rom rsegs))).
  { step. if_cases K0; zify_cond K0. { exfalso. clear - K0 A'0. lia. } clear K0.
    step. rewrite (unsigned_lit A) by lia. replace (A + old + - A) with old by lia. step.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - apply evt_done. exists n. split; [subst k; lia| reflexivity].
    - step. apply evt_done. exists old. split; [subst k; lia| reflexivity]. }
  cbv beta. intros ms1 (kk & -> & ->).
  set (src := firstn (Z.to_nat k) oldbs) in *.

  eapply (implM_bind rsegs _ _ _ (fun u s'' ms'' => exists m3 : mem, rpres_except (fun a => A' <= a < A' + k) m2 m3 /\ rw_cells rsegs m3 A' [Cells.CB (Z.to_nat k) src]
       /\ rfree_post (Z_to_bv 64 0x4b5d4) (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 F fc
             s' ((p', A', n) :: LB) p lo B errv2 m3 u s'' ms'')).
  { eapply (implM_evt rsegs _ _ _ (fun ms2 => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m3 : mem),
       munch [(A', A' + k)] m2 m3 /\ wmono rsegs m2 m3 /\ mem_inv rsegs m3 /\ rw_cells rsegs m3 A' [Cells.CB (Z.to_nat k) src]
       /\ ms2 = MS (mkR (Z_to_bv 64 0x4b5d4) (Z_to_bv 64 sp1) gp tp x5 x6 x7 (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 rfree_entry) fc None m3 (seg_rom rsegs))).
    {
      step. step. step.
      eapply evt_cut.
      { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 k)).
        - rewrite (unsigned_lit A) by lia. exact OLDk.
        - rewrite (unsigned_lit k) by lia. exact LK.
        - rewrite (unsigned_lit A'), (unsigned_lit k) by lia. exact DST.
        - rewrite (unsigned_lit A), (unsigned_lit A'), (unsigned_lit k) by lia. clear - DISJ HK. lia.
        - exact MI2. }
      cbv beta. intros ms2 (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
      assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - A0 ACE HO; lia).
      assert (UA' : bv_unsigned (Z_to_bv 64 A') = A') by (apply unsigned_lit; clear - A'0 A'CE HN; lia).
      assert (UK : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; clear - HK HN; lia).
      rewrite UA', UK in MU3. rewrite UA', UK in DST3. rewrite UA in SRC3. clear UA UA' UK.
      replace (ret_pc (Z_to_bv 64 0x4b5cc)) with (Z_to_bv 64 0x4b5cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      step. step. apply evt_done. do 14 eexists. exists m3. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact DST3|].
      unfold rfree_entry. reflexivity. }
    cbv beta. intros ms2 (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & MU3 & WM3 & MI3 & DST3 & ->).
    assert (PE23 : rpres_except (fun a => A' <= a < A' + k) m2 m3).
    { eapply rpres_except_of_munch'; [exact MU3| exact WM3|]. intros lo' hi' [EI|[]] x Hx. inversion EI; subst lo' hi'. exact Hx. }
    assert (HEAP3 : RHEAP s' ((p', A', n) :: LB) m3).
    { eapply RHEAP_frame_proof; [exact HEAP2| exact MU3| exact WM3|]. constructor; [| constructor]. right. right.
      exists (p', A', n). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. clear - HK. lia. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [| constructor]. cbn [fst snd].
      destruct AUX2 as (av & q3 & q4 & q5 & q16 & q6 & q11 & q12 & q23 & rnd & _ & _ & _ & CB' & _). unfold RAUXV_CELL, RLIBC. pose_ceil. clear - CB' A'CE A'IMG HK HN. lia. }
    assert (ST3 : stk rsegs m3 lo sp1) by (eapply rpres_except_stk; [exact PE23| exact ST2| cbv beta; intros; subst sp1; clear - H A'CE CLOv LO; lia]).
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 errv2]).
    { eapply rpres_except_rw_cells; [exact PE23| exact ERR2|]. rewrite ETP. cbn [cells_size csize Z.of_nat Nat.add Pos.of_succ_nat]. cbv beta. intros a Ha. clear - Ha A'IMG HK HN. lia. }
    pose proof HFREE as X. unfold rfree_impl_stmt in X.
    eapply implM_mono.
    { eapply X with (lo := lo) (B := B); clear X;
      [exact HEAP3| right; exact HinL| exact AUX3| rewrite SP1; subst sp1; lia| rewrite SP1; exact ST3| exact CLO
      | rewrite SP1; subst sp1; unfold RFREE_STACK; lia| exact ERR3| exact MI3| exact TP| reflexivity]. }
    cbv beta. intros u s'' ms'' PF. exists m3. split; [exact PE23|]. split; [exact DST3| exact PF]. }
  cbv beta. intros u s'' ms'' (m3 & PE23 & DST3 & PF).
  destruct PF as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m4 & -> & MI4 & ST4 & ERR4 & AUX4 & AUXC34 & PRES34 & EFA4 & ESO4 & HEAP4).
  rewrite SP1 in ST4, PRES34.
  replace (ret_pc (Z_to_bv 64 0x4b5d4)) with (Z_to_bv 64 0x4b5d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR3 : rw_cells rsegs m3 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rpres_except_rw_cells; [exact PE23| exact FR2|]. cbn [cells_size csize Z.of_nat Nat.add Pos.of_succ_nat]. cbv beta. intros a Ha. subst sp1. clear - Ha A'CE CLOv LO HK. lia. }
  assert (FR4 : rw_cells rsegs m4 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rheap_pres_rw_cells _ _ _ _ _ _ PRES34) in FR3; [exact FR3| left; lia]. }
  apply implM_ret.

  step. step. do 10 step.
  replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; lia); subst sp1; lia).
  release_frame FR4 ST4 (bv_unsigned sp).

  assert (ELB : lb_remove p ((p', A', n) :: LB) = (p', A', n) :: lb_remove p LB).
  { assert (Hb : bptr_eqb p' p = false).
    { unfold bptr_eqb. destruct (aptr_eqb_spec (fst p') (fst p)) as [E1|NE1]; [| reflexivity].
      destruct (Z.eqb_spec (snd p') (snd p)) as [E2|NE2]; [| reflexivity]. exfalso. apply NEp. destruct p', p; cbn in E1, E2; congruence. }
    unfold lb_remove. rewrite filter_cons_True; [reflexivity|]. unfold blk_id. cbn [fst]. rewrite Hb. exact I. }
  rewrite ELB in PRES34, HEAP4.

  assert (NC23 : forall a, rclient_addr (lb_remove p LB) (bv_unsigned sp) a -> ~ (A' <= a < A' + k)).
  { intros a [X|[[X NS]|(b' & Hb' & Hab)]] Y; [clear - X Y A'CE CLOv LO HK SPR; lia| clear - X Y A'IMG HK HN; lia|].
    unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' NEQ].
    assert (NEb : blk_id (p', A', n) <> blk_id b').
    { cbn [blk_id fst]. intros E1. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND. cbn [map blk_id fst] in ND.
      apply List.NoDup_cons_iff in ND as [NI _]. apply NI. rewrite E1. apply in_map. exact Hb'. }
    pose proof (RHEAP_blocks_disjoint_proof _ _ _ (p', A', n) b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb') NEb) as D.
    cbn [blk_addr blk_size fst snd] in D. clear - D Hab Y HK. lia. }
  assert (PRES03 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m3).
  { eapply rheap_pres_trans.
    - eapply rheap_pres_weaken; [exact PRES02| apply Z.le_refl| intros b' Hb'; unfold lb_remove in Hb'; apply In_filter_b in Hb' as [Hb' _]; exact Hb'].
    - intros a Ha HC. apply PE23; [exact Ha| exact (NC23 a HC)]. }
  assert (PRES04 : rheap_pres (lb_remove p LB) (bv_unsigned sp) m m4).
  { eapply rheap_pres_trans; [exact PRES03|]. eapply rheap_pres_weaken; [exact PRES34| subst sp1; clear; lia| intros b' Hb'; right; exact Hb']. }
  assert (AUXC04 : rauxcell_pres m m4).
  { eapply rauxcell_pres_trans; [exact AUXC02|]. eapply rauxcell_pres_trans; [| exact AUXC34].
    intros a Ha. unfold RAUXV_CELL, RLIBC in Ha. apply (proj1 (PE23 a ltac:(clear - Ha; lia) ltac:(cbv beta; clear - Ha A'IMG HK HN; lia))). }

  assert (TAIL3 : bytes_at rsegs m3 (A' + k) (skipn (Z.to_nat k) junk)).
  { eapply rpres_except_bytes_at; [exact PE23| exact TAILB| cbv beta; intros a Ha; clear - Ha; lia]. }
  assert (BLK3 : rw_cells rsegs m3 A' [Cells.CB (Z.to_nat n) (src ++ skipn (Z.to_nat k) junk)]).
  { destruct DST3 as [[_ HB3] HW3]. cbn [cells_bytes cbytes] in HB3. rewrite app_nil_r in HB3.
    split; [split|].
    - cbn. split; [| exact I]. rewrite length_app, LK, length_skipn, LJ. clear - HK. lia.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact HB3|]. rewrite LK, Z2Nat.id by lia. exact TAIL3.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. destruct BLK as [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r, Z2Nat.id in HW by lia.
      cbn [cells_size csize] in HW3. rewrite Nat.add_0_r, Z2Nat.id in HW3 by lia.
      assert (HWt : wr_at rsegs m3 (A' + k) (n - k)).
      { eapply rpres_except_wr_at; [exact PE23| eapply wr_at_sub; [exact HW| clear - HK; lia| clear - HK; lia]| cbv beta; intros a Ha; clear - Ha; lia]. }
      destruct HW3 as (W0 & W1 & W3). destruct HWt as (V0 & V1 & Vt). split; [exact W0|]. split; [clear - V1 HK; lia|].
      intros i Hi. destruct (Z.lt_ge_cases i k) as [LT|GE]; [apply W3; clear - Hi LT HK; lia|].
      replace (A' + i) with (A' + k + (i - k)) by lia. apply Vt. clear - Hi GE HK. lia. }
  assert (BLK4 : rw_cells rsegs m4 A' [Cells.CB (Z.to_nat n) (src ++ skipn (Z.to_nat k) junk)]).
  { eapply rheap_pres_rw_cells; [exact PRES34| exact BLK3|]. right. right. exists (p', A', n). split; [left; reflexivity|].
    cbn [blk_addr blk_size fst snd cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. clear; lia. }
  apply evt_done. unfold POST, rrealloc_post. do 15 eexists. exists m4, errv2. split; [reflexivity|].
  split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [exact AUX4|]. split; [exact AUXC04|].
  split; [exact PRES04|]. split; [rewrite EFA4; exact EFA2|]. split; [rewrite ESO4; exact ESO2|].
  exists A', (skipn (Z.to_nat k) junk). split; [reflexivity|]. split; [exact BR'|]. split; [exact HEAP4|].
  replace (Z.to_nat (Z.min old n)) with (Z.to_nat k) by (subst k; clear; lia). exact BLK4.
Qed.

Lemma arm_ccM : conc st c = r_base r + snd c.
Proof. apply conc_region'. rewrite FC. exact Hr. Qed.

Lemma move_armB : forall (rax t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29 y30 y31 : word),
  move_cond A n E (m_sizeclass mr) ->
  implM rsegs (realloc_body p A n (ps_m s)) s POST
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 A) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
               (Z_to_bv 64 (A + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (Z_to_bv 64 0x4b59c) fc None m1 (seg_rom rsegs)).
Proof.
  intros. pose proof arm_ccM as CC. destruct H as [NI NR].
  assert (RC : realloc_case (strip st) (fst p) A n = RcMove).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). fold c. rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_end rg_g rg_idx rg_stride rg_start].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    assert (EE : conc st c + stride - IB - A = E - A).
    { subst E Bg. rewrite CB, Z.mul_add_distr_l, Z.mul_1_r, CC, Ec. cbn [snd]. unfold UNIT, IB. clear. lia. }
    rewrite EE.
    destruct (Z.leb_spec n (E - A)); destruct (Z.ltb_spec n MMAP_THRESHOLD); destruct (Z.leb_spec (m_sizeclass mr) (size_to_class n + 1)); cbn [andb];
      try (exfalso; apply NI; clear - H H0 H1; tauto).
    all: destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.leb_spec 48 (m_sizeclass mr)); cbn [andb]; try reflexivity; exfalso; first [apply NR; clear - H2 H3; tauto| clear - H0 H2; lia]. }
  unfold realloc_body. rewrite <- Hst, RC. apply move_arm.
Qed.
End ARM.

End CEIL.
End TwinB.
