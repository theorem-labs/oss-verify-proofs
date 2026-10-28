(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame ITree Nodes Decode Tac SysStep SysMm.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepK KStepC KRemapDef MRemapOp KStepR.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocHINV MallocFacts_A MallocFacts_B Malloc_iface MallocTree MallocFacts_inv2 MallocFacts_inv3 F_malloc_entry F_free_spec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.P0 Require Import AllocLink. From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import AllocInst F_memcpy F_mm_syscalls RF_realloc_A RF_realloc_D RF_realloc_ip RF_realloc_spec RF_realloc_M RF_realloc_mm AllocRealloc.

Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma P0_realloc_general {HGW : HasGuard} {HCEIL : HasCeiling} :
  forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3c s4c s5c s6c t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (s : PState) (LB : list block) (k : bptr) (A sz n lo B : Z)
         (old : list byte) (errv : word),
  RHEAP s LB m1 -> In (k, A, sz) LB ->
  rw_cells rsegs m1 A [CB (Z.to_nat sz) old] ->
  rauxv_ok m1 B -> bv_unsigned sp <= B ->
  stk rsegs m1 lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m1 RERRNO [C4 errv] -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  heap_pres AI_P0 LB (bv_unsigned sp) m m1 ->
  0 <= n < 2^32 ->
  SREACH AI_P0 (realloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m)
    (MS (mkR (Z_to_bv 64 0x19cf8) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 n)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + sz)) s3c s4c s5c s6c s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom rsegs)) s LB.
Proof.
  intros until errv. intros HRm1 HIN OLDm1 HEm1 HB ST1 CLO LOLE ERRm1 MI1 FR1 HPm1 Hn.
  pose proof (P0_block_range _ _ _ _ HRm1 HIN) as (A1' & _ & SZ0 & ATOP & AIMG). cbn [blk_addr blk_size fst snd ai_L AI_P0 P0L al_img] in A1', SZ0, ATOP, AIMG.
  cbn [ai_L AI_P0 P0L al_realloc_pc al_tp al_stack al_errno RHEAP RENV LINK ai_PS ai_K ai_K_eqb ai_keep ai_mrel] in *.
  pose proof CLO as CLO'. idtac.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HRm1) as ND.
  ceil_facts.

  eapply sreach_bind.
  { eapply (P0_malloc_sreach rmalloc_entry rmalloc_entry_spec);
      [exact HRm1| exact HEm1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| idtac; ceil_facts; lia
      | rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| exact ERRm1| exact MI1| reflexivity| lia]. }
  intros s' LB' ms' POSTm.
  destruct POSTm as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & FRAMEm & RES).
  destruct FRAMEm as (MI' & ST' & HE' & [errv' ERR'] & HP'). cbn [ai_L AI_P0 P0L al_errno] in ERR'.
  rewrite unsigned_lit in ST', HP' by lia.
  replace (ret_pc (Z_to_bv 64 0x19cf8)) with (Z_to_bv 64 0x19cf8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR' : rw_cells rsegs m' (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
  { eapply heap_pres_rw_cells; [exact HP'| exact FR1|]. cbn. intros a Ha. left. lia. }
  destruct RES as [(-> & -> & HRf)|(k' & A' & junk & -> & -> & BR' & HR'' & NEW)].
  +
    eapply sreach_evt.
    { eapply (rrgen_fail _ sp gp (Z_to_bv 64 RATP)); [exact FR'| exact ST'| lia| exact MI']. }
    intros ms'' [-> ST''].
    apply sreach_ret. unfold realloc_post. do 15 eexists. exists m'. split; [reflexivity|].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [| exact HRf].
    split; [exact MI'|]. split; [exact ST''|]. split; [exact HE'|]. split; [exists errv'; exact ERR'|].
    eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPm1| lia| auto]|]. eapply heap_pres_weaken; [exact HP'| lia| auto].
  +
    pose proof (RHEAP_blocks_nodup_proof _ _ _ HR'') as ND'. cbn [map blk_id fst] in ND'.
    inversion ND' as [|x l NIk ND0]; subst x l.
    assert (INk : In k (map blk_id LB)) by (change k with (blk_id (k, A, sz)); apply in_map; exact HIN).
    assert (NEk : k' <> k) by (intros ->; exact (NIk INk)).
    destruct BR' as (BA1 & BA2 & _ & BA4 & BAI). cbn [ai_L AI_P0 P0L al_img] in BAI. ceil_facts.
    apply Forall_cons_iff in BAI as [BI1 BAI]. apply Forall_cons_iff in BAI as [BI2 _]. cbn [fst snd] in BI1, BI2.
    assert (DISJ : A + sz <= A' \/ A' + n <= A).
    { destruct (P0_blocks_disjoint s' ((k', A', n) :: LB) m' (k', A', n) (k, A, sz) HR'' ltac:(left; reflexivity) ltac:(right; exact HIN)
                 ltac:(intros E; inversion E; subst; exact (NEk eq_refl))) as [D|D]; cbn [blk_addr blk_size fst snd] in D; lia. }
    assert (OLDm' : rw_cells rsegs m' A [CB (Z.to_nat sz) old]).
    { eapply heap_pres_rw_cells; [exact HP'| exact OLDm1|]. cbn [cells_size csize Nat.add]. intros a Ha. right. right.
      exists (k, A, sz). split; [exact HIN|]. cbn [AllocIF.blk_addr AllocIF.blk_size fst snd]. lia. }
    assert (LENold : length old = Z.to_nat sz) by (destruct OLDm' as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
    set (mn := Z.to_nat (Z.min n sz)) in *.
    assert (LENjunk : length junk = Z.to_nat n) by (destruct NEW as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
    assert (NEW2 : rw_cells rsegs m' A' [CB mn (firstn mn junk); CB (Z.to_nat n - mn) (skipn mn junk)]).
    { apply rw_cells_CB_split; [| rewrite firstn_length; lia]. rewrite firstn_skipn. replace (mn + (Z.to_nat n - mn))%nat with (Z.to_nat n) by lia. exact NEW. }
    apply rw_cells_CB2_split in NEW2 as [DST REST].

    eapply sreach_evt.
    { eapply (rrgen_tocpy _ (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) _ _ _ _ _ _ _ _ _ _ s3c s4c s5c s6c s7 s8 s9 s10 s11 _ _ _ _ F fc m' A' A n (A + sz)); lia. }
    intros ms2 ->. replace (A + sz - A) with sz by lia.

    eapply sreach_evt.
    { eapply (memcpy_spec _ _ gp (Z_to_bv 64 RATP) _ _ _ _ _ (Z_to_bv 64 A') (Z_to_bv 64 A) (Z_to_bv 64 (Z.min n sz)) _ _ _ _ _ _ s3c s4c s5c s6c s7 s8 s9 s10 s11 _ _ _ _ F fc m'
                (firstn mn old) (firstn mn junk)); rewrite ?unsigned_lit by lia.
      - destruct OLDm' as [[_ BO] _]. cbn [cells_bytes cbytes] in BO. rewrite app_nil_r in BO. apply bytes_at_firstn. exact BO.
      - rewrite firstn_length. lia.
      - fold mn. exact DST.
      - lia.
      - exact MI'. }
    intros ms3 POSTc. unfold memcpy_post in POSTc.
    destruct POSTc as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m'' & -> & MU2 & WM2 & MI2 & CPY & _).
    rewrite ?unsigned_lit in MU2, CPY by lia. fold mn in CPY.
    replace (ret_pc (Z_to_bv 64 0x19d18)) with (Z_to_bv 64 0x19d18) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MN : 0 <= Z.min n sz <= n) by lia.
    assert (FR2 : rw_cells rsegs m'' (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FR'| exact MU2| exact WM2|]. cbn. lia. }
    assert (ST2 : stk rsegs m'' lo (bv_unsigned sp + -64)).
    { eapply stk_transport_disjoint; [exact ST'| exact MU2| exact WM2|]. cbn. lia. }
    assert (HR2 : RHEAP s' ((k', A', n) :: LB) m'').
    { eapply P0_heap_frame; [exact HR''| exact MU2| exact WM2|]. constructor; [| constructor]. right. right. right.
      exists (k', A', n). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
    assert (HE2 : rauxv_ok m'' B).
    { eapply rauxv_ok_frame; [exact HE'| exact MU2| exact WM2|]. constructor; [| constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
    assert (ERR2 : rw_cells rsegs m'' RERRNO [C4 errv']).
    { eapply rw_cells_transport; [exact ERR'| exact MU2| exact WM2|]. cbn. unfold RERRNO, RATP. lia. }
    assert (REST2 : rw_cells rsegs m'' (A' + Z.of_nat mn) [CB (Z.to_nat n - mn) (skipn mn junk)]).
    { eapply rw_cells_transport; [exact REST| exact MU2| exact WM2|]. cbn. lia. }
    pose proof (rw_cells_CB2_join _ _ _ _ _ _ CPY REST2) as NEW3.
    replace (mn + (Z.to_nat n - mn))%nat with (Z.to_nat n) in NEW3 by lia.
    assert (HPc : heap_pres AI_P0 (lb_remove k LB) (bv_unsigned sp) m' m'').
    { eapply heap_pres_of_munch; [exact MU2| exact WM2|]. intros a Ha Hc. cbn. split; [| exact I].
      destruct Hc as [Hc|[(lo' & hi' & CS & Hlo)|(b & Hb & Hab)]]; [lia| |].
      - cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. lia.
      - cbn [ai_K AI_P0] in Hab. pose proof (lb_remove_sub _ _ _ Hb) as HbL.
        assert (NEb : (k', A', n) <> b).
        { intros <-. apply NIk. change k' with (blk_id (k', A', n)). apply in_map. exact HbL. }
        destruct (P0_blocks_disjoint s' ((k', A', n) :: LB) m' (k', A', n) b HR'' ltac:(left; reflexivity) ltac:(right; exact HbL) NEb) as [D|D];
          cbn [blk_addr blk_size fst snd] in D; unfold blk_addr, blk_size in D; unfold AllocIF.blk_addr, AllocIF.blk_size in Hab; lia. }

    eapply sreach_evt; [apply rrgen_tofree|]. intros ms4 ->.

    eapply sreach_bind.
    { eapply (P0_free_sreach rfree_entry rfree_entry_spec);
        [exact HR2| right; exact HIN| exact HE2| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST2
        | idtac; ceil_facts; lia| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia| exact ERR2| exact MI2| reflexivity]. }
    intros s'' LB'' ms5 POSTf.
    destruct POSTf as (z0 & z1 & z2 & ra1 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m3 & -> & FRAMEf & -> & HR3).
    destruct FRAMEf as (MI3 & ST3 & HE3 & [errv3 ERR3] & HP3). cbn [ai_L AI_P0 P0L al_errno] in ERR3.
    rewrite unsigned_lit in ST3, HP3 by lia.
    replace (ret_pc (Z_to_bv 64 0x19d20)) with (Z_to_bv 64 0x19d20) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite (lb_remove_cons_other LB k k' A' n NEk) in HR3, HP3 |- *.
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply heap_pres_rw_cells; [exact HP3| exact FR2|]. cbn. intros a Ha. left. lia. }

    eapply sreach_evt.
    { eapply (rrgen_end _ sp gp (Z_to_bv 64 RATP)); [exact FR3| exact ST3| lia| exact MI3]. }
    intros ms6 [-> ST6].
    apply sreach_ret. unfold realloc_post. do 15 eexists. exists m3. split; [reflexivity|].
    right. exists k', A', (skipn mn junk). split; [reflexivity|]. split; [reflexivity|].
    split; [| split; [| split; [exact HR3|]]].
    * unfold block_range. cbn [ai_L AI_P0 P0L al_img]. ceil_facts.
      split; [exact BA1|]. split; [exact BA2|]. split; [lia|]. split; [exact BA4|].
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    * split; [exact MI3|]. split; [exact ST6|]. split; [exact HE3|]. split; [exists errv3; exact ERR3|].
      eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HPm1| lia| intros b Hb; exact (lb_remove_sub _ _ _ Hb)]|].
      eapply heap_pres_trans; [eapply heap_pres_weaken; [exact HP'| lia| intros b Hb; exact (lb_remove_sub _ _ _ Hb)]|].
      eapply heap_pres_trans; [exact HPc|].
      eapply heap_pres_weaken; [exact HP3| lia|]. intros b Hb. right. exact Hb.
    * eapply heap_pres_rw_cells; [exact HP3| exact NEW3|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. intros a Ha. right. right.
      exists (k', A', n). split; [left; reflexivity|]. cbn [AllocIF.blk_addr AllocIF.blk_size fst snd]. lia.
Qed.

Definition p0_avoid : list (Z * Z) := [(0x10000, 0x2a000); (0x2a000, 0x5d000)]%Z.

Lemma pcovered_p0 : forall maps, map wwZ maps = p0_reserved -> Forall (pcovered maps) p0_avoid.
Proof.
  intros [|[e1 z1] [|[e2 z2] [|[e3 z3] [|[e4 z4] [|x l]]]]] E; cbn in E; try discriminate.
  unfold wwZ in E. cbn [fst snd] in E. injection E as E1 F1 E2 F2 E3 F3 E4 F4.
  unfold p0_avoid. constructor; [| constructor; [| constructor]]; (split; [cbn; lia|]); cbn [fst snd]; intros x Hx.
  - destruct (Z_lt_le_dec x 0x13000).
    + exists e1, z1. split; [left; reflexivity| lia].
    + exists e2, z2. split; [right; left; reflexivity| lia].
  - destruct (Z_lt_le_dec x 0x2b000).
    + exists e3, z3. split; [right; right; left; reflexivity| lia].
    + exists e4, z4. split; [right; right; right; left; reflexivity| lia].
Qed.

Lemma p0_avoids_windows : forall a k, avoids a k p0_avoid = true ->
  ((a + k <= 0x10000 \/ 0x2a000 <= a) /\ (a + k <= 0x2a000 \/ 0x5d000 <= a))%Z.
Proof.
  intros a k H. unfold avoids, p0_avoid in H. cbn [forallb fst snd] in H.
  rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le in H. lia.
Qed.

Theorem P0_realloc_contract_mm {HGW : HasGuard} {HCEIL : HasCeiling} :
  forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (k : bptr) (A sz n lo B : Z)
         (old : list byte) (errv : word),
  RHEAP s LB m -> In (k, A, sz) LB ->
  rw_cells rsegs m A [CB (Z.to_nat sz) old] ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m RERRNO [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  MMAP_THRESHOLD <= n ->
  SREACH AI_P0 (realloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m)
    (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1995c) fc None m (seg_rom rsegs)) s LB.
Proof.
  intros until errv. intros HR HIN CELLS HE HB ST CLO LOLE ERR MI Ha0 Ha1 Hn NT.
  cbn [ai_L AI_P0 P0L al_realloc_pc al_tp al_stack al_errno RHEAP RENV LINK ai_PS ai_K ai_K_eqb ai_keep ai_mrel] in *.
  pose proof CLO as CLO'. idtac.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HR) as ND.
  pose proof (P0_block_range _ _ _ _ HR HIN) as (A1' & _ & SZ0 & ATOP & AIMG). cbn [blk_addr blk_size fst snd ai_L AI_P0 P0L al_img] in A1', SZ0, ATOP, AIMG.
  apply Forall_cons_iff in AIMG as [AI1 AIMG]. apply Forall_cons_iff in AIMG as [AI2 _]. cbn [fst snd] in AI1, AI2.

  pose proof HR as (st & LB0 & PERM & Hst & HMR & [BL AR]).
  assert (Hin0 : In (k, A, sz) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact HIN]).
  pose proof (areach_cinv_proof _ _ AR) as C.
  destruct (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (k, A, sz) Hin0) as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  change (blk_slot (k, A, sz)) with (fst k) in SL, HBg, OA, OS, OK, HK, NG. cbn [blk_addr blk_size fst snd] in OA, OS, SZ, OK, HK.
  eapply sreach_evt.
  { eapply (rrealloc_walk_mm gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo CLO' ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
              m st (k, A, sz) off n g i AR Hin0 O0 OA SL HMR MI ST ltac:(lia) Ha0 Ha1 ltac:(split; [exact NT| lia])). }
  change (blk_slot (k, A, sz)) with (fst k). cbn [blk_addr blk_size fst snd].
  intros ms' [[SC48 GEN]|(SC63 & I0 & O255 & m1 & rg & M1 & Hrg & Krg & EON & CC & CASES)].
  -
    destruct GEN as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & FR1 & ST1 & MU1 & WM1 & MI1).
    ceil_facts.
    assert (HPm1 : heap_pres AI_P0 LB (bv_unsigned sp) m m1).
    { eapply heap_pres_of_munch; [exact MU1| exact WM1|]. intros a Ha Hc. cbn. split; [| exact I].
      destruct Hc as [Hc|[(lo' & hi' & CS & Hlo)|(b' & Hb & Hab)]]; [lia| |].
      - cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. lia.
      - pose proof (P0_block_range _ _ _ _ HR Hb) as (_ & _ & _ & BT & _). idtac. ceil_facts.
        unfold AllocIF.blk_addr, AllocIF.blk_size, blk_addr, blk_size in BT, Hab.
        cbn [ai_K AI_P0] in Hab. clear - BT Hab CLO LOLE CEILB. lia. }
    assert (HRm1 : RHEAP s LB m1).
    { eapply P0_heap_frame; [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. idtac. ceil_facts. lia. }
    assert (HEm1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (ERRm1 : rw_cells rsegs m1 RERRNO [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold RERRNO, RATP. lia. }
    assert (OLDm1 : rw_cells rsegs m1 A [CB (Z.to_nat sz) old]).
    { eapply rw_cells_transport; [exact CELLS| exact MU1| exact WM1|]. cbn. lia. }
    eapply (P0_realloc_general ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); first [exact HRm1| exact HIN| exact OLDm1| exact HEm1| exact HB| exact ST1| exact ERRm1| exact MI1| exact FR1| exact HPm1| lia| idtac].
    all: ceil_facts; lia.
  -
    subst i. destruct M1 as (FR1 & ST1 & MU1 & WM1 & MI1 & MR1). cbv zeta in CASES.
    ceil_facts.
    assert (PE01 : rpres_except (fun a => lo <= a < bv_unsigned sp) m m1).
    { apply (rpres_except_of_munch_cov _ _ m m1 MU1 WM1). cbn [ivs_covered]. split; [| exact I]. intros x Hx. lia. }
    set (c := fst k) in *.
    assert (Ek : k = (c, snd k)) by (destruct k; reflexivity).
    assert (HX : In (c, snd k) (map blk_id LB)) by (rewrite <- Ek; change k with (blk_id (k, A, sz)); apply in_map; exact HIN).
    assert (HsS : s_slots (ps_m s) !! c = Some (g, 0)) by (rewrite <- Hst; exact SL).
    assert (SCS : m_sizeclass (MI_Inv.MR (ps_m s) g) = 63) by (rewrite <- Hst; exact SC63).
    assert (HrgS : s_regions (ps_m s) !! fst c = Some rg) by (rewrite <- Hst; exact Hrg).
    pose proof MR1 as ((Hres & _ & WR & _) & _ & (_ & _ & _ & GOT1 & SSP1 & _) & _).
    destruct (WR _ _ Hrg) as (RB0 & RBAL & RL0 & RBC & RF). ceil_facts. rewrite <- EON in RBC, RF.
    set (nn := mremap_needed off n) in *.
    assert (NNG : n + 16 * off + 16 + 4 <= nn < n + 16 * off + 16 + 4 + 4096 /\ nn mod 4096 = 0).
    { subst nn. unfold mremap_needed. pose proof (MI_Cnt.round_up_pg_spec (n + UNIT * off + UNIT + IB)) as RS. unfold UNIT, IB in RS. exact RS. }
    unfold MMAP_THRESHOLD in NT.
    destruct CASES as [[EQ HAT]|[NE HC]].
    +
      intros mo HL. cbn [LINK AI_P0] in HL. unfold P0_LINK in HL.
      pose proof (own_group_facts (map blk_id LB) G0 s mo c (snd k) g rg HL HX HsS SCS HrgS) as (_ & R0 & RA & RL & RC & EML & RPG & RONA & _ & _ & _ & MINV & HALT).
      unfold rold, ron, PGSZ in R0, RA, RL, RC, EML, RPG, RONA.
      destruct (own_remap_inplace (map blk_id LB) G0 s mo c (snd k) g rg HL frame_ok_G0 HX HsS SCS HrgS ltac:(unfold ron, PGSZ; lia)) as [OKc OWN'].
      unfold rold, ron in OKc, OWN'. rewrite <- EON, EQ in OKc, OWN'.
      eapply (Bridge.sr_evt node rsegs (at_node rsegs) nstep nexit minv nsafe (nodes_sound rsegs)); [split; [exact HALT| exact MINV]| |].
      { eapply (rrealloc_mm_finish gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra sp s LB LB0 lo st k A sz old m m1 m1 g rg off n (r_base rg)
                  CLO' ltac:(lia) PERM Hst BL AR HIN O0 OA SL SC63 Hrg ltac:(unfold MMAP_THRESHOLD; lia) CELLS PE01 MR1 ltac:(rewrite Hst; exact OKc));
          [intros; reflexivity| intros; reflexivity| intros o Ho; exfalso; rewrite EQ, Z.min_id in Ho; lia| exact MI1| exact FR1| exact ST1| exact HAT]. }
      intros msf POST. apply sr_done. unfold linked. cbn [cfg_ms cfg_model LINK AI_P0 ai_keep ai_mrel].
      destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & junk & -> & MI' & ST' & AUX & ERRP & HP' & HR' & BR & CELLS').
      exists (set_m (cremap (ps_m s) (fst c) g (r_base rg) nn) s), ((k, r_base rg + 16 + UNIT * off, n) :: lb_remove k LB).
      split. { unfold P0_LINK. cbn [map blk_id fst]. eapply OWN_perm; [| exact OWN']. eapply lb_remove_perm; [exact ND| exact HIN]. }
      split; [split; reflexivity|]. split; [apply P0_mrel_refl|].
      unfold realloc_post. do 15 eexists. exists m'. split; [reflexivity|].
      right. exists k, (r_base rg + 16 + UNIT * off), junk. split; [reflexivity|]. split; [reflexivity|]. split; [| split; [| split; [exact HR'| exact CELLS']]].
      * destruct BR as (B1 & B2 & B3 & B4 & B5 & B6). unfold block_range. cbn [ai_L AI_P0 P0L al_img].
        ceil_facts. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
        split; [first [exact B4 | unfold alloc_ceiling; cbn; lia]|].
        constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
      * split; [exact MI'|]. split; [exact ST'|]. split; [exact (AUX B HE HB)|]. split; [exists errv; exact (ERRP errv ERR)|].
        apply heap_pres_of_rheap_pres. exact HP'.
    +
      destruct HC as (t0' & a5' & a6' & a7' & t4' & t5' & t6' & ->).
      intros mo HL. cbn [LINK AI_P0] in HL. unfold P0_LINK in HL.
      pose proof (own_group_facts (map blk_id LB) G0 s mo c (snd k) g rg HL HX HsS SCS HrgS) as (_ & R0 & RA & RL & RC & EML & RPG & RONA & _ & RSVD & RSVE & MINV & HALT).
      unfold rold, ron, PGSZ in R0, RA, RL, RC, EML, RPG, RONA, RSVD. rewrite <- EON in RC, EML, RPG, RONA, RSVD.

      assert (CEQ : s_ceil (ps_m s) = alloc_ceiling).
      { rewrite <- Hst, s_ceil_strip. pose proof MR1 as ((_ & CE1 & _) & _). exact CE1. }
      rewrite CEQ in RC. ceil_facts.
      assert (ERR1 : rw_cells rsegs m1 RERRNO [C4 errv]).
      { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold RERRNO, RATP. lia. }
      pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as DRo.
      assert (COV : Forall (pcovered (vm_reserved (m_vmmaps mo))) p0_avoid).
      { apply pcovered_p0. rewrite RSVE, <- Hst. exact Hres. }
      set (on := m_maplen (get_meta_rec st g) * 4096) in *.

      pose proof (p0mremap_spec (Z_to_bv 64 0x19c44) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0' (Z_to_bv 64 (r_base rg + 16)) (Z_to_bv 64 0x1ffec)
                    (Z_to_bv 64 nn) (wz (conc st g)) (Z_to_bv 64 (r_base rg)) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1) (Z_to_bv 64 on) a5' a6' a7'
                    (Z_to_bv 64 (A + sz)) (Z_to_bv 64 (UNIT * off)) (Z_to_bv 64 4095) (Z_to_bv 64 A) (Z_to_bv 64 n) s7 s8 s9 s10 s11 (Z_to_bv 64 0x1ffeb) t4' t5' t6'
                    F fc m1 (r_base rg) on nn p0_avoid errv guard_word lo) as IMPL.
      rewrite errno_addr_RATP, ?(SysMm.mmap_len_aligned on) in IMPL by lia.
      assert (F1 : 0 < on <= 2^62) by (clear - RPG RC R0 CEILB; lia).
      assert (F2 : 0 < nn <= 2^62) by (clear - NNG NT O0 O255 Hn; lia).
      assert (F3 : r_base rg + on <= alloc_ceiling) by (clear - RC; lia).
      assert (F4 : (r_base rg + on <= 65536 \/ 172032 <= r_base rg) /\ (r_base rg + on <= 172032 \/ 380928 <= r_base rg)) by (clear - DRo; lia).
      assert (F5 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) - 112) by (rewrite unsigned_lit by (clear - SPR LOLE CLO CEILB; lia); clear - SPR LOLE CLO CEILB; lia).
      assert (F6 : RERRNO + 4 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) - 112 \/ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) <= RERRNO).
      { rewrite unsigned_lit by (clear - SPR LOLE CLO CEILB; lia). unfold RERRNO. clear - SPR LOLE CLO CEILB; lia. }
      assert (F7 : (RERRNO + 4 <= 172368 \/ 172368 + 8 <= RERRNO) /\ (RERRNO + 4 <= 375432 \/ 375432 + 8 <= RERRNO)) by (unfold RERRNO; clear; lia).
      assert (F8 : r_base rg + on <= RERRNO \/ RERRNO + 4 <= r_base rg) by (unfold RERRNO; clear - F4 RPG; lia).
      assert (F9 : forall a k, avoids a k p0_avoid = true -> a + k <= RERRNO \/ RERRNO + 4 <= a).
      { intros a' k' Hav. pose proof (p0_avoids_windows a' k' Hav). unfold RERRNO. clear - H. lia. }
      assert (F10 : 164 <= bv_unsigned (Z_to_bv 64 RATP)) by (unfold RATP; rewrite unsigned_lit by (clear; lia); clear; lia).
      specialize (IMPL ltac:(rewrite unsigned_lit by (clear - SPR LOLE CLO CEILB; lia); exact ST1) ERR1 GOT1 SSP1 MI1 eq_refl eq_refl eq_refl eq_refl R0 RA F1 F2 F3 F4
                       p0_avoids_windows F5 CLO F6 F7 F8 F9 F10).

      assert (NA' : nn mod PGSZ = 0) by (unfold PGSZ; clear - NNG; lia).
      assert (N2' : 2 * PGSZ <= nn) by (unfold PGSZ; clear - NNG NT O0; lia).
      assert (NL' : nn < LEN_MAX) by (unfold LEN_MAX; clear - F2; lia).
      set (KP := fun (r : exc mremap_ans) (mo' : Model) => match r with Unr => False | Ok a =>
             match a with
             | MrErr _ => OWN (map blk_id LB) G0 s mo'
             | MrSame => r_base rg + nn <= alloc_ceiling /\ cremap_ok (ps_m s) c (r_base rg) nn /\ OWN (map blk_id LB) G0 (set_m (cremap (ps_m s) (fst c) g (r_base rg) nn) s) mo'
             | MrMoved dst => on < nn /\ cremap_ok (ps_m s) c dst nn /\ OWN (map blk_id LB) G0 (set_m (cremap (ps_m s) (fst c) g dst nn) s) mo'
             end end).
      assert (STWF : stwfR node nstep nexit nsafe P0_mrel (enode (NMremap (r_base rg) on nn) (dec_mremap (r_base rg) on nn p0_avoid)) mo KP).
      { cbn [stwfR enode]. split; [| split].
        - pose proof (own_mremap_nsafe (map blk_id LB) G0 s mo c (snd k) g rg HL HX HsS SCS HrgS nn ltac:(clear - F2; lia)) as NSF.
          unfold rold, ron in NSF. rewrite <- EON in NSF. exact NSF.
        - intros code mo' X. exact X.
        - intros rsp mo' evs STEP.
          pose proof (own_mremap (map blk_id LB) G0 s mo c (snd k) g rg HL frame_ok_G0 HX HsS SCS HrgS nn p0_avoid rsp mo' evs NA' N2' NL' COV) as OM.
          unfold rold, ron in OM. rewrite <- EON in OM. specialize (OM STEP). destruct OM as (Eevs & FRm & MINV' & HALT' & a & Hd & Ha).
          split; [exact Eevs|]. split; [apply P0_mrel_of_frame; exact FRm|]. rewrite Hd. cbn [stwfR]. unfold KP.
          destruct a as [e| |dst]; [exact Ha| | exact Ha].
          destruct Ha as [[E _]|(_ & DC' & OKc & OWN')]; [exfalso; exact (NE E)|]. rewrite CEQ in DC'. auto. }
      pose proof (Bridge.impl_stwfR_safe_reach node rsegs (at_node rsegs) nstep nexit minv nsafe (nodes_sound rsegs) P0_mrel P0_mrel_refl P0_mrel_trans
                    _ _ _ mo KP IMPL STWF ltac:(split; [exact HALT| exact MINV])) as SR.
      eapply sr_bind; [exact SR|]. intros [msx mox] (r & HQ & HKP & MFx & MRx). cbn [cfg_ms cfg_model] in HQ, HKP, MFx, MRx.
      destruct r as [|ans]; [destruct HKP|]. cbn [epost] in HQ. unfold p0mremap_post in HQ. cbv zeta in HQ. rewrite ?errno_addr_RATP in HQ.
      rewrite ?(SysMm.mmap_len_aligned on), ?(SysMm.mmap_len_aligned nn) in HQ by first [exact RONA| clear - NNG; lia].
      replace (ret_pc (Z_to_bv 64 0x19c44)) with (Z_to_bv 64 0x19c44) in HQ by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (LINKED : forall msf s' LB', OWN (map blk_id LB') G0 s' mox -> P0_keep s s' ->
                realloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m s' LB' msf ->
                linked AI_P0 s mo (realloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m) (mkCfg msf mox)).
      { intros msf s' LB' O' K' Q'. unfold linked. cbn [cfg_ms cfg_model LINK AI_P0 ai_keep ai_mrel]. exists s', LB'. auto. }
      assert (FINPOST : forall dst msf, OWN (map blk_id LB) G0 (set_m (cremap (ps_m s) (fst c) g dst nn) s) mox ->
                rrmm_spec_post ra sp gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (set_m (cremap (ps_m s) (fst (fst k)) g dst nn) s) LB k (dst + 16 + UNIT * off) sz n lo old m msf ->
                linked AI_P0 s mo (realloc_post AI_P0 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k A sz n lo B old m) (mkCfg msf mox)).
      { intros dst msf OWN' POST.
        destruct POST as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & junk & -> & MI' & ST' & AUX & ERRP & HP' & HR' & BR & CELLS').
        apply (LINKED _ (set_m (cremap (ps_m s) (fst c) g dst nn) s) ((k, dst + 16 + UNIT * off, n) :: lb_remove k LB)).
        - cbn [map blk_id fst]. eapply OWN_perm; [| exact OWN']. eapply lb_remove_perm; [exact ND| exact HIN].
        - split; reflexivity.
        - unfold realloc_post. do 15 eexists. exists m'. split; [reflexivity|].
          right. exists k, (dst + 16 + UNIT * off), junk. split; [reflexivity|]. split; [reflexivity|]. split; [| split; [| split; [exact HR'| exact CELLS']]].
          + destruct BR as (B1 & B2 & B3 & B4 & B5 & B6). unfold block_range. cbn [ai_L AI_P0 P0L al_img].
            ceil_facts. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
            split; [first [exact B4 | unfold alloc_ceiling; cbn; lia]|].
            constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
          + split; [exact MI'|]. split; [exact ST'|]. split; [exact (AUX B HE HB)|]. split; [exists errv; exact (ERRP errv ERR)|].
            apply heap_pres_of_rheap_pres. exact HP'. }
      destruct ans as [e| |dst].
      *
        cbn [KP] in HKP.
        destruct HQ as (z0 & z1 & z2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & _ & _ & He).
        rewrite ?unsigned_lit in MU2, ST2 by (clear - SPR LOLE CLO CEILB; lia).
        eapply (Bridge.sr_evt node rsegs (at_node rsegs) nstep nexit minv nsafe (nodes_sound rsegs)); [exact MFx| |].
        { eapply evt_cut; [apply rrealloc_mm_ret|]. cbv beta. intros ms1 ->. apply rrealloc_mm_fail. }
        cbv beta. intros ms2 [a3x ->].
        assert (MU12 : munch [(bv_unsigned sp - 176, bv_unsigned sp); (RERRNO, RERRNO + 4)]%Z m m2).
        { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; intros x Hx; cbn in Hx |- *; destruct Hx as (Hx1 & Hx2 & _);
            unfold RERRNO in *; repeat split; try exact I; clear - Hx1 Hx2 SPR; lia. }
        assert (WM12 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
        assert (HPm2 : heap_pres AI_P0 LB (bv_unsigned sp) m m2).
        { eapply heap_pres_of_munch; [exact MU12| exact WM12|]. intros a Ha Hc. cbn. split; [| split; [| exact I]].
          - destruct Hc as [Hc|[(lo' & hi' & CS & Hlo)|(b' & Hb & Hab)]]; [clear - Hc; lia| |].
            + cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. clear - CS Hlo CLO LOLE CEILB; lia.
            + pose proof (P0_block_range _ _ _ _ HR Hb) as (_ & _ & _ & BT & _). idtac. ceil_facts.
              unfold AllocIF.blk_addr, AllocIF.blk_size, blk_addr, blk_size in BT, Hab. cbn [ai_K AI_P0] in Hab. clear - BT Hab CLO LOLE CEILB. lia.
          - destruct Hc as [Hc|[(lo' & hi' & CS & Hlo)|(b' & Hb & Hab)]]; [unfold RERRNO; clear - Hc CLO LOLE CEILB; lia| |].
            + cbn [ai_L AI_P0 P0L al_client_static] in CS. unfold p0_client_static in CS. unfold RERRNO in *. clear - CS Hlo; lia.
            + pose proof (P0_block_range _ _ _ _ HR Hb) as (_ & _ & _ & _ & BI). cbn [ai_L AI_P0 P0L al_img] in BI.
              apply Forall_cons_iff in BI as [_ BI]. apply Forall_cons_iff in BI as [BI _]. cbn [fst snd] in BI.
              unfold AllocIF.blk_addr, AllocIF.blk_size, blk_addr, blk_size in BI, Hab. cbn [ai_K AI_P0] in Hab. unfold RERRNO. clear -BI Hab. lia. }
        assert (HRm2 : RHEAP s LB m2).
        { eapply P0_heap_frame; [exact HR| exact MU12| exact WM12|]. constructor; [| constructor; [| constructor]].
          - left. cbn. idtac. ceil_facts. clear - CLO LOLE CEILB; lia.
          - right. right. left. cbn. unfold RERRNO. lia. }
        assert (HEm2 : rauxv_ok m2 B).
        { eapply rauxv_ok_frame; [exact HE| exact MU12| exact WM12|]. constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold RAUXV_CELL, RERRNO; clear - HB CLO LOLE SPR CEILB; lia. }
        assert (OLDm2 : rw_cells rsegs m2 A [CB (Z.to_nat sz) old]).
        { eapply rw_cells_transport; [exact CELLS| exact MU12| exact WM12|]. cbn. unfold RERRNO. clear - ATOP AI2 SZ0 CLO LOLE CEILB. lia. }
        assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
        { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. unfold RERRNO. clear - SPR CLO LOLE CEILB. lia. }
        eapply sr_mono.
        { eapply (P0_realloc_general ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m m2 s LB k A sz n lo B old (Z_to_bv 64 e)
                    HRm2 HIN OLDm2 HEm2 HB ST2 ltac:(idtac; exact CLO) LOLE ERR2 MI2 FR2 HPm2 Hn).
          cbn [LINK AI_P0]. exact HKP. }
        intros cfg (s' & LB' & L1 & K1 & M1' & Q1). exists s', LB'. split; [exact L1|]. split; [exact K1|]. split; [eapply P0_mrel_trans; [exact MRx| exact M1']| exact Q1].
      *
        cbn [KP] in HKP. destruct HKP as (DC' & OKc & OWN').
        destruct HQ as [[_ BAD]|HQ]; [exfalso; clear - BAD DC'; lia|].
        destruct HQ as (z0 & z1 & z2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m2x & -> & MU2 & WM2 & MI2x & ST2 & ERR2 & _ & _ & SHAPE).
        rewrite ?unsigned_lit in MU2, ST2 by (clear - SPR LOLE CLO CEILB; lia).
        assert (MR2x : rmrep st m2x).
        { eapply rmrep_transport_high; [exact MR1| exact MU2| exact WM2|]. intros l h [E1|[]]. inversion E1; subst. ceil_facts. clear - SPR LOLE CLO CEILB; lia. }
        assert (PE02 : rpres_except (fun a => lo <= a < bv_unsigned sp) m m2x).
        { eapply rpres_except_trans; [exact PE01|]. apply (rpres_except_of_munch_cov _ _ m1 m2x MU2 WM2). cbn [ivs_covered]. split; [| exact I]. intros x Hx. clear - Hx SPR LOLE CLO CEILB; lia. }
        assert (FR2x : rw_cells rsegs m2x (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
        { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. clear - SPR CLO LOLE CEILB. lia. }
        pose proof OKc as (_ & _ & _ & _ & _ & _ & RESVn & _). rewrite <- Hst in RESVn. cbn [s_reserved strip] in RESVn. rewrite Hres in RESVn.
        pose proof (rreserved_disjoint1 _ _ RESVn ltac:(clear - F2; lia)) as DRn.
        assert (RCM : r_base rg + Z.max on nn <= alloc_ceiling) by (clear - RC DC'; lia).
        pose proof (same_raw_facts (r_base rg) on nn m2x R0 ltac:(clear - F1; lia) ltac:(clear - F2; lia) RCM ltac:(clear - F4 DRn; lia))
          as (H2a & H2b & H2c & MIr & RWr).
        eapply (Bridge.sr_evt node rsegs (at_node rsegs) nstep nexit minv nsafe (nodes_sound rsegs)); [exact MFx| |].
        { eapply evt_cut; [apply rrealloc_mm_ret|]. cbv beta. intros ms1 ->.
          eapply (rrealloc_mm_finish gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra sp s LB LB0 lo st k A sz old m m2x (mremap_same_raw (r_base rg) on nn m2x) g rg off n (r_base rg)
                    CLO' ltac:(clear - LOLE; lia) PERM Hst BL AR HIN O0 OA SL SC63 Hrg ltac:(unfold MMAP_THRESHOLD; clear - NT Hn; lia) CELLS PE02 MR2x ltac:(rewrite Hst; exact OKc));
            [exact H2a| exact H2b| exact H2c| apply MIr; exact MI2x| apply RWr; [exact FR2x| ceil_facts; clear - RC DC' SPR CLO LOLE CEILB; lia]| exact ST2| unfold rrmm_at; do 17 eexists; reflexivity]. }
        intros msf POST. apply sr_done. exact (FINPOST (r_base rg) msf OWN' POST).
      *
        cbn [KP] in HKP. destruct HKP as (LT & OKc & OWN').
        destruct HQ as [BAD|HQ].
        { exfalso. destruct OKc as (_ & _ & _ & _ & _ & DCm & _). rewrite CEQ in DCm. clear - BAD DCm. lia. }
        destruct HQ as (z0 & z1 & z2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z4 & z5 & z6 & m2x & -> & MU2 & WM2 & MI2x & ST2 & ERR2 & _ & _ & (DA & D0 & DC' & _) & AVD).
        rewrite ?unsigned_lit in MU2, ST2 by (clear - SPR LOLE CLO CEILB; lia).
        assert (MR2x : rmrep st m2x).
        { eapply rmrep_transport_high; [exact MR1| exact MU2| exact WM2|]. intros l h [E1|[]]. inversion E1; subst. ceil_facts. clear - SPR LOLE CLO CEILB; lia. }
        assert (PE02 : rpres_except (fun a => lo <= a < bv_unsigned sp) m m2x).
        { eapply rpres_except_trans; [exact PE01|]. apply (rpres_except_of_munch_cov _ _ m1 m2x MU2 WM2). cbn [ivs_covered]. split; [| exact I]. intros x Hx. clear - Hx SPR LOLE CLO CEILB; lia. }
        assert (FR2x : rw_cells rsegs m2x (bv_unsigned sp + -64) (rr_frame s6 s5 s4 s3 s2 s1 s0 ra)).
        { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. clear - SPR CLO LOLE CEILB. lia. }
        pose proof (p0_avoids_windows _ _ AVD) as DRn. ceil_facts.
        pose proof (move_raw_facts (r_base rg) on dst nn m2x R0 ltac:(clear - F1; lia) LT D0 RC DC' ltac:(clear - DRn; lia))
          as (H2a & H2b & H2c & MIr & RWr).
        eapply (Bridge.sr_evt node rsegs (at_node rsegs) nstep nexit minv nsafe (nodes_sound rsegs)); [exact MFx| |].
        { eapply evt_cut; [apply rrealloc_mm_ret|]. cbv beta. intros ms1 ->.
          eapply (rrealloc_mm_finish gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra sp s LB LB0 lo st k A sz old m m2x (mremap_move_raw (r_base rg) on dst nn m2x) g rg off n dst
                    CLO' ltac:(clear - LOLE; lia) PERM Hst BL AR HIN O0 OA SL SC63 Hrg ltac:(unfold MMAP_THRESHOLD; clear - NT Hn; lia) CELLS PE02 MR2x ltac:(rewrite Hst; exact OKc));
            [exact H2a| exact H2b| exact H2c| apply MIr; exact MI2x| apply RWr; [exact FR2x| ceil_facts; clear - SPR CLO LOLE CEILB; lia]| exact ST2| unfold rrmm_at; do 17 eexists; reflexivity]. }
        intros msf POST. apply sr_done. exact (FINPOST dst msf OWN' POST).
Qed.

Theorem P0_realloc_contract {HGW : HasGuard} {HCEIL : HasCeiling} : realloc_contract_at AI_P0 (al_realloc_pc (ai_L rsegs AI_P0)).
Proof.
  intros ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB k A sz n lo B old errv
         HR HIN CELLS HE HB ST CLO LOLE ERR MI Ha0 Ha1 Hn.
  cbn [ai_L AI_P0 P0L al_realloc_pc al_tp al_stack al_errno RENV] in *.
  destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [LT|GE].
  - eapply P0_realloc_contract_basic; eassumption || exact LT.
  - eapply P0_realloc_contract_mm; eassumption || exact GE.
Qed.

Definition AC_P0 {HGW : HasGuard} {HCEIL : HasCeiling} : alloc_contracts AI_P0 :=
  mkAC rsegs AI_P0 P0_malloc_contract P0_free_contract P0_free_null_contract P0_realloc_contract P0_realloc_null_contract.
