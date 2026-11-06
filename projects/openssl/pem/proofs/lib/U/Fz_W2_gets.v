(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OSSVerify.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OSSVerify.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OSSVerify.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W1_sync Fz_W1_bits Fz_W1_write Fz_W1_read Fz_W1_gets Fz_W1_misc Fz_W3_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Lemma meth_bgets : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) -> rw_cells usegs m (meth + 56) [C8 (wz 0x1835f0)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM.
  - cimg_cell CIMG m (0x2d3fc8 + 56) [C8 (wz 0x1835f0)] H. exact H.
  - cimg_cell CIMG m (0x2d4038 + 56) [C8 (wz 0x1835f0)] H. exact H.
Qed.

Theorem bio_gets_proof : bio_gets_stmt.
Proof.
  unfold bio_gets_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m s LBall LB0 L f K pl BI meth len max off LB lo B bs
         Cst Room Rep OwnLn LnFree LnLen LnCells ArgBio ArgLn ArgSz.
  subst a0 a1 a2. unfold BGETS_STACK in Room.
  destruct Rep as (BM & BB & RP & fl & rrw & padw & nr & nw & OwnBi & NdBlk & MethIs & Head & W1 & FlOk & Tail & Inner).
  destruct Inner as (rmaxw & OwnBb & BbC & OwnBm & OwnRp & OffRg & LenMax & MaxB & Data).
  pose proof Cst as (Heap & ClOwn & (errv & Aux & SpB & Stk & CeilLo & Errno & Inv & TpEq) & Lxs & Latch & Img & GlobTop).
  clear Errno. unfold GLOBALS_TOP in GlobTop.
  pose proof (bv_unsigned_in_range 64 sp) as SpRg. unfold bv_modulus in SpRg. cbn in SpRg.
  ceil_bounds.
  (* where each block of the BIO and the line buffer lies *)
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBi)) as (BiPos & BiAl & _ & BiTop & BiZone).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBb)) as (BbPos & BbAl & _ & BbTop & BbZone).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBm)) as (BmPos & BmAl & _ & BmTop & BmZone).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnRp)) as (RpPos & RpAl & _ & RpTop & RpZone).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnLn)) as (LnPos & LnAl & _ & LnTop & LnZone).
  hide BiZone. hide BbZone. hide BmZone. hide RpZone. hide LnZone.
  assert (MethRg : 65536 <= meth /\ meth mod 8 = 0 /\ meth + 64 <= 3485696)
    by (destruct MethIs as [-> | ->]; unfold M_MEM, M_SECMEM; lia).
  pose proof (meth_bgets m meth Img Inv MethIs) as MethB.
  (* the BIO header in pieces: the flags word is the only one the method writes *)
  unfold bio_head in Head. unfold bio_tail in Tail. unfold bio_w1_cells in W1.
  apply (rw_cells_app usegs m (BI + 40) [C8 (Z_to_bv 64 4294967297)]) in W1 as [InitC W1].
  apply (rw_cells_app usegs m _ [C4 (Z_to_bv 64 fl)]) in W1 as [FlC W1].
  apply (rw_cells_app usegs m _ [C4 rrw; C4 (Z_to_bv 64 4294967295); C4 padw]) in W1 as [MidC PtrC].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FlC, MidC, PtrC.
  replace (BI + 40 + 8) with (BI + 48) in FlC, MidC, PtrC by lia.
  replace (BI + 48 + 4) with (BI + 52) in MidC, PtrC by lia.
  replace (BI + 52 + 12) with (BI + 64) in PtrC by lia.
  apply (proj2 (t_cells_halves usegs m (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in InitC.
  (* the blocks are distinct, so they do not overlap *)
  pose proof NdBlk as Fresh. unfold mbio_blocks in Fresh.
  apply NoDup_cons_iff in Fresh as [BiNew Fresh].
  apply NoDup_cons_iff in Fresh as [BbNew Fresh].
  apply NoDup_cons_iff in Fresh as [BmNew Fresh].
  apply NoDup_cons_iff in Fresh as [RpNew _].
  cbn [In app] in BiNew, BbNew, BmNew, RpNew. unfold mbio_T in LnFree.
  assert (IdBiBb : k_bi K <> k_bb K) by (intro Same; apply BiNew; left; symmetry; exact Same).
  assert (IdBiBm : k_bi K <> k_bm K) by (intro Same; apply BiNew; right; left; symmetry; exact Same).
  assert (IdBiRp : k_bi K <> k_rp K) by (intro Same; apply BiNew; right; right; left; symmetry; exact Same).
  assert (IdBbBm : k_bb K <> k_bm K) by (intro Same; apply BbNew; left; symmetry; exact Same).
  assert (IdBbRp : k_bb K <> k_rp K) by (intro Same; apply BbNew; right; left; symmetry; exact Same).
  assert (IdBmRp : k_bm K <> k_rp K) by (intro Same; apply BmNew; left; symmetry; exact Same).
  assert (IdLnBi : pl <> k_bi K) by (intro Same; apply LnFree; left; exact Same).
  assert (IdLnBb : pl <> k_bb K) by (intro Same; apply LnFree; right; left; exact Same).
  assert (IdLnBm : pl <> k_bm K) by (intro Same; apply LnFree; right; right; left; exact Same).
  assert (IdLnRp : pl <> k_rp K) by (intro Same; apply LnFree; right; right; right; left; exact Same).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBi) (proj1 OwnBb) IdBiBb) as SepBiBb.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBi) (proj1 OwnBm) IdBiBm) as SepBiBm.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBi) (proj1 OwnRp) IdBiRp) as SepBiRp.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBb) (proj1 OwnBm) IdBbBm) as SepBbBm.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBb) (proj1 OwnRp) IdBbRp) as SepBbRp.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnBm) (proj1 OwnRp) IdBmRp) as SepBmRp.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnLn) (proj1 OwnBi) IdLnBi) as SepLnBi.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnLn) (proj1 OwnBb) IdLnBb) as SepLnBb.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnLn) (proj1 OwnBm) IdLnBm) as SepLnBm.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnLn) (proj1 OwnRp) IdLnRp) as SepLnRp.
  hide SepBiBb. hide SepBiBm. hide SepBiRp. hide SepBbBm. hide SepBbRp. hide SepBmRp.
  hide SepLnBi. hide SepLnBb. hide SepLnBm. hide SepLnRp.
  (* three cases: unread data left (A), a data buffer read to its end (B), no data buffer (C) *)
  destruct (k_d K) as [pd|] eqn:KD;
    [ destruct Data as (D & nm & junk & OwnD & MaxPos & BmC & RpC & JunkLen & DCells);
      pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnD)) as (DPos & _ & _ & DTop & DZone); hide DZone;
      assert (IdDBi : pd <> k_bi K) by (intro Same; apply BiNew; right; right; right; left; exact Same);
      assert (IdDLn : pd <> pl) by (intro Same; apply LnFree; right; right; right; right; rewrite Same; reflexivity);
      assert (IdDBm : pd <> k_bm K) by (intro Same; apply BmNew; right; left; exact Same);
      assert (IdDRp : pd <> k_rp K) by (intro Same; apply RpNew; left; exact Same);
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnD) (proj1 OwnBi) IdDBi) as SepDBi;
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnD) (proj1 OwnLn) IdDLn) as SepDLn;
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnD) (proj1 OwnBm) IdDBm) as SepDBm;
      pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Cst (proj1 OwnD) (proj1 OwnRp) IdDRp) as SepDRp;
      hide SepDBi; hide SepDLn; hide SepDBm; hide SepDRp;
      unfold readp_cells in RpC;
      destruct (Z_lt_le_dec off len) as [Ahead|AtEnd];
      [ | replace (len - off) with 0 in RpC by lia ]
    | destruct Data as (MaxZ & BmC & RpC);
      unfold readp_cells in RpC; change (0 - 0) with 0 in RpC;
      assert (AtEnd : len <= off) by lia ].
  (* BIO_gets up to the indirect call of the method's bgets *)
  all: apply climpl_from_evt; unfold FZ_BIO_GETS.
  all: pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (BI + 48, BI + 52); (LB, LB + 256); (RP, RP + 24)] m) as Mu.
  all: pose proof (wmono_refl usegs m) as Wm.
  all: ths; th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat Stk.
  all: do 7 ths.
  all: ths; ubs_if.
  all: do 2 ths; ths; ubs_if.
  all: ths; ths; ubs_if.
  all: do 2 ths; ths; ubs_if.
  all: do 5 (ths; ths; th_if_lit).
  all: do 2 (ths; ths; ubs_if).
  all: do 5 ths.
  (* A: bgets copies a line of k bytes, 1 <= k *)
  1: {
    apply (rw_cells_CB_split_at usegs _ LB 256 bs 255 ltac:(lia)) in LnCells as [OutC SpareC].
    eapply evt_cut.
    { eapply (W1_gets_data_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                lo BI BB BM RP D len max off fl 255 LB rmaxw (Z_to_bv 64 (msec meth)) junk (take 255 bs)).
      all: th_strip_ulit; try first [reflexivity | eassumption | lia].
      - exact (proj1 PtrC).
      - exact (proj1 BbC).
      - rewrite length_take, LnLen. reflexivity.
      - unfold hideP in SepDLn. lia.
      - unfold hideP in SepLnRp. lia.
      - unfold tbox. unfold hideP in SepLnBi, SepDBi, SepBiRp, SepBiBb, SepLnBb, SepBbRp.
        repeat split; lia. }
    intros ms' Ret.
    destruct Ret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & rmaxw' & fl' & k & oj & mR
                     & -> & KRg & MuR & WmR & InvR & StkR & FlOkR & FlR & RpR & OjLen & OjNul & OjC).
    lazymatch type of MuR with munch _ ?mC _ => rename mC into mCall end.
    th_strip_ulit_in MuR. th_strip_ulit_in StkR. unfold readp_cells in RpR.
    eapply (rw_cells_transport usegs _ mCall mR) in Head; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi, SepBiRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in InitC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi, SepBiRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in MidC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi, SepBiRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in PtrC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi, SepBiRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in Tail; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi, SepBiRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in BbC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepBiBb, SepLnBb, SepBbRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in BmC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepBiBm, SepLnBm, SepBmRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in DCells; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepDBi, SepDLn, SepDRp; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in MethB; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in BiZone, LnZone, RpZone; lia].
    eapply (rw_cells_transport usegs _ mCall mR) in SpareC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi, SepLnRp; lia].
    transport_after_call usegs mCall mR MuR WmR.
    clear MuR WmR Inv.
    th_ret_lit. cbv beta delta [mkR].
    (* k > 0: store k as readbytes; readbytes <= size holds, so k is returned *)
    ths. ths.
    rewrite bv_lts_zero_l, (unsigned_lit k) by lia.
    rewrite (proj2 (Z.ltb_lt 0 k)) by lia. rewrite (proj2 (Z.ltb_lt k (2 ^ 63))) by lia.
    cbn [andb negb].
    ths. ths.
    do 3 (ths; ths; th_if_lit).
    do 6 ths.
    do 5 ths.
    th_release FR (bv_unsigned sp).
    ths. ths.
    apply evt_done. cbv beta. apply climpl_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into mFin end.
    assert (NoClamp : v_sltu (Z_to_bv 64 255) (Z_to_bv 64 k) = Z_to_bv 64 0).
    { unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. rewrite (proj2 (Z.ltb_ge 255 k)) by lia. reflexivity. }
    rewrite NoClamp, (unsigned_lit 0), (unsigned_lit k) by lia.
    change (0 + - 0) with 0. rewrite (unsigned_lit 0) by lia. rewrite Z.lor_0_l, (unsigned_lit k), Z.add_0_r, t_swrap_small by lia.
    unfold cpost. exists (Z_to_bv 64 k), mFin, LBall.
    split. { unfold cret. do 14 eexists. reflexivity. }
    split. { lia. }
    split. { apply cgrow_refl. }
    split.
    { eapply (cstate_seg _ s LBall LB0 L m mFin sp sp tp lo B (bv_unsigned sp) Cst Mu Wm InvR).
      - apply Forall_cons; [apply cwin_stack; lia|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact (proj1 OwnBi) | cbn; lia | cbn; lia]|].
        apply Forall_cons; [apply (cwin_block _ _ _ (pl, LB, 256)); [exact (proj1 OwnLn) | cbn; lia | cbn; lia]|].
        apply Forall_cons; [apply (cwin_block _ _ _ (k_rp K, RP, 32)); [exact (proj1 OwnRp) | cbn; lia | cbn; lia]|].
        apply Forall_nil.
      - lia.
      - lia.
      - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BiZone, LnZone, RpZone. lia.
      - exact StkR.
      - lia. }
    split.
    { eapply (cframe_seg _ [] (bv_unsigned sp) s LBall L m s LBall L m _ mFin (cframe_refl _ _ _ _ _ _ _) Mu Wm Heap); [lia |].
      apply Forall_cons; [apply cseg_ok_stack; lia|].
      apply Forall_cons.
      { apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact (proj1 OwnBi) | | cbn; lia | cbn; lia].
        intros b0 _ NotT Same. apply NotT. cbn in Same. rewrite Same. left. left. reflexivity. }
      apply Forall_cons.
      { apply (cseg_ok_block _ _ _ _ _ (pl, LB, 256)); [exact (proj1 OwnLn) | | cbn; lia | cbn; lia].
        intros b0 _ NotT Same. apply NotT. cbn in Same. rewrite Same. right. reflexivity. }
      apply Forall_cons; [| apply Forall_nil].
      apply (cseg_ok_block _ _ _ _ _ (k_rp K, RP, 32)); [exact (proj1 OwnRp) | | cbn; lia | cbn; lia].
      intros b0 _ NotT Same. apply NotT. cbn in Same. rewrite Same. left. right. right. right. left. reflexivity. }
    unfold bio_gets_res. exists k, (oj ++ drop 255 bs).
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split. { rewrite length_app, OjLen, length_drop, LnLen. reflexivity. }
    split.
    { pose proof (proj2 (rw_cells_app usegs mFin LB [CB (Z.to_nat 255) oj] [CB (256 - 255) (drop 255 bs)]) (conj OjC SpareC)) as Whole.
      refine (th_cells_congr _ _ _ _ _ _ _ _ Whole).
      - cbn [cells_bytes cbytes app]. rewrite ?app_nil_r. reflexivity.
      - reflexivity.
      - cbn. split; [| exact I]. rewrite length_app, OjLen, length_drop, LnLen. reflexivity. }
    right. split; [lia|]. split.
    { rewrite nth_error_app1 by (rewrite OjLen; lia). exact OjNul. }
    unfold mbio_rep, mbio_repx. exists BM, BB, RP, fl', rrw, padw, nr, nw.
    split; [exact OwnBi|]. split; [exact NdBlk|]. split; [exact MethIs|]. split; [exact Head|].
    split.
    { unfold bio_w1_cells.
      apply (rw_cells_app usegs mFin (BI + 40) [C8 (Z_to_bv 64 4294967297)]). split.
      { exact (proj1 (t_cells_halves usegs mFin (BI + 40) 1 1 ltac:(lia) ltac:(lia)) InitC). }
      apply (rw_cells_app usegs mFin _ [C4 (Z_to_bv 64 fl')]). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (BI + 40 + 8) with (BI + 48) by lia. split; [exact FlR|].
      apply (rw_cells_app usegs mFin _ [C4 rrw; C4 (Z_to_bv 64 4294967295); C4 padw]). cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
      replace (BI + 48 + 4) with (BI + 52) by lia. replace (BI + 52 + 12) with (BI + 64) by lia. split; [exact MidC | exact PtrC]. }
    split; [exact FlOkR|]. split; [exact Tail|].
    unfold mb_inner. exists rmaxw'.
    split; [exact OwnBb|]. split; [exact BbC|]. split; [exact OwnBm|]. split; [exact OwnRp|].
    split; [lia|]. split; [exact LenMax|]. split; [exact MaxB|].
    rewrite KD. exists D, nm, junk.
    split; [exact OwnD|]. split; [exact MaxPos|]. split; [exact BmC|]. split; [exact RpR|]. split; [exact JunkLen | exact DCells].
  }
  (* B and C: nothing left to read; bgets stores the terminating NUL only and returns 0 *)
  all: destruct bs as [|b0 rest]; [discriminate LnLen|].
  all: apply (rw_cells_CB_split_at usegs _ LB 256 (b0 :: rest) 1 ltac:(lia)) in LnCells as [OutC SpareC].
  all: cbn [take drop] in OutC, SpareC.
  all: assert (OutB : rw_cells usegs _ LB [C1 b0])
         by (refine (th_cells_congr _ _ _ _ _ _ _ _ OutC); [reflexivity | reflexivity | cbn; split; exact I]).
  all: clear OutC.
  all: eapply evt_cut;
    [ eapply (W1_gets_empty_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                lo BI BB BM RP fl 255 LB _ rmaxw (Z_to_bv 64 (msec meth)) b0);
      th_strip_ulit;
      try first [ reflexivity | eassumption | lia
                | exact (proj1 PtrC) | exact (proj1 BbC) | exact (proj1 RpC)
                | unfold tbox; unfold hideP in SepBiRp, SepLnBi; repeat split; lia ]
    | ].
  all: intros ms' Ret.
  all: destruct Ret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & fl' & mR
                        & -> & MuR & WmR & InvR & StkR & FlOkR & FlR & OutR).
  all: lazymatch type of MuR with munch _ ?mC _ => rename mC into mCall end.
  all: th_strip_ulit_in MuR; th_strip_ulit_in StkR.
  all: eapply (rw_cells_transport usegs _ mCall mR) in Head; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in InitC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in MidC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in PtrC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in Tail; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in BbC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepBiBb, SepLnBb; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in BmC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepBiBm, SepLnBm; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in RpC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepBiRp, SepLnRp; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in MethB; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in BiZone, LnZone; lia].
  all: eapply (rw_cells_transport usegs _ mCall mR) in SpareC; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepLnBi; lia].
  1: eapply (rw_cells_transport usegs _ mCall mR) in DCells; [| exact MuR | exact WmR | cbn [disjoint_from]; simpl_sizes; unfold hideP in SepDBi, SepDLn; lia].
  all: transport_after_call usegs mCall mR MuR WmR.
  all: clear MuR WmR Inv.
  all: th_ret_lit; cbv beta delta [mkR].
  (* k = 0: skip readbytes, return 0 *)
  all: ths; ths; th_if_lit.
  all: do 2 (ths; ths; th_if_lit).
  all: ths; ths; th_if_lit.
  all: ths.
  all: do 5 ths.
  all: th_release FR (bv_unsigned sp).
  all: ths; ths.
  all: apply evt_done; cbv beta; apply climpl_done.
  all: lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] => rename mm into mFin end.
  all: unfold cpost; exists (Z_to_bv 64 0), mFin, LBall.
  all: split; [unfold cret; do 14 eexists; reflexivity|].
  all: split; [lia|].
  all: split; [apply cgrow_refl|].
  all: split;
    [ eapply (cstate_seg _ s LBall LB0 L m mFin sp sp tp lo B (bv_unsigned sp) Cst Mu Wm InvR);
      [ apply Forall_cons; [apply cwin_stack; lia|];
        apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact (proj1 OwnBi) | cbn; lia | cbn; lia]|];
        apply Forall_cons; [apply (cwin_block _ _ _ (pl, LB, 256)); [exact (proj1 OwnLn) | cbn; lia | cbn; lia]|];
        apply Forall_cons; [apply (cwin_block _ _ _ (k_rp K, RP, 32)); [exact (proj1 OwnRp) | cbn; lia | cbn; lia]|];
        apply Forall_nil
      | lia | lia
      | cbn [disjoint_from]; unfold LX_FLAGS; unfold hideP in BiZone, LnZone, RpZone; lia
      | exact StkR | lia ]
    | ].
  all: split;
    [ eapply (cframe_seg _ [] (bv_unsigned sp) s LBall L m s LBall L m _ mFin (cframe_refl _ _ _ _ _ _ _) Mu Wm Heap); [lia |];
      apply Forall_cons; [apply cseg_ok_stack; lia|];
      apply Forall_cons;
      [ apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact (proj1 OwnBi) | | cbn; lia | cbn; lia];
        intros b0' _ NotT Same; apply NotT; cbn in Same; rewrite Same; left; left; reflexivity |];
      apply Forall_cons;
      [ apply (cseg_ok_block _ _ _ _ _ (pl, LB, 256)); [exact (proj1 OwnLn) | | cbn; lia | cbn; lia];
        intros b0' _ NotT Same; apply NotT; cbn in Same; rewrite Same; right; reflexivity |];
      apply Forall_cons; [| apply Forall_nil];
      apply (cseg_ok_block _ _ _ _ _ (k_rp K, RP, 32)); [exact (proj1 OwnRp) | | cbn; lia | cbn; lia];
      intros b0' _ NotT Same; apply NotT; cbn in Same; rewrite Same; left; right; right; right; left; reflexivity
    | ].
  all: unfold bio_gets_res; exists 0, (Z_to_bv 8 0 :: rest).
  all: split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
  all: split; [exact LnLen|].
  all: split;
    [ pose proof (proj2 (rw_cells_app usegs mFin LB [C1 (Z_to_bv 8 0)] [CB (256 - 1) rest]) (conj OutR SpareC)) as Whole;
      refine (th_cells_congr _ _ _ _ _ _ _ _ Whole);
      [ cbn [cells_bytes cbytes app]; rewrite ?app_nil_r; reflexivity | reflexivity | split; [exact LnLen | exact I] ]
    | ].
  all: left; split; [reflexivity|]; split; [lia|].
  all: unfold mbio_rep, mbio_repx; exists BM, BB, RP, fl', rrw, padw, nr, nw.
  all: split; [exact OwnBi|]; split; [exact NdBlk|]; split; [exact MethIs|]; split; [exact Head|].
  all: split;
    [ unfold bio_w1_cells;
      apply (rw_cells_app usegs mFin (BI + 40) [C8 (Z_to_bv 64 4294967297)]); split;
      [ exact (proj1 (t_cells_halves usegs mFin (BI + 40) 1 1 ltac:(lia) ltac:(lia)) InitC) |];
      apply (rw_cells_app usegs mFin _ [C4 (Z_to_bv 64 fl')]); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
      replace (BI + 40 + 8) with (BI + 48) by lia; split; [exact FlR|];
      apply (rw_cells_app usegs mFin _ [C4 rrw; C4 (Z_to_bv 64 4294967295); C4 padw]); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
      replace (BI + 48 + 4) with (BI + 52) by lia; replace (BI + 52 + 12) with (BI + 64) by lia; split; [exact MidC | exact PtrC]
    | ].
  all: split; [exact FlOkR|]; split; [exact Tail|].
  all: unfold mb_inner; exists rmaxw.
  all: split; [exact OwnBb|]; split; [exact BbC|]; split; [exact OwnBm|]; split; [exact OwnRp|].
  all: split; [lia|]; split; [exact LenMax|]; split; [exact MaxB|].
  all: rewrite KD.
  - exists D, nm, junk.
    split; [exact OwnD|]. split; [exact MaxPos|]. split; [exact BmC|].
    split; [unfold readp_cells; replace (len - off) with 0 by lia; exact RpC|].
    split; [exact JunkLen | exact DCells].
  - split; [exact MaxZ|]. split; [exact BmC | exact RpC].
Qed.
End WithCeiling0.
