(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_A MallocBlocks MallocHINV MallocFacts_B MallocFacts_R.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp MallocKit_B MallocKit_B2 F_ntf F_free_K F_free F_free_spec Malloc_ifaceP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMallocTreeX RMallocKit_B RMallocKit_B2 RMalloc_fp RMalloc_iface RMalloc_ifaceP RF_ntf RF_free_K RF_free RF_free_spec RF_malloc_implT RF_memcpy RF_realloc_hdr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation RAREACH := (AREACH_from ref_reserved).
Notation RMFACTS := (@MFACTS_g ref_reserved).

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition rreallocT_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (b : block) (n lo B : Z) (old : list byte) (m : mem)
    (res : mstate * optr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ rmrep (fst res) m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s /\ brk_link_ps (fst res) s'
    /\ match snd res with
       | None => a0 = Z_to_bv 64 0 /\ RAREACH (fst res) LB /\ rheap_pres LB (bv_unsigned sp) m m'
       | Some q => exists (bid : bptr) junk,
           let A := conc (fst res) q in
           let k := Z.min n (blk_size b) in
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RAREACH (fst res) ((bid, A, n) :: lbrm LB b)
           /\ rheap_pres (lbrm LB b) (bv_unsigned sp) m m'
           /\ rw_cells rsegs m' A [CB (Z.to_nat k) (firstn (Z.to_nat k) old); CB (Z.to_nat (n - k)) junk]
       end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_client_write : forall st LB m m' W,
  RAREACH st LB -> rmrep st m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> rmrep st m'.
Proof.
  intros st LB m m' W AR MR MU WM FW.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  eapply (rmrep_transport_unowned st m m' W MR MU WM).
  intros lo hi a Hin Ha RF.
  pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
  destruct (rrepfoot_where st m a MR RF) as [AC AW].
  destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
  - unfold alloc_ceiling in *. lia.
  - unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD, alloc_ceiling in *. lia.
  - destruct (rblock_inside st LB m b MF MR Hb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    + unfold RCTX in R1. lia.
    + unfold RMLOCK in R2. lia.
    + unfold RNEED_LOCKS in R3. lia.
    + unfold RPAGE_SIZE in R4'. lia.
    + destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
      destruct (DJ _ _ _ _ Hra Hr NEr); lia.
    + destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' Hb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
      * pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
    + destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
      * rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (mf_blk_unknown _ _ MF b r Hb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
      * pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
    + unfold RGOT_SSP in R8. lia.
    + unfold RSSP_GUARD in R9. lia.
Qed.

(* [comment removed for export] *)
Lemma rblocks_disjoint st LB m b1 b2 :
  RAREACH st LB -> rmrep st m -> In b1 LB -> In b2 LB -> blk_slot b1 <> blk_slot b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros AR MR I1 I2 NS. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
  - exact (mf_blocks_disjoint _ _ MF b1 b2 I1 I2 EF NS).
  - destruct (rblock_inside st LB m b1 MF MR I1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
    destruct (rblock_inside st LB m b2 MF MR I2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
    pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
    pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
    destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

Lemma lbrm_cons_keep LB (nb b : block) : blk_slot nb <> blk_slot b -> lbrm (nb :: LB) b = nb :: lbrm LB b.
Proof.
  intros NE. unfold lbrm. rewrite filter_cons. rewrite (aptr_eqb_neq _ _ NE).
  destruct (decide _) as [D|D]; [reflexivity| exfalso; apply D; exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MOVE.
Variables (gp tp : word) (s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (lo B : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Lemma rrealloc_move_walk :
  forall (ra sp s0 s1 s2 s3 s4 s5 s6 : word)                                  (* [comment removed for export] *)
         (rax s0x s1x s3x s4x s5x s6x t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)   (* [comment removed for export] *)
         (o m0 m1 : mem) (s : PState) (st0 : mstate) (LB : list block) (b : block) (pf : aptr)
         (n : Z) (old : list byte) (errv : word) (t : N) (OSE : Z),
  let st := set_tick t st0 in
  RAREACH st0 LB -> (s_tick st0 <= t)%N -> rmrep st m1 -> brk_link_ps st0 s -> unk_agree st o m1 ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st0 pf = blk_addr b ->
  bytes_at rsegs m1 (blk_addr b) old -> Z.of_nat (length old) = blk_size b ->
  rauxv_ok m1 B -> bv_unsigned sp <= B ->
  stk rsegs m1 lo (bv_unsigned sp - 64) -> lo <= bv_unsigned sp - 64 - 8192 ->
  rw_cells rsegs m1 (bv_unsigned sp + -64) (rre_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> mem_inv rsegs m1 ->
  rheap_pres LB (bv_unsigned sp) m0 m1 ->
  bv_unsigned a0 = blk_addr b -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  OSE - blk_addr b = blk_size b ->
  rimplTX o (realloc_move st pf n) s
    (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m0)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 OSE) s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x194fc) fc None m1 (seg_rom rsegs)).
Proof.
  intros until OSE. intros st AR TT MR BL UA Hb Hfst Hconc OLD LEN AUXB SB ST SLO FR ERR MI HP0 HA0 HA1 N HOSE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as CLO. unfold alloc_ceiling in CLO.
  assert (AR1 : RAREACH st LB) by (apply areach_tick; [exact AR| exact TT]).
  assert (BL1 : brk_link_ps st s) by exact BL.
  unfold realloc_move.
  eapply rimplTX_bind.
  { (* [comment removed for export] *)
    riprefixTX. unfold rre_frame in FR.
    step. step. step. step.
    apply evt_done. apply rimplTX_xlift.
    eapply (rmalloc_implT _ _ gp tp); first [exact AR1 | exact MR | exact BL1 | exact UA | exact AUXB | exact ERR | exact MI | exact TP | exact HA1 | exact N | idtac].
    - pose proof (bv_unsigned_in_range 64 sp). rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia. exact ST.
    - exact LO.
    - rewrite unsigned_lit by lia. lia. }
  cbv beta. intros [st1 r] s' ms' POST.
  unfold rmallocT_post in POST. cbn [fst snd] in POST.
  destruct POST as (x0 & x1 & x2 & ya0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & errv2 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & HP2 & PE2 & REL2 & BL2 & PSM2 & PSF2 & PSO2 & MLEAF & RES).
  replace (ret_pc (Z_to_bv 64 0x1950c)) with (Z_to_bv 64 0x1950c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite unsigned_lit in ST2, HP2, PE2 by lia.
  (* [comment removed for export] *)
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact HP2| exact FR|]. left. cbn. lia. }
  destruct r as [q|].
  - (* [comment removed for export] *)
    destruct RES as (c & cst & rg & junk & -> & BR & AR2 & Hc & Hrg & Krg & Q16 & QN & UCH).
    set (LB1 := ((c, fresh_off cst c n), conc st1 q, n) :: LB) in *.
    set (Q := conc st1 q) in *.
    pose proof BR as BR'. unfold rblock_range, alloc_ceiling in BR'. destruct BR' as (Q0 & QAL & N0 & QC & QIMG).
    pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR2) as C1.
    pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR2) as MF1.
    assert (HbL1 : In b LB1) by (right; exact Hb).
    assert (HnL1 : In ((c, fresh_off cst c n), Q, n) LB1) by (left; reflexivity).
    (* [comment removed for export] *)
    assert (CONC1 : conc st1 pf = blk_addr b).
    { destruct MLEAF as (ans & o' & FF). rewrite (areach_malloc_keeps_conc st LB n o o' ans st1 (Some q) b pf AR1 ltac:(lia) FF Hb Hfst).
      rewrite <- Hconc. reflexivity. }
    assert (SZ0 : 0 <= blk_size b) by (pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C1) b HbL1) as [_ _ BZ]; exact BZ).
    pose proof (bytes_at_bound _ _ _ _ OLD) as OB. rewrite LEN in OB.
    assert (NSL : forall bx, In bx LB -> c <> blk_slot bx).
    { pose proof (mf_nodup _ _ MF1) as ND. cbn [map LB1 blk_slot fst] in ND. inversion ND; subst.
      intros bx Hbx E. apply H1. rewrite E. apply in_map_iff. exists bx. split; [reflexivity| exact Hbx]. }
    pose proof (NSL b Hb) as NSLOT.
    pose proof (rblocks_disjoint st1 LB1 m2 _ b AR2 MR2 HnL1 HbL1 NSLOT) as DISJ. cbn [blk_addr blk_size fst snd] in DISJ.
    (* [comment removed for export] *)
    assert (OLD2 : bytes_at rsegs m2 (blk_addr b) old).
    { eapply rheap_pres_bytes_at; [exact HP2| exact OLD|]. right; right. exists b. split; [exact Hb|]. lia. }
    (* [comment removed for export] *)
    riprefixTX.
    step. if_cases K; zify_cond K. { exfalso. subst Q. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. rewrite HA0. replace (OSE + - blk_addr b) with (blk_size b) by lia.
    step. subst a1.
    (* [comment removed for export] *)
    set (k := Z.min n (blk_size b)).
    assert (J : forall a2v : word, a2v = Z_to_bv 64 k ->
      rimplTX o (st2 <-- xlift (free st1 (Some pf));; SRet (st2, Some q)) s'
        (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m0)
        (MS (mkR (Z_to_bv 64 0x1950c) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 x1 x2 (Z_to_bv 64 n) a0 (Z_to_bv 64 Q) (Z_to_bv 64 (blk_size b)) a2v y3 y4 y5 y6 y7
                 (Z_to_bv 64 OSE) s3x s4x s5x s6x s7 s8 s9 s10 s11 x3 x4 x5 x6)
            F (Z_to_bv 64 0x19520) fc None m2 (seg_rom rsegs))).
    2:{ unfold mkR in J. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
        - apply evt_done. apply J. unfold k. f_equal. rewrite ?land_ones_small in K by lia. lia.
        - step. apply evt_done. apply J. unfold k. f_equal. rewrite ?land_ones_small in K by lia. lia. }
    intros a2v ->.
    assert (KR : 0 <= k <= n /\ k <= blk_size b) by (unfold k; lia).
    (* [comment removed for export] *)
    pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C1) b HbL1) as [(g & i & bb & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG _].
    destruct (go_region _ _ _ (ci_gmetas _ _ C1 bb g HBg)) as (rb & Hrb & Krb & _).
    assert (Hrpf : s_regions st1 !! fst pf = Some rb) by (rewrite Hfst, <- FB; exact Hrb).
    assert (Epf : pf = aadd (blk_slot b) (UNIT * off)).
    { unfold aadd. apply injective_projections; cbn [fst snd]; [exact Hfst|].
      pose proof (conc_region' st1 pf rb Hrpf) as X1. pose proof (conc_region' st1 (blk_slot b) rb ltac:(rewrite <- FB; exact Hrb)) as X2. lia. }
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB rsegs m2 Q [] (Z.to_nat n) junk [] [Z.to_nat k; Z.to_nat (n - k)] UCH ltac:(cbn; lia)) as UCH2.
    cbn [mk_CB_cells app] in UCH2.
    lazymatch type of UCH2 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in UCH2 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in UCH2. destruct UCH2 as [DST REST]. cbn [cells_size csize Nat.add] in REST.
    rewrite Nat.add_0_r, Z2Nat.id in REST by lia.
    assert (SRC : bytes_at rsegs m2 (bv_unsigned a0) (firstn (Z.to_nat k) old)).
    { rewrite HA0. rewrite <- (firstn_skipn (Z.to_nat k) old) in OLD2. apply (proj1 (bytes_at_app _ _ _ _ _)) in OLD2. destruct OLD2 as [X _]. exact X. }
    assert (LENk : length (firstn (Z.to_nat k) old) = Z.to_nat (bv_unsigned (Z_to_bv 64 k))).
    { rewrite unsigned_lit by lia. rewrite length_firstn. lia. }
    clear UCH OLD2.
    riprefixTX.
    (* [comment removed for export] *)
    step. step. step.
    eapply evt_cut.
    { eapply (memcpy_spec _ _ gp tp); [exact SRC| exact LENk| rewrite ?unsigned_lit by lia; exact DST| rewrite ?unsigned_lit by lia; rewrite HA0; lia| exact MI2]. }
    cbv beta. intros ms3 POSTm. unfold memcpy_post in POSTm.
    destruct POSTm as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & -> & MU3 & WM3 & MI3 & DST3 & SRC3).
    rewrite (unsigned_lit Q), (unsigned_lit k) in MU3 by lia.
    rewrite (unsigned_lit Q), (unsigned_lit k) in DST3 by lia. rewrite HA0 in SRC3.
    replace (ret_pc (Z_to_bv 64 0x1952c)) with (Z_to_bv 64 0x1952c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (DJ3 : forall A len, (A + len <= Q \/ Q + k <= A) -> disjoint_from [(Q, Q + k)] A len) by (intros A len HA; cbn; lia).
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3| apply DJ3; cbn; lia]. }
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -64)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| apply DJ3; lia]. }
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 errv2]).
    { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| apply DJ3; cbn]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. lia. }
    assert (REST3 : rw_cells rsegs m3 (Q + k) [CB (Z.to_nat (n - k)) (firstn (Z.to_nat (n - k)) (skipn (Z.to_nat k) junk))]).
    { eapply rw_cells_transport; [exact REST| exact MU3| exact WM3| apply DJ3; cbn; lia]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (MR3 : rmrep st1 m3).
    { eapply (rmrep_client_write st1 LB1); [exact AR2| exact MR2| exact MU3| exact WM3|].
      constructor; [|constructor]. right; right. exists ((c, fresh_off cst c n), Q, n). split; [exact HnL1|]. cbn. lia. }
    clear FR2 ST2 ERR2 REST DST SRC MI2.
    assert (Ea0 : a0 = Z_to_bv 64 (blk_addr b)) by (rewrite <- HA0; symmetry; apply Z_to_bv_bv_unsigned).
    (* [comment removed for export] *)
    step. step. apply evt_done.
    eapply rimplTX_bind.
    { apply rimplTX_xlift.
      eapply (rimplT_oracle (free st1 (Some pf)) m3 o).
      { exact (areach_free_nopeek st1 LB1 b pf AR2 HbL1 Hfst CONC1). }
      apply rimplT_reach. rewrite Epf.
      eapply (rlibc_free_implT gp tp _ _ _ s3x s4x s5x s6x s7 s8 s9 s10 s11 F fc LB1 lo LO TP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 s' st1 b off errv2 C1 HbL1 O0 OA MR3 MI3);
        [rewrite unsigned_lit by lia; exact ST3| rewrite unsigned_lit by lia; lia| exact ERR3| exact Ea0]. }
    cbv beta. intros st2 s'' ms'' [[-> FE] LEAF].
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MI4 & ST4 & ERR4 & MR4 & PE4 & SHR & BLKR & EB & BRKR).
    rewrite ?unsigned_lit in ST4, PE4 by lia.
    replace (ret_pc (Z_to_bv 64 0x19534)) with (Z_to_bv 64 0x19534 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (LS : lo <= bv_unsigned sp + -64) by lia.
    assert (ELB : lbrm LB1 b = ((c, fresh_off cst c n), Q, n) :: lbrm LB b) by (unfold LB1; apply lbrm_cons_keep; exact NSLOT).
    assert (HnL : In ((c, fresh_off cst c n), Q, n) (lbrm LB1 b)) by (rewrite ELB; left; reflexivity).
    (* [comment removed for export] *)
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. apply (rfp_not_high st1 st2 lo _ m3 MR3 LO LS). cbn in Ha. lia. }
    assert (DST4 : rw_cells rsegs m4 Q [CB (Z.to_nat k) (firstn (Z.to_nat k) old)]).
    { eapply rpres_except_rw_cells; [exact PE4| exact DST3|]. intros a Ha. apply (rfp_not_block st1 st2 LB1 b lo _ m3 C1 MR3 LO BLKR SHR _ a HnL). cbn in Ha |- *. lia. }
    assert (REST4 : rw_cells rsegs m4 (Q + k) [CB (Z.to_nat (n - k)) (firstn (Z.to_nat (n - k)) (skipn (Z.to_nat k) junk))]).
    { eapply rpres_except_rw_cells; [exact PE4| exact REST3|]. intros a Ha. apply (rfp_not_block st1 st2 LB1 b lo _ m3 C1 MR3 LO BLKR SHR _ a HnL). cbn in Ha |- *. lia. }
    apply rimplTX_ret.
    (* [comment removed for export] *)
    step. step. do 10 step.
    release_frame FR4 ST4 (bv_unsigned sp).
    apply evt_done. unfold rreallocT_post. cbn [fst snd]. do 15 eexists. exists m4, errv2.
    split; [reflexivity|]. split; [exact MR4|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|].
    split; [exact (rauxv_ok_free st1 st2 lo _ m3 m4 MR3 LO LS PE4 B AUX3 ltac:(lia))|].
    split; [exact PSM2|]. split; [exact PSF2|]. split; [exact PSO2|].
    split. { unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st1)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
             unfold conc, get_region. rewrite (BRKR brid boff eq_refl). exact BL2. }
    assert (CQ : conc st2 q = Q).
    { unfold Q. apply MallocFacts_inv.conc_same. destruct (BLKR _ HnL) as [r' Hr']. cbn [blk_slot fst] in Hr'. rewrite Hc in Hr'.
      exists r'. split; [apply SHR; exact Hr'| exact Hr']. }
    exists (c, fresh_off cst c n), (firstn (Z.to_nat (n - k)) (skipn (Z.to_nat k) junk)). cbv zeta. rewrite CQ. fold k.
    split; [reflexivity|]. split; [exact BR|].
    split. { rewrite <- ELB. destruct LEAF as (ans & o' & FO). exact (areach_free st1 LB1 b pf m3 o' ans st2 AR2 HbL1 Hfst CONC1 FO). }
    split.
    { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP0| lia| intros bb' Hbb'; unfold lbrm in Hbb'; apply In_filter_iff in Hbb'; destruct Hbb' as [X _]; exact X]|].
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP2| lia| intros bb' Hbb'; unfold lbrm in Hbb'; apply In_filter_iff in Hbb'; destruct Hbb' as [X _]; exact X]|].
      eapply rheap_pres_trans.
      - (* [comment removed for export] *)
        intros a Ha CA. split.
        + apply MU3. cbn. rewrite wa_unsigned by lia.
          destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]]; [lia| lia|].
          unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' Hne'].
          pose proof (rblocks_disjoint st1 LB1 m2 _ blk' AR2 MR2 HnL1 ltac:(right; exact Hin') (NSL blk' Hin')) as DJ'.
          cbn [blk_addr blk_size fst snd] in DJ'. lia.
        + intros W. apply WM3. exact W.
      - eapply rheap_pres_weaken; [apply (rheap_pres_free st1 st2 LB1 b lo _ m3 m4 C1 MR3 LO LS BLKR SHR PE4 (lbrm LB b))| lia| auto].
        intros bb' Hbb'. rewrite ELB. right. exact Hbb'. }
    pose proof (proj2 (rw_cells_app rsegs m4 Q [CB (Z.to_nat k) (firstn (Z.to_nat k) old)] [CB (Z.to_nat (n - k)) (firstn (Z.to_nat (n - k)) (skipn (Z.to_nat k) junk))])) as J2.
    cbn [cells_size csize Nat.add app] in J2. rewrite Nat.add_0_r, Z2Nat.id in J2 by lia. apply J2. split; [exact DST4| exact REST4].
  - (* [comment removed for export] *)
    destruct RES as [-> AR2].
    apply rimplTX_ret.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    do 10 step.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evt_done. unfold rreallocT_post. cbn [fst snd]. do 15 eexists. exists m2, errv2.
    split; [reflexivity|]. split; [exact MR2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|].
    split; [exact PSM2|]. split; [exact PSF2|]. split; [exact PSO2|]. split; [exact BL2|].
    split; [reflexivity|]. split; [exact AR2|].
    eapply rheap_pres_trans; [exact HP0|]. eapply rheap_pres_weaken; [exact HP2| lia| auto].
Qed.
End MOVE.
End RC__1.
