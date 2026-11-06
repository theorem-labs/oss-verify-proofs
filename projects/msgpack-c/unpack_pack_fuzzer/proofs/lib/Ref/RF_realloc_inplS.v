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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Arith MI_Inv MI_Read MI_Geom MI_Pres2 MI_Cnt MI_WFree MI_WGroup Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog ProgR A_Realloc A_Realloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_free_spec RRealloc_iface RF_realloc_inpl.

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

Lemma nodup_slot_unique (LB0 : list block) (b b' : block) :
  List.NoDup (map blk_slot LB0) -> In b LB0 -> In b' LB0 -> blk_slot b' = blk_slot b -> b' = b.
Proof.
  intros ND Hb Hb' EQ. induction LB0 as [|x l IH]; [destruct Hb|].
  cbn in ND. inversion ND as [|x' l' NI ND']; subst.
  destruct Hb as [->|Hb]; destruct Hb' as [->|Hb']; [reflexivity| | | exact (IH ND' Hb Hb')].
  - exfalso. apply NI. rewrite <- EQ. apply in_map. exact Hb'.
  - exfalso. apply NI. rewrite EQ. apply in_map. exact Hb.
Qed.

Section ARM.
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

Lemma arm_cc : conc st c = r_base r + snd c.
Proof. apply conc_region'. rewrite FC. exact Hr. Qed.

Lemma inpl_arm : forall (t1v y7 a2v a4v a5v a7v y28 : word),
  n <= E - A -> n < MMAP_THRESHOLD -> m_sizeclass mr <= size_to_class n + 1 ->
  evt rsegs (POST (Some p) s)
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) t1v y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) a2v
               (Z_to_bv 64 (m_sizeclass mr)) a4v a5v (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x49dd8) fc None m1 (seg_rom rsegs)).
Proof.
  intros t1v y7 a2v a4v a5v a7v y28 NAV NTH SCL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil.
  pose proof arm_cc as CC.
  assert (Sc : snd c = snd bg + UNIT + stride * idx) by (rewrite Ec; reflexivity).
  pose proof (size_to_class_ok n ltac:(unfold MMAP_THRESHOLD in *; lia)) as (SCR & _).
  assert (SC48 : m_sizeclass mr < 48) by (destruct (Z.lt_ge_cases (m_sizeclass mr) 48) as [X|X]; [exact X| pose proof (SC63 X); lia]). specialize (SSTR SC48).
  assert (SK0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SK1 : stride * (idx + 1) = stride * idx + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  rewrite SK1 in SPAN. unfold UNIT, IB in *.
  assert (HE : E = r_base r + snd c + stride - 4) by (subst E Bg; rewrite CB, Sc, Z.mul_add_distr_l, Z.mul_1_r; unfold UNIT, IB; lia). clearbody E.
  assert (HAE : A = r_base r + snd c + 16 * off) by (rewrite HA, CC; unfold UNIT; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - SPAN SK0 S16 B0; lia)) as DRr.
  assert (AIMG0 : A + old <= 0x10000 \/ 0x88000 <= A) by (clear - DRr HAE HE FIT Hoff HO SPAN Sc SK0 B0 RUP; lia).
  assert (HK0 : 0 <= Z.min old n <= old) by (clear - HO HN; lia).
  destruct (SH _ _ Hr Kr) as [WRr RDr].
  pose proof (realloc_ticks _ _ _ AR) as TK.
  pose proof (realloc_nogrp ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM) as NOGRP. fold mr in NOGRP. fold stride in NOGRP.
  lazymatch type of K3 with known _ _ ?v => set (b3 := v) in K3 end.
  assert (B3K : Z.land b3 31 = idx).
  { subst b3. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
    lazymatch goal with |- context [Z.min ?a 5] => destruct (Z.min_spec a 5) as [[X1 X2]|[X1 X2]]; rewrite X2 end.
    all: clear - FIT Hoff HO Hidx X1 LI; Z.div_mod_to_equations; lia. }
  destruct (RDr (snd c + 16 * off - 3) b3 ltac:(lia) ltac:(rewrite <- FC; exact K3)) as [BK B3R].
  replace (r_base r + (snd c + 16 * off - 3)) with (A - 3) in BK by lia.
  assert (WRs : wr_at rsegs m1 (A - 3) (E - A + 3)).
  { eapply wr_at_sub; [exact WRr| lia| lia]. }
  assert (FR' : rw_cells rsegs m1 (bv_unsigned (Z_to_bv 64 sp1)) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { rewrite unsigned_lit by (subst sp1; lia). exact FR. }

  eapply evt_mono.
  { apply (inpl_798 ra (Z_to_bv 64 sp1) gp tp s7 s8 s9 s10 s11 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 F fc m1 A n E b3);
      rewrite ?unsigned_lit by (subst sp1; lia); try exact FR; try exact WRs; try exact BK; try exact MI1; unfold UNIT, IB in *; try lia. }

  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m' & -> & EM & MI' & FR2).
  rewrite unsigned_lit in FR2 |- * by (subst sp1; lia).
  replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; lia); subst sp1; lia).

  set (C := fun a : Z => ((lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) \/ (a = A - 3 \/ A + n <= a < E)).
  assert (PE : rpres_except C m m').
  { rewrite EM. unfold rinplace_mem. cbv zeta.
    assert (P1 : rpres_except C m m1) by (eapply rpres_except_mono; [exact PRES1| intros a Ha; subst C; cbv beta in *; clear - Ha; tauto]).
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    set (rr := E - A - n) in *.
    set (m3 := if rr =? 0 then _ else _).
    assert (P3 : rpres_except C m m3).
    { subst m3. destruct (Z.eqb_spec rr 0); [exact P1|]. apply rpres_write; [exact P1| lia| cbn; lia| cbn; intros; subst C; cbv beta in *; lia]. }
    clearbody m3.
    set (m4 := if 5 <=? rr then _ else _).
    assert (P4 : rpres_except C m (fst m4) /\ 0 <= snd m4 <= 5).
    { subst m4. destruct (Z.leb_spec 5 rr); cbn [fst snd].
      - split; [|lia]. apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros; subst C; cbv beta in *; lia].
        apply rpres_write; [exact P3| lia| cbn; lia| cbn; intros; subst C; cbv beta in *; lia].
      - split; [exact P3| lia]. }
    clearbody m4. destruct m4 as [m4 r']. cbn [fst snd] in P4 |- *. destruct P4 as [P4 _].
    apply rpres_write; [exact P4| lia| cbn; lia| cbn; intros; subst C; cbv beta in *; lia]. }

  assert (NCstk : forall a, bv_unsigned sp <= a -> ~ C a) by (intros a Ha [[X|X]|X]; unfold RERRNO in *; lia).
  assert (NCimg : forall a, a < 0x88000 -> 0x10000 <= a -> ~ (RERRNO <= a < RERRNO + 4) -> ~ C a) by (intros a Ha Hb He [[X|X]|X]; unfold UNIT, IB in *; lia).
  assert (NCblk : forall b' a, In b' (lb_remove p LB) -> blk_addr b' <= a < blk_addr b' + blk_size b' -> ~ C a).
  { intros b' a Hb' Hab [[X|X]|X].
    -
      unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' _].
      assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
      destruct (RHEAP_block_range_proof s LB0 m1 b' ltac:(exists st, LB0; split; [apply Permutation_refl|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]) Hb0) as (_ & _ & _ & BC' & _).
      pose_ceil. lia.
    -
      unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' _].
      assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
      destruct (RHEAP_block_range_proof s LB0 m1 b' ltac:(exists st, LB0; split; [apply Permutation_refl|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]) Hb0) as (_ & _ & _ & BC' & BI').
      unfold RERRNO in X. clear - X Hab BI'. lia.
    - unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' NEQ].
      assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
      assert (NE : blk_slot b' <> c).
      { intros EQ. pose proof (nodup_slot_unique LB0 (p, A, old) b' (realloc_nodup _ _ _ AR) Hin0 Hb0 EQ) as ->.
        unfold bptr_eqb, blk_id in NEQ. cbn [fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. discriminate. }
      exact (realloc_slot_private ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM b' Hb0 NE a ltac:(cbv delta [MR]; rewrite CC; unfold UNIT, IB; generalize X HAE HE Hoff HN NAV; clear; cbv delta [stride mr]; intros; match goal with |- ?G => idtac G end; lia) Hab). }

  assert (PE1 : rpres_except (fun a => a = A - 3 \/ A + n <= a < E) m1 m').
  { rewrite EM. unfold rinplace_mem. cbv zeta. set (rr := E - A - n) in *.
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    set (m3 := if rr =? 0 then _ else _).
    assert (P3 : rpres_except (fun a => a = A - 3 \/ A + n <= a < E) m1 m3).
    { subst m3. destruct (Z.eqb_spec rr 0); [apply rpres_except_refl|]. apply rpres_write; [apply rpres_except_refl| lia| cbn; lia| cbn; intros; lia]. }
    clearbody m3.
    set (m4 := if 5 <=? rr then _ else _).
    assert (P4 : rpres_except (fun a => a = A - 3 \/ A + n <= a < E) m1 (fst m4) /\ 0 <= snd m4 <= 5).
    { subst m4. destruct (Z.leb_spec 5 rr); cbn [fst snd].
      - split; [|lia]. apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros; lia].
        apply rpres_write; [exact P3| lia| cbn; lia| cbn; intros; lia].
      - split; [exact P3| lia]. }
    clearbody m4. destruct m4 as [m4 r']. cbn [fst snd] in P4 |- *. destruct P4 as [P4 _].
    apply rpres_write; [exact P4| lia| cbn; lia| cbn; intros; lia]. }
  assert (ST' : stk rsegs m' lo sp1) by (eapply rpres_except_stk; [exact PE1| exact ST1| cbv beta; intros; lia]).
  release_frame FR2 ST' (bv_unsigned sp).
  assert (ETP : bv_unsigned tp + -164 = 422892) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (ERR' : rw_cells rsegs m' (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR1|]. rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros. lia. }
  assert (AUX' : rauxv_ok m' B).
  { eapply rauxv_ok_pres_B; [exact AUX1| exact PE1| cbv beta; intros; lia| cbv beta; unfold RAUXV_CELL, RLIBC; intros; lia]. }

  pose proof (areach_realloc_inplace ref_reserved st LB0 p A old n off AR Hin0 HN HA) as ARI.
  assert (RC : realloc_case (strip st) (fst p) A n = RcInPlace).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). fold c. rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_end rg_g rg_idx rg_stride rg_start].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    replace (n <=? conc st c + stride - IB - A) with true by (symmetry; apply Z.leb_le; rewrite CC; unfold IB; lia).
    replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  specialize (ARI RC).
  destruct (rinplace_mrep st m1 g bg r idx n off b3 RMR TK Hr Kr B0 ltac:(lia) ltac:(change (get_meta_rec st g) with mr; fold stride; lia)
              ltac:(change (get_meta_rec st g) with mr; fold stride; lia) ltac:(exact NOGRP) ltac:(lia) ltac:(lia)
              ltac:(change (get_meta_rec st g) with mr; fold stride; lia) ltac:(change (get_meta_rec st g) with mr; fold stride; lia)
              ltac:(change (get_meta_rec st g) with mr; fold stride; rewrite <- Ec; exact SL) B3K) as [RMR' TK'].
  change (get_meta_rec st g) with mr in RMR'. fold stride in RMR'. change (16) with UNIT in RMR' at 1. rewrite <- Ec in RMR', TK'.
  replace (conc st bg + 16 + stride * idx + 16 * off) with A in RMR' by (fold Bg; rewrite CB, HAE, Sc; lia).
  replace (conc st bg + 16 + stride * idx + stride - 4) with E in RMR' by (fold Bg; rewrite CB, HE, Sc; lia).
  rewrite <- EM in RMR'.

  pose proof (realloc_nodup _ _ _ AR) as ND0.
  assert (PERM' : Permutation (rLB' LB0 p n A) ((p, A, n) :: lb_remove p LB)).
  { unfold rLB'. apply perm_skip. rewrite (lb_remove_lbrm LB p A old (NoDup_map_perm blk_slot LB0 LB PERM ND0) ltac:(eapply Permutation_in; [exact PERM| exact Hin0])).
    unfold lbrm. cbn [blk_slot fst]. fold c. apply filter_Permutation. exact PERM. }

  set (k := Z.to_nat (Z.min old n)).
  assert (OLDk : bytes_at rsegs m A (firstn k oldbs)).
  { rewrite <- (firstn_skipn k oldbs) in OLDB. apply bytes_at_app in OLDB as [X _]. exact X. }
  assert (LK : length (firstn k oldbs) = k) by (rewrite length_firstn; subst k; lia).
  assert (OLDk' : bytes_at rsegs m' A (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PE| exact OLDk|]. rewrite LK. intros a Ha [[X|X]|[X|X]]; subst k; unfold RERRNO in *; first [clear - Ha X AIMG0 HK0; lia| lia]. }
  assert (WRn : wr_at rsegs m' A n) by (eapply rpres_except_wr_at; [exact PE1| eapply wr_at_sub; [exact WRs| lia| lia]| cbv beta; intros; lia]).
  destruct (rwr_at_bytes_exist m' (A + Z.of_nat k) (n - Z.of_nat k) ltac:(eapply wr_at_sub; [exact WRn| lia| lia]) ltac:(subst k; lia) ltac:(subst k; lia)) as (junk & LJ & BJ).
  assert (BLK : rw_cells rsegs m' A [Cells.CB (Z.to_nat n) (firstn k oldbs ++ junk)]).
  { split; [split|].
    - cbn. split; [| exact I]. rewrite length_app, LK, LJ. subst k. lia.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OLDk'|]. rewrite LK. exact BJ.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WRn. }

  unfold POST, rrealloc_post. do 15 eexists. exists m', errv. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { intros a Ha. apply (proj1 (PE a ltac:(unfold RAUXV_CELL in Ha; lia) ltac:(apply NCimg; unfold RAUXV_CELL, RLIBC, RERRNO in *; lia))). }
  split. { intros a Ha HCa. apply PE; [exact Ha|]. destruct HCa as [X|[[X NS]|(b' & Hb' & Hab)]]; [apply NCstk; exact X| apply NCimg; unfold ralloc_static, RERRNO in *; clear -X NS; lia| exact (NCblk b' a Hb' Hab)]. }
  split; [reflexivity|]. split; [reflexivity|].
  exists A, junk.
  split; [reflexivity|].
  assert (AL16 : A mod 16 = 0).
  { assert (X1 : (stride * idx) mod 16 = 0) by (rewrite Z.mul_mod, SMOD, Z.mul_0_l by lia; reflexivity).
    rewrite HAE, Sc. set (si := stride * idx) in *. clearbody si. clear - RBAL BG16 X1. Z.div_mod_to_equations. lia. }
  split. { unfold rblock_range. pose_ceil. repeat split; lia. }
  split.
  { exists (inplace_full st c off n), (rLB' LB0 p n A). split; [exact PERM'|]. split; [rewrite strip_inplace_full; exact Hst|]. split; [exact RMR'|].
    split; [| exact ARI].
    unfold brk_link in HBL |- *. change (ctx (inplace_full st c off n)) with (s_ctx (inplace_full st c off n)).
    rewrite <- (s_ctx_strip (inplace_full st c off n)), strip_inplace_full, s_ctx_strip. change (s_ctx st) with (ctx st).
    destruct (c_brk (ctx st)) as [| |brid boff]; [exact HBL| exact HBL|].
    unfold conc, get_region in HBL |- *. rewrite <- (s_regions_strip (inplace_full st c off n)), strip_inplace_full, s_regions_strip. exact HBL. }
  exact BLK.
Qed.

Lemma inpl_armB : forall (t1v y7 a2v a4v a5v a7v y28 : word),
  n <= E - A -> n < MMAP_THRESHOLD -> m_sizeclass mr <= size_to_class n + 1 ->
  implM rsegs (realloc_body p A n (ps_m s)) s POST
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) t1v y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) a2v
               (Z_to_bv 64 (m_sizeclass mr)) a4v a5v (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x49dd8) fc None m1 (seg_rom rsegs)).
Proof.
  intros t1v y7 a2v a4v a5v a7v y28 NAV NTH SCL.
  pose proof arm_cc as CC.
  assert (RC : realloc_case (strip st) (fst p) A n = RcInPlace).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). fold c. rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_end rg_g rg_idx rg_stride rg_start].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    replace (n <=? conc st c + stride - IB - A) with true.
    2:{ symmetry. apply Z.leb_le. subst E Bg. rewrite CB, Z.mul_add_distr_l, Z.mul_1_r in NAV. rewrite CC, Ec. cbn [snd]. unfold UNIT, IB in *. clear - NAV. lia. }
    replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  unfold realloc_body. rewrite <- Hst, RC. apply implM_ret. apply inpl_arm; assumption.
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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Cnt OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WGroup OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Realloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ProgR OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc2.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_A.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_free_spec.TwinB RRealloc_iface.TwinB RF_realloc_inpl.TwinB.

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

Lemma nodup_slot_unique (LB0 : list block) (b b' : block) :
  List.NoDup (map blk_slot LB0) -> In b LB0 -> In b' LB0 -> blk_slot b' = blk_slot b -> b' = b.
Proof.
  intros ND Hb Hb' EQ. induction LB0 as [|x l IH]; [destruct Hb|].
  cbn in ND. inversion ND as [|x' l' NI ND']; subst.
  destruct Hb as [->|Hb]; destruct Hb' as [->|Hb']; [reflexivity| | | exact (IH ND' Hb Hb')].
  - exfalso. apply NI. rewrite <- EQ. apply in_map. exact Hb'.
  - exfalso. apply NI. rewrite EQ. apply in_map. exact Hb.
Qed.

Section ARM.
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

Lemma arm_cc : conc st c = r_base r + snd c.
Proof. apply conc_region'. rewrite FC. exact Hr. Qed.

Lemma inpl_arm : forall (t1v y7 a2v a4v a5v a7v y28 : word),
  n <= E - A -> n < MMAP_THRESHOLD -> m_sizeclass mr <= size_to_class n + 1 ->
  evt rsegs (POST (Some p) s)
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) t1v y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) a2v
               (Z_to_bv 64 (m_sizeclass mr)) a4v a5v (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x4b5dc) fc None m1 (seg_rom rsegs)).
Proof.
  intros t1v y7 a2v a4v a5v a7v y28 NAV NTH SCL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil.
  pose proof arm_cc as CC.
  assert (Sc : snd c = snd bg + UNIT + stride * idx) by (rewrite Ec; reflexivity).
  pose proof (size_to_class_ok n ltac:(unfold MMAP_THRESHOLD in *; lia)) as (SCR & _).
  assert (SC48 : m_sizeclass mr < 48) by (destruct (Z.lt_ge_cases (m_sizeclass mr) 48) as [X|X]; [exact X| pose proof (SC63 X); lia]). specialize (SSTR SC48).
  assert (SK0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SK1 : stride * (idx + 1) = stride * idx + stride) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; reflexivity).
  rewrite SK1 in SPAN. unfold UNIT, IB in *.
  assert (HE : E = r_base r + snd c + stride - 4) by (subst E Bg; rewrite CB, Sc, Z.mul_add_distr_l, Z.mul_1_r; unfold UNIT, IB; lia). clearbody E.
  assert (HAE : A = r_base r + snd c + 16 * off) by (rewrite HA, CC; unfold UNIT; lia).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - SPAN SK0 S16 B0; lia)) as DRr.
  assert (AIMG0 : A + old <= 0x10000 \/ 0x8a000 <= A) by (clear - DRr HAE HE FIT Hoff HO SPAN Sc SK0 B0 RUP; lia).
  assert (HK0 : 0 <= Z.min old n <= old) by (clear - HO HN; lia).
  destruct (SH _ _ Hr Kr) as [WRr RDr].
  pose proof (realloc_ticks _ _ _ AR) as TK.
  pose proof (realloc_nogrp ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM) as NOGRP. fold mr in NOGRP. fold stride in NOGRP.
  lazymatch type of K3 with known _ _ ?v => set (b3 := v) in K3 end.
  assert (B3K : Z.land b3 31 = idx).
  { subst b3. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
    lazymatch goal with |- context [Z.min ?a 5] => destruct (Z.min_spec a 5) as [[X1 X2]|[X1 X2]]; rewrite X2 end.
    all: clear - FIT Hoff HO Hidx X1 LI; Z.div_mod_to_equations; lia. }
  destruct (RDr (snd c + 16 * off - 3) b3 ltac:(lia) ltac:(rewrite <- FC; exact K3)) as [BK B3R].
  replace (r_base r + (snd c + 16 * off - 3)) with (A - 3) in BK by lia.
  assert (WRs : wr_at rsegs m1 (A - 3) (E - A + 3)).
  { eapply wr_at_sub; [exact WRr| lia| lia]. }
  assert (FR' : rw_cells rsegs m1 (bv_unsigned (Z_to_bv 64 sp1)) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { rewrite unsigned_lit by (subst sp1; lia). exact FR. }

  eapply evt_mono.
  { apply (inpl_798 ra (Z_to_bv 64 sp1) gp tp s7 s8 s9 s10 s11 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 F fc m1 A n E b3);
      rewrite ?unsigned_lit by (subst sp1; lia); try exact FR; try exact WRs; try exact BK; try exact MI1; unfold UNIT, IB in *; try lia. }

  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m' & -> & EM & MI' & FR2).
  rewrite unsigned_lit in FR2 |- * by (subst sp1; lia).
  replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; lia); subst sp1; lia).

  set (C := fun a : Z => ((lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) \/ (a = A - 3 \/ A + n <= a < E)).
  assert (PE : rpres_except C m m').
  { rewrite EM. unfold rinplace_mem. cbv zeta.
    assert (P1 : rpres_except C m m1) by (eapply rpres_except_mono; [exact PRES1| intros a Ha; subst C; cbv beta in *; clear - Ha; tauto]).
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    set (rr := E - A - n) in *.
    set (m3 := if rr =? 0 then _ else _).
    assert (P3 : rpres_except C m m3).
    { subst m3. destruct (Z.eqb_spec rr 0); [exact P1|]. apply rpres_write; [exact P1| lia| cbn; lia| cbn; intros; subst C; cbv beta in *; lia]. }
    clearbody m3.
    set (m4 := if 5 <=? rr then _ else _).
    assert (P4 : rpres_except C m (fst m4) /\ 0 <= snd m4 <= 5).
    { subst m4. destruct (Z.leb_spec 5 rr); cbn [fst snd].
      - split; [|lia]. apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros; subst C; cbv beta in *; lia].
        apply rpres_write; [exact P3| lia| cbn; lia| cbn; intros; subst C; cbv beta in *; lia].
      - split; [exact P3| lia]. }
    clearbody m4. destruct m4 as [m4 r']. cbn [fst snd] in P4 |- *. destruct P4 as [P4 _].
    apply rpres_write; [exact P4| lia| cbn; lia| cbn; intros; subst C; cbv beta in *; lia]. }

  assert (NCstk : forall a, bv_unsigned sp <= a -> ~ C a) by (intros a Ha [[X|X]|X]; unfold RERRNO in *; lia).
  assert (NCimg : forall a, a < 0x8a000 -> 0x10000 <= a -> ~ (RERRNO <= a < RERRNO + 4) -> ~ C a) by (intros a Ha Hb He [[X|X]|X]; unfold UNIT, IB in *; lia).
  assert (NCblk : forall b' a, In b' (lb_remove p LB) -> blk_addr b' <= a < blk_addr b' + blk_size b' -> ~ C a).
  { intros b' a Hb' Hab [[X|X]|X].
    -
      unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' _].
      assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
      destruct (RHEAP_block_range_proof s LB0 m1 b' ltac:(exists st, LB0; split; [apply Permutation_refl|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]) Hb0) as (_ & _ & _ & BC' & _).
      pose_ceil. lia.
    -
      unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' _].
      assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
      destruct (RHEAP_block_range_proof s LB0 m1 b' ltac:(exists st, LB0; split; [apply Permutation_refl|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]) Hb0) as (_ & _ & _ & BC' & BI').
      unfold RERRNO in X. clear - X Hab BI'. lia.
    - unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' NEQ].
      assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
      assert (NE : blk_slot b' <> c).
      { intros EQ. pose proof (nodup_slot_unique LB0 (p, A, old) b' (realloc_nodup _ _ _ AR) Hin0 Hb0 EQ) as ->.
        unfold bptr_eqb, blk_id in NEQ. cbn [fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. discriminate. }
      exact (realloc_slot_private ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM b' Hb0 NE a ltac:(cbv delta [MR]; rewrite CC; unfold UNIT, IB; generalize X HAE HE Hoff HN NAV; clear; cbv delta [stride mr]; intros; match goal with |- ?G => idtac G end; lia) Hab). }

  assert (PE1 : rpres_except (fun a => a = A - 3 \/ A + n <= a < E) m1 m').
  { rewrite EM. unfold rinplace_mem. cbv zeta. set (rr := E - A - n) in *.
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    set (m3 := if rr =? 0 then _ else _).
    assert (P3 : rpres_except (fun a => a = A - 3 \/ A + n <= a < E) m1 m3).
    { subst m3. destruct (Z.eqb_spec rr 0); [apply rpres_except_refl|]. apply rpres_write; [apply rpres_except_refl| lia| cbn; lia| cbn; intros; lia]. }
    clearbody m3.
    set (m4 := if 5 <=? rr then _ else _).
    assert (P4 : rpres_except (fun a => a = A - 3 \/ A + n <= a < E) m1 (fst m4) /\ 0 <= snd m4 <= 5).
    { subst m4. destruct (Z.leb_spec 5 rr); cbn [fst snd].
      - split; [|lia]. apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros; lia].
        apply rpres_write; [exact P3| lia| cbn; lia| cbn; intros; lia].
      - split; [exact P3| lia]. }
    clearbody m4. destruct m4 as [m4 r']. cbn [fst snd] in P4 |- *. destruct P4 as [P4 _].
    apply rpres_write; [exact P4| lia| cbn; lia| cbn; intros; lia]. }
  assert (ST' : stk rsegs m' lo sp1) by (eapply rpres_except_stk; [exact PE1| exact ST1| cbv beta; intros; lia]).
  release_frame FR2 ST' (bv_unsigned sp).
  assert (ETP : bv_unsigned tp + -164 = 429036) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (ERR' : rw_cells rsegs m' (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1| exact ERR1|]. rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros. lia. }
  assert (AUX' : rauxv_ok m' B).
  { eapply rauxv_ok_pres_B; [exact AUX1| exact PE1| cbv beta; intros; lia| cbv beta; unfold RAUXV_CELL, RLIBC; intros; lia]. }

  pose proof (areach_realloc_inplace ref_reserved st LB0 p A old n off AR Hin0 HN HA) as ARI.
  assert (RC : realloc_case (strip st) (fst p) A n = RcInPlace).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). fold c. rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_end rg_g rg_idx rg_stride rg_start].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    replace (n <=? conc st c + stride - IB - A) with true by (symmetry; apply Z.leb_le; rewrite CC; unfold IB; lia).
    replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  specialize (ARI RC).
  destruct (rinplace_mrep st m1 g bg r idx n off b3 RMR TK Hr Kr B0 ltac:(lia) ltac:(change (get_meta_rec st g) with mr; fold stride; lia)
              ltac:(change (get_meta_rec st g) with mr; fold stride; lia) ltac:(exact NOGRP) ltac:(lia) ltac:(lia)
              ltac:(change (get_meta_rec st g) with mr; fold stride; lia) ltac:(change (get_meta_rec st g) with mr; fold stride; lia)
              ltac:(change (get_meta_rec st g) with mr; fold stride; rewrite <- Ec; exact SL) B3K) as [RMR' TK'].
  change (get_meta_rec st g) with mr in RMR'. fold stride in RMR'. change (16) with UNIT in RMR' at 1. rewrite <- Ec in RMR', TK'.
  replace (conc st bg + 16 + stride * idx + 16 * off) with A in RMR' by (fold Bg; rewrite CB, HAE, Sc; lia).
  replace (conc st bg + 16 + stride * idx + stride - 4) with E in RMR' by (fold Bg; rewrite CB, HE, Sc; lia).
  rewrite <- EM in RMR'.

  pose proof (realloc_nodup _ _ _ AR) as ND0.
  assert (PERM' : Permutation (rLB' LB0 p n A) ((p, A, n) :: lb_remove p LB)).
  { unfold rLB'. apply perm_skip. rewrite (lb_remove_lbrm LB p A old (NoDup_map_perm blk_slot LB0 LB PERM ND0) ltac:(eapply Permutation_in; [exact PERM| exact Hin0])).
    unfold lbrm. cbn [blk_slot fst]. fold c. apply filter_Permutation. exact PERM. }

  set (k := Z.to_nat (Z.min old n)).
  assert (OLDk : bytes_at rsegs m A (firstn k oldbs)).
  { rewrite <- (firstn_skipn k oldbs) in OLDB. apply bytes_at_app in OLDB as [X _]. exact X. }
  assert (LK : length (firstn k oldbs) = k) by (rewrite length_firstn; subst k; lia).
  assert (OLDk' : bytes_at rsegs m' A (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PE| exact OLDk|]. rewrite LK. intros a Ha [[X|X]|[X|X]]; subst k; unfold RERRNO in *; first [clear - Ha X AIMG0 HK0; lia| lia]. }
  assert (WRn : wr_at rsegs m' A n) by (eapply rpres_except_wr_at; [exact PE1| eapply wr_at_sub; [exact WRs| lia| lia]| cbv beta; intros; lia]).
  destruct (rwr_at_bytes_exist m' (A + Z.of_nat k) (n - Z.of_nat k) ltac:(eapply wr_at_sub; [exact WRn| lia| lia]) ltac:(subst k; lia) ltac:(subst k; lia)) as (junk & LJ & BJ).
  assert (BLK : rw_cells rsegs m' A [Cells.CB (Z.to_nat n) (firstn k oldbs ++ junk)]).
  { split; [split|].
    - cbn. split; [| exact I]. rewrite length_app, LK, LJ. subst k. lia.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OLDk'|]. rewrite LK. exact BJ.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WRn. }

  unfold POST, rrealloc_post. do 15 eexists. exists m', errv. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { intros a Ha. apply (proj1 (PE a ltac:(unfold RAUXV_CELL in Ha; lia) ltac:(apply NCimg; unfold RAUXV_CELL, RLIBC, RERRNO in *; lia))). }
  split. { intros a Ha HCa. apply PE; [exact Ha|]. destruct HCa as [X|[[X NS]|(b' & Hb' & Hab)]]; [apply NCstk; exact X| apply NCimg; unfold ralloc_static, RERRNO in *; clear -X NS; lia| exact (NCblk b' a Hb' Hab)]. }
  split; [reflexivity|]. split; [reflexivity|].
  exists A, junk.
  split; [reflexivity|].
  assert (AL16 : A mod 16 = 0).
  { assert (X1 : (stride * idx) mod 16 = 0) by (rewrite Z.mul_mod, SMOD, Z.mul_0_l by lia; reflexivity).
    rewrite HAE, Sc. set (si := stride * idx) in *. clearbody si. clear - RBAL BG16 X1. Z.div_mod_to_equations. lia. }
  split. { unfold rblock_range. pose_ceil. repeat split; lia. }
  split.
  { exists (inplace_full st c off n), (rLB' LB0 p n A). split; [exact PERM'|]. split; [rewrite strip_inplace_full; exact Hst|]. split; [exact RMR'|].
    split; [| exact ARI].
    unfold brk_link in HBL |- *. change (ctx (inplace_full st c off n)) with (s_ctx (inplace_full st c off n)).
    rewrite <- (s_ctx_strip (inplace_full st c off n)), strip_inplace_full, s_ctx_strip. change (s_ctx st) with (ctx st).
    destruct (c_brk (ctx st)) as [| |brid boff]; [exact HBL| exact HBL|].
    unfold conc, get_region in HBL |- *. rewrite <- (s_regions_strip (inplace_full st c off n)), strip_inplace_full, s_regions_strip. exact HBL. }
  exact BLK.
Qed.

Lemma inpl_armB : forall (t1v y7 a2v a4v a5v a7v y28 : word),
  n <= E - A -> n < MMAP_THRESHOLD -> m_sizeclass mr <= size_to_class n + 1 ->
  implM rsegs (realloc_body p A n (ps_m s)) s POST
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) t1v y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) a2v
               (Z_to_bv 64 (m_sizeclass mr)) a4v a5v (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x4b5dc) fc None m1 (seg_rom rsegs)).
Proof.
  intros t1v y7 a2v a4v a5v a7v y28 NAV NTH SCL.
  pose proof arm_cc as CC.
  assert (RC : realloc_case (strip st) (fst p) A n = RcInPlace).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). fold c. rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_end rg_g rg_idx rg_stride rg_start].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    replace (n <=? conc st c + stride - IB - A) with true.
    2:{ symmetry. apply Z.leb_le. subst E Bg. rewrite CB, Z.mul_add_distr_l, Z.mul_1_r in NAV. rewrite CC, Ec. cbn [snd]. unfold UNIT, IB in *. clear - NAV. lia. }
    replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  unfold realloc_body. rewrite <- Hst, RC. apply implM_ret. apply inpl_arm; assumption.
Qed.
End ARM.

End CEIL.
End TwinB.
