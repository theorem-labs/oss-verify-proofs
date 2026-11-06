(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocKit_A2 Malloc_iface Malloc_ifaceP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_A MallocBlocks MallocHINV MallocFacts_B MallocFacts_Bpres MallocFacts_R MallocFacts_inv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc ReallocKeep MI_Inv MI_Read.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require MI_WRemap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp MallocKit_B MallocKit_B2 F_ntf F_free_K F_free F_free_spec F_malloc_join F_malloc_entry F_mm_syscalls.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMallocTreeX UMallocKit_B UMallocKit_B2 UMallocKit_A2 UMalloc_fp UMalloc_iface UMalloc_ifaceP UF_mremap UMallocRemap UF_malloc_implT UF_realloc_hdr UF_realloc_ip UF_realloc_A UF_realloc_mv UF_realloc_bt UF_realloc UF_realloc_spec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation RAREACH := (AREACH_from ref_reserved).
Notation RMFACTS := (@MFACTS_g ref_reserved).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rptrs_but_of_cinv st LB m rid r g :
  CINV st LB -> rmrep st m ->
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = rid -> b = (rid, 0)) ->
  (forall m' b', m_mem (get_meta_rec st m') = Some b' -> fst b' = rid -> m' = g /\ b' = (rid, 0)) ->
  ptrs_but st rid g.
Proof.
  intros C MR Hr Kr GRP MEM. pose proof (KINV_of_CINV _ _ C) as K.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (ci_mp _ _ C) as (M1 & M2 & M3 & M4 & M5).
  assert (MSr : forall q, meta_slot st q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ci_links _ _ C) as [LN LP LNN LS].
  unfold ptrs_but. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st LB 0 h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st LB 0 sc a K Ha))).
  - destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ci_bk _ _ C brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros q. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP q pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN q nx Hn)).
    + destruct (m_mem (get_meta_rec st q)) as [b'|] eqn:MB; cbn; [| left; exact I].
      destruct (N.eq_dec (fst b') rid) as [E|NE]; [| left; exact NE].
      right. destruct (MEM q b' MB E) as [-> ->]. auto.
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split.
    + destruct (ci_grps _ _ C b gh Hb) as (g' & Hg & _). rewrite Hg. cbn. apply MSr.
      assert (HB : hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
      exact (go_slot _ _ _ (ci_gmetas _ _ C b g' HB)).
    + destruct (N.eq_dec (fst b) rid) as [E|NE]; [right; exact (GRP b gh Hb E)| left; exact NE].
Qed.

(* [comment removed for export] *)
Lemma areach_live_nonempty st LB : RAREACH st LB ->
  forall q rq, (s_regions st) !! q = Some rq -> lr_lo rq < r_base rq + round_up_pg (r_len rq).
Proof.
  intros AR q rq Hq. destruct (areach_inv _ st LB AR) as (L & LS & BL & INV & _).
  pose proof INV as (IR & _). pose proof (ir_shape _ _ _ IR q rq Hq) as (B0 & BAL & L0 & LM & BC & MK).
  pose proof (round_up_pg_ge (r_len rq)). unfold lr_lo.
  destruct (r_kind rq) eqn:EK; try lia.
  destruct (MK ltac:(left; exact EK)) as [_ M2]. unfold PGSZ in M2. lia.
Qed.

Lemma land_pgmask y : 0 <= y < 2^64 -> Z.land y 18446744073709547520 = y / 4096 * 4096.
Proof.
  intros Hy. change 18446744073709547520 with (Z.shiftl (Z.ones 52) 12).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 12).
  - rewrite Z.shiftl_spec_low by lia. rewrite andb_false_r. symmetry.
    replace (y / 4096 * 4096) with (Z.shiftl (y / 4096) 12) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    apply Z.shiftl_spec_low. lia.
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones_nonneg by lia.
    replace (y / 4096 * 4096) with (Z.shiftl (Z.shiftr y 12) 12) by (rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia; reflexivity).
    rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.ltb_spec (i - 12) 52); [rewrite andb_true_r; reflexivity|].
    rewrite andb_false_r. symmetry. destruct (Z.eq_dec y 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma round_up_pg_div x : 0 <= x -> round_up_pg x = (x + 4095) / 4096 * 4096.
Proof. intros. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma meta_word_pg mr : 0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr ->
  meta_word mr / 4096 * 4096 = m_maplen mr * 4096 /\ meta_word mr mod 4096 = m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr.
Proof. intros. unfold meta_word. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma write_same_at (m : mem) A bs (x : word) :
  bytes_at usegs m A bs -> (A + Z.of_nat (length bs) <= 0x10000 \/ 0x57000 <= A) -> write_to_mem m (wa A) bs x = m x.
Proof.
  intros (A0 & A1 & HB) IMG. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
  specialize (HB (Z.to_nat (bv_unsigned x - A)) ltac:(lia)). rewrite <- HB. unfold mrd.
  replace (wa (A + Z.of_nat (Z.to_nat (bv_unsigned x - A)))) with x.
  2:{ unfold wa. replace (A + Z.of_nat (Z.to_nat (bv_unsigned x - A))) with (bv_unsigned x) by lia. symmetry. apply Z_to_bv_bv_unsigned. }
  destruct (m x) eqn:E; [reflexivity|]. rewrite ref_seg_rom_none; [reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_shift (mx my : mem) A A' bs :
  bytes_at usegs mx A bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> my (wa (A' + i)) = mx (wa (A + i))) ->
  0 <= A' -> A' + Z.of_nat (length bs) <= 2^64 ->
  (A + Z.of_nat (length bs) <= 0x10000 \/ 0x57000 <= A) -> (A' + Z.of_nat (length bs) <= 0x10000 \/ 0x57000 <= A') ->
  bytes_at usegs my A' bs.
Proof.
  intros (B0 & B1 & HB) SH A0 A1 I1 I2. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite <- (HB i Hi). unfold mrd. rewrite (SH (Z.of_nat i)) by lia.
  rewrite !ref_seg_rom_none by (rewrite wa_unsigned by lia; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mremap_ok_cases live old osz nsz r :
  mremap_answer_ok live old osz nsz r = true ->
  is_errno_form r = true
  \/ (r = old /\ (nsz < osz \/ (old + nsz <= alloc_ceiling /\ ranges_free live (old + osz) (nsz - osz) = true)))
  \/ (r <> old /\ 0 < r /\ r mod PGSZ = 0 /\ r + nsz <= alloc_ceiling /\ ranges_free live r nsz = true).
Proof.
  intros H. unfold mremap_answer_ok in H.
  destruct (is_errno_form r) eqn:EF; [left; reflexivity| right]. cbn [orb] in H.
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - left. apply Bool.andb_true_iff in H as [E H]. apply Z.eqb_eq in E. split; [exact E|].
    apply Bool.orb_true_iff in H. destruct H as [H|H]; [left; apply Z.ltb_lt; exact H| right].
    apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. auto.
  - right. apply Bool.andb_true_iff in H as [H H5]. apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3].
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. apply Z.leb_le in H4. auto 6.
Qed.

Lemma ctx_wr8 p v st : ctx (wr8 p v st) = ctx st.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rbt_fp (m : mem) G NB ND P E n k mw :
  16 <= P -> 0 <= n -> P + n <= E -> E + 5 <= 2^64 -> 0 <= E - P - n < 2^32 -> 0 <= G -> G + 40 <= 2^64 ->
  E = NB + ND - 4 ->
  let mF := rset_size_mem (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (Z_to_bv 64 NB))) (wa (G + 32)) (le8 (wz mw))) (wa E) [b8 0]) P E n k in
  munch [(G, G + 40); (P - 3, E + 1)] m mF /\ wmono usegs m mF
  /\ (forall A cs, rw_cells usegs m A cs -> P <= A -> A + Z.of_nat (cells_size cs) <= P + n ->
        (A + Z.of_nat (cells_size cs) <= G + 16 \/ G + 40 <= A) -> rw_cells usegs mF A cs).
Proof.
  intros P16 N0 PNE E5 R32 G0 G40 HE mF.
  destruct (rset_size_mem_fp (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (Z_to_bv 64 NB))) (wa (G + 32)) (le8 (wz mw))) (wa E) [b8 0]) P E n k
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (MU3 & WM3 & MID3).
  fold mF in MU3, WM3, MID3.
  split; [| split].
  - eapply munch_trans; [| eapply munch_weaken; [| exact MU3]; intros x; cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| rewrite length_le8; lia| rewrite length_le8; cbn; lia].
    apply munch_write; [apply munch_refl| lia| rewrite length_le8; lia| rewrite length_le8; cbn; lia].
  - eapply wmono_trans; [| exact WM3]. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl.
  - intros A cs HA LA HA2 DG. apply MID3; [| exact LA| exact HA2].
    apply rw_cells_frame; [| lia| cbn; lia| cbn; lia].
    apply rw_cells_frame; [| lia| rewrite length_le8; lia| rewrite length_le8; lia].
    apply rw_cells_frame; [exact HA| lia| rewrite length_le8; lia| rewrite length_le8; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section TAILREP.
Variables (stX : mstate) (mZ : mem) (g : aptr) (rid : N) (rX : region) (NB ND n off k : Z).
Let bm : aptr := (rid, 0).
Let P := NB + 16 + 16 * off.
Let E := NB + ND - 4.
Hypothesis MRZ : rmrep stX mZ.
Hypothesis TKX : ticks_ok stX.
Hypothesis HrX : (s_regions stX) !! rid = Some rX.
Hypothesis KrX : r_kind rX = RKGroup.
Hypothesis BrX : r_base rX = NB.
Hypothesis LrX : round_up_pg (r_len rX) = ND.
Hypothesis LIX : m_last_idx (get_meta_rec stX g) = 0.
Hypothesis MLX : m_maplen (get_meta_rec stX g) * 4096 = ND.
Hypothesis GX : forall b gh, (s_groups stX) !! b = Some gh -> fst b = rid -> b = bm.
Hypothesis ND4096 : 4096 <= ND.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 20 <= ND.
Hypothesis SMALL : ND - 20 - 16 * off - n < 4096.
Hypothesis K31 : 0 <= k /\ Z.land k 31 = 0.

Lemma strideX : get_stride (get_meta_rec stX g) = ND - 16.
Proof.
  unfold get_stride. rewrite LIX. cbn [Z.eqb andb].
  destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g)) 0); [exfalso; lia|]. cbn [negb]. unfold UNIT. lia.
Qed.

Lemma rbig_tail_rep :
  rmrep (fst (realloc_big_tail stX bm (16 * off) 0 ND n)) (rset_size_mem (write_to_mem mZ (wa E) [b8 0]) P E n k)
  /\ ticks_ok (fst (realloc_big_tail stX bm (16 * off) 0 ND n))
  /\ conc (fst (realloc_big_tail stX bm (16 * off) 0 ND n)) (rid, 16 + 16 * off) = P
  /\ snd (realloc_big_tail stX bm (16 * off) 0 ND n) = Some (rid, 16 + 16 * off).
Proof.
  pose proof strideX as SX. destruct K31 as [K0' K31'].
  assert (Ep : aadd bm (UNIT + 16 * off) = (rid, 16 + 16 * off)) by (unfold aadd, bm, UNIT; cbn; f_equal; lia).
  assert (Ee : aadd bm (ND - IB) = (rid, ND - 4)) by (unfold aadd, bm, IB; cbn; f_equal; lia).
  unfold realloc_big_tail. rewrite Ep, Ee. cbn [fst snd].
  set (st2 := wr8 (rid, ND - 4) 0 stX).
  assert (NOGRP : forall b' gh, (s_groups stX) !! b' = Some gh -> fst b' = fst bm ->
            snd b' + 9 <= snd bm + 16 + get_stride (get_meta_rec stX g) * 0 - 4
            \/ snd bm + 16 + get_stride (get_meta_rec stX g) * 0 + get_stride (get_meta_rec stX g) - 4 <= snd b').
  { intros b' gh Hb' Hf. pose proof (GX b' gh Hb' Hf) as ->. cbn. lia. }
  pose proof (rmrep_wr8 stX mZ (rid, ND - 4) 0 rX MRZ TKX HrX KrX ltac:(cbn; rewrite LrX; lia)
                ltac:(intros b' gh Hb' Hf; cbn in Hf |- *; pose proof (GX b' gh Hb' Hf) as ->; cbn; lia) ltac:(lia)) as MR2.
  pose proof (ticks_ok_wr8 stX (rid, ND - 4) 0 TKX) as TK2.
  cbn [snd] in MR2. fold st2 in MR2, TK2. rewrite BrX in MR2.
  replace (NB + (ND - 4)) with E in MR2 by (unfold E; lia).
  assert (SX2 : get_stride (get_meta_rec st2 g) = ND - 16) by exact SX.
  destruct (rset_size_rep st2 (write_to_mem mZ (wa E) [b8 0]) g bm rX 0 n off k MR2 TK2 HrX KrX ltac:(cbn; lia) ltac:(lia)
              ltac:(rewrite SX2, LrX; cbn; lia) ltac:(rewrite SX2; lia)
              ltac:(intros b' gh Hb' Hf; pose proof (GX b' gh Hb' Hf) as ->; rewrite SX2; cbn; lia)
              OFF0 N0 ltac:(rewrite SX2; lia) ltac:(rewrite SX2; lia) K0') as [MR3 TK3].
  cbv zeta in MR3, TK3. rewrite SX2 in MR3, TK3. change (fst bm) with rid in MR3, TK3. change (snd bm) with 0 in MR3, TK3.
  replace (0 + 16 + (ND - 16) * 0 + 16 * off) with (16 + 16 * off) in MR3, TK3 by lia.
  replace (0 + 16 + (ND - 16) * 0 + (ND - 16) - 4) with (ND - 4) in MR3, TK3 by lia.
  assert (CB : conc st2 bm = NB) by (unfold st2; rewrite conc_wr8; unfold bm; rewrite (conc_region stX rid 0 rX HrX), BrX; lia).
  rewrite CB in MR3.
  replace (NB + 16 + (ND - 16) * 0 + 16 * off) with P in MR3 by (unfold P; lia).
  replace (NB + 16 + (ND - 16) * 0 + (ND - 16) - 4) with E in MR3 by (unfold E; lia).
  rewrite (set_size_b3 _ _ n k 0 st2) in MR3, TK3 by (rewrite K31'; reflexivity).
  destruct (rmrep_havoc _ _ (rid, 16 + 16 * off) n MR3 TK3) as [MR4 TK4].
  split; [exact MR4|]. split; [exact TK4|]. split; [| reflexivity].
  rewrite conc_havoc, conc_set_size. unfold st2. rewrite conc_wr8. rewrite (conc_region stX rid _ rX HrX), BrX. unfold P. lia.
Qed.
End TAILREP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section BIG.
Variables (gp tp : word) (s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo B : Z).

Theorem rbig_proof : rbig_stmt gp tp s7 s8 s9 s10 s11 F fc lo B.
Proof.
  cbv beta delta [rbig_stmt].
  intros ra sp s0 s1 s2 s3 s4 s5 s6 a0 a1 t2 t3 t4 t5 t6 o m0 m1 s st0 LB b pf g bm i n old errv off rsv.
  intros st mr stride S P LO TP AR MR1 BL UA Hb Hfst Hconc SL Hmem Fbm OFF0 RSV0 Eslot Epf Ersv SC63 NTH HDREQ OLD1 LEN AUX1 SB ST1 SLO FR1 ERR1 MI1 HP01 A0 A1 N.
  unfold RREALLOC_STACK_MIN in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as CLO. unfold alloc_ceiling in CLO.
  assert (AR1 : RAREACH st LB) by (apply areach_tick; [exact AR| subst st; cbn; lia]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR1) as C1.
  pose proof (ci_ticks _ _ C1) as TK.
  assert (Hconc1 : conc st pf = blk_addr b) by exact Hconc.
  assert (SL1 : s_slots st !! blk_slot b = Some (g, i)) by exact SL.
  pose proof (areach_blk63_alone st LB b pf AR1 Hb Hfst Hconc1 g i SL1 SC63) as B63. cbv zeta in B63.
  destruct B63 as (I0 & ESL & EPF & P16 & HM & LI0 & MLNZ & (rg & Hrg & Krg & EML & EADDR & FITB) & GRPS & BLKS & SLOTS & MEMS).
  fold mr in HM, LI0, MLNZ, EML, FITB.
  set (rid := fst (blk_slot b)) in *.
  assert (Ebm : bm = (rid, 0)) by (rewrite Hmem in HM; injection HM as E; exact E).
  destruct (areach_blk_hdr st LB b pf AR1 Hb Hfst Hconc1 g i SL1) as (bm' & off' & rsv' & q' & Hm' & _ & HOST & _ & Eslot' & _ & Epf' & BSZ0 & Ersv' & _ & _ & _ & _ &
            _ & C3 & _ & _ & _ & _ & CE & UNK & _).
  change (get_meta_rec st g) with mr in Hm', Eslot', Ersv'. fold stride in Eslot', Ersv'. rewrite Hmem in Hm'. injection Hm' as <-.
  assert (off' = off) as -> by (clear -Epf Epf' Eslot Eslot'; unfold UNIT in *; lia).
  assert (rsv' = rsv) as -> by (clear -Ersv Ersv'; lia). clear Eslot' Epf' Ersv'.
  pose proof (ci_gmetas _ _ C1 bm g HOST) as GO.
  pose proof (go_slot _ _ _ GO) as MSL. pose proof (go_li _ _ _ GO) as GLI. pose proof (go_freeable _ _ _ GO) as GFR.
  pose proof (go_maplen _ _ _ GO) as GML. fold mr in GLI, GFR, GML.
  assert (GSC : 0 <= m_sizeclass mr < 64) by (rewrite SC63; lia).
  (* [comment removed for export] *)
  assert (STR : stride = m_maplen mr * 4096 - 16).
  { subst stride. unfold get_stride. rewrite LI0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen mr) 0); [lia|]. cbn [negb]. unfold UNIT. lia. }
  set (osz := m_maplen mr * 4096) in *. set (oldb := r_base rg) in *.
  pose proof MR1 as (WF & _ & GL & _ & _ & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  pose proof (rregion_facts st m1 rid rg MR1 Hrg) as (R4096 & RAL & RC & RI1 & RI2). rewrite <- EML in RC, RI1, RI2. fold oldb in R4096, RAL, RC, RI1, RI2.
  assert (ESPF : snd pf = 16 + 16 * off) by (rewrite Epf, ESL; unfold UNIT; cbn; lia).
  assert (HS : S = oldb + 16) by (subst S; rewrite ESL; unfold rid, oldb; rewrite (conc_region st _ _ rg Hrg); unfold UNIT; lia).
  assert (HP : P = oldb + 16 + 16 * off) by (subst P; rewrite EADDR, ESPF; unfold oldb; lia).
  assert (OSZ16 : 16 + 16 * off + blk_size b + 4 <= osz) by (unfold IB in FITB; rewrite ESPF in FITB; lia).
  unfold alloc_ceiling in RC.
  assert (OI : oldb + osz <= 0x10000 \/ 0x57000 <= oldb) by (pose proof (RI1 ltac:(lia)); pose proof (RI2 ltac:(lia)); lia).
  destruct (meta_word_pg mr ltac:(lia) ltac:(lia) GSC ltac:(lia)) as [MWD MWM].
  assert (MWR : 0 <= meta_word mr < 2^64) by (unfold meta_word; lia).
  set (needed := round_up_pg (n + 16 * off + 20)).
  pose proof (round_up_pg_div (n + 16 * off + 20) ltac:(lia)) as NDV. fold needed in NDV.
  assert (NDR : n + 16 * off + 20 <= needed < n + 16 * off + 20 + 4096 /\ needed mod 4096 = 0) by (rewrite NDV; Z.div_mod_to_equations; lia).
  assert (ECRID : conc st (rid, 0) = oldb) by (rewrite (conc_region st rid 0 rg Hrg); unfold oldb; lia).
  assert (ECBM : conc st bm = oldb) by (rewrite Ebm; exact ECRID).
  assert (HP0 : blk_addr b = oldb + 16 + 16 * off) by (rewrite <- HP; reflexivity).
  destruct (SH rid rg Hrg Krg) as (HW & HBY & HBD). rewrite <- EML in HW, HBY, HBD. fold oldb in HW, HBY.
  pose proof (rmrep_meta_chunk st m1 g MR1 MSL) as CH. unfold meta_cells in CH. change (get_meta_rec st g) with mr in CH.
  (* [comment removed for export] *)
  assert (GDJA : forall q rq, (s_regions st) !! q = Some rq -> r_kind rq = RKGroup ->
                 conc st g + 40 <= r_base rq \/ r_base rq + round_up_pg (r_len rq) <= conc st g).
  { intros q rq Hq Kq. destruct MSL as (ga & gar & gk & Hga & Hgk & Eg).
    destruct (rarea_conc st ga gar WF Hga) as (rga & Hrga & Ca & Sa0 & Sa1 & SaL & NK & _).
    pose proof (rarea_lr_lo st ga gar rga WF Hga Hrga) as LRa.
    assert (NEr : fst ga <> q) by (intros E; rewrite E, Hq in Hrga; inversion Hrga; subst; exact (NK Kq)).
    assert (HG : conc st g = conc st ga + (AREA_HDR + META_SIZE * gk)) by (rewrite Eg, conc_aadd by (rewrite Hrga; eauto); reflexivity).
    pose proof (DISJ _ _ _ _ Hrga Hq NEr) as D. rewrite (lr_lo_group rq Kq) in D.
    clear -D HG LRa Sa1 Hgk Ca. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
  assert (GDJ : conc st g + 40 <= oldb \/ oldb + osz <= conc st g).
  { pose proof (GDJA rid rg Hrg Krg) as D. rewrite <- EML in D. exact D. }
  pose proof (rmeta_slot_bounds st m1 g MR1 MSL) as (GB1 & GB2 & GB3 & _).
  (* [comment removed for export] *)
  assert (TREE : rbig_tree st pf g i n =
      if osz =? needed then SRet (realloc_big_tail st bm (16 * off) i needed n)
      else if PTRDIFF_MAX <=? needed then realloc_move st pf n
      else SVis (XMremap oldb osz needed MREMAP_MAYMOVE) (fun r =>
        if negb (mremap_answer_ok (live_ranges st) oldb osz needed r) then xbad_answer (SRet (st, None))
        else if is_err r then realloc_move st pf n
        else SRet (realloc_big_tail (remap_region rid g r needed st) bm (16 * off) i needed n))).
  { unfold rbig_tree. change (get_meta_rec st g) with mr. fold stride. rewrite Hmem. cbn [default id].
    replace (snd pf - snd (slot_start' mr i)) with (16 * off) by (unfold slot_start'; rewrite Hmem, Ebm, I0; cbn [snd fst aadd default from_option id]; rewrite ESPF; unfold UNIT; lia).
    replace (round_up_pg (n + 16 * off + UNIT + IB)) with needed by (unfold needed, UNIT, IB; f_equal; lia).
    fold osz. rewrite ECBM. replace (fst bm) with rid by (rewrite Ebm; reflexivity). reflexivity. }
  (* [comment removed for export] *)
  unfold rre_frame in FR1.
  riprefixTX.
  (* [comment removed for export] *)
  rewrite A0, A1.
  assert (SR : 0 <= S < 2^64) by (rewrite HS; lia).
  step. step. step. step. step. step. step. step. step.
  rewrite (unsigned_lit S) by exact SR.
  replace (n + 4095 + (blk_addr b + - S) + 20) with (n + 16 * off + 20 + 4095) by (fold P; rewrite HP, HS; lia).
  rewrite (unsigned_lit (n + 16 * off + 20 + 4095)) by lia. rewrite (land_pgmask (n + 16 * off + 20 + 4095)) by lia. rewrite <- NDV.
  unfold wz at 3. rewrite (unsigned_lit (meta_word mr)) by exact MWR. rewrite (land_pgmask (meta_word mr)) by exact MWR. rewrite MWD. fold osz.
  (* [comment removed for export] *)
  step. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold wz at 2. rewrite ECBM.
    step. step. if_cases KF; zify_cond KF. { exfalso. clear -KF R4096 RC GML. lia. }
    apply evt_done.
    (* [comment removed for export] *)
    rewrite TREE. rewrite (proj2 (Z.eqb_eq _ _) KE). apply rimplTX_ret.
    replace (Z_to_bv 64 (blk_addr b + - S) : word) with (Z_to_bv 64 (16 * off) : word) by (f_equal; fold P; rewrite HP, HS; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_bt_walk ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 ra (Z_to_bv 64 (conc st g)) _ s5 s6
               _ _ _ _ _ F fc m1 (conc st g) oldb needed (16 * off) (meta_word mr) n (i + 32 * Z.min rsv 5) lo);
        first [exact MI1| exact FR1| exact ST1| exact CH| idtac].
      - apply unsigned_lit. lia.
      - lia.
      - unfold alloc_ceiling; lia.
      - eapply wr_at_sub; [exact HW| lia| lia].
      - replace (oldb + 16 + 16 * off - 3) with (oldb + (snd pf - 3)) by (rewrite ESPF; lia).
        refine (proj1 (HBY _ _ _ C3)). lia.
      - exact MWR.
      - rewrite I0. pose proof (Z.le_min_l rsv 5). split; [lia|]. assert (Z.min rsv 5 <= 5) by apply Z.le_min_r. lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - apply NDR.
      - lia.
      - lia.
      - unfold alloc_ceiling. lia.
      - lia.
      - unfold alloc_ceiling. lia.
      - lia. }
    cbv beta. intros msf PS. unfold rss_post in PS.
    destruct PS as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & -> & MI2 & ST2).
    set (mZ := write_to_mem (write_to_mem m1 (wa (conc st g + 16)) (le8 (Z_to_bv 64 oldb))) (wa (conc st g + 32)) (le8 (wz (Z.land (meta_word mr) 4095 + needed)))) in *.
    set (P' := oldb + 16 + 16 * off) in *. set (E' := oldb + needed - 4) in *.
    set (k := i + 32 * Z.min rsv 5) in *.
    (* [comment removed for export] *)
    assert (EZ : forall x, mZ x = m1 x).
    { intros x. unfold mZ.
      rewrite (write_same_at (write_to_mem m1 (wa (conc st g + 16)) (le8 (Z_to_bv 64 oldb))) (conc st g + 32)).
      - apply write_same_at; [| rewrite length_le8; lia].
        pose proof CH as [[_ HBc] _]. cbn [cells_bytes cbytes] in HBc.
        apply bytes_at_app in HBc. destruct HBc as [_ HBc]. rewrite length_le8 in HBc.
        apply bytes_at_app in HBc. destruct HBc as [_ HBc]. rewrite length_le8 in HBc.
        apply bytes_at_app in HBc. destruct HBc as [HBc _].
        replace (conc st g + Z.of_nat 8 + Z.of_nat 8) with (conc st g + 16) in HBc by lia.
        unfold pw, oconc in HBc. rewrite HM, ECRID in HBc. exact HBc.
      - apply bytes_at_write_other; [| lia| rewrite length_le8; lia| rewrite !length_le8; lia].
        pose proof CH as [[_ HBc] _]. cbn [cells_bytes cbytes] in HBc.
        do 5 (apply bytes_at_app in HBc; destruct HBc as [_ HBc]). rewrite !length_le8, !length_le4 in HBc. rewrite app_nil_r in HBc.
        replace (conc st g + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4) with (conc st g + 32) in HBc by lia.
        replace (wz (Z.land (meta_word mr) 4095 + needed)) with (wz (meta_word mr)); [exact HBc|].
        unfold wz. f_equal. rewrite <- KE. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. lia.
      - rewrite length_le8. lia. }
    assert (MRZ : rmrep st mZ).
    { eapply rmrep_agree; [exact MR1| | | | | | |]; intros; hnf; intros; apply EZ. }
    destruct (rbig_tail_rep st mZ g rid rg oldb needed n off k MRZ TK Hrg Krg eq_refl ltac:(rewrite <- EML; exact KE) LI0 KE
                (fun b' gh Hb' Hf => proj1 (GRPS b' gh Hb' Hf)) ltac:(unfold MMAP_THRESHOLD in NTH; lia) OFF0 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(subst k; rewrite I0, hdr_b3_idx by (pose proof (Z.le_min_l rsv 5); lia); pose proof (Z.le_min_l rsv 5); lia))
      as (MRF & TKF & CONCF & RESF).
    fold P' E' in MRF. fold P' in CONCF.
    rewrite Ebm, I0. set (res := realloc_big_tail st (rid, 0) (16 * off) 0 needed n) in *.
    set (mF := rset_size_mem (write_to_mem mZ (wa E') [b8 0]) P' E' n k) in *.
    (* [comment removed for export] *)
    destruct (rbt_fp m1 (conc st g) oldb needed P' E' n k (Z.land (meta_word mr) 4095 + needed)
                ltac:(clear -R4096 OFF0 P'; lia) ltac:(clear -N; lia) ltac:(clear -KE OSZ16 NDR BSZ0 P' E'; lia) ltac:(clear -RC KE E'; lia)
                ltac:(clear -KE OSZ16 NDR BSZ0 P' E'; lia) ltac:(clear -GB1; lia) ltac:(clear -GB2; lia) ltac:(clear; unfold E'; lia)) as (MUF & WMF & MIDF).
    fold mZ in MUF, WMF, MIDF. fold mF in MUF, WMF, MIDF.
    apply evt_done. unfold rreallocT_post. rewrite RESF. cbn [fst snd]. do 15 eexists. exists mF, errv.
    split; [reflexivity|]. split; [exact MRF|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply rw_cells_transport; [exact ERR1| exact MUF| exact WMF|]. rewrite TP. unfold RATP. rewrite unsigned_lit by (clear; lia). cbn.
             clear -GB3 OI KE OFF0 NDR GML P' E'. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX1| exact MUF| exact WMF|]. constructor; [| constructor; [|constructor]]; cbn; unfold RAUXV_CELL;
             clear -GB2 GB3 CLO SLO SB RC OI KE NDR OFF0 GML P' E' SPR; lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split. { unfold brk_link_ps in *. unfold res, realloc_big_tail. cbn [fst]. rewrite ctx_havoc, ctx_set_size, ctx_wr8. change (ctx st) with (ctx st0).
             destruct (c_brk (ctx st0)) as [| |brid boff]; [exact BL| exact BL|]. rewrite conc_havoc, conc_set_size, conc_wr8. exact BL. }
    (* [comment removed for export] *)
    set (kk := Z.min n (blk_size b)).
    assert (KK : 0 <= kk <= n /\ kk <= blk_size b) by (subst kk; clear -N BSZ0; lia).
    pose proof (bytes_at_bound _ _ _ _ OLD1) as OB. rewrite LEN in OB.
    destruct (rwr_at_bytes_exist m1 (P' + kk) (n - kk)) as (bs & LBS & BS).
    { eapply wr_at_sub; [exact HW| clear -KK OFF0 P'; lia| clear -KK KE NDR P'; lia]. }
    { clear -KK; lia. }
    { clear -KK OI KE NDR OFF0 P' N. lia. }
    assert (OLD1' : bytes_at usegs m1 P' old) by (replace P' with (blk_addr b) by (rewrite HP0; reflexivity); exact OLD1).
    assert (UCH1 : rw_cells usegs m1 P' [CB (Z.to_nat kk) (firstn (Z.to_nat kk) old); CB (Z.to_nat (n - kk)) bs]).
    { apply rw_cells_of_bytes.
      - cbn. rewrite length_firstn. clear -KK LEN LBS. repeat split; lia.
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
        + rewrite <- (firstn_skipn (Z.to_nat kk) old) in OLD1'. apply (proj1 (bytes_at_app _ _ _ _ _)) in OLD1'. destruct OLD1' as [X _]. exact X.
        + rewrite length_firstn. replace (Z.of_nat (Z.to_nat kk `min` length old)) with kk by (rewrite <- (Nat2Z.id (length old)), LEN in |- *; clear -KK; lia). exact BS.
      - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat kk + Z.to_nat (n - kk))) with n by (clear -KK N; lia).
        eapply wr_at_sub; [exact HW| clear -OFF0 P'; lia| clear -KE NDR OFF0 N P'; lia]. }
    pose proof (MIDF _ _ UCH1 ltac:(clear; lia) ltac:(cbn [cells_size csize]; clear -KK N; lia) ltac:(cbn [cells_size csize]; clear -KK N GDJ KE NDR OFF0 P'; lia)) as UCH2.
    exists (blk_id b), bs. cbv zeta. fold P' in CONCF |- *.
    replace (conc (fst res) (rid, 16 + 16 * off)) with P' by (symmetry; exact CONCF). fold kk.
    split; [reflexivity|].
    split. { clear -R4096 RAL OFF0 N KE NDR RC OI P'. unfold rblock_range, alloc_ceiling. Z.div_mod_to_equations. lia. }
    split. { assert (CONCP : conc (fst res) pf = P') by (rewrite EPF at 1; rewrite ESPF; exact CONCF).
             pose proof (areach_realloc_keep st0 LB b pf n (fst res) AR Hb ltac:(clear -N; lia) Hfst Hconc) as X. rewrite CONCP in X. apply X. clear X.
             split; [unfold size_overflows; apply Z.leb_gt; clear -N; lia|].
             exists g, i, (blk_size b). split; [exact HDREQ|]. cbv zeta. right.
             cbn [rk_of rk_st0 rk_e rk_avail rk_g rk_idx rk_gmem rk_base rk_needed rk_maplen4096]. fold st. change (get_meta_rec st g) with mr. fold stride.
             replace (snd pf - snd (slot_start' mr i)) with (16 * off) by (unfold slot_start'; rewrite Hmem, Ebm, I0; cbn [snd fst aadd default from_option id]; rewrite ESPF; unfold UNIT; lia).
             replace (round_up_pg (n + 16 * off + UNIT + IB)) with needed by (unfold needed, UNIT, IB; f_equal; lia).
             rewrite Hmem. cbn [default from_option id]. fold osz. rewrite SC63.
             split. { replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; clear -NTH; lia). rewrite andb_false_r. reflexivity. }
             split. { replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact NTH). reflexivity. }
             split; [reflexivity|]. left. split; [exact KE|]. unfold res. rewrite Ebm, I0. reflexivity. }
    split.
    { pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR1) as MF1.
      eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP01| clear; lia| intros bb' Hbb'; unfold lbrm in Hbb'; apply In_filter_iff in Hbb'; destruct Hbb' as [X _]; exact X]|].
      intros a Ha CA. split; [| intros W; apply WMF; exact W]. apply MUF. rewrite wa_unsigned by exact Ha. cbn.
      destruct CA as [CA|[[CA _]|(blk' & Hb' & Hab)]].
      - clear -CA GB2 CLO SLO RC KE NDR OFF0 E' P'. unfold alloc_ceiling in *. lia.
      - clear -CA GB3 OI KE NDR OFF0 GML E' P'. lia.
      - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' Hne'].
        assert (NS' : blk_slot blk' <> blk_slot b) by (intros EE; rewrite EE, aptr_eqb_refl in Hne'; exact Hne').
        assert (NF : fst (blk_slot blk') <> rid) by (intros EF; apply NS'; rewrite (BLKS blk' Hin' EF); reflexivity).
        destruct (rblock_inside st LB m1 blk' MF1 MR1 Hin') as (r2 & _ & _ & Hr2 & Kr2 & _ & LO2 & HI2 & _).
        pose proof (DISJ _ _ _ _ Hr2 Hrg NF) as D2. rewrite (lr_lo_group r2 Kr2), (lr_lo_group rg Krg), <- EML in D2. fold oldb in D2.
        pose proof (GDJA _ _ Hr2 Kr2) as D3.
        clear -Hab LO2 HI2 D2 D3 KE NDR OFF0 E' P'. lia. }
    exact UCH2.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (areach_live_nonempty st LB AR1) as NEL.
    assert (PT : ptrs_but st rid g).
    { eapply (rptrs_but_of_cinv st LB m1 rid rg g C1 MR1 Hrg Krg).
      - intros b' gh Hb' Hf. exact (proj1 (GRPS b' gh Hb' Hf)).
      - intros m' b' Hm' Hf'. exact (MEMS m' b' Hm' Hf'). }
    assert (N33 : needed < 2^48) by (clear -NDR N OFF0 OSZ16 RC BSZ0 R4096 GML; lia).
    assert (ETP : bv_unsigned tp = 0x356a0) by (rewrite TP; unfold RATP; apply unsigned_lit; clear; lia).
    assert (RB : forall q rq, (s_regions st) !! q = Some rq -> 4096 <= r_base rq /\ r_base rq + round_up_pg (r_len rq) <= alloc_ceiling).
    { intros q rq Hq. pose proof (rregion_facts st m1 q rq MR1 Hq) as (X1 & _ & X2 & _). split; [exact X1| exact X2]. }
    assert (RFRES : forall x L, ranges_free (live_ranges st) x L = true -> ranges_free ref_reserved x L = true).
    { intros x L RF. apply ranges_free_intro. intros b0 k0 HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite Hres. exact HI. }
    assert (WR2of : forall m2, munch [(bv_unsigned sp - 176, bv_unsigned sp - 64); (0x356a0 + -164, 0x356a0 + -164 + 4)] m1 m2 ->
                    forall i0, 0 <= i0 < osz -> m2 (wa (oldb + i0)) <> None).
    { intros m2 MU i0 Hi0. rewrite MU. 2:{ rewrite wa_unsigned by (clear -Hi0 R4096 RC; lia). cbn. clear -Hi0 R4096 RC OI CLO SLO. lia. }
      apply (wr_at_some m1 oldb osz i0 HW OI Hi0). }
    (* [comment removed for export] *)
    assert (SUCC : forall (NB : Z) (mf : mem) (q0 q1 q2 w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 : word),
      0 < NB -> NB mod 4096 = 0 -> NB + needed <= alloc_ceiling ->
      (NB = oldb /\ (needed <= osz \/ ranges_free (live_ranges st) (oldb + osz) (needed - osz) = true)) \/ ranges_free (live_ranges st) NB needed = true ->
      mremap_answer_ok (live_ranges st) oldb osz needed NB = true -> is_err NB = false ->
      mem_inv usegs mf -> stk usegs mf lo (bv_unsigned sp - 64) ->
      (forall a, 0 <= a < 2^64 -> (a + 1 <= oldb \/ oldb + osz <= a) -> (a + 1 <= NB \/ NB + needed <= a) ->
                 ~ (bv_unsigned sp - 176 <= a < bv_unsigned sp - 64) -> ~ (RERRNO <= a < RERRNO + 4) -> mf (wa a) = m1 (wa a)) ->
      (forall o, 0 <= o < Z.min osz needed -> mf (wa (NB + o)) = m1 (wa (oldb + o))) ->
      (forall o, osz <= o < needed -> mf (wa (NB + o)) = Some (b8 0)) ->
      wr_at usegs mf NB needed ->
      (forall a, 0 <= a < 2^64 -> (a + 1 <= oldb \/ oldb + osz <= a) -> wview usegs m1 (wa a) <> None -> wview usegs mf (wa a) <> None) ->
      rw_cells usegs mf (errno_addr tp) [C4 errv] ->
      rimplTX o (SRet (realloc_big_tail (remap_region rid g NB needed st) bm (16 * off) i needed n)) s
        (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m0)
        (MS (mkR (Z_to_bv 64 0x19dc0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp q0 q1 q2 (Z_to_bv 64 needed) (wz (conc st g)) (Z_to_bv 64 NB) w1 w2 w3 w4 w5 w6 w7
                 (Z_to_bv 64 (S + stride - 4 - rsv)) (Z_to_bv 64 (blk_addr b + - S)) (Z_to_bv 64 4095) (Z_to_bv 64 (blk_addr b)) (Z_to_bv 64 n) s7 s8 s9 s10 s11 q3 q4 q5 q6)
            F (Z_to_bv 64 0x19dc0) fc None mf (seg_rom usegs))).
    { intros NB mf q0 q1 q2 w1 w2 w3 w4 w5 w6 w7 q3 q4 q5 q6 NB0 NBAL NBC ANS OKs IEs MIf STf AGf CPf ZFf WNf WVf ERRf.
      assert (ANS' : NB = r_base rg /\ (needed <= round_up_pg (r_len rg) \/ ranges_free (live_ranges st) (r_base rg + round_up_pg (r_len rg)) (needed - round_up_pg (r_len rg)) = true)
                     \/ ranges_free (live_ranges st) NB needed = true) by (rewrite <- EML; exact ANS).
      assert (N0' : 0 < needed) by (clear -NDR N OFF0; lia). assert (NAL' : needed mod 4096 = 0) by (apply NDR).
      assert (NBC' : NB + needed <= alloc_ceiling) by exact NBC.
      pose proof (new_off_image st m1 rid g rg NB needed MR1 Hrg N0' NAL' NB0 ANS') as NI.
      pose proof (new_vs_region st m1 rid g rg NB needed MR1 Hrg Krg NEL N0' NB0 NBAL NBC' ANS') as NVR.
      pose proof (G_bounds st m1 rid g rg NB needed MR1 Hrg Krg MSL HM PT NEL N0' NB0 NBAL NBC' ANS') as (_ & _ & _ & _ & GNB).
      unfold alloc_ceiling in NBC.
      apply rimplTX_ret.
      (* [comment removed for export] *)
      assert (FRf : rw_cells usegs mf (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree; [exact FR1|]. intros y Hy. cbn in Hy. apply AGf; unfold RERRNO; clear -Hy SPR CLO SLO RC NBC; lia. }
      assert (CHf : rw_cells usegs mf (conc st g) [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (pw st (m_mem mr)); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))]).
      { eapply rrw_cells_agree; [exact CH|]. intros y Hy. cbn in Hy. apply AGf; unfold RERRNO; clear -Hy GB1 GB2 GB3 GDJ GNB CLO SLO; lia. }
      assert (STf' : stk usegs mf lo (bv_unsigned sp + -64)) by (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; exact STf).
      (* [comment removed for export] *)
      step. step. step. step. step. if_cases KF; zify_cond KF; rewrite ?unsigned_lit in KF by (clear -NB0 NBC NDR N OFF0; lia). { exfalso. clear -KF NB0 NBC NDR N OFF0. lia. }
      replace (Z_to_bv 64 (blk_addr b + - S) : word) with (Z_to_bv 64 (16 * off) : word) by (f_equal; fold P; rewrite HP, HS; lia).
      set (k := i + 32 * Z.min rsv 5).
      assert (HK : 0 <= k < 256 /\ Z.land k 31 = 0).
      { subst k. rewrite I0. pose proof (Z.le_min_l rsv 5). pose proof (Z.le_min_r rsv 5). split; [clear -H H0 RSV0; lia|].
        rewrite hdr_b3_idx by (clear -H RSV0; lia). reflexivity. }
      (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (rrealloc_bt_walk ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ (Z_to_bv 64 0x19dc0) (Z_to_bv 64 (conc st g)) _ _ _
                 _ _ _ _ _ F fc mf (conc st g) NB needed (16 * off) (meta_word mr) n k lo);
          first [exact MIf| exact FRf| exact STf'| exact CHf| exact MWR| exact GNB| idtac].
        - apply unsigned_lit. clear -GB1 GB2; lia.
        - clear -SLO; lia.
        - unfold alloc_ceiling; clear -CLO; lia.
        - eapply wr_at_sub; [exact WNf| clear -OFF0; lia| clear -NDR OFF0 N; lia].
        - apply bytes_at1_of_some; [clear -NB0 OFF0; lia| clear -NBC NDR N OFF0; lia|].
          replace (NB + 16 + 16 * off - 3) with (NB + (snd pf - 3)) by (rewrite ESPF; lia).
          rewrite CPf by (rewrite ESPF; clear -OFF0 OSZ16 BSZ0 NDR N; lia).
          apply (bytes_at1_some m1); [| rewrite ESPF; clear -OI OFF0 OSZ16 BSZ0; lia].
          refine (proj1 (HBY _ _ _ C3)). rewrite ESPF. clear -OFF0 OSZ16 BSZ0; lia.
        - exact (proj1 HK).
        - clear -OFF0; lia.
        - clear -N; lia.
        - exact NB0.
        - exact N0'.
        - exact NAL'.
        - clear -NDR; lia.
        - clear -NDR; lia.
        - unfold alloc_ceiling. exact NBC.
        - exact GB1.
        - unfold alloc_ceiling; exact GB2. }
      cbv beta. intros msf PS. unfold rss_post in PS.
      destruct PS as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & -> & MI2 & ST2).
      set (mZ := write_to_mem (write_to_mem mf (wa (conc st g + 16)) (le8 (Z_to_bv 64 NB))) (wa (conc st g + 32)) (le8 (wz (Z.land (meta_word mr) 4095 + needed)))) in *.
      set (P' := NB + 16 + 16 * off) in *. set (E' := NB + needed - 4) in *.
      (* [comment removed for export] *)
      assert (EMW : wz (Z.land (meta_word mr) 4095 + needed) = wz (meta_word (m_set_maplen (needed / 4096) mr))).
      { unfold wz. f_equal. rewrite (mr'_word st g rg NB needed N0' ltac:(clear -N33; lia) NAL') by (change (get_meta_rec st g) with mr; clear -GLI GFR GSC GML; lia).
        change (get_meta_rec st g) with mr. change 4095 with (Z.ones 12). rewrite Z.land_ones by (clear; lia). reflexivity. }
      assert (MGc : rw_cells usegs mZ (conc st g) [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz NB); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word (m_set_maplen (needed / 4096) mr)))]).
      { unfold mZ. rewrite EMW.
        pose proof (rw_cells_write usegs _ _ _ 16 (C8 (pw st (m_mem mr))) (C8 (Z_to_bv 64 NB)) CHf eq_refl eq_refl I) as X1.
        cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in X1. change (Z.of_nat 16) with 16 in X1.
        pose proof (rw_cells_write usegs _ _ _ 32 (C8 (wz (meta_word mr))) (C8 (wz (meta_word (m_set_maplen (needed / 4096) mr)))) X1 eq_refl eq_refl I) as X2.
        cbn [cell_upd cbytes Nat.eqb Nat.sub csize] in X2. change (Z.of_nat 32) with 32 in X2. exact X2. }
      assert (MRZ : rmrep (remap_region rid g NB needed st) mZ).
      { eapply (rmrep_remap st m1 mZ rid g rg NB needed MR1 Hrg Krg MSL HM PT NEL N0' NAL' NB0 NBAL NBC' ANS');
          [| | | exact MGc| change (get_meta_rec st g) with mr; clear -GLI; lia| | exact GSC| change (get_meta_rec st g) with mr; clear -GML; lia].
        - intros y Hy DG REP.
          assert (OUT : (y + 1 <= oldb \/ oldb + osz <= y) /\ (y + 1 <= NB \/ NB + needed <= y) /\ ~ (bv_unsigned sp - 176 <= y < bv_unsigned sp - 64) /\ ~ (RERRNO <= y < RERRNO + 4)).
          { destruct REP as [RS|(q & rq & Hq & NEq & Rq)].
            - pose proof RS as RS'. unfold rrep_static, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD, RERRNO in *. clear -RS' OI NI CLO SLO R4096 GML OSZ16 OFF0 BSZ0 NDR N. lia.
            - pose proof (DISJ _ _ _ _ Hq Hrg NEq) as D1. rewrite (lr_lo_group rg Krg), <- EML in D1. fold oldb in D1.
              pose proof (NVR q rq Hq NEq) as D2. destruct (RB q rq Hq) as [B1 B2]. destruct (WR _ _ Hq) as (_ & _ & _ & _ & RFq).
              pose proof (NEL q rq Hq) as NE1. pose proof (lr_lo_ge rq) as LG. pose proof (rreserved_disjoint1 _ _ RFq ltac:(clear -NE1 LG; lia)) as IMq.
              unfold alloc_ceiling, RERRNO in *. clear -Rq D1 D2 B1 B2 IMq LG CLO SLO. lia. }
          destruct OUT as (O1 & O2 & O3 & O4).
          unfold mZ. rewrite write_to_mem_spec by (rewrite ?length_le8; clear -GB1 GB2; lia). rewrite length_le8, wa_unsigned by exact Hy.
          destruct (Z.leb_spec0 (conc st g + 32) y) as [La|La]; destruct (Z.ltb_spec0 y (conc st g + 32 + Z.of_nat 8)) as [Lb|Lb]; cbn [andb]; try (exfalso; clear -DG La Lb; lia).
          all: rewrite write_to_mem_spec by (rewrite ?length_le8; clear -GB1 GB2; lia); rewrite length_le8, wa_unsigned by exact Hy.
          all: destruct (Z.leb_spec0 (conc st g + 16) y) as [Lc|Lc]; destruct (Z.ltb_spec0 y (conc st g + 16 + Z.of_nat 8)) as [Ld|Ld]; cbn [andb]; try (exfalso; clear -DG Lc Ld; lia).
          all: apply AGf; assumption.
        - intros o1 Ho1. rewrite <- EML in Ho1. unfold mZ.
          rewrite write_to_mem_spec by (rewrite ?length_le8; clear -GB1 GB2; lia). rewrite length_le8, wa_unsigned by (clear -Ho1 NB0 NBC; lia).
          destruct (Z.leb_spec0 (conc st g + 32) (NB + o1)) as [La|La]; destruct (Z.ltb_spec0 (NB + o1) (conc st g + 32 + Z.of_nat 8)) as [Lb|Lb]; cbn [andb]; try (exfalso; clear -GNB Ho1 La Lb; lia).
          all: rewrite write_to_mem_spec by (rewrite ?length_le8; clear -GB1 GB2; lia); rewrite length_le8, wa_unsigned by (clear -Ho1 NB0 NBC; lia).
          all: destruct (Z.leb_spec0 (conc st g + 16) (NB + o1)) as [Lc|Lc]; destruct (Z.ltb_spec0 (NB + o1) (conc st g + 16 + Z.of_nat 8)) as [Ld|Ld]; cbn [andb]; try (exfalso; clear -GNB Ho1 Lc Ld; lia).
          all: apply CPf; exact Ho1.
        - intros o1 Ho1. rewrite <- EML in Ho1. unfold mZ.
          rewrite write_to_mem_spec by (rewrite ?length_le8; clear -GB1 GB2; lia). rewrite length_le8, wa_unsigned by (clear -Ho1 NB0 NBC GML; lia).
          destruct (Z.leb_spec0 (conc st g + 32) (NB + o1)) as [La|La]; destruct (Z.ltb_spec0 (NB + o1) (conc st g + 32 + Z.of_nat 8)) as [Lb|Lb]; cbn [andb]; try (exfalso; clear -GNB Ho1 La Lb GML; lia).
          all: rewrite write_to_mem_spec by (rewrite ?length_le8; clear -GB1 GB2; lia); rewrite length_le8, wa_unsigned by (clear -Ho1 NB0 NBC GML; lia).
          all: destruct (Z.leb_spec0 (conc st g + 16) (NB + o1)) as [Lc|Lc]; destruct (Z.ltb_spec0 (NB + o1) (conc st g + 16 + Z.of_nat 8)) as [Ld|Ld]; cbn [andb]; try (exfalso; clear -GNB Ho1 Lc Ld GML; lia).
          all: apply ZFf; exact Ho1.
        - change (get_meta_rec st g) with mr. rewrite GFR. clear; lia. }
      pose proof (ticks_ok_remap st rid g NB needed TK) as TKr.
      assert (MLr : m_maplen (get_meta_rec (remap_region rid g NB needed st) g) * 4096 = needed).
      { rewrite rr_meta_g, (mr'_maplen st g rg NB needed N0' ltac:(clear -N33; lia)). clear -NDR. Z.div_mod_to_equations. lia. }
      destruct (rbig_tail_rep (remap_region rid g NB needed st) mZ g rid (mkRegion RKGroup NB needed) NB needed n off k MRZ TKr
                  (rr_lookup_new st rid g rg NB needed Hrg Krg) eq_refl eq_refl ltac:(cbn [r_len]; apply round_up_pg_id; [clear -N0'; lia| exact NAL'])
                  ltac:(rewrite rr_meta_g; exact LI0) MLr
                  ltac:(intros b' gh Hb' Hf; rewrite rr_groups in Hb'; exact (proj1 (GRPS b' gh Hb' Hf)))
                  ltac:(clear -N0' NAL'; Z.div_mod_to_equations; lia) OFF0 ltac:(clear -N; lia) ltac:(clear -NDR; lia) ltac:(clear -NDR; lia) (conj (proj1 (proj1 HK)) (proj2 HK)))
        as (MRF & TKF & CONCF & RESF).
      fold P' E' in MRF. fold P' in CONCF.
      rewrite Ebm, I0. set (res := realloc_big_tail (remap_region rid g NB needed st) (rid, 0) (16 * off) 0 needed n) in *.
      set (mF := rset_size_mem (write_to_mem mZ (wa E') [b8 0]) P' E' n k) in *.
      destruct (rbt_fp mf (conc st g) NB needed P' E' n k (Z.land (meta_word mr) 4095 + needed)
                  ltac:(clear -NB0 OFF0 P'; lia) ltac:(clear -N; lia) ltac:(clear -NDR P' E'; lia) ltac:(clear -NBC E'; lia)
                  ltac:(clear -NDR P' E'; lia) ltac:(clear -GB1; lia) ltac:(clear -GB2; lia) ltac:(clear; unfold E'; lia)) as (MUF & WMF & MIDF).
      fold mZ in MUF, WMF, MIDF. fold mF in MUF, WMF, MIDF.
      apply evt_done. unfold rreallocT_post. rewrite RESF. cbn [fst snd]. do 15 eexists. exists mF, errv.
      split; [reflexivity|]. split; [exact MRF|]. split; [exact MI2|]. split; [exact ST2|].
      split. { eapply rw_cells_transport; [exact ERRf| exact MUF| exact WMF|]. rewrite ETP. cbn. clear -GB3 NI OFF0 NDR N P' E'. lia. }
      split. { destruct AUX1 as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AB1 & AB2 & ABB & ABA & AAV & ABR & ARN & REST).
               exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [| split; [| split; [| repeat (split; [assumption|]); exact REST]]].
               - eapply rw_cells_transport; [| exact MUF| exact WMF| cbn; unfold RAUXV_CELL; clear -GB3 NI OFF0 NDR N P' E'; lia].
                 eapply rrw_cells_agree; [exact AC|]. intros y Hy. cbn in Hy. apply AGf; unfold RAUXV_CELL, RERRNO in *; clear -Hy OI NI CLO SLO R4096 GML; lia.
               - eapply bytes_at_transport; [| exact MUF| cbn; unfold alloc_ceiling in *; clear -GB2 NBC ABB ABA SB P' E'; lia].
                 pose proof (bytes_at_bound _ _ _ _ AB1) as [_ L1].
                 eapply rbytes_at_agree; [exact AB1|]. intros y Hy. apply AGf; unfold RERRNO, alloc_ceiling in *; clear -Hy L1 ABB ABA SB RC NBC CLO SLO SPR; lia.
               - eapply bytes_at_transport; [| exact MUF| cbn; unfold alloc_ceiling in *; clear -GB2 NBC ABB ABR SB P' E'; lia].
                 eapply rbytes_at_agree; [exact AB2|]. intros y Hy. cbn in Hy. apply AGf; unfold RERRNO, alloc_ceiling in *; clear -Hy ABB ABR ARN SB RC NBC CLO SLO SPR; lia. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split. { unfold brk_link_ps in *. unfold res, realloc_big_tail. cbn [fst]. rewrite ctx_havoc, ctx_set_size, ctx_wr8, rr_ctx. change (ctx st) with (ctx st0).
               destruct (c_brk (ctx st0)) as [| |brid boff] eqn:HBK; [exact BL| exact BL|]. rewrite conc_havoc, conc_set_size, conc_wr8.
               rewrite (rr_conc st rid g rg NB needed Hrg Krg); [exact BL|]. cbn [fst]. intros E.
               destruct (ci_bk _ _ C1 brid boff HBK) as (rb & Hrb & Krb). rewrite E, Hrg in Hrb. inversion Hrb; subst rb. rewrite Krg in Krb. discriminate. }
      (* [comment removed for export] *)
      set (kk := Z.min n (blk_size b)).
      assert (KK : 0 <= kk <= n /\ kk <= blk_size b) by (subst kk; clear -N BSZ0; lia).
      pose proof (bytes_at_bound _ _ _ _ OLD1) as OB. rewrite LEN in OB.
      destruct (rwr_at_bytes_exist mf (P' + kk) (n - kk)) as (bs & LBS & BS).
      { eapply wr_at_sub; [exact WNf| clear -KK OFF0 P'; lia| clear -KK NDR P'; lia]. }
      { clear -KK; lia. }
      { clear -KK NI NDR OFF0 P' N. lia. }
      assert (OLDf : bytes_at usegs mf P' (firstn (Z.to_nat kk) old)).
      { pose proof OLD1 as X. rewrite <- (firstn_skipn (Z.to_nat kk) old) in X. apply (proj1 (bytes_at_app _ _ _ _ _)) in X. destruct X as [X _].
        rewrite HP0 in X. eapply (bytes_at_shift m1 mf _ P'); [exact X| | clear -NB0 OFF0 P'; lia| rewrite length_firstn; clear -KK NBC NDR P'; lia
          | rewrite length_firstn; clear -KK OI OSZ16 OFF0; lia| rewrite length_firstn; clear -KK NI NDR OFF0 P' N; lia].
        intros j Hj. rewrite length_firstn in Hj. unfold P'. replace (NB + 16 + 16 * off + j) with (NB + (16 + 16 * off + j)) by lia.
        replace (oldb + 16 + 16 * off + j) with (oldb + (16 + 16 * off + j)) by lia. apply CPf. clear -Hj KK OSZ16 NDR OFF0. lia. }
      assert (UCH1 : rw_cells usegs mf P' [CB (Z.to_nat kk) (firstn (Z.to_nat kk) old); CB (Z.to_nat (n - kk)) bs]).
      { apply rw_cells_of_bytes.
        - cbn. rewrite length_firstn. clear -KK LEN LBS. repeat split; lia.
        - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OLDf|].
          rewrite length_firstn. replace (Z.of_nat (Z.to_nat kk `min` length old)) with kk by (rewrite <- (Nat2Z.id (length old)), LEN in |- *; clear -KK; lia). exact BS.
        - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat kk + Z.to_nat (n - kk))) with n by (clear -KK N; lia).
          eapply wr_at_sub; [exact WNf| clear -OFF0 P'; lia| clear -NDR OFF0 N P'; lia]. }
      pose proof (MIDF _ _ UCH1 ltac:(clear; lia) ltac:(cbn [cells_size csize]; clear -KK N; lia) ltac:(cbn [cells_size csize]; clear -KK N GNB NDR OFF0 P'; lia)) as UCH2.
      exists (blk_id b), bs. cbv zeta. fold P' in CONCF |- *.
      replace (conc (fst res) (rid, 16 + 16 * off)) with P' by (symmetry; exact CONCF). fold kk.
      split; [reflexivity|].
      split. { clear -NB0 NBAL OFF0 N NDR NBC NI P'. unfold rblock_range, alloc_ceiling. Z.div_mod_to_equations. lia. }
      split. { assert (CONCP : conc (fst res) pf = P') by (rewrite EPF at 1; rewrite ESPF; exact CONCF).
               pose proof (areach_realloc_keep st0 LB b pf n (fst res) AR Hb ltac:(clear -N; lia) Hfst Hconc) as X. rewrite CONCP in X. apply X. clear X.
               split; [unfold size_overflows; apply Z.leb_gt; clear -N; lia|].
               exists g, i, (blk_size b). split; [exact HDREQ|]. cbv zeta. right.
               cbn [rk_of rk_st0 rk_e rk_avail rk_g rk_idx rk_gmem rk_base rk_needed rk_maplen4096]. fold st. change (get_meta_rec st g) with mr. fold stride.
               replace (snd pf - snd (slot_start' mr i)) with (16 * off) by (unfold slot_start'; rewrite Hmem, Ebm, I0; cbn [snd fst aadd default from_option id]; rewrite ESPF; unfold UNIT; lia).
               replace (round_up_pg (n + 16 * off + UNIT + IB)) with needed by (unfold needed, UNIT, IB; f_equal; lia).
               rewrite Hmem. cbn [default from_option id]. fold osz. rewrite SC63.
               split. { replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; clear -NTH; lia). rewrite andb_false_r. reflexivity. }
               split. { replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact NTH). reflexivity. }
               split; [reflexivity|]. right. split; [exact KE|]. split; [unfold PTRDIFF_MAX; clear -N33; lia|].
               exists NB. split; [rewrite ECBM; exact OKs|]. split; [exact IEs|]. unfold res. rewrite Ebm, I0. reflexivity. }
      split.
      { pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR1) as MF1.
        assert (CL : forall y, 0 <= y < 2^64 -> rclient_addr (lbrm LB b) (bv_unsigned sp) y ->
                   (y + 1 <= oldb \/ oldb + osz <= y) /\ (y + 1 <= NB \/ NB + needed <= y) /\ ~ (bv_unsigned sp - 176 <= y < bv_unsigned sp - 64) /\ ~ (RERRNO <= y < RERRNO + 4)
                   /\ (y + 1 <= conc st g \/ conc st g + 40 <= y)).
        { intros y Hy CA. destruct CA as [CA|[[CA NA]|(blk' & Hb' & Hab)]].
          - unfold RERRNO, alloc_ceiling in *. clear -CA Hy GB2 CLO SLO RC NBC SPR. lia.
          - unfold ralloc_static, RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *. clear -CA NA GB3 OI NI CLO SLO R4096 GML OSZ16 OFF0 BSZ0 NDR N. lia.
          - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' Hne'].
            assert (NS' : blk_slot blk' <> blk_slot b) by (intros EE; rewrite EE, aptr_eqb_refl in Hne'; exact Hne').
            assert (NF : fst (blk_slot blk') <> rid) by (intros EF; apply NS'; rewrite (BLKS blk' Hin' EF); reflexivity).
            destruct (rblock_inside st LB m1 blk' MF1 MR1 Hin') as (r2 & _ & _ & Hr2 & Kr2 & _ & LO2 & HI2 & _ & _ & RC2 & RIM2).
            pose proof (DISJ _ _ _ _ Hr2 Hrg NF) as D2. rewrite (lr_lo_group r2 Kr2), (lr_lo_group rg Krg), <- EML in D2. fold oldb in D2.
            pose proof (NVR _ _ Hr2 NF) as D3. rewrite (lr_lo_group r2 Kr2) in D3. pose proof (GDJA _ _ Hr2 Kr2) as D4.
            unfold alloc_ceiling, RERRNO in *. clear -Hab LO2 HI2 RC2 RIM2 D2 D3 D4 CLO SLO. lia. }
        eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP01| clear; lia| intros bb' Hbb'; unfold lbrm in Hbb'; apply In_filter_iff in Hbb'; destruct Hbb' as [X _]; exact X]|].
        eapply rheap_pres_trans.
        - intros y Hy CA. destruct (CL y Hy CA) as (O1 & O2 & O3 & O4 & O5). split; [apply AGf; assumption| intros W; apply WVf; assumption].
        - intros y Hy CA. destruct (CL y Hy CA) as (O1 & O2 & O3 & O4 & O5). split; [| intros W; apply WMF; exact W]. apply MUF. rewrite wa_unsigned by exact Hy. cbn.
          clear -O2 O5 OFF0 NDR N P' E'. lia. }
      exact UCH2. }
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    apply evt_done.
    rewrite TREE. replace (osz =? needed) with false by (symmetry; apply Z.eqb_neq; exact KE).
    replace (PTRDIFF_MAX <=? needed) with false by (symmetry; apply Z.leb_gt; unfold PTRDIFF_MAX; clear -N33; lia).
    unfold MREMAP_MAYMOVE. pose proof GL as (_ & _ & _ & G4 & G5).
    eapply rimplTX_mremap.
    { unfold wz. rewrite ECBM.
      eapply rmremap_spec with (lo := lo).
      - rewrite unsigned_lit by (clear -SPR SLO CLO; lia). replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia. exact ST1.
      - exact ERR1.
      - exact G4.
      - exact G5.
      - exact MI1.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - clear -R4096; lia.
      - clear -OSZ16 OFF0 BSZ0; lia.
      - unfold alloc_ceiling. clear -RC; lia.
      - exact OI.
      - clear -N33 NDR N OFF0; lia.
      - rewrite unsigned_lit by (clear -SPR SLO CLO; lia). clear -SLO; lia.
      - exact LO.
      - exact TP. }
    intros a ms' [DEC POST]. cbv beta.
    destruct (mremap_answer_ok (live_ranges st) oldb osz needed (mremap_val oldb a)) eqn:OK; cbn [negb]; [| apply rimplTX_xbad].
    destruct a as [e| |d]; cbn [mremap_val mremap_decoded] in OK, DEC |- *.
    + (* [comment removed for export] *)
      replace (is_err (neg_errno e)) with true by (symmetry; unfold is_err, neg_errno, TWO64; apply Z.ltb_lt; clear -DEC; lia).
      destruct (POST I) as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & _ & _ & He).
      cbn [mremap_mem mremap_ret mremap_errno] in *.
      replace (ret_pc (Z_to_bv 64 0x19dc0)) with (Z_to_bv 64 0x19dc0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite unsigned_lit in MU2, ST2 by (clear -SPR SLO CLO; lia).
      replace (bv_unsigned sp + -64 - 112) with (bv_unsigned sp - 176) in MU2 by lia. rewrite ETP in MU2.
      (* [comment removed for export] *)
      assert (MR2 : rmrep st m2).
      { eapply rmrep_agree; [exact MR1| | | | | | |]; intros; hnf; intros y Hy.
        - unfold RMLOCK in *. clear -Hy CLO SLO MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia.
        - unfold RLIBC in *. clear -Hy CLO SLO MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia.
        - unfold RGOT_SSP in *. clear -Hy CLO SLO MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia.
        - unfold RSSP_GUARD in *. clear -Hy CLO SLO MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia.
        - match goal with Ha : (s_areas st) !! _ = Some _ |- _ =>
            destruct (rarea_conc st _ _ WF Ha) as (rga & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC);
            destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa); pose proof (rreserved_disjoint1 _ _ RFa ltac:(clear -Sa0 Sa1; lia)) as IMG end.
          unfold alloc_ceiling in *. clear -Hy CLO SLO Ca Sa0 Sa1 RBC RB0 IMG MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia.
        - match goal with Hb : (s_groups st) !! _ = Some _ |- _ =>
            destruct (rgroup_conc st _ _ WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RBb & RBCb);
            destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb); pose proof (rreserved_disjoint1 _ _ RFb ltac:(clear -Sb0 Sb1; lia)) as IMG end.
          unfold alloc_ceiling in *. clear -Hy CLO SLO Cb Sb0 Sb1 RBCb RBb IMG MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia.
        - match goal with Hq : (s_regions st) !! _ = Some ?rq |- _ =>
            destruct (WR _ _ Hq) as (RB0 & _ & _ & RBC & RFq); pose proof (rreserved_disjoint1 _ _ RFq) as IMG end.
          unfold alloc_ceiling in *. clear -Hy CLO SLO RB0 RBC IMG MU2. apply MU2. rewrite wa_unsigned by lia. cbn. lia. }
      assert (UA2 : unk_agree st o m2).
      { eapply unk_agree_munch; [exact UA| exact MU2| |].
        - intros q rq Hq Kq. destruct (RB q rq Hq). destruct (WR _ _ Hq) as (_ & _ & _ & _ & RFq).
          pose proof (NEL q rq Hq) as NE1. rewrite (lr_lo_group rq Kq) in NE1. pose proof (rreserved_disjoint1 _ _ RFq ltac:(clear -NE1; lia)).
          cbn. unfold alloc_ceiling in *. clear -H H0 H1 CLO SLO. lia.
        - intros q rq Hq. destruct (RB q rq Hq). unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len rq)). clear -H H0 H1. lia. }
      assert (OLD2 : bytes_at usegs m1 (blk_addr b) old -> bytes_at usegs m2 (blk_addr b) old).
      { intros X. eapply bytes_at_transport; [exact X| exact MU2|]. cbn. rewrite LEN. unfold RERRNO. clear -HP0 R4096 RC OSZ16 OI BSZ0 OFF0 CLO SLO. lia. }
      specialize (OLD2 OLD1).
      assert (AUX2 : rauxv_ok m2 B).
      { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. constructor; [| constructor; [| constructor]]; cbn; unfold RAUXV_CELL, RERRNO; clear -SB SPR SLO CLO; lia. }
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. unfold RERRNO. clear -SPR SLO CLO. lia. }
      assert (HP02 : rheap_pres LB (bv_unsigned sp) m0 m2).
      { eapply rheap_pres_trans; [exact HP01|]. intros y Hy CA. split; [| intros W; apply WM2; exact W]. apply MU2. rewrite wa_unsigned by exact Hy. cbn.
        destruct CA as [CA|[[CA NA]|(blk' & Hb' & Hab)]].
        - unfold RERRNO. clear -CA Hy SPR SLO CLO. lia.
        - unfold ralloc_static, RERRNO in *. clear -CA NA CLO SLO. lia.
        - pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR1) as MF1.
          destruct (rblock_inside st LB m1 blk' MF1 MR1 Hb') as (r2 & _ & _ & _ & _ & _ & LO2 & HI2 & _ & _ & RC2 & RIM2).
          unfold alloc_ceiling, RERRNO in *. clear -Hab LO2 HI2 RC2 RIM2 CLO SLO. lia. }
      (* [comment removed for export] *)
      riprefixTX. step. step. step. step. step.
      if_cases KF; zify_cond KF. 2:{ exfalso. apply KF. reflexivity. }
      apply evt_done.
      eapply (rrealloc_move_walk gp tp s7 s8 s9 s10 s11 F fc lo B LO TP ra sp s0 s1 s2 s3 s4 s5 s6 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (blk_addr b)) (Z_to_bv 64 n) _ _ _ _ _ _ _ _ _ _
                o m0 m2 s st0 LB b pf n old (Z_to_bv 64 e) (N.succ (s_tick st0)) (S + stride - 4 - rsv));
        first [exact AR| exact MR2| exact BL| exact UA2| exact Hb| exact Hfst| exact Hconc| exact OLD2| exact LEN| exact AUX2| exact SB
              | exact ST2| exact FR2| exact ERR2| exact MI2| exact HP02| reflexivity| exact N| idtac].
      * clear; lia.
      * clear -SLO; lia.
      * apply unsigned_lit. clear -R4096 RC HP0 OFF0 OSZ16 BSZ0 GML; lia.
      * rewrite HS, HP0, Ersv, STR. clear -OSZ16 OFF0 BSZ0. unfold IB, UNIT. lia.
    + (* [comment removed for export] *)
      replace (is_err oldb) with false by (symmetry; unfold is_err, TWO64; apply Z.ltb_ge; clear -GML R4096 RC GML; lia).
      pose proof (mremap_ok_cases _ _ _ _ _ OK) as OKC.
      assert (ANS1 : needed < osz \/ (oldb + needed <= alloc_ceiling /\ ranges_free (live_ranges st) (oldb + osz) (needed - osz) = true)).
      { destruct OKC as [EF|[[_ X]|[NE _]]]; [| exact X| exfalso; apply NE; reflexivity].
        exfalso. unfold is_errno_form, TWO64 in EF. apply andb_prop in EF. destruct EF as [EF _]. apply Z.leb_le in EF. clear -GML EF R4096 RC GML. lia. }
      assert (GOOD : mremap_good oldb osz needed MrSame).
      { unfold mremap_good. intros GT. destruct ANS1 as [LT|[C1' RF]]; [exfalso; clear -GML GT LT; lia|]. split; [exact C1'|].
        pose proof (rreserved_disjoint1 _ _ (RFRES _ _ RF) ltac:(clear -GML GT; lia)) as X. clear -GML X. lia. }
      destruct (POST GOOD) as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & _ & _ & _).
      cbn [mremap_ret mremap_errno] in *.
      replace (ret_pc (Z_to_bv 64 0x19dc0)) with (Z_to_bv 64 0x19dc0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite unsigned_lit in MU2, ST2 by (clear -GML SPR SLO CLO; lia).
      replace (bv_unsigned sp + -64 - 112) with (bv_unsigned sp - 176) in MU2 by lia. rewrite ETP in MU2.
      unfold mremap_mem. replace (osz =? needed) with false by (symmetry; apply Z.eqb_neq; exact KE).
      assert (WR2o : wr_at usegs m2 oldb osz) by (eapply wr_at_transport; [exact HW| exact WM2]).
      destruct (Z.lt_ge_cases needed osz) as [SHR|GRW].
      * (* [comment removed for export] *)
        replace (needed <? osz) with true by (symmetry; apply Z.ltb_lt; exact SHR).
        assert (Hza : 0 <= oldb + needed < 2^64) by (clear -GML R4096 RC NDR N OFF0 SHR GML; lia).
        assert (Hzn : 0 <= osz - needed < 2^64) by (clear -GML SHR RC R4096 NDR N OFF0 GML; lia).
        assert (Hzan : oldb + needed + (osz - needed) <= 2^64) by (clear -GML RC R4096; lia).
        apply (SUCC oldb); clear SUCC.
        -- clear -GML R4096; lia.
        -- exact RAL.
        -- unfold alloc_ceiling. clear -GML RC SHR; lia.
        -- left. split; [reflexivity| left; clear -GML SHR; lia].
        -- exact OK.
        -- unfold is_err, TWO64. apply Z.ltb_ge. clear -GML R4096 RC GML; lia.
        -- apply (mem_inv_unmaps _ _ _ _ Hza Hzn Hzan MI2).
        -- apply (stk_unmaps_other usegs _ _ _ Hza Hzn Hzan _ _ ST2). unfold alloc_ceiling in *. clear -GML RC CLO. lia.
        -- intros y Hy Ho Hn Hf He. rewrite (unmaps_outside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by exact Hy; clear -GML Ho NDR N OFF0; lia).
           apply MU2. rewrite wa_unsigned by exact Hy. cbn. unfold RERRNO in He. clear -GML Hf He. lia.
        -- intros o1 Ho1. rewrite (unmaps_outside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by (clear -GML Ho1 R4096 RC; lia); clear -GML Ho1; lia).
           apply MU2. rewrite wa_unsigned by (clear -GML Ho1 R4096 RC; lia). cbn. clear -GML Ho1 R4096 RC OI CLO SLO. lia.
        -- intros o1 Ho1. exfalso. clear -GML Ho1 SHR. lia.
        -- apply (wr_at_unmaps_other usegs _ _ _ Hza Hzn Hzan); [| clear; lia]. eapply wr_at_sub; [exact WR2o| clear; lia| clear -GML SHR; lia].
        -- intros y Hy Ho W. unfold wview. rewrite (unmaps_outside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by exact Hy; clear -GML Ho SHR NDR N OFF0; lia).
           apply WM2. exact W.
        -- apply (rw_cells_unmaps_other usegs _ _ _ Hza Hzn Hzan _ _ ERR2). rewrite ETP. cbn. clear -GML R4096 RC OI NDR N OFF0. lia.
      * (* [comment removed for export] *)
        replace (needed <? osz) with false by (symmetry; apply Z.ltb_ge; exact GRW).
        destruct ANS1 as [LT|[C1' RF]]; [exfalso; clear -GML GRW LT; lia|].
        pose proof (rreserved_disjoint1 _ _ (RFRES _ _ RF) ltac:(clear -GML GRW KE; lia)) as TI.
        assert (Hza : 0 <= oldb + osz < 2^64) by (clear -GML R4096 RC GML; lia).
        assert (Hzn : 0 <= needed - osz < 2^64) by (clear -GML GRW N33 GML; lia).
        assert (Hzan : oldb + osz + (needed - osz) <= 2^64) by (unfold alloc_ceiling in C1'; clear -GML C1' R4096; lia).
        apply (SUCC oldb); clear SUCC.
        -- clear -GML R4096; lia.
        -- exact RAL.
        -- exact C1'.
        -- left. split; [reflexivity| right; exact RF].
        -- exact OK.
        -- unfold is_err, TWO64. apply Z.ltb_ge. clear -GML R4096 RC GML; lia.
        -- apply (mem_inv_zeros _ _ _ _ Hza Hzn Hzan MI2). intros x Hx. apply ref_ro_addr_false. clear -GML Hx TI. lia.
        -- apply (stk_zeros usegs _ _ _ Hza Hzn Hzan _ _ ST2).
        -- intros y Hy Ho Hn Hf He. rewrite (zeros_outside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by exact Hy; clear -GML Hn GRW OSZ16 OFF0 BSZ0; lia).
           apply MU2. rewrite wa_unsigned by exact Hy. cbn. unfold RERRNO in He. clear -GML Hf He. lia.
        -- intros o1 Ho1. rewrite (zeros_outside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by (clear -GML Ho1 R4096 RC; lia); clear -GML Ho1; lia).
           apply MU2. rewrite wa_unsigned by (clear -GML Ho1 R4096 RC; lia). cbn. clear -GML Ho1 R4096 RC OI CLO SLO. lia.
        -- intros o1 Ho1. rewrite (zeros_inside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by (unfold alloc_ceiling in C1'; clear -GML Ho1 R4096 C1'; lia); clear -GML Ho1; lia). reflexivity.
        -- split; [clear -GML R4096; lia|]. split; [unfold alloc_ceiling in C1'; clear -GML C1'; lia|]. intros i0 Hi0.
           destruct (Z.lt_ge_cases i0 osz).
           ++ unfold wview. rewrite (zeros_outside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by (unfold alloc_ceiling in C1'; clear -GML Hi0 R4096 C1'; lia); clear -GML H; lia).
              pose proof (WR2of m2 MU2 i0 ltac:(clear -Hi0 H; lia)) as X. destruct (m2 (wa (oldb + i0))); [discriminate| exfalso; apply X; reflexivity].
           ++ unfold wview. rewrite (zeros_inside _ _ _ Hza Hzn Hzan) by (rewrite wa_unsigned by (unfold alloc_ceiling in C1'; clear -GML Hi0 R4096 C1'; lia); clear -GML H Hi0; lia). discriminate.
        -- intros y Hy Ho W. apply (wview_zeros_mono usegs _ _ _ Hza Hzn Hzan). apply WM2. exact W.
        -- apply (rw_cells_zeros_other usegs _ _ _ Hza Hzn Hzan _ _ ERR2). rewrite ETP. cbn. clear -GML R4096 RC TI GRW KE. lia.
    + (* [comment removed for export] *)
      destruct DEC as [GT DOK]. pose proof (mremap_dst_ok_true _ _ _ _ DOK) as ((DAL & D0 & DC & DNE) & _).
      unfold alloc_ceiling in DC. change State.page_size with 4096 in DAL.
      replace (is_err d) with false by (symmetry; unfold is_err, TWO64; apply Z.ltb_ge; clear -GML DC D0 N33 NDR N OFF0; lia).
      pose proof (mremap_ok_cases _ _ _ _ _ OK) as OKC.
      assert (RF : ranges_free (live_ranges st) d needed = true).
      { destruct OKC as [EF|[[E _]|(_ & _ & _ & _ & X)]]; [| exfalso; exact (DNE E)| exact X].
        exfalso. unfold is_errno_form, TWO64 in EF. apply andb_prop in EF. destruct EF as [EF _]. apply Z.leb_le in EF. clear -GML EF DC D0 NDR N OFF0. lia. }
      pose proof (rreserved_disjoint1 _ _ (RFRES _ _ RF) ltac:(clear -GML NDR N OFF0; lia)) as DI.
      assert (DDJ : oldb + osz <= d \/ d + needed <= oldb).
      { pose proof (In_live_ranges st rid rg Hrg) as HI. unfold region_live_range in HI. rewrite Krg in HI.
        pose proof (ranges_free_In _ _ _ _ _ RF HI) as X. rewrite <- EML in X. clear -GML X. lia. }
      assert (GOOD : mremap_good oldb osz needed (MrMoved d)) by (unfold mremap_good; split; [exact DI| exact DDJ]).
      destruct (POST GOOD) as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & _ & _ & _).
      cbn [mremap_ret mremap_errno] in *.
      replace (ret_pc (Z_to_bv 64 0x19dc0)) with (Z_to_bv 64 0x19dc0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite unsigned_lit in MU2, ST2 by (clear -GML SPR SLO CLO; lia).
      replace (bv_unsigned sp + -64 - 112) with (bv_unsigned sp - 176) in MU2 by lia. rewrite ETP in MU2.
      unfold mremap_mem.
      assert (Hold : 0 <= oldb) by (clear -GML R4096; lia). assert (Hosz : 0 < osz) by (clear -GML OSZ16 OFF0 BSZ0; lia).
      assert (Hon : oldb + osz <= 2^64) by (clear -GML RC R4096; lia). assert (Hd : 0 <= d) by (clear -GML D0; lia).
      assert (Hdn : d + needed <= 2^64) by (clear -GML DC D0; lia).
      apply (SUCC d); clear SUCC.
      * exact D0.
      * exact DAL.
      * unfold alloc_ceiling. exact DC.
      * right. exact RF.
      * exact OK.
      * unfold is_err, TWO64. apply Z.ltb_ge. clear -GML DC D0 N33 NDR N OFF0; lia.
      * apply (mem_inv_mremap usegs m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ MI2). intros x Hx. apply ref_ro_addr_false. clear -GML Hx DI. lia.
      * apply (stk_mremap_other usegs m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ _ _ ST2); unfold alloc_ceiling in *; [clear -GML RC CLO; lia| clear -GML DC CLO; lia].
      * intros y Hy Ho Hn Hf He. rewrite (mremap_outside m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ) by (rewrite wa_unsigned by exact Hy; clear -GML Ho Hn; lia).
        apply MU2. rewrite wa_unsigned by exact Hy. cbn. unfold RERRNO in He. clear -GML Hf He. lia.
      * intros o1 Ho1. rewrite (mremap_copied m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ) by (rewrite wa_unsigned by (clear -GML Ho1 Hd Hdn; lia); clear -GML Ho1; lia).
        rewrite wa_unsigned by (clear -GML Ho1 Hd Hdn; lia). replace (oldb + (d + o1 - d)) with (oldb + o1) by lia. change (Z_to_bv 64 (oldb + o1)) with (wa (oldb + o1)).
        apply MU2. rewrite wa_unsigned by (clear -GML Ho1 R4096 RC; lia). cbn. clear -GML Ho1 R4096 RC OI CLO SLO. lia.
      * intros o1 Ho1. rewrite (mremap_zeroed m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ) by (rewrite wa_unsigned by (clear -GML Ho1 Hd Hdn Hosz; lia); clear -GML Ho1; lia). reflexivity.
      * apply (wr_at_mremap_new usegs m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ). exact (WR2of m2 MU2).
      * intros y Hy Ho W. destruct (Z.lt_ge_cases y d) as [Y1|Y1]; [| destruct (Z.lt_ge_cases y (d + needed)) as [Y2|Y2]].
        -- unfold wview. rewrite (mremap_outside m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ) by (rewrite wa_unsigned by exact Hy; clear -GML Ho Y1; lia). apply WM2. exact W.
        -- pose proof (wr_at_mremap_new usegs m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ (WR2of m2 MU2)) as (_ & _ & X).
           replace y with (d + (y - d)) by lia. apply X. clear -GML Y1 Y2. lia.
        -- unfold wview. rewrite (mremap_outside m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ) by (rewrite wa_unsigned by exact Hy; clear -GML Ho Y2; lia). apply WM2. exact W.
      * apply (rw_cells_mremap_other usegs m2 oldb osz d needed Hold Hosz Hon Hd GT Hdn DDJ _ _ ERR2); rewrite ETP; cbn; [clear -GML R4096 OI Hosz; lia| clear -DI NDR N OFF0; lia].
Qed.
End BIG.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rrealloc_spec : rrealloc_stmt.
Proof. exact (rrealloc_spec_gen rbig_proof). Qed.
End RC__1.
