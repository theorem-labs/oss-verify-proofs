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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_enframe F_ntf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_B MallocFacts_R.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc MI_Inv MI_Read.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocKit_A MallocKit_B MallocKit_B2 MallocKit_B3.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMallocTreeX RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_get_meta RF_realloc_hdr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation RAREACH := (AREACH_from ref_reserved).

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rimplTX_hguard {R S} o t (c : bool) (k bail : Malloc.M R) (K : R -> MX S) s Q ms :
  (c = true -> rimplTX o (sbind (xlift k) K) s Q ms) -> rimplTX o (sbind (xlift (guard t c k bail)) K) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity|]. cbn [xlift sbind]. apply rimplTX_undef. Qed.

Lemma rimplTX_hrd8 {R S} o st q (k : Z -> Malloc.M R) (K : R -> MX S) s Q ms :
  rimplTX o (sbind (xlift (k (rdv pans_mem o st q))) K) s Q ms -> rimplTX o (sbind (xlift (rd8 st q k)) K) s Q ms.
Proof.
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  cbn [xlift sbind]. apply rimplTX_peek. cbv beta. rewrite peek_ok_pans. exact H.
Qed.

Lemma rimplTX_hrd16 {R S} o st q (k : Z -> Malloc.M R) (K : R -> MX S) s Q ms :
  rimplTX o (sbind (xlift (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)))) K) s Q ms ->
  rimplTX o (sbind (xlift (rd16 st q k)) K) s Q ms.
Proof. intros H. unfold rd16. apply rimplTX_hrd8, rimplTX_hrd8. exact H. Qed.

Lemma rimplTX_hrd32 {R S} o st q (k : Z -> Malloc.M R) (K : R -> MX S) s Q ms :
  rimplTX o (sbind (xlift (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3)))) K) s Q ms ->
  rimplTX o (sbind (xlift (rd32 st q k)) K) s Q ms.
Proof. intros H. unfold rd32. apply rimplTX_hrd8, rimplTX_hrd8, rimplTX_hrd8, rimplTX_hrd8. exact H. Qed.

Lemma rimplTX_hif {R S} o (c : bool) (t1 t2 : Malloc.M R) (K : R -> MX S) s Q ms :
  (c = true -> rimplTX o (sbind (xlift t1) K) s Q ms) -> (c = false -> rimplTX o (sbind (xlift t2) K) s Q ms) ->
  rimplTX o (sbind (xlift (if c then t1 else t2)) K) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

Lemma rimplTX_hret {R S} o (r : R) (K : R -> MX S) s Q ms :
  rimplTX o (K r) s Q ms -> rimplTX o (sbind (xlift (ret r)) K) s Q ms.
Proof. intros H. exact H. Qed.

Lemma rimplTX_hundef {R S} o w (k : Z -> Malloc.M R) (K : R -> MX S) s Q ms :
  rimplTX o (sbind (xlift (SVis (EUndef w) k)) K) s Q ms.
Proof. cbn [xlift sbind]. apply rimplTX_undef. Qed.

Lemma guard_true {R} t (c : bool) (k bail : Malloc.M R) : c = true -> guard t c k bail = k.
Proof. intros ->. reflexivity. Qed.
Lemma rd8_known' {R} st q (k : Z -> Malloc.M R) v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hdr_b3_idx i k : 0 <= i < 32 -> 0 <= k -> Z.land (i + 32 * k) 31 = i.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Lemma hdr_b3_rsv i k : 0 <= i < 32 -> 0 <= k -> Z.shiftr (i + 32 * k) 5 = k.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Lemma byte_of_2 q : 0 <= q < 2^16 -> byte_of q 0 + 256 * byte_of q 1 = q.
Proof.
  intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma byte_of_4 v : 0 <= v < 2^32 ->
  byte_of v 0 + 256 * byte_of v 1 + 65536 * byte_of v 2 + 16777216 * byte_of v 3 = v.
Proof.
  intros. unfold byte_of. rewrite !Z.shiftr_div_pow2 by lia. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  change (2^(8*0)) with 1. change (2^(8*1)) with 256. change (2^(8*2)) with 65536. change (2^(8*3)) with 16777216. change (2^8) with 256.
  rewrite Z.div_1_r. Z.div_mod_to_equations. lia.
Qed.

Lemma mod16_slot bmo stride i off : bmo mod 16 = 0 -> stride mod 16 = 0 -> (bmo + UNIT + stride * i + UNIT * off) mod 16 = 0.
Proof.
  intros H1 H2. unfold UNIT. rewrite <- Zplus_mod_idemp_r, (Z.mul_comm 16 off), Z_mod_mult, Z.add_0_r.
  rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_l, H2, Z.mul_0_l, (Z.mod_small 0), Z.add_0_r by lia.
  rewrite <- Zplus_mod_idemp_l, H1. reflexivity.
Qed.

Lemma off_fit stride off d : stride mod 16 = 0 -> 0 <= d -> 16 * off <= stride - 4 - d -> 16 * off + 16 <= stride.
Proof. intros. Z.div_mod_to_equations. lia. Qed.

Lemma le4_byte_of v : 0 <= v < 2^32 -> le4 (wz v) = [b8 (byte_of v 0); b8 (byte_of v 1); b8 (byte_of v 2); b8 (byte_of v 3)].
Proof.
  intros. rewrite le4_bytes by lia. unfold byte_of. rewrite !Z.shiftr_div_pow2 by lia. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  change (2^(8*0)) with 1. change (2^(8*1)) with 256. change (2^(8*2)) with 65536. change (2^(8*3)) with 16777216. change (2^8) with 256.
  rewrite Z.div_1_r. do 3 f_equal. f_equal. f_equal. symmetry. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rhdrQ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : mem) (G P B b3 mword sc S stride rsv : Z) : machine_state -> Prop :=
  rrhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 t5 t6 F fc lo st m G P B b3 mword sc S stride rsv.

Section HDR.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Lemma rrealloc_hdr_phase {X} :
  forall (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (o m : mem) (s : PState) (st0 : mstate) (LB : list block) (b : block) (pf : aptr) (n : Z) (t : N) (g : aptr) (i : Z)
         (K : option (aptr * Z * Z) -> MX X) (Q : X -> PState -> machine_state -> Prop),
  let st := set_tick t st0 in
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  RAREACH st0 LB -> (s_tick st0 <= t)%N -> rmrep st m -> mem_inv rsegs m ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st0 pf = blk_addr b -> s_slots st0 !! blk_slot b = Some (g, i) ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 ->
  a0 = Z_to_bv 64 (blk_addr b) -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  (forall ms' (bm : aptr) (off rsv : Z),
      m_mem mr = Some bm -> fst bm = fst pf -> 0 <= off -> 0 <= rsv ->
      snd (blk_slot b) = snd bm + UNIT + stride * i ->
      snd pf = snd (blk_slot b) + UNIT * off ->
      rsv = stride - IB - UNIT * off - blk_size b ->
      0 <= i <= m_last_idx mr -> 16 <= stride -> 0 <= m_sizeclass mr < 64 ->
      ((0 <= m_sizeclass mr < 48 /\ m_maplen mr <= 256) \/ (m_sizeclass mr = 63 /\ m_last_idx mr = 0 /\ m_maplen mr <> 0)) ->
      realloc_hdr st pf = ret (Some (g, i, blk_size b)) ->
      rhdrQ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 t5 t6 F fc lo st m
            (conc st g) (blk_addr b) (conc st bm) (i + 32 * Z.min rsv 5) (meta_word mr) (m_sizeclass mr)
            (conc st (blk_slot b)) stride rsv ms' ->
      rimplTX o (K (Some (g, i, blk_size b))) s Q ms') ->
  rimplTX o (sbind (xlift (realloc_hdr st pf)) K) s Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until Q. intros st mr stride AR TT MR MI Hb Hfst Hconc SL ST SLO A0 A1 N HK.
  assert (AR1 : RAREACH st LB) by (apply areach_tick; [exact AR| exact TT]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR1) as C.
  pose proof (ci_ticks _ _ C) as TK.
  assert (Hconc1 : conc st pf = blk_addr b) by exact Hconc.
  assert (SL1 : s_slots st !! blk_slot b = Some (g, i)) by exact SL.
  pose proof (areach_blk_hdr st LB b pf AR1 Hb Hfst Hconc1 g i SL1) as HH. cbv zeta in HH.
  fold mr in HH. fold stride in HH.
  destruct HH as (bm & off & rsv & q & Hmem & Fbm & HOST & Ii & Eslot & OFF0 & Epf & SZ0 & Ersv & RSV0 & Eq & Eq16 & QR &
                  C4 & C3 & C2 & C1 & BIG & CZ & CE & UNK & SCF & S16 & SM).
  pose proof (ci_gmetas _ _ C bm g HOST) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct HOST as [ai Hgh].
  set (po := snd pf) in *.
  assert (Fp : fst pf = fst bm) by (rewrite Hfst, <- Fbm; reflexivity).
  assert (Hrp : s_regions st !! fst pf = Some r) by (rewrite Fp; exact Hr).
  assert (HP : blk_addr b = r_base r + po) by (rewrite <- Hconc1; apply conc_region'; exact Hrp).
  assert (HB : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  assert (HS : conc st (blk_slot b) = r_base r + snd (blk_slot b)) by (apply conc_region'; rewrite <- Hfst; exact Hrp).
  assert (I32 : 0 <= i < 32) by (pose proof (go_li _ _ _ GO) as LI'; change (get_meta_rec st g) with mr in LI'; lia).
  assert (MIN5 : 0 <= Z.min rsv 5 <= 5) by lia.
  set (b3 := i + 32 * Z.min rsv 5) in *.
  assert (B3R : 0 <= b3 < 256) by (subst b3; lia).
  pose proof (hdr_b3_idx i (Z.min rsv 5) I32 ltac:(lia)) as B3I. fold b3 in B3I.
  pose proof (hdr_b3_rsv i (Z.min rsv 5) I32 ltac:(lia)) as B3S. fold b3 in B3S.
  pose proof (byte_of_range q 0 ltac:(lia) ltac:(lia)) as Q0R. pose proof (byte_of_range q 1 ltac:(lia) ltac:(lia)) as Q1R.
  pose proof (byte_of_2 q QR) as EQQ.
  assert (EB : aadd pf (- (UNIT * q) - UNIT) = bm).
  { unfold aadd. apply injective_projections; cbn [fst snd]; [exact Fp| unfold UNIT in *; fold po in Eq16; lia]. }
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold sstart_of in SPAN. fold mr in SPAN. rewrite Hmem in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  unfold realloc_hdr, get_meta.
  apply rimplTX_hguard. intros _.
  apply rimplTX_hrd16. apply rimplTX_hrd8. cbv zeta. apply rimplTX_hrd8.
  rewrite (rdv_known o st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; rewrite Hfst; replace (po + -4) with (po - 4) by lia; exact C4).
  rewrite (rdv_known o st (aadd pf (-3)) b3) by (cbn [aadd fst snd]; rewrite Hfst; replace (po + -3) with (po - 3) by lia; exact C3).
  rewrite (rdv_known o st (aadd pf (-2)) (byte_of q 0)) by (cbn [aadd fst snd]; rewrite Hfst; replace (po + -2) with (po - 2) by lia; exact C2).
  rewrite (rdv_known o st (aadd (aadd pf (-2)) 1) (byte_of q 1)) by (cbn [aadd fst snd]; rewrite Hfst; replace (po + -2 + 1) with (po - 1) by lia; exact C1).
  rewrite EQQ, B3I. cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta]. fold mr.
  apply rimplTX_hguard; intros G11. apply rimplTX_hguard; intros G12. apply rimplTX_hguard; intros G13. apply rimplTX_hguard; intros G14.
  destruct (s_areas st !! area_of g) as [ar|] eqn:AR0; [| apply rimplTX_hguard; intros; discriminate].
  apply rimplTX_hguard; intros G15. apply rimplTX_hguard; intros G16. apply rimplTX_hguard; intros G17. cbv beta.
  apply Z.eqb_eq in G15.
  (* [comment removed for export] *)
  unfold slot_start. rewrite Hmem. cbv beta zeta iota. fold stride.
  set (e := aadd (aadd bm (UNIT + stride * i)) (stride - IB)).
  assert (Fe : fst e = fst bm) by reflexivity.
  assert (Se : snd e = snd (blk_slot b) + stride - IB) by (unfold e; cbn [aadd snd]; rewrite Eslot; unfold UNIT, IB; lia).
  assert (Hre : s_regions st !! fst e = Some r) by (rewrite Fe; exact Hr).
  assert (ESZ : snd e - rsv - po = blk_size b) by (rewrite Se; fold po in Epf; rewrite Ersv, Epf; unfold UNIT, IB; lia).
  assert (CEk : forall k, cell_read (get_shadow st (fst e)) (snd e + - k) = cell_read (get_shadow st (fst (blk_slot b))) (snd (blk_slot b) + stride - IB - k)).
  { intros k. rewrite Fe, Fbm, Se. f_equal; lia. }
  (* [comment removed for export] *)
  unfold get_nominal_size. apply rimplTX_hrd8. cbv zeta.
  rewrite (rdv_known o st (aadd pf (-3)) b3) by (cbn [aadd fst snd]; rewrite Hfst; replace (po + -3) with (po - 3) by lia; exact C3).
  rewrite B3S.
  (* [comment removed for export] *)
  assert (FIN : a_check ar = c_secret (ctx st) ->
                (if m_sizeclass mr <? 48 then (size_class (m_sizeclass mr) * i <=? q) && (q <? size_class (m_sizeclass mr) * (i + 1)) else m_sizeclass mr =? 63) = true ->
                (if negb (m_maplen mr =? 0) then q <=? m_maplen mr * 4096 / UNIT - 1 else true) = true ->
                rimplTX o (K (Some (g, i, snd e - rsv - po))) s Q
                  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom rsegs))).
  2:{ specialize (FIN G15 G16 G17).
      (* [comment removed for export] *)
      assert (CAT : forall q' d v, fst q' = fst bm -> snd q' = snd e - d ->
                cell_read (get_shadow st (fst (blk_slot b))) (snd (blk_slot b) + stride - IB - d) = Known v ->
                rdv pans_mem o st q' = v).
      { intros q' d v Hf Hs Hc. apply rdv_known. rewrite Hf, Fbm, Hs, Se. rewrite <- Hc. f_equal; lia. }
      apply rimplTX_hif; intros HR5.
      - (* [comment removed for export] *)
        apply Z.leb_le in HR5. assert (R5 : 5 <= rsv) by lia. destruct (BIG R5) as (E4 & E3 & E2 & E1 & E5 & R32).
        apply rimplTX_hguard; intros _.
        apply rimplTX_hrd32.
        rewrite (CAT (aadd e (-4)) 4 (byte_of rsv 0) eq_refl ltac:(cbn; lia) E4).
        rewrite (CAT (aadd (aadd e (-4)) 1) 3 (byte_of rsv 1) eq_refl ltac:(cbn; lia) E3).
        rewrite (CAT (aadd (aadd e (-4)) 2) 2 (byte_of rsv 2) eq_refl ltac:(cbn; lia) E2).
        rewrite (CAT (aadd (aadd e (-4)) 3) 1 (byte_of rsv 3) eq_refl ltac:(cbn; lia) E1).
        rewrite (byte_of_4 rsv) by lia.
        apply rimplTX_hguard; intros _.
        apply rimplTX_hrd8. rewrite (CAT (aadd e (-5)) 5 0 eq_refl ltac:(cbn; lia) E5).
        apply rimplTX_hguard; intros _. cbv beta.
        apply rimplTX_hguard; intros _.
        apply rimplTX_hrd8. rewrite (CAT (aadd e (- rsv)) rsv 0 eq_refl ltac:(cbn; lia) (CZ ltac:(lia))).
        apply rimplTX_hguard; intros _.
        apply rimplTX_hrd8. rewrite (CAT e 0 0 eq_refl ltac:(lia) ltac:(rewrite Z.sub_0_r; exact CE)).
        apply rimplTX_hguard; intros _. exact FIN.
      - (* [comment removed for export] *)
        apply Z.leb_gt in HR5. assert (R5 : Z.min rsv 5 = rsv) by lia. rewrite R5.
        apply rimplTX_hguard; intros _.
        apply rimplTX_hrd8.
        assert (CZ' : cell_read (get_shadow st (fst (blk_slot b))) (snd (blk_slot b) + stride - IB - rsv) = Known 0).
        { destruct (Z.eq_dec rsv 0) as [->|NZ]; [rewrite Z.sub_0_r; exact CE| apply CZ; lia]. }
        rewrite (CAT (aadd e (- rsv)) rsv 0 eq_refl ltac:(cbn; lia) CZ').
        apply rimplTX_hguard; intros _.
        apply rimplTX_hrd8. rewrite (CAT e 0 0 eq_refl ltac:(lia) ltac:(rewrite Z.sub_0_r; exact CE)).
        apply rimplTX_hguard; intros _. exact FIN. }
  intros _ _ _.
  (* [comment removed for export] *)
  assert (NFR : Z.testbit (m_avail mr) i = false /\ Z.testbit (m_freed mr) i = false).
  { apply negb_true_iff in G13. apply negb_true_iff in G14. split; [exact G13| exact G14]. }
  destruct NFR as [TA TF].
  pose proof (go_avail _ _ _ GO) as AV. pose proof (go_freed _ _ _ GO) as FRD. pose proof (go_li _ _ _ GO) as LI.
  pose proof (go_freeable _ _ _ GO) as FB. pose proof (go_maplen _ _ _ GO) as ML. pose proof (go_sc _ _ _ GO) as GSC.
  change (get_meta_rec st g) with mr in AV, FRD, LI, FB, ML, GSC.
  pose proof (proj2 (proj2 (proj2 (ci_cx _ _ C)))) as [_ SE].
  assert (Hslot : r_base r + snd bm <= r_base r + snd (blk_slot b)) by (rewrite Eslot; unfold UNIT; lia).
  assert (ETOP : snd (blk_slot b) + stride <= round_up_pg (r_len r)) by (rewrite Eslot; unfold UNIT in *; lia).
  (* [comment removed for export] *)
  destruct (SH (fst bm) r Hr Kr) as (_ & HBY & _).
  assert (BY : forall d v, 0 <= d <= snd (blk_slot b) + stride - IB ->
            cell_read (get_shadow st (fst (blk_slot b))) (snd (blk_slot b) + stride - IB - d) = Known v ->
            bytes_at rsegs m (r_base r + (snd (blk_slot b) + stride - IB - d)) [b8 v]).
  { intros d v Hd Hc. rewrite <- Fbm in Hc.
    assert (RNG : 0 <= snd (blk_slot b) + stride - IB - d < round_up_pg (r_len r)). { clear -Hd ETOP Eslot B0 SI0. unfold UNIT, IB in *; lia. }
    exact (proj1 (HBY _ v RNG Hc)). }
  pose proof (mod16_slot (snd bm) stride i off B16 SM) as PAL. rewrite <- Eslot in PAL. fold po in Epf. rewrite <- Epf in PAL.
  pose proof (off_fit stride off (blk_size b) SM SZ0 ltac:(clear -Ersv RSV0; unfold IB, UNIT in *; lia)) as OFIT.
  assert (B160 : 160 <= b3 <-> 5 <= rsv) by (subst b3; clear -I32 RSV0; lia).
  pose proof (go_slot _ _ _ GO) as MSL.
  assert (G0 : 0 <= snd g).
  { destruct MSL as (a' & ar' & k' & Ha' & Hk' & Eg). rewrite Eg. cbn [aadd snd]. destruct (WA a' ar' Ha') as (ra' & _ & A0' & _).
    unfold AREA_HDR, META_SIZE, NSLOTS in *. clear -Hk' A0'. lia. }
  assert (P16' : 16 <= po /\ po + 16 <= snd (blk_slot b) + stride) by (clear -Epf Eslot B0 SI0 OFF0 OFIT; unfold UNIT in *; lia).
  eapply rimplTX_evt.
  { eapply (rrealloc_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n st pf r g (mkGhdr (Some g) ai) ar
              b3 (byte_of q 0) (byte_of q 1) rsv MR MI ST LO SLO Hrp Kr).
    all: rewrite ?EQQ, ?B3I, ?B3S, ?EB, ?Hfst.
    all: change (get_meta_rec st g) with mr; fold stride.
    - rewrite A0, unsigned_lit; [exact HP|]. clear -HP RB0 RBC P16' ETOP OFIT Epf OFF0. unfold alloc_ceiling, UNIT in *. pose proof (round_up_pg_ge (r_len r)). lia.
    - exact PAL.
    - exact A1.
    - exact N.
    - clear -Epf Eslot B0 SI0 OFF0. unfold UNIT in *. lia.
    - clear -Eq16 B0. unfold UNIT in *. lia.
    - clear -Epf OFIT ETOP. unfold UNIT in *. lia.
    - exact C4.
    - exact C3.
    - exact C2.
    - exact C1.
    - exact Hgh.
    - reflexivity.
    - exact MSL.
    - exact G0.
    - exact Hmem.
    - exact AR0.
    - exact G15.
    - exact AV.
    - exact FRD.
    - exact SE.
    - clear -LI; lia.
    - rewrite FB; lia.
    - clear -GSC; lia.
    - clear -ML; lia.
    - clear -Ii; lia.
    - exact TA.
    - exact TF.
    - intros Hlt. rewrite (proj2 (Z.ltb_lt _ _) Hlt) in G16. apply andb_prop in G16 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. split; [exact X1| exact X2].
    - clear -GSC; lia.
    - intros Hml. rewrite (proj2 (Z.eqb_neq _ _) Hml) in G17. cbn [negb] in G17. apply Z.leb_le in G17. unfold UNIT in G17.
      rewrite <- (Z.mul_assoc), (Z.mul_comm 4096) in G17 || idtac.
      replace (m_maplen mr * 4096 / 16) with (m_maplen mr * 256) in G17 by (rewrite <- (Z.div_mul (m_maplen mr * 256) 16) by lia; f_equal; lia). exact G17.
    - clear -GSC; lia.
    - exact S16.
    - rewrite HB. clear -Epf Eslot OFIT Ersv RSV0 SZ0. unfold UNIT, IB in *. lia.
    - rewrite HB. clear -ETOP Eslot. unfold UNIT, IB in *. lia.
    - intros H160. assert (R5 : 5 <= rsv) by (apply B160; exact H160). destruct (BIG R5) as (E4 & E3 & E2 & E1 & E5 & R32).
      split; [clear -R5; lia|]. split; [clear -R5 R32; lia|]. rewrite HB. split.
      + rewrite (le4_byte_of rsv) by (clear -R5 R32; lia).
        change [b8 (byte_of rsv 0); b8 (byte_of rsv 1); b8 (byte_of rsv 2); b8 (byte_of rsv 3)] with ([b8 (byte_of rsv 0)] ++ ([b8 (byte_of rsv 1)] ++ ([b8 (byte_of rsv 2)] ++ [b8 (byte_of rsv 3)]))).
        apply bytes_at_app. split.
        { replace (r_base r + snd bm + UNIT + stride * i + stride - IB - 4) with (r_base r + (snd (blk_slot b) + stride - IB - 4)) by (rewrite Eslot; lia). apply (BY 4); [clear -ETOP Eslot B0 SI0 S16; unfold UNIT, IB in *; lia| exact E4]. }
        apply bytes_at_app. split.
        { cbn [length Z.of_nat Pos.of_succ_nat]. replace (r_base r + snd bm + UNIT + stride * i + stride - IB - 4 + 1) with (r_base r + (snd (blk_slot b) + stride - IB - 3)) by (rewrite Eslot; lia). apply (BY 3); [clear -ETOP Eslot B0 SI0 S16; unfold UNIT, IB in *; lia| exact E3]. }
        apply bytes_at_app. split.
        { cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (r_base r + snd bm + UNIT + stride * i + stride - IB - 4 + 1 + 1) with (r_base r + (snd (blk_slot b) + stride - IB - 2)) by (rewrite Eslot; lia). apply (BY 2); [clear -ETOP Eslot B0 SI0 S16; unfold UNIT, IB in *; lia| exact E2]. }
        { cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (r_base r + snd bm + UNIT + stride * i + stride - IB - 4 + 1 + 1 + 1) with (r_base r + (snd (blk_slot b) + stride - IB - 1)) by (rewrite Eslot; lia). apply (BY 1); [clear -ETOP Eslot B0 SI0 S16; unfold UNIT, IB in *; lia| exact E1]. }
      + replace (r_base r + snd bm + UNIT + stride * i + stride - IB - 5) with (r_base r + (snd (blk_slot b) + stride - IB - 5)) by (rewrite Eslot; lia). apply (BY 5); [clear -ETOP Eslot B0 SI0 S16; unfold UNIT, IB in *; lia| exact E5].
    - replace (if 160 <=? b3 then rsv else Z.min rsv 5) with rsv by (destruct (Z.leb_spec 160 b3); [reflexivity| clear -B160 H RSV0; lia]).
      rewrite HB. clear -Epf Eslot Ersv RSV0 SZ0. unfold UNIT, IB in *. lia.
    - replace (if 160 <=? b3 then rsv else Z.min rsv 5) with rsv by (destruct (Z.leb_spec 160 b3); [reflexivity| clear -B160 H RSV0; lia]).
      replace (conc st bm + UNIT + stride * i + stride - IB - rsv) with (r_base r + (snd (blk_slot b) + stride - IB - rsv)) by (rewrite HB, Eslot; lia).
      apply (BY rsv); [clear -ETOP Eslot B0 SI0 S16 RSV0 Ersv SZ0 OFF0; unfold UNIT, IB in *; lia|].
      destruct (Z.eq_dec rsv 0) as [->|NZ]; [rewrite Z.sub_0_r; exact CE| apply CZ; clear -NZ RSV0; lia].
    - replace (conc st bm + UNIT + stride * i + stride - IB) with (r_base r + (snd (blk_slot b) + stride - IB - 0)) by (rewrite HB, Eslot; lia).
      apply (BY 0); [clear -ETOP Eslot B0 SI0 S16; unfold UNIT, IB in *; lia| rewrite Z.sub_0_r; exact CE]. }
  cbv beta. intros ms' HP'.
  rewrite ?EQQ, ?EB, ?B3I, ?B3S, <- ?HP in HP'.
  replace (if 160 <=? b3 then rsv else Z.min rsv 5) with rsv in HP' by (destruct (Z.leb_spec 160 b3); [reflexivity| clear -B160 H RSV0; lia]).
  replace (conc st bm + UNIT + get_stride (get_meta_rec st g) * i) with (conc st (blk_slot b)) in HP' by (rewrite HS, HB, Eslot; fold mr stride; lia).
  rewrite ESZ.
  eapply (HK ms' bm off rsv Hmem); [rewrite Hfst, <- Fbm; reflexivity| exact OFF0| exact RSV0| exact Eslot| exact Epf| exact Ersv| exact Ii| exact S16| clear -GSC; lia| | |].
  - exact SCF.
  - (* [comment removed for export] *)
    assert (CK : forall q' o' v, fst q' = fst (blk_slot b) -> snd q' = o' -> cell_read (get_shadow st (fst (blk_slot b))) o' = Known v ->
                 cell_read (get_shadow st (fst q')) (snd q') = Known v) by (intros q' o' v -> -> Hc; exact Hc).
    unfold realloc_hdr, get_meta. rewrite guard_true by (apply Z.eqb_eq; exact PAL).
    unfold rd16. rewrite (rd8_known' st _ _ (byte_of q 0)) by (apply (CK _ (po - 2)); [cbn; exact Hfst| cbn; lia| exact C2]).
    rewrite (rd8_known' st _ _ (byte_of q 1)) by (apply (CK _ (po - 1)); [cbn; exact Hfst| cbn; lia| exact C1]).
    rewrite (rd8_known' st _ _ b3) by (apply (CK _ (po - 3)); [cbn; exact Hfst| cbn; lia| exact C3]).
    cbv beta. rewrite (rd8_known' st _ _ 0) by (apply (CK _ (po - 4)); [cbn; exact Hfst| cbn; lia| exact C4]).
    cbv beta. cbn [Z.eqb negb]. rewrite EQQ, EB. unfold get_group. rewrite Hgh. cbn [g_meta]. change (get_meta_rec st g) with mr.
    rewrite B3I. rewrite (guard_true 11) by exact G11. rewrite (guard_true 12) by exact G12. rewrite (guard_true 13) by exact G13. rewrite (guard_true 14) by exact G14.
    rewrite AR0. rewrite (guard_true 15) by (apply Z.eqb_eq; exact G15). rewrite (guard_true 16) by exact G16. rewrite (guard_true 17) by exact G17.
    cbv beta. unfold slot_start. rewrite Hmem. cbv beta iota zeta. fold stride. fold e.
    unfold get_nominal_size. rewrite (rd8_known' st _ _ b3) by (apply (CK _ (po - 3)); [cbn; exact Hfst| cbn; lia| exact C3]). cbv beta zeta. rewrite B3S.
    assert (CK2 : forall q' d v, fst q' = fst bm -> snd q' = snd e - d -> cell_read (get_shadow st (fst (blk_slot b))) (snd (blk_slot b) + stride - IB - d) = Known v ->
                 cell_read (get_shadow st (fst q')) (snd q') = Known v).
    { intros q' d v Hf Hs Hc. rewrite Hf, Fbm, Hs, Se. rewrite <- Hc. f_equal; lia. }
    rewrite <- ESZ.
    destruct (Z.leb_spec 5 (Z.min rsv 5)) as [HR5|HR5].
    + assert (R5 : 5 <= rsv) by (clear -HR5; lia). destruct (BIG R5) as (E4 & E3 & E2 & E1 & E5 & R32).
      rewrite (guard_true 20) by (apply Z.eqb_eq; clear -HR5; lia).
      unfold rd32. rewrite (rd8_known' st _ _ (byte_of rsv 0)) by (apply (CK2 _ 4); [reflexivity| cbn; lia| exact E4]).
      rewrite (rd8_known' st _ _ (byte_of rsv 1)) by (apply (CK2 _ 3); [reflexivity| cbn; lia| exact E3]).
      rewrite (rd8_known' st _ _ (byte_of rsv 2)) by (apply (CK2 _ 2); [reflexivity| cbn; lia| exact E2]).
      rewrite (rd8_known' st _ _ (byte_of rsv 3)) by (apply (CK2 _ 1); [reflexivity| cbn; lia| exact E1]).
      cbv beta. rewrite (byte_of_4 rsv) by (clear -R5 R32; lia). rewrite (guard_true 21) by (apply Z.leb_le; exact R5).
      rewrite (rd8_known' st _ _ 0) by (apply (CK2 _ 5); [reflexivity| cbn; lia| exact E5]). cbv beta. rewrite (guard_true 25) by reflexivity.
      rewrite (guard_true 22) by (apply Z.leb_le; rewrite Se; clear -Epf Eslot Ersv RSV0 SZ0; unfold UNIT, IB in *; lia).
      rewrite (rd8_known' st _ _ 0) by (apply (CK2 _ rsv); [reflexivity| cbn; lia| apply CZ; clear -R5; lia]). cbv beta. rewrite (guard_true 23) by reflexivity.
      rewrite (rd8_known' st _ _ 0) by (apply (CK2 _ 0); [reflexivity| cbn; lia| rewrite Z.sub_0_r; exact CE]). cbv beta. rewrite (guard_true 24) by reflexivity.
      reflexivity.
    + assert (R5 : Z.min rsv 5 = rsv) by (clear -HR5 RSV0; lia). rewrite R5.
      rewrite (guard_true 22) by (apply Z.leb_le; rewrite Se; clear -Epf Eslot Ersv RSV0 SZ0; unfold UNIT, IB in *; lia).
      assert (CZ' : cell_read (get_shadow st (fst (blk_slot b))) (snd (blk_slot b) + stride - IB - rsv) = Known 0).
      { destruct (Z.eq_dec rsv 0) as [->|NZ]; [rewrite Z.sub_0_r; exact CE| apply CZ; clear -NZ RSV0; lia]. }
      rewrite (rd8_known' st _ _ 0) by (apply (CK2 _ rsv); [reflexivity| cbn; lia| exact CZ']). cbv beta. rewrite (guard_true 23) by reflexivity.
      rewrite (rd8_known' st _ _ 0) by (apply (CK2 _ 0); [reflexivity| cbn; lia| rewrite Z.sub_0_r; exact CE]). cbv beta. rewrite (guard_true 24) by reflexivity.
      reflexivity.
  - exact HP'.
Qed.
End HDR.
End RC__1.
