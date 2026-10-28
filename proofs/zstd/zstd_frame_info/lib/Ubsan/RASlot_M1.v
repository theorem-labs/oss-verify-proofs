(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_I ASlot_M0 ASlot_M1.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W9 RASlot_M0.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

#[using="LBK"] Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

#[using="rc LB sc F ER SC RQ FIT TR GM MSK K0 LBK"] Lemma rta_slot_ok : exists b r,
  m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ slot_ok st' g b r k req
  /\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
  /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
               < r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
        free_slot_addr st0 a).
Proof.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).
  (* [comment removed for export] *)
  destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "00R0>11065263809.9515866215106.9316041791520.8430496497480.8430549869362.8431084497720.7231990092368.8433168643095.7833773540332.8434880930398.6934882981568.7441361156040.8441418117990.7847404385131.8951792396311.7851792400061.6951792577318.6351792693346.6451794592666.7451796692231.9451804965815.7151807072550.9351963384145.7551967810899.8457680746506.8857680746506.9457691186219.9359723841081.8759974749697.8462062374277.7065158581089.8465502415534.8967483933522.849879911069.88 00000D00L00g00o01601A01T01\01d01k02202:02>02R02Y02`02g02n03503<03C03J03U03`04304F04Y04f04n05?05J05N06806@S2K02B04SPAN2Ha1H2H0S2B03KLIS2RQ3FIT2K02B04SFIT3AVX3P2kS3MPL2B0S2LI2B0S2K02B03KLIS2RQ3FIT2K02B04SFITS3MSK2B0S2B03S16S2SC2B0S2SC2B0S2B03FRXS2B0S2RQ2K02B03S202OF2H0S2K02B0S2K02B0S2K02B0S2K02B0S2K02B0S2K02B0S2K02B0S2K02B0S2K02B03KLIS2K02B03KLIS2RQ3FIT2K02B04SFITS2RQ3FIT2K02B04SFITS2RQ3FIT2K02B04SFITS2RQ2K02B02OFS3GS02B0S2K03E632B05GSC48S2FB2B03MW2S2B0S2RQ2K03GS02B03S164SMOD3S313S202EL3MW13ST2S2B03KLI".
assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
  assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
  { apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  destruct (FM g b Hmem) as (FM1 & FM2 & _).
  assert (KLI : k <= m_last_idx (get_meta_rec st g)).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
    cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
  assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
  cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
  { pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
    exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
  pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
  pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
  unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
  destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
  assert (P2k : 0 < 2 ^ k <= msk).
  { split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
  exists b, r.
  split; [exact Hmem|]. split; [exact Hr|].
  split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
  split; [| split; [exact ST'|]].
  - pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
    assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
    constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
    + exact Hmem.
    + unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
    + exact Hk.
    + exact B0.
    + exact B16.
    + lia.
    + lia.
    + exact SPAN.
    + unfold UNIT in S16. lia.
    + unfold UNIT in SMOD. exact SMOD.
    + lia.
    + exact RQ.
    + lia.
    + intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
      destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
    + unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
    + intros off O0 OF.
      assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
      assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
    + unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
    + unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
    + unfold msk, mr in *. lia.
    + unfold mr. lia.
    + lia.
    + lia.
    + left. lia.
  - intros a Ha. rewrite ST' in Ha.
    destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
    assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
    destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
    exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
    split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
    + pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
    + assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
        by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End TASLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

#[using="rc R k o s Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req errv ERR TP HK"] Lemma rerrno_lit : errno_addr tp = 0x2df8c.
Proof. subst tp. unfold RATP. Local Ltac2 Set LiaHints.tbl := fun () => "0010>15706896144.70000001S".
rewrite unsigned_lit by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="st0 LB errv AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK F0"] Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
  rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
  rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
  rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof.
  intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
  unfold as_k. Local Ltac2 Set LiaHints.tbl := fun () => "00E0?10526002752.12611063064163.133121119566.119  16075364609.12117514996479.12126737759560.13333240656455.14134937747118.12237990650584.1344239425949.119 4239425949.97  44587665320.12159311736870.98 59323410545.12259323410545.12559323410545.13359323410545.13459323410545.13559323410545.1456440940956.133 909466635.99   00000>00M00N00R00V00]00l00m01701;01?01F01J01d02?02S03<03H03e04804<S2KK2Xq2L03H0'S2KK2Xq2B04B16'SS2HaS2HaS2KK2HoS2KK2Xq2Cb2B01ESS2KK2B02BES2KKS2KKS2KK2HcS2KKS3CLO2KK2Ha1X5ATOPR2LO3ASGS2KK2Ha2Xq2GI3CLO2LO3ASG2GCS3CLO2KK2Ho1X2RC3RI2S2KK2Ha2Xq2Cb2B02BE3RI13RI23CLO2LO3ASG2RCS2KK2Ho2Xq1HS2KK2Ho2Xq2Cb2B04B16'1H2H12H0S2KK2Ho2R02RC5ATOPRS2RQ".
replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
  cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
  pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
  pose proof (isf_mf _ _ F0) as MF.
  set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
  subst msk.
  destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
    as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
  fold st' in Hr', SO, STR, FSA.
  (* [comment removed for export] *)
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  (* [comment removed for export] *)
  assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
  { intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - left. left. exact X.
    - left. right. right. left. exact X.
    - left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
      exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
    - do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct ER as [_ EG EGR _ _ _ _ _].
      destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
      exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
      pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
  assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).
  (* [comment removed for export] *)
  assert (NIMG : forall a, 0x10000 <= a < 0x4f000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - atop_facts. lia.
    - exact (Hc X).
    - destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
      pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
  apply HK. unfold ras_post2.
  exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
  split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
  split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
           - intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
             + lia. + unfold RCTX in X. atop_facts. lia.
             + destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). atop_facts. lia.
             + destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). atop_facts. lia.
           - intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. { (* [comment removed for export] *)
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). atop_facts. lia. }
    intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
    - destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
    - destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
    - destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
      destruct (N.eq_dec (fst bq) rid) as [E|NE].
      + apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
      + pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
  split; [exact PE'|].
  split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
           intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
  split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
           unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { (* [comment removed for export] *) constructor.
    - intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
    - intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
    - unfold st'. cbn. apply (tr_tick _ _ _ TR).
    - intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
      unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
      destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
      exact (AC rid sh o' v t Esh Hc).
    - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
  split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
           pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
  right. split; [lia|]. exists g3, b, r.
  split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
  - intros a Ha. do 2 right. left. apply FSA. exact Ha.
  - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LEVEL.
End CANSEC1.
