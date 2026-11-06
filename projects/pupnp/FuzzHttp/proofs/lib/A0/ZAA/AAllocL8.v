(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P F_alloc_M
                        F_malloc_icpt ALedger AHeap2 AHeapB AFreeF AFreeZ AFreeL8 AAllocF AMallocP AMallocL8 AFsEnv AFteF.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section AL8.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Variable FI : fs_if.
Variable AI : am_if FI.

Definition fclass (lo q0 : Z) (iv : Z * Z) : Prop :=
  sub_iv lo q0 iv \/ iastat iv \/ iv = (THR + 3168, THR + 3169) \/ sub_iv (THR + 2800) (THR + 3168) iv.

#[using="Type"] Lemma fclass_mtouch : forall lo q0 X c v iv, fclass lo q0 iv -> mtouch AL lo q0 X c v iv.
Proof.
  intros lo q0 X c v iv [S1|[IA|[UB|TS]]].
  - left. left. exact S1.
  - do 5 right. left. exact IA.
  - do 6 right. exact UB.
  - left. right. right. left. unfold sub_iv in *. lia.
Qed.

Definition al8_post {ART : Type} (AX : ART -> pstate) (dn : Z) (gp : word) (F_ : bvmap 5 word) (fc : bv 32) (q0 lo q' : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (m0 mS : mem)
    : ART -> (word -> bool) -> machine_state -> Prop :=
  fun r H1 ms1 => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 s1' (A : Z) (junk : list byte) W,
    ms1 = MS (mkR ra (wz q') gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m1 (seg_rom asegs)
    /\ bs_ghost s1' = (H1, bs_pages s) /\ bs_X s1' = AX r /\ bs_quar s1' = bs_quar s /\ bs_nsec s1' = bs_nsec s + dn
    /\ (exists ach, bs_live s1' = (ach, n) :: bs_live s /\ A = lc_user AL ach)
    /\ mem_inv asegs m1 /\ stk asegs m1 lo q' /\ asan_env asegs m1 /\ RFAKE FI st m1
    /\ (forall LBk : list (block (am_K FI AI)),
          (forall b, In b LBk -> exists r, In r (bs_live s) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) -> apres FI AI LBk q0 m0 m1)
    /\ (forall r B cs, In r (bs_live s) -> qc_blk AL (fst r) <= B -> B + Z.of_nat (cells_size cs) <= qc_blk AL (fst r) + qc_bsize (fst r) ->
                       rw_cells asegs m0 B cs -> rw_cells asegs m1 B cs)
    /\ RHEAP_B AL E s1' ((A, A, n) :: LB) m1
    /\ rw_cells asegs m1 A [CB (Z.to_nat n) junk] /\ rw_cells asegs m1 (sh A) (shadow_cells (block_shadow n))
    /\ wmono asegs m0 m1
    /\ munch W mS m1 /\ (forall B k, q' <= B -> disjoint_from W B k).

Definition al8_stmt {ART : Type} (ATREE : itree nodeL (exc ART)) (AX : ART -> pstate) (dn : Z) (ASTK : Z)
    (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (tr : list Z) (q0 lo : Z) : Prop :=
  forall (gp : word) (F_ : bvmap 5 word) (fc : bv 32) (q' : Z) (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m0 mS : mem) (FT0 : list (Z * Z)) (STK TR : Z) (ws : list word),
    RHEAP_B AL E s LB m0 -> mem_inv asegs m0 -> asan_env asegs m0 -> RFAKE FI st m0 ->
    munch FT0 m0 mS -> wmono asegs m0 mS -> Forall (fclass lo q0) FT0 ->
    mclean (bs_H s) mS -> stk asegs mS lo q' ->
    dr_inv AL E (bs_X s) (bs_H s) mS (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s) ->
    alloc_env mS -> thread_env2 AL mS -> hooks_env mS -> RDEPOT D (bs_depot s) (bs_dtotal s) mS ->
    (exists inited, ia_cells 262144 262728 inited mS) ->
    rw_cells asegs mS STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q' <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs mS TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> q' <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    lo <= q' - ASTK -> q' <= q0 -> q0 <= 2^47 -> q' mod 16 = 0 ->
    implA (bs_H s) ATREE (al8_post AX dn gp F_ fc q0 lo q' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st n m0 mS)
      (MS (mkR ra (wz q') gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz n) (wz 8) (wz STK) (wz 1) (wz 1) a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz allocate_entry) fc None mS (seg_rom asegs)).

Hypothesis AO : alayout_ok AL.
Hypothesis SWIN_LO : 65536 <= SWIN D.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.

#[using="AO SWIN_LO FSBE STAT"] Lemma alloc_prim_L8 : forall s LB (st : fsstate FI) n tr q0 lo,
  alloc_ceiling <= lo -> In tr A0_TRACES -> 0 <= n <= A0_MAXREQ -> a0_need n <= 65536 ->
  (lbcZ LB (class_of (a0_need n)) + 1) * a0_csz (class_of (a0_need n)) <= A0_CAP (class_of (a0_need n)) ->
  al8_stmt (mp_tree AL (bs_prim s) n) (fun _ : unit => (fst (cache_alloc (bs_prim s) (class_of (a0_need n))), bs_sec s)) 0 ALLOC_STACK s LB st n tr q0 lo.
Proof.
  intros s LB st n tr q0 lo CLO TRIN NR NP CAP. unfold al8_stmt.
  intros gp F_ fc q' ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m0 mS FT0 STK TR ws
         HR MI AE RF MU0 WM0 FC0 MC ST INVS AENVS TE2S HKES RDS IAS SOBJ QSTK STKH BUF TRW LENW QTR TRH LOQ QQ0 Q0H Q16.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  destruct (traces_rng tr TRIN) as [LTR RNG].
  pose proof (rheap_stats AL E s LB m0 HR) as (CA0 & CM0 & CM1).
  assert (CR : 1 <= class_of (a0_need n) <= 31).
  { rewrite class_of_a0. assert (1 <= a0_need n) by (unfold a0_need; assert (8 <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia);
      assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia); lia). pose proof (a0_class_of_range (a0_need n) ltac:(lia)). lia. }
  pose proof (rheap_refill_budget AL E s LB m0 HR _ CR) as RB.
  assert (DOK0 : depot_ok (bs_depot0 s) (bs_depot s) (bs_dtotal s)) by (destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DOK & _); exact DOK).
  destruct (depot_room AL _ _ _ tr DOK0 ltac:(clear - LTR; lia) SWIN_LO) as (RN & RFo & RT).
  assert (AS : 128 <= ALLOC_STACK) by (vm_compute; discriminate).
  eapply implA_mono.
  - eapply (allocate_prim_spec AL E AO gp F_ fc q' lo LOH CLO LOQ ltac:(clear - QQ0 Q0H; lia) Q16
              ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (bs_X s) (bs_H s) mS n (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s)
              STK TR (bs_dtotal s) (bs_depot s) ws tr);
      [ exact MC | exact ST | exact INVS | exact NR | exact NP | exact RB | exact CA0 | exact CM0 | exact CM1 | exact AENVS | exact TE2S | exact HKES | exact RDS
      | exact SOBJ | exact QSTK | exact STKH | exact BUF | exact TRW | exact LENW | exact LTR | exact RNG | exact QTR | exact TRH | exact RN | exact RFo | exact RT ].
  - intros r H' ms' PO. unfold allocate_post_p in PO. cbv zeta in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & W & hs' & total' & EMS & EH & MU2 & WM2 & FW2 & INV' & WFC & HKN & LREP & STK' & C1 & C2 & V0 & V1 & V2 & RD' & DEP).
    assert (LQ : lo <= q0) by (clear - LOQ QQ0 AS; lia).
    set (X := bs_X s) in *. set (c := class_of (a0_need n)) in *. set (P' := fst (cache_alloc (fst X) c)) in *. set (v := snd (cache_alloc (fst X) c)) in *.
    set (ch := al_chunk_p (fst X) n) in *.
    assert (EK : qc_kind ch = QPrim c v) by reflexivity.
    pose proof HR as (PLB & LOK & AOx & INVB & QLG & GC & (TQC & QLL) & MTX & (CST & AFM) & QWF & RD & DOK & WFL & REPL & HKL & PSEC & COV & TE2 & HKE & (TR1 & TR2 & TR3) & AENV & _ & CCL & CCQ & SLK & BUD & FTE).
    pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (RP & _ & RS & _ & _ & _ & _ & _ & _ & _ & HOK & _).
    pose proof INV' as (RP' & _ & RS' & MI' & _ & _ & _ & _ & _ & _ & HOK' & _).
    destruct (clear_ctx AL (P', snd X) m1 RP' RS') as (WFN & _ & _). cbn [fst] in WFN.
    set (hs0 := map bpair (bs_gl s) ++ flat_map prim_of (flat_map qb_chunks (bs_gl s)) ++ heldB s).
    assert (HON : held_ok P' ((c, v) :: hs0)).
    { eapply held_ok_perm'; [| exact HOK']. unfold hs0, prim_of at 2. rewrite EK. cbn [fst app]. apply Permutation_sym.
      rewrite !app_assoc. apply Permutation_middle. }
    pose proof HON as [_ FHN]. apply Forall_cons_iff in FHN as [HN1 _].

    set (FT := FT0 ++ W).
    assert (MUT : munch FT m0 m1) by (unfold FT; exact (munch_joinP _ _ m0 mS m1 MU0 MU2)).
    assert (FTC : Forall (mtouch AL lo q0 X c v) FT).
    { unfold FT. apply Forall_app. split.
      - eapply Forall_impl; [| exact FC0]. intros iv FCx. exact (fclass_mtouch lo q0 X c v iv FCx).
      - eapply Forall_impl; [| exact FW2]. intros iv [AT|[CI|[CI|[DS|DR]]]].
        + left. eapply (atouch_mono AL lo q0 (fst X) (snd X) _ _ lo q' (fst X) (snd X) _ _); [lia| lia| intros; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact AT].
        + right; left; exact CI.
        + right; right; left; exact CI.
        + right; right; right; left; exact DS.
        + right; right; right; right; left; exact DR. }
    assert (FTZ : Forall (czone AL lo q0 (snd X)) FT) by (eapply Forall_impl; [| exact FTC]; intros iv MT; exact (mtouch_czone AL AO lo q0 X m0 P' c v iv RP RS HN1 WFN MT)).
    destruct (clear_ctx AL X m0 RP RS) as (_ & SOK & _).
    pose proof (fun W1 A k => mtouch_img_dj AL AO lo q0 X m0 P' c v LOH CLO RP RS HN1 WFN W1 A k) as IMGD.
    pose proof (fun A k => mtouch_thr_dj AL AO lo q0 X m0 P' c v LOH CLO RP RS HN1 WFN FT A k FTC) as THRD.
    assert (HULL : forall ch', held_kind X ch' -> (forall cv, In cv (prim_of ch') -> In cv hs0) -> forall A k, qc_hull AL ch' A k -> disjoint_from FT A k).
    { intros ch' HK' INH A k HU. apply dj_of_Forall. eapply Forall_impl; [| exact FTC]. intros iv MT.
      pose proof (hull_mtouch_dj AL AO lo q0 X m0 P' c v hs0 ch' iv A k LOH CLO RP RS HK' HON WFN INH MT HU) as DD. destruct iv as [a b]. cbn [disjoint_from] in DD. exact (proj1 DD). }
    assert (INHL : forall ch', In ch' (live_chunks s) -> forall cv, In cv (prim_of ch') -> In cv hs0).
    { intros ch' Hc cv Hcv. unfold hs0, heldB. apply in_or_app. right. apply in_or_app. right. apply in_flat_map. exists ch'. split; assumption. }
    destruct (malloc_prim_budget AL E s LB m0 c ch n H' hs' total' HR ltac:(clear - C1; lia) EK CAP) as [PI1 BUD']. cbv zeta in PI1, BUD'.
    pose proof LREP as (_ & _ & (ub & UB) & _ & _ & SHU & _). cbv zeta in UB, SHU.
    assert (ENQ : qc_n ch = al_n n) by reflexivity.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1,
           (mkASB H' (bs_pages s) P' (bs_sec s) (bs_quar s) hs' total' (bs_nsec s) ((ch, n) :: bs_live s) (bs_depot0 s)),
           (qc_hdr AL ch + 16), (if n =? 0 then [] else ub), W.
    split; [exact EMS|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [cbn [bs_nsec]; clear; lia|].
    split; [exists ch; split; reflexivity|].
    split; [exact MI'|]. split; [exact STK'|].
    split; [exact (asan_env_frame_m asegs m0 m1 _ AE MUT (czone_env_safe AL AO lo q0 (snd X) LOH SOK _ FTZ))|].
    split.
    { eapply (rfake_frame_m FI st m0 m1 _ RF MUT). eapply Forall_impl; [| exact FTZ]. intros iv CZ. left. rewrite FSBE. exact (czone_fs_dj AL AO lo q0 (snd X) LOH CLO SOK iv CZ). }
    split.
    { intros LBk HB. apply (apres_of_czone AL FI AI FSBE STAT lo q0 X m0 m1 _ (bs_live s) LBk AO LOH CLO RP RS MUT FTZ); [| exact HB|].
      - intros A k HA. exact (mtouch_above AL AO lo q0 X m0 P' c v LOH CLO RP RS HN1 WFN FT A k LQ FTC HA).
      - intros r0 Hr. assert (INC : In (fst r0) (live_chunks s)) by (unfold live_chunks; apply in_map; exact Hr).
        split; [exact (proj1 (Forall_forall _ _) LOK r0 Hr)|]. split; [exact (proj1 (Forall_forall _ _) HKL _ INC)|].
        split; [exact (proj1 (Forall_forall _ _) WFL _ INC)|]. exact (HULL _ (proj1 (Forall_forall _ _) HKL _ INC) (INHL _ INC)). }
    split.
    { intros r0 B cs Hr HB1 HB2 CS. assert (INC : In (fst r0) (live_chunks s)) by (unfold live_chunks; apply in_map; exact Hr).
      eapply rw_cells_transport_m; [exact CS| exact MUT|].
      eapply disjoint_from_sub; [exact (HULL _ (proj1 (Forall_forall _ _) HKL _ INC) (INHL _ INC) _ _ ltac:(left; split; reflexivity))| exact HB1| exact HB2]. }
    split.
    {
      pose proof AO as (_ & _ & _ & TLOx & _). pose proof TLOx as (_ & _ & T3x & _).
      unfold RHEAP_B. cbv zeta. unfold bs_X, bs_gl, live_chunks, heldB. cbn [bs_H bs_prim bs_sec bs_quar bs_depot bs_dtotal bs_live bs_depot0 q_glob q_loc map flat_map fst].
      split; [apply perm_skip; exact PLB|].
      split; [constructor; [unfold lr_ok; cbn [fst snd]; rewrite ENQ; unfold al_n; destruct (Z.eqb_spec n 0) as [->|NE]; [right; split; reflexivity| left; reflexivity]| exact LOK]|].
      split; [exact AO|].
      split; [exact (proj1 (dr_invB_of AL E _ _ _ _ _ _ INV'))|].
      assert (HBP : forall b, In b (bs_gl s) -> held1 (fst X) (bpair b) /\ In (bpair b) hs0).
      { intros b Hb. destruct HOK as [_ FH]. split; [apply (proj1 (Forall_forall _ _) FH)|]; apply in_or_app; left; apply in_map; exact Hb. }
      assert (QLF : forall l, incl l (bs_gl s) -> qlist_rep AL m0 l 0 -> qlist_rep AL m1 l 0).
      { intros l INC QL. apply (qlist_rep_hull AL FT m0 m1 l 0 MUT QL). apply Forall_forall. intros b Hb. destruct (HBP b (INC b Hb)) as [HB1 HB2].
        split; [exact (HULL (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) HB1 ltac:(intros cv [<-|[]]; exact HB2) _ _ ltac:(left; split; reflexivity))
               | exact (HULL (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) HB1 ltac:(intros cv [<-|[]]; exact HB2) _ _ ltac:(right; left; split; reflexivity))]. }
      split; [apply QLF; [unfold bs_gl; intros b Hb; apply in_or_app; left; exact Hb| exact QLG]|].
      split; [eapply rw_cells_transport_m; [exact GC| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add qcells]; clear; lia]]|].
      split.
      { split; [eapply rw_cells_transport_m; [exact TQC| exact MUT| apply THRD; cbn [cells_size csize Nat.add]; clear; lia]|].
        apply QLF; [unfold bs_gl; intros b Hb; apply in_or_app; right; exact Hb| exact QLL]. }
      split; [eapply rw_cells_transport_m; [exact MTX| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]]|].
      split; [split; (eapply rw_cells_transport_m; [eassumption| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
      split; [exact QWF|]. split; [exact RD'|].
      split; [exact (depot_ok_step _ _ _ tr hs' total' DOK TRIN ltac:(clear - LTR; lia) DEP)|].
      split; [constructor; [exact WFC| exact WFL]|].
      split.
      { constructor; [exact LREP|]. apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
        exact (lchunk_rep_hull AL X _ m0 m1 ch' AO RP RS HK' (proj1 (Forall_forall _ _) REPL ch' Hch') (proj1 (Forall_forall _ _) WFL ch' Hch') MUT (HULL ch' HK' (INHL ch' Hch'))). }
      split.
      { constructor; [exact HKN|]. apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
        unfold held_kind in *. destruct (qc_kind ch') as [c' v'|sc] eqn:EK'; [| exact HK'].
        destruct HON as [_ FHA]. apply (proj1 (Forall_forall _ _) FHA). right. apply (INHL ch' Hch'). unfold prim_of. rewrite EK'. left. reflexivity. }
      pose proof PI1 as (_ & _ & COV' & _ & _ & _ & PSEC').
      split; [exact PSEC'|]. split; [exact COV'|].
      split; [eapply (thread_env2_frame_m AL _ m0 m1 TE2 MUT); apply THRD; clear; lia|].
      split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]]|].
      split; [unfold trace_env; split; [| split]; (eapply rw_cells_transport_m; [eassumption| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
      split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
      split.
      {
        destruct IAS as (inited & IA).
        assert (TRC : forall A cs, rw_cells asegs mS A cs -> 740096 <= A -> A + Z.of_nat (cells_size cs) <= 1323916 -> rw_cells asegs m1 A cs).
        { intros A cs C0 H1 H2. eapply rw_cells_transport_m; [exact C0| exact MU2|].
          exact (alloc_W_ia_dj AL AO lo q' X m0 P' c v W A _ LOH CLO RP RS HN1 WFN FW2 H1 H2). }
        destruct IA as (FL & [j0 C0] & [j2 [C2x Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). exists inited. unfold ia_cells.
        split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; destruct inited; cbn [cells_size csize Nat.add]; clear; lia]|].
        split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
        split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2x| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
        split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
        split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
        exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
      split; [constructor; [unfold ch_cls_ok; rewrite EK; split; [rewrite ENQ; exact C2| clear - C1; lia]| exact CCL]|].
      split; [exact CCQ|]. split; [constructor; [unfold sec_slack_ok; rewrite EK; exact I| exact SLK]|]. split; [exact BUD'|].
      exact (fs_tls_env_frame_m _ _ _ _ _ FT m0 m1 FTE MUT (mtouch_fte AL AO lo q0 X m0 P' c v LOH CLO RP RS HN1 WFN FT FTC)). }
    split.
    { unfold al_n in ENQ. destruct (Z.eqb_spec n 0) as [->|NE]; [exact (rw_cells_CB0 m1 _ _ ub UB)|]. rewrite ENQ in UB. exact UB. }
    split.
    { unfold al_n in ENQ. destruct (Z.eqb_spec n 0) as [->|NE]; [| rewrite ENQ in SHU; exact SHU].
      change (shadow_cells (block_shadow 0)) with (@nil cell). destruct SHU as [[_ (SB0 & SB1 & _)] (SW0 & SW1 & _)].
      unfold rw_cells, cells_at, bytes_at, wr_at. cbn [cells_wf cells_bytes cells_size length Z.of_nat].
      assert (SH64 : sh (qc_hdr AL ch + 16) <= 2^64) by (clear - SB0 SB1; lia).
      repeat split; try lia; intros i Hi; cbn in Hi; lia. }
    split; [exact (wmono_trans asegs _ _ _ WM0 WM2)|].
    split; [exact MU2|].
    intros B k HB.
    assert (V1' : 16 * v + class_size c <= FA_OFF).
    { pose proof (WFN c ltac:(clear - C1; lia)) as PW. unfold pclass_wf in PW. cbv zeta in PW. destruct PW as (_ & _ & _ & _ & _ & _ & PW1 & PW2 & _). clear - V1 PW1 PW2. lia. }
    eapply (alloc_W_above AL AO X m0 lo q' c v W B k LOH CLO).
    + clear - LOQ AS. lia.
    + exact RP.
    + exact RS.
    + clear - C1. lia.
    + exact V0.
    + exact V1'.
    + exact FW2.
    + exact HB.
Qed.

End AL8.

