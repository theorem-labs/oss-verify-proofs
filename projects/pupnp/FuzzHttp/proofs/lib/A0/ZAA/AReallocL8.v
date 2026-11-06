(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P F_alloc_M
                        F_malloc_icpt F_realloc_icpt F_memcpy ALedger AHeap2 AHeapB AFreeF AFreeZ AFreeL8 AAllocF AMallocP AMallocL8 AAllocL8 AHeapLaws.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section RAL8.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis AO : alayout_ok AL.
Hypothesis SWIN_LO : 65536 <= SWIN D.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.

#[using="Type"] Lemma GOT_RMEM : forall m : mem, asan_env asegs m -> rw_cells asegs m 696568 [C8 (wz 704376)].
Proof.
  intros m AE. pose proof (asan_env_icpt asegs m AE) as IE. unfold icpt_env in IE.
  destruct IE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G.
Qed.

Definition dl8_tree (X : pstate) (Q : aquar) (ch : qchunk) : itree nodeL (exc unit) :=
  ebind (t_enq AL (fst X) (q_loc Q)) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) (q_loc Q)), snd X) (put_todo (fst X) (q_glob Q) (q_loc Q) ch)).

Definition dl8_state (s : astB) (ch : qchunk) (l1 l2 : list (qchunk * Z)) (H2 : word -> bool) (hs2 : list Z) (total2 : Z) : astB :=
  let X := bs_X s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let P := fst X in let X1 := (fst (enq_prim P loc), snd X) in let todo := put_todo P glob loc ch in
  mkASB H2 (bs_pages s) (fst (dorecycle X1 todo)) (snd (dorecycle X1 todo)) (mkAQ (put_loc P loc ch) (put_glob P glob loc ch)) hs2 total2 (bs_nsec s) (l1 ++ l2) (bs_depot0 s).

Definition dl8_post (gp : word) (F_ : bvmap 5 word) (fc : bv 32) (lo q' : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : astB) (LB : list (block Z)) (st : fsstate FI) (ch : qchunk) (l1 l2 : list (qchunk * Z)) (m : mem)
    : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H2 ms2 => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 W hs2 total2,
    ms2 = MS (mkR ra (wz q') gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m2 (seg_rom asegs)
    /\ mem_inv asegs m2 /\ stk asegs m2 lo q' /\ asan_env asegs m2 /\ RFAKE FI st m2
    /\ (forall LBk : list (block (am_K FI AI)),
          (forall b, In b LBk -> exists r, In r (l1 ++ l2) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) -> apres FI AI LBk q' m m2)
    /\ (forall r B cs, In r (l1 ++ l2) -> qc_blk AL (fst r) <= B -> B + Z.of_nat (cells_size cs) <= qc_blk AL (fst r) + qc_bsize (fst r) ->
                       rw_cells asegs m B cs -> rw_cells asegs m2 B cs)
    /\ RHEAP_B AL E (dl8_state s ch l1 l2 H2 hs2 total2) (lb_remove Z.eqb (lc_user AL ch) LB) m2
    /\ munch W m m2 /\ (forall B k, q' <= B -> disjoint_from W B k).

#[using="AO SWIN_LO FSBE STAT"] Lemma dealloc_L8_at : forall (gp : word) (F_ : bvmap 5 word) (fc : bv 32) (q' lo : Z)
    (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    s LB (m : mem) (st : fsstate FI) ch n l1 l2 (tr : list Z) (STK TR : Z) (ws : list word),
  RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
  bs_live s = l1 ++ (ch, n) :: l2 -> List.NoDup (map (@blk_id Z) LB) ->
  stk asegs m lo q' -> alloc_ceiling <= lo -> lo <= q' - DEALLOC_STACK -> q' <= 2^47 -> q' mod 16 = 0 ->
  In tr A0_TRACES ->
  rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q' <= STK -> STK + 16 <= 2^47 ->
  u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> q' <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
  implA (bs_H s) (dl8_tree (bs_X s) (bs_quar s) ch)
    (dl8_post gp F_ fc lo q' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st ch l1 l2 m)
    (MS (mkR ra (wz q') gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz (qc_hdr AL ch + 16)) (wz 0) (wz 0) (wz STK) (wz 1) a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz deallocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros gp F_ fc q' lo ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s LB m st ch n l1 l2 tr STK TR ws
         HR MC MI AE RF EL NDK ST CLO LOQ QH Q16 TRIN SOBJ QSTK STKH BUF TRW LENW QTR TRH.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  destruct (traces_rng tr TRIN) as [LTR RNG].
  destruct (free_pre_at AL E s LB m ch n l1 l2 HR MI EL) as (INV & HK & WFC & LREP & NSC & HINB).
  pose proof (rheap_stats AL E s LB m HR) as (CA0 & CM0 & CM1). pose proof (rheap_refill_budget AL E s LB m HR K_BCLASS ltac:(lia)) as RB24.
  pose proof HR as (PLB & LOK & _ & _ & QLG & GC & QCL & MTX & (CST & AFM) & (FWF & QBL & QBG) & RD & DOK & _ & _ & _ & _ & _ & TE2 & HKE & TRE & AENV & (inited & IA) & _).
  assert (FWF' : Forall qbatch_wf (q_glob (bs_quar s) ++ q_loc (bs_quar s))) by (eapply Permutation_Forall; [apply Permutation_app_comm| exact FWF]).
  destruct (depot_room AL _ _ _ tr DOK ltac:(clear - LTR; lia) SWIN_LO) as (RN & RFo & RT).
  assert (DS : 96 <= DEALLOC_STACK) by (vm_compute; discriminate).
  unfold dl8_tree.
  eapply implA_mono.
  - eapply (deallocate_spec AL E AO gp s10 s11 F_ fc q' lo LOH CLO LOQ QH Q16 ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6
              (bs_X s) (bs_H s) m (q_glob (bs_quar s)) (q_loc (bs_quar s)) ch _ STK TR (bs_dtotal s) (bs_depot s) ws tr);
      [ exact MC | exact ST | exact INV | exact HK | exact WFC | exact LREP | exact NSC | exact QLG | exact GC | exact QCL | exact MTX | exact CST | exact AFM | exact FWF'
      | rewrite qbytes_app; lia
      | exact RB24
      | exact CA0 | exact CM0 | exact CM1
      | apply Forall_app in FWF as [FWL _]; pose proof (qbytes_len _ FWL) as QL; lia
      | exact TE2 | exact HKE | exact RD | exact SOBJ | exact QSTK | exact STKH | exact BUF | exact TRW | exact LENW | exact LTR | exact RNG | exact QTR | exact TRH
      | exact RN | exact RFo | exact RT ].
  - intros r H2 ms2 PO. unfold qchunk_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & W & hs2 & total2 & PO). cbv zeta in PO.
    destruct PO as (EMS & EH & MU & FW & INV' & XLE & STK' & QLG' & GC' & QCL' & MTX' & VNG & NBX & RD' & DEP).
    set (X := bs_X s) in *. set (glob := q_glob (bs_quar s)) in *. set (loc := q_loc (bs_quar s)) in *.
    pose proof INV as (RP & _ & RS & _ & _ & _ & _ & _ & _ & _ & HOK & _).
    change (bs_gl s) with (glob ++ loc) in *.
    assert (TCH : Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch)).
    { destruct HOK as [_ FH]. unfold tc_of. rewrite <- app_assoc. rewrite !app_assoc in FH. apply Forall_app in FH as [FH _]. rewrite <- !app_assoc in FH. exact FH. }
    assert (TSI : incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X))).
    { destruct (dr_inv_tc AL E X (bs_H s) m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) [] (prim_of ch ++ flat_map prim_of (map fst (l1 ++ l2))) ltac:(rewrite app_nil_r; exact INV)) as [_ TSI0].
      apply incl_app; [exact TSI0|]. destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
    assert (FWT : Forall (ftouch AL q' lo X glob loc ch) W).
    { eapply Forall_impl; [| exact FW]. intros iv [AT|[NB|[DSx|DR]]]; [left; exact AT| right; left; exact NB| right; right; left; exact DSx| right; right; right; left; exact DR]. }

    assert (IA' : exists i, ia_cells 262144 262728 i m2).
    { assert (TRC : forall A cs, rw_cells asegs m A cs -> 740096 <= A -> A + Z.of_nat (cells_size cs) <= 1323916 -> rw_cells asegs m2 A cs).
      { intros A cs C0 H1 H2x. eapply rw_cells_transport_m; [exact C0| exact MU|].
        apply (ficpt_img_dj AL AO q' lo LOH CLO q' X m glob loc ch W A _ RP RS TCH TSI VNG FW); [clear - H1; lia| clear - H2x; lia]. }
      destruct IA as (FL & [j0 C0] & [j2 [C2x Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). exists inited. unfold ia_cells.
      split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; destruct inited; cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2x| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
      split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
      exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
    pose proof (free_post_core AL E FI AI FSBE STAT q' lo s LB m ch n l1 l2 tr st H2 m2 W hs2 total2 HR MI AE RF EL NDK CLO ltac:(clear - LOQ DS; lia) TRIN) as CORE.
    cbv zeta in CORE. fold X glob loc in CORE.
    destruct (CORE MU FWT INV' QLG' GC' QCL' MTX' VNG NBX RD' IA' DEP) as (MI' & AE' & RF' & AP' & BLK' & HR').
    unfold dl8_post. exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W), hs2, total2.
    split; [exact EMS|]. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|]. split; [exact AP'|]. split; [exact BLK'|].
    split; [exact HR'|]. split; [exact MU|].
    intros B k HB. exact (qchunk_W_above AL AO q' lo LOH CLO LOQ X m glob loc ch W B k RP RS TCH TSI VNG FW HB).
Qed.

Definition reallocate_entry : Z := 0x3408c.

Definition rl_cpre (s : astB) (mW : mem) : Prop :=
  dr_inv AL E (bs_X s) (bs_H s) mW (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s)
  /\ alloc_env mW /\ thread_env2 AL mW /\ hooks_env mW /\ RDEPOT D (bs_depot s) (bs_dtotal s) mW /\ ia_cells 262144 262728 true mW.

Definition rl8_cpost {ART : Type} (AX : ART -> pstate) (dn : Z) (q0 : Z) (s : astB) (LB : list (block Z)) (st : fsstate FI)
    (ch : qchunk) (l1 l2 : list (qchunk * Z)) (n oldn : Z) (old : list byte) (m0 : mem)
    : mem -> ART -> (word -> bool) -> word -> mem -> Prop :=
  fun _ r H3 a0 m3 => exists s1' ach hs3 total3 (A' : Z) (junk : list byte) (m1 : mem),
    a0 = wz A'
    /\ bs_X s1' = AX r /\ bs_quar s1' = bs_quar s /\ bs_nsec s1' = bs_nsec s + dn /\ bs_pages s1' = bs_pages s
    /\ bs_live s1' = (ach, n) :: bs_live s
    /\ RHEAP_B AL E s1' ((A', A', n) :: LB) m1
    /\ mem_inv asegs m3 /\ asan_env asegs m3 /\ RFAKE FI st m3
    /\ (forall LBk : list (block (am_K FI AI)),
          (forall b, In b LBk -> exists r0, In r0 (l1 ++ l2) /\ blk_addr b = lc_user AL (fst r0) /\ blk_size b = snd r0) -> apres FI AI LBk q0 m0 m3)
    /\ RHEAP_B AL E (dl8_state s1' ch ((ach, n) :: l1) l2 H3 hs3 total3) ((A', A', n) :: lb_remove Z.eqb (lc_user AL ch) LB) m3
    /\ rw_cells asegs m3 A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n oldn)) old ++ junk)]
    /\ rw_cells asegs m3 (sh A') (shadow_cells (block_shadow n)).

Definition rl8_post {ART : Type} (AX : ART -> pstate) (dn : Z) (gp : word) (F_ : bvmap 5 word) (fc : bv 32) (q0 lo q' : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s : astB) (LB : list (block Z)) (st : fsstate FI)
    (ch : qchunk) (l1 l2 : list (qchunk * Z)) (n oldn : Z) (old : list byte) (m0 mW : mem)
    : ART -> (word -> bool) -> machine_state -> Prop :=
  fun r H3 ms3 => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3 W,
    ms3 = MS (mkR ra (wz q') gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m3 (seg_rom asegs)
    /\ munch W mW m3 /\ (forall B k, q' <= B -> disjoint_from W B k) /\ stk asegs m3 lo q'
    /\ rl8_cpost AX dn q0 s LB st ch l1 l2 n oldn old m0 mW r H3 a0 m3.

Definition rl8_tree {ART : Type} (ATREE : itree nodeL (exc ART)) (AX : ART -> pstate) (Q : aquar) (ch : qchunk) : itree nodeL (exc ART) :=
  ebind ATREE (fun r => ebind (dl8_tree (AX r) Q ch) (fun _ => Ret (Ok r))).

Definition memcpy_post_z (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dd Ss N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Dd) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Dd, Dd + N)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Dd [CB (Z.to_nat N) src] /\ bytes_at asegs m' Ss src.

#[using="Type"] Lemma memcpy_spec_z : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dd Ss N : Z) (src junk : list byte),
  bytes_at asegs m Ss src -> length src = Z.to_nat N -> rw_cells asegs m Dd [CB (Z.to_nat N) junk] ->
  (Ss + N <= Dd \/ Dd + N <= Ss) -> mem_inv asegs m ->
  0 <= Dd < 2^64 -> 0 <= Ss < 2^64 -> 0 <= N < 2^64 ->
  evt asegs (memcpy_post_z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dd Ss N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Dd) (wz Ss) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xa1e18) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros SRC LEN DST SEP MI HD HS HN.
  assert (Ed : bv_unsigned (Z_to_bv 64 Dd) = Dd) by (apply unsigned_lit; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 Ss) = Ss) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memcpy_spec; rewrite ?Ed, ?Es, ?En; eauto. }
  intros ms' Q. unfold memcpy_post in Q. rewrite !Ed, !Es, !En in Q. exact Q.
Qed.

#[using="Type"] Lemma bytes_at_det : forall (m : mem) A (x y : list byte), bytes_at asegs m A x -> bytes_at asegs m A y -> length x = length y -> x = y.
Proof.
  intros m A x y (_ & _ & HX) (_ & _ & HY) LEN. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length x)) as [LT|GE].
  - rewrite <- (HX i LT). rewrite <- (HY i ltac:(rewrite <- LEN; exact LT)). reflexivity.
  - rewrite (proj2 (nth_error_None x i) GE). symmetry. apply nth_error_None. rewrite <- LEN. exact GE.
Qed.

#[using="AO FSBE STAT"] Lemma copy_frame : forall s1 LB1 (m1 m2 : mem) (st : fsstate FI) ach n rest A' k q0 lo,
  RHEAP_B AL E s1 LB1 m1 -> mem_inv asegs m1 -> bs_live s1 = (ach, n) :: rest -> A' = lc_user AL ach -> In (A', A', n) LB1 -> 0 <= k <= n ->
  munch [(A', A' + k)] m1 m2 -> wmono asegs m1 m2 -> alloc_ceiling <= lo -> lo <= q0 ->
  RHEAP_B AL E s1 LB1 m2
  /\ (asan_env asegs m1 -> asan_env asegs m2)
  /\ (RFAKE FI st m1 -> RFAKE FI st m2)
  /\ (forall lo' q', stk asegs m1 lo' q' -> alloc_ceiling <= lo' -> lo' <= q' -> stk asegs m2 lo' q')
  /\ (forall LBk : list (block (am_K FI AI)),
        (forall b, In b LBk -> exists r0, In r0 rest /\ blk_addr b = lc_user AL (fst r0) /\ blk_size b = snd r0) -> apres FI AI LBk q0 m1 m2).
Proof.
  intros s1 LB1 m1 m2 st ach n rest A' k q0 lo HR MI EL EA HIN KR MU WM CLO LQ.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof HR as (_ & LOK & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _ & HKL & _).
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (RP & _ & RS & _).
  unfold live_chunks in WFL, HKL. rewrite EL in LOK, WFL, HKL. cbn [map fst] in WFL, HKL.
  apply Forall_cons_iff in LOK as [LRA LOKr]. apply Forall_cons_iff in WFL as [WFA WFr]. apply Forall_cons_iff in HKL as [HKA HKr].
  unfold lr_ok in LRA. cbn [fst snd] in LRA.
  pose proof (held_hull_geo AL AO (bs_X s1) m1 ach RP RS HKA) as G. cbv zeta in G. destruct G as (_ & _ & _ & G4 & G5 & G6 & _ & G8 & _).
  pose proof WFA as (RZ16 & RZM & NA1 & RZN & _).
  assert (RU0 : qc_n ach <= rup8 (qc_n ach)) by (unfold rup8; clear - NA1; Z.div_mod_to_equations; lia).
  assert (EA2 : A' = qc_blk AL ach + qc_rz ach) by (rewrite EA; unfold lc_user, qc_hdr; clear; lia).

  assert (IN1 : qc_blk AL ach <= A' /\ A' + k <= qc_blk AL ach + qc_bsize ach) by (clear - EA2 RZ16 RZN RU0 KR LRA; lia).
  layout_facts AO 4%nat LF4. destruct LF4 as ((FPL & _) & FCE & FMOD & _).
  assert (FSH : sh (al_fsb AL) + A0_FS_SHSIZE = sh (al_fsb AL + A0_FS_SIZE)) by (unfold sh; clear - FMOD; Z.div_mod_to_equations; lia).
  assert (FS1 : 2147450880 <= sh (al_fsb AL) /\ sh (al_fsb AL + A0_FS_SIZE) <= 17594333495296)
    by (unfold sh, SHADOW_OFF; clear - FPL FCE ACR; Z.div_mod_to_equations; lia).
  split.
  { apply (law_heap_frame AL E AO FI FSBE s1 LB1 m1 m2 [(A', A' + k)] HR MU WM). constructor; [| constructor].
    right. right. left. exists (A', A', n). split; [exact HIN|]. unfold blk_addr, blk_size. cbn [fst snd]. clear - KR. lia. }
  split.
  { intros AE. apply (asan_env_frame_m asegs m1 m2 _ AE MU). unfold env_safe. constructor; [| constructor]. left. cbn [fst]. clear - IN1 G4. lia. }
  split.
  { intros RF. apply (rfake_frame_m FI st m1 m2 _ RF MU). constructor; [| constructor]. left. cbn [fst snd]. rewrite FSBE, FSH.
    split; [clear - IN1 G8; lia| clear - IN1 G6 FS1; lia]. }
  split.
  { intros lo' q' ST CL' LQ'. apply (stk_transport_m _ m1 m2 lo' q' ST MU). cbn [disjoint_from]. clear - IN1 G5 CL'. lia. }
  intros LBk HB a Ha AC.
  assert (NI : ~ (A' <= a < A' + k)).
  { intros RNG. destruct AC as [AC|[AC|[AC|[AC|[AC|AC]]]]].
    - clear - AC RNG IN1 G5 CLO LQ. lia.
    - destruct AC as (lo' & hi' & STx & RNGs). apply STAT in STx. unfold a0_static in STx.
      assert (S6 : 0x800b9200 <= sh alloc_ceiling - sh alloc_ceiling mod 8) by (unfold sh, SHADOW_OFF; clear - ACR; Z.div_mod_to_equations; lia).
      clear - STx RNGs RNG IN1 G4 G6 S6. lia.
    - destruct AC as (b & Hb & RNGb). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      assert (APc : chunk_apart AL ach ch').
      { pose proof (live_fop AL E AO s1 LB1 m1 HR) as FOP. unfold live_chunks in FOP. rewrite EL in FOP. cbn [map fst] in FOP.
        inversion FOP as [|x0 l0 FA0 _]; subst x0 l0. apply (proj1 (Forall_forall _ _) FA0). apply in_map_iff. exists (ch', cn). split; [reflexivity| exact Hr]. }
      pose proof (proj1 (Forall_forall _ _) WFr ch' ltac:(apply in_map_iff; exists (ch', cn); split; [reflexivity| exact Hr])) as (RZ16' & _ & NR' & RZN' & _).
      pose proof (proj1 (Forall_forall _ _) LOKr (ch', cn) Hr) as LR'. unfold lr_ok in LR'. cbn [fst snd] in LR'.
      assert (RU' : qc_n ch' <= rup8 (qc_n ch')) by (unfold rup8; clear - NR'; Z.div_mod_to_equations; lia).
      unfold chunk_apart in APc. unfold lc_user, qc_hdr in BA. clear - APc RNG RNGb IN1 BA BS RZ16' RZN' RU' LR' NR'. lia.
    - rewrite FSBE in AC. clear - AC RNG IN1 G8. lia.
    - rewrite FSBE, FSH in AC. clear - AC RNG IN1 G6 FS1. lia.
    - destruct AC as (b & Hb & RNGb). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      pose proof (proj1 (Forall_forall _ _) HKr ch' ltac:(apply in_map_iff; exists (ch', cn); split; [reflexivity| exact Hr])) as HK'.
      pose proof (held_hull_geo AL AO (bs_X s1) m1 ch' RP RS HK') as G'. cbv zeta in G'. destruct G' as (_ & _ & _ & G4' & G5' & _).
      pose proof (proj1 (Forall_forall _ _) WFr ch' ltac:(apply in_map_iff; exists (ch', cn); split; [reflexivity| exact Hr])) as (RZ16' & _ & NR' & RZN' & _).
      pose proof (proj1 (Forall_forall _ _) LOKr (ch', cn) Hr) as LR'. unfold lr_ok in LR'. cbn [fst snd] in LR'.
      assert (RU' : qc_n ch' <= rup8 (qc_n ch')) by (unfold rup8; clear - NR'; Z.div_mod_to_equations; lia).
      assert (BL : Z.of_nat (length (block_shadow (blk_size b))) <= blk_size b / 8 + 1).
      { rewrite BS. destruct LR' as [LR'|[LR' _]]; rewrite LR'; [rewrite (block_shadow_len (qc_n ch') ltac:(clear - NR'; lia)); unfold rup8; clear; Z.div_mod_to_equations; lia| change (Z.of_nat (length (block_shadow 0))) with 0; clear; Z.div_mod_to_equations; lia]. }
      unfold lc_user, qc_hdr in BA. rewrite BA in RNGb.
      assert (SHB : 2147450880 + 791040 <= sh (qc_blk AL ch' + qc_rz ch' - 16 + 16)
                    /\ sh (qc_blk AL ch' + qc_rz ch' - 16 + 16) + (blk_size b / 8 + 1) <= 17594333495296).
      { unfold sh, SHADOW_OFF. rewrite BS. clear - G4' G5' RZ16' RZN' RU' LR' NR' ACR. Z.div_mod_to_equations. lia. }
      clear - RNG RNGb IN1 G4 G6 BL SHB. lia. }
  assert (O : outside [(A', A' + k)] (bv_unsigned (wa a))) by (rewrite wa_unsigned by lia; cbn [outside]; split; [clear - NI; lia| exact I]).
  split; [left; exact (MU _ O)|]. unfold wview. rewrite (MU _ O). exact (fun Hx => Hx).
Qed.

Section REALLOCATE.
  Variable ART : Type.
  Variable ATREE : itree nodeL (exc ART).
  Variable AX : ART -> pstate.
  Variables (dn ASTK : Z).
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q' q0 lo : Z).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQA : lo <= q' - 48 - ASTK.
  Hypothesis LOQD : lo <= q' - 48 - DEALLOC_STACK.
  Hypothesis QQ0 : q' <= q0.
  Hypothesis Q0H : q0 <= 2^47.
  Hypothesis Q16 : q' mod 16 = 0.

  #[using="AO SWIN_LO FSBE STAT CLO LOQA LOQD QQ0 Q0H Q16"] Theorem reallocate_L8 : forall (ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (s : astB) (LB : list (block Z)) (st : fsstate FI) (ch : qchunk) (oldn : Z) (l1 l2 : list (qchunk * Z)) (n : Z) (tr : list Z) (old : list byte)
        (m0 mW : mem) (FT0 : list (Z * Z)) (STK TR : Z) (ws : list word),
    RHEAP_B AL E s LB m0 -> mem_inv asegs m0 -> asan_env asegs m0 -> RFAKE FI st m0 ->
    bs_live s = l1 ++ (ch, oldn) :: l2 -> rw_cells asegs m0 (qc_hdr AL ch + 16) [CB (Z.to_nat oldn) old] ->
    munch FT0 m0 mW -> wmono asegs m0 mW -> Forall (fclass AL lo q0) FT0 ->
    mclean (bs_H s) mW -> stk asegs mW lo q' -> rl_cpre s mW ->
    rw_cells asegs mW STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> q' <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs mW TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> q' <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n tr q0 lo ->
    0 < n <= A0_MAXREQ -> In tr A0_TRACES ->
    implA (bs_H s) (rl8_tree ATREE AX (bs_quar s) ch)
      (rl8_post AX dn gp F_ fc q0 lo q' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st ch l1 l2 n oldn old m0 mW)
      (MS (mkR ra (wz q') gp (wz A0_TP) t0 t1 t2 s0 s1 (wz INSTANCE) (wz (qc_hdr AL ch + 16)) (wz n) (wz STK) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz reallocate_entry) fc None mW (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s LB st ch oldn l1 l2 n tr old m0 mW FT0 STK TR ws
           HR MI AE RF EL OLD0 MU0 WM0 FC0 MC ST (INVW & AENVW & TE2W & HKEW & RDW & IAW) SOBJ QSTK STKH BUF TRW LENW QTR TRH ALLOC NR TRIN.
    unfold reallocate_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    assert (DS : 96 <= DEALLOC_STACK) by (vm_compute; discriminate).
    assert (QH : q' <= 2^47) by (clear - QQ0 Q0H; lia).
    assert (LQ1 : lo <= q' - 48 - 96) by (clear - LOQD DS; lia).
    pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
    destruct (free_pre_at AL E s LB m0 ch oldn l1 l2 HR MI EL) as (INV0 & HK & WFC & LREP0 & NSC & HINB).
    pose proof INV0 as (RP0 & _ & RS0 & _).
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL (bs_X s) m0 ch AO RP0 RS0 HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
    set (B := qc_blk AL ch) in *. set (rz := qc_rz ch) in *. set (bs := qc_bsize ch) in *. set (on := qc_n ch) in *.
    assert (EM : qc_hdr AL ch = B + rz - 16) by reflexivity.
    set (M := qc_hdr AL ch) in *.
    assert (RU0 : 0 <= rup8 on /\ rup8 on mod 8 = 0 /\ on <= rup8 on) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    assert (MR : 6328320 <= M /\ M + 16 + on <= alloc_ceiling) by (clear - EM GLO GHI RZ16 RZN RU0; lia).
    pose proof INVW as (RPW & _ & RSW & MIW & _ & TEW & _).
    pose proof SOBJ as SOBJ0. hide SOBJ0. pose proof BUF as BUF0. hide BUF0.
    hide MU0. hide WM0. hide OLD0.
    pose proof (munch_refl [(q' - 48, q')] mW) as MU. pose proof (wmono_refl asegs mW) as WM.
    lz_go.
    zstep. carve_frame 48%nat ST.
    do 6 zstep.

    zstep. if_cases KP; zify_cond KP. { exfalso. clear - KP MR ACR N1. rewrite ?Z.mod_small in KP by lia. lia. } clear KP.
    zstep.
    zstep. if_cases KN; zify_cond KN. { exfalso. clear - KN NR. unfold A0_MAXREQ in NR. rewrite ?Z.mod_small in KN by lia. lia. } clear KN.
    do 3 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q' + -48) with (q' - 48) in * by lia.
    assert (TEA : thread_env L mA).
    { eapply thread_env_frame; [exact TEW| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
    eapply evt_cut.
    { eapply (gcts_spec L _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc (q' - 48) mA lo).
      - exact ST.
      - exact CLO.
      - clear - LQ1; lia.
      - clear - Q16; Z.div_mod_to_equations; lia.
      - clear - QH; lia.
      - exact TEA.
      - exact TLO.
      - assumption. }
    cbv beta. unfold gcts_post. intros msT (h1 & mH & -> & MUh & WMh & MIH & STH & TEH).

    replace (ret_pc (Z_to_bv 64 213188)) with (Z_to_bv 64 213188) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (DJH : forall A k, (A + k <= q' - 80 \/ q' - 48 <= A) -> disjoint_from [(q' - 48 - 32, q' - 48)] A k)
      by (intros A k D1; cbn [disjoint_from]; clear - D1; lia).
    eapply (rw_cells_transport asegs _ mA mH) in FR; [| exact MUh| exact WMh| cbn [cells_size csize Nat.add]; apply DJH; clear; lia].
    pose proof RPW as (_ & _ & _ & _ & (ts & TS)).
    eapply (rw_cells_transport asegs _ mW mA) in TS; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from]; clear - T4 CLO LQ1; lia].
    eapply (rw_cells_transport asegs _ mA mH) in TS; [| exact MUh| exact WMh| cbn [cells_size csize Nat.add]; apply DJH; clear - T4 CLO LQ1; lia].
    pose proof (rw_cells_split_CB asegs mH (THR + 2800) [] _ ts [] [56%nat; 8%nat; 8%nat; 296%nat] TS ltac:(reflexivity)) as TSS.
    cbn [mk_CB_cells app] in TSS. clear TS.
    remember (firstn 56 ts) as tsa eqn:Etsa. remember (skipn 56 ts) as ts1 eqn:Ets1. clear Etsa Ets1.
    remember (firstn 8 ts1) as tb1 eqn:E1. remember (skipn 8 ts1) as ts2 eqn:E2. clear E1 E2.
    remember (firstn 8 ts2) as tb2 eqn:E1. remember (skipn 8 ts2) as ts3 eqn:E2. clear E1 E2.
    remember (firstn 296 ts3) as tsb eqn:E1. clear E1.
    apply (rw_cells_CB_C8 asegs mH (THR + 2800) [CB 56 tsa] tb1) in TSS. cbn [app] in TSS.
    apply (rw_cells_CB_C8 asegs mH (THR + 2800) [CB 56 tsa; C8 (le_bytes_to_word tb1)] tb2) in TSS. cbn [app] in TSS.
    do 2 zstep.
    do 2 zstep.
    hide MU. hide WM. hide MUh. hide WMh.
    pose proof (munch_refl [(THR + 2800, THR + 3168)] mH) as MUt. pose proof (wmono_refl asegs mH) as WMt.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
    do 6 zstep.
    zstep.

    lz_here.

    unhide MU. unhide WM. unhide MUh. unhide WMh.
    assert (MU4 : munch [(q' - 80, q'); (THR + 2800, THR + 3168)] mW mT).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_trans; [eapply munch_weaken; [| exact MUh]| eapply munch_weaken; [| exact MUt]]];
        unfold sub_fp; cbn [outside]; intros xo (O1 & O2 & _).
      - split; [clear - O1; lia| exact I].
      - split; [clear - O1; lia| exact I].
      - split; [exact O2| exact I]. }
    pose proof (wmono_trans asegs _ _ _ WM (wmono_trans asegs _ _ _ WMh WMt)) as WM4.
    assert (MIT : mem_inv asegs mT) by assumption.
    assert (TS' : exists ts', rw_cells asegs mT (THR + TSTATS_OFF) [CB 368 ts']) by (destruct (rw_cells_forget _ _ _ _ TSS) as [ts' X0]; exists ts'; exact X0).
    pose proof (dr_inv_tstats AL E (bs_X s) (bs_H s) mW mT _ _ _ lo q' (q' - 80) q' AO LOH CLO ltac:(clear - LQ1; lia) ltac:(clear; lia) ltac:(clear; lia) INVW MU4 WM4 MIT TS') as INVT.
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36. layout_apart_fact AO 2%nat 3%nat A23.
    assert (DJ4 : forall A k, A + k <= q' - 80 \/ q' <= A -> (A + k <= THR + 2800 \/ THR + 3168 <= A) -> disjoint_from [(q' - 80, q'); (THR + 2800, THR + 3168)] A k)
      by (intros A k D1 D3; cbn [disjoint_from]; clear - D1 D3; lia).
    assert (AENVT : alloc_env mT).
    { ae_split AENVW; unfold alloc_env; repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_transport_m; [eassumption| exact MU4| cbn [cells_size csize Nat.add]; apply DJ4; clear - LOH LQ1 T3; lia]). }
    assert (TE2T : thread_env2 AL mT) by (eapply (thread_env2_frame_m AL _ mW mT TE2W MU4); apply DJ4; clear - LOH LQ1 CLO T1 T2 T3 T4 T5 A23; lia).
    assert (HKET : hooks_env mT) by (unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKEW| exact MU4| cbn [cells_size csize Nat.add]; apply DJ4; clear - LOH LQ1 T3; lia]).
    assert (RDT : RDEPOT D (bs_depot s) (bs_dtotal s) mT) by (eapply (RDEPOT_frame_m AL _ _ _ mW mT DLO SWB RDW MU4); apply DJ4; clear - LOH LQ1 CLO N1d N2d S1d S2d A35 A36 T3; lia).
    assert (IAT : ia_cells 262144 262728 true mT).
    { assert (TRC : forall A cs, rw_cells asegs mW A cs -> 740096 <= A -> A + Z.of_nat (cells_size cs) <= 1323916 -> rw_cells asegs mT A cs).
      { intros A cs C0 H1 H2x. eapply rw_cells_transport_m; [exact C0| exact MU4|]. apply DJ4; clear - H1 H2x LOH LQ1 T3; lia. }
      destruct IAW as (FL & [j0 C0] & [j2 [C2x Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
      split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2x| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
      split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
      exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
    unhide SOBJ0. unhide BUF0.
    eapply (rw_cells_transport_m _ mW mT) in SOBJ0; [| exact MU4| cbn [cells_size csize Nat.add]; apply DJ4; clear - QSTK T4 CLO LQ1; lia].
    eapply (u64arr_transport_m _ mW mT) in BUF0; [| exact MU4| apply DJ4; clear - QTR T4 CLO LQ1; lia].

    unhide MU0. unhide WM0.
    set (FT1 := FT0 ++ [(q' - 80, q'); (THR + 2800, THR + 3168)]).
    assert (MU1 : munch FT1 m0 mT) by (unfold FT1; exact (munch_joinP _ _ m0 mW mT MU0 MU4)).
    pose proof (wmono_trans asegs _ _ _ WM0 WM4) as WM1.
    assert (FC1 : Forall (fclass AL lo q0) FT1).
    { unfold FT1. apply Forall_app. split; [exact FC0|]. constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ1 QQ0; lia|].
      constructor; [| constructor]. right; right; right. unfold sub_iv. cbn [fst snd]. clear. lia. }

    unfold rl8_tree.
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (ALLOC gp F_ fc (q' - 48) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 mT FT1 STK TR ws);
        [ exact HR | exact MI | exact AE | exact RF | exact MU1 | exact WM1 | exact FC1 | eassumption | exact STH | exact INVT | exact AENVT | exact TE2T | exact HKET | exact RDT
        | exists true; exact IAT | exact SOBJ0 | clear - QSTK; lia | exact STKH | exact BUF0 | exact TRW | exact LENW | clear - QTR; lia | exact TRH
        | clear - LOQA; lia | clear - QQ0; lia | exact Q0H | clear - Q16; Z.div_mod_to_equations; lia ]. }
    intros r H1 ms1 [PO MC1]. unfold al8_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & s1' & A' & njunk & W1 & -> & GH1 & EX1 & EQ1 & ENS1 & (ach & EL1 & EA') & MI1 & STK1 & AE1 & RF1 & AP1 & BLK1 & HR1 & NB1 & NSH1 & WMo1 & MUW1 & ABV1).
    clean_ms_mem MC1.

    eapply (rw_cells_transport_m _ mT m1) in FR; [| exact MUW1| apply ABV1; clear; lia].
    eapply (rw_cells_transport_m _ mT m1) in SOBJ0; [| exact MUW1| apply ABV1; clear - QSTK; lia].
    eapply (u64arr_transport_m _ mT m1) in BUF0; [| exact MUW1| apply ABV1; clear - QTR; lia].
    assert (EL1' : bs_live s1' = ((ach, n) :: l1) ++ (ch, oldn) :: l2) by (rewrite EL1, EL; reflexivity).
    destruct (free_pre_at AL E s1' _ m1 ch oldn ((ach, n) :: l1) l2 HR1 MI1 EL1') as (INV1 & HK1 & _ & LREP1 & NSC1 & HINB1).
    assert (LR : lr_ok (ch, oldn)).
    { destruct HR as (_ & LOK & _). apply (proj1 (Forall_forall _ _) LOK). rewrite EL. apply in_or_app. right. left. reflexivity. }
    unfold lr_ok in LR. cbn [fst snd] in LR. fold on in LR.
    assert (ONB : 0 <= oldn <= on) by (clear - LR N1; lia).
    unhide OLD0.
    assert (OLD1 : rw_cells asegs m1 (M + 16) [CB (Z.to_nat oldn) old]).
    { apply (BLK1 (ch, oldn)); [rewrite EL; apply in_or_app; right; left; reflexivity| | | exact OLD0]; cbn [fst cells_size csize].
      - fold B. clear - EM RZ16. lia.
      - fold B bs. rewrite Nat.add_0_r, Z2Nat.id by (clear - ONB; lia). clear - EM RZN RU0 ONB. lia. }
    destruct (law_block_range AL E AO FI FSBE s1' _ m1 (A', A', n) HR1 ltac:(left; reflexivity)) as (AP0 & AP16 & _ & APC & AP5 & APB & APF).
    unfold blk_addr, blk_size in AP0, AP16, APC, AP5, APB, APF. cbn [fst snd] in AP0, AP16, APC, AP5, APB, APF.
    lz_go.
    replace (ret_pc (Z_to_bv 64 213240)) with (Z_to_bv 64 213240) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    zstep. if_cases KA; zify_cond KA. { exfalso. clear - KA AP0 APC ACR. rewrite ?Z.mod_small in KA by lia. lia. } clear KA.

    pose proof LREP1 as ((bits & actx & BITS & HD) & _ & (ub & UB) & _). fold M on in HD, UB.
    assert (HS : rw_cells asegs m1 M [C1 (Z_to_bv 8 2); C1 bits; C2 (wz 0); C4 (wz on); C8 actx]).
    { eapply rw_cells_rebytes; [exact HD| clear; cbn; tauto| | reflexivity]. reflexivity. }
    clear HD.
    pose proof (GOT_RMEM m1 AE1) as GOTM.
    pose proof (asan_env_icpt asegs m1 AE1) as (_ & _ & _ & _ & RMEM & _). unfold env_real_mem in RMEM.
    remember M as M0 eqn:HM0 in HS, UB |- *.
    replace (M0 + 16 + -16) with M0 by (clear; lia).
    zstep.
    zstep.
    zstep.
    zstep. lit_branch.
    do 2 zstep.
    zstep.
    zstep. lit_branch.
    replace (M0 + 16 + -14) with (M0 + 2) by (clear; lia). replace (M0 + 16 + -12) with (M0 + 4) by (clear; lia).
    zstep.
    zstep.
    change (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    replace (zx32 (Z_to_bv 64 on)) with (Z_to_bv 64 on) by (unfold zx32; rewrite unsigned_lit by (clear - N1; lia); rewrite Z.mod_small by (clear - N1; lia); reflexivity).
    do 2 zstep.

    change (Z.lor 0 on) with on.

    assert (JOIN : forall k, k = Z.min n on ->
      evt asegs (lzk H1 (ebind (dl8_tree (AX r) (bs_quar s) ch) (fun _ : unit => Ret (Ok r)))
                   (rl8_post AX dn gp F_ fc q0 lo q' ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st ch l1 l2 n oldn old m0 mW))
        (MS (mkR (wz 213240) (wz (q' - 48)) gp (wz A0_TP) u0 u1 u2 (wz STK) (wz (M0 + 16)) (wz on) (wz on) b2 (wz 663064) b4 b5 b6 b7
                 (wz 721560) (wz k) (wz A') s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F_ (wz 213344) fc None m1 (seg_rom asegs))); [|
      zstep; if_cases K1; zify_cond K1;
      [ apply JOIN; clear - K1 NR N1; unfold A0_MAXREQ in NR; rewrite ?Z.mod_small in K1 by lia; lia
      | zstep; apply JOIN; clear - K1 NR N1; unfold A0_MAXREQ in NR; rewrite ?Z.mod_small in K1 by lia; lia ] ].
    intros k EK.
    assert (KR : 1 <= k <= n /\ k <= on) by (clear - EK NR N1; lia).

    assert (LUB : length ub = Z.to_nat on) by (destruct UB as [[WFu _] _]; exact (proj1 WFu)).
    assert (LNJ : length njunk = Z.to_nat n) by (destruct NB1 as [[WFu _] _]; exact (proj1 WFu)).
    set (src := firstn (Z.to_nat k) ub).
    assert (LSRC : length src = Z.to_nat k) by (unfold src; rewrite firstn_length_le; [reflexivity| rewrite LUB; clear - KR; lia]).
    assert (SRC : bytes_at asegs m1 (M0 + 16) src).
    { destruct UB as [[_ BAu] _]. cbn [cells_bytes cbytes] in BAu. rewrite app_nil_r in BAu. rewrite <- (firstn_skipn (Z.to_nat k) ub) in BAu.
      apply bytes_at_app in BAu as [BA1 _]. exact BA1. }
    pose proof (rw_cells_split_CB asegs m1 A' [] _ njunk [] [Z.to_nat k; (Z.to_nat n - Z.to_nat k)%nat] NB1 ltac:(cbn [sum_nat]; clear - KR; lia)) as NBS.
    cbn [mk_CB_cells app] in NBS.
    apply (proj1 (rw_cells_app asegs m1 A' [CB (Z.to_nat k) (firstn (Z.to_nat k) njunk)] _)) in NBS. destruct NBS as [DST NREST].
    cbn [cells_size csize Nat.add] in NREST. rewrite Nat.add_0_r, Z2Nat.id in NREST by (clear - KR; lia).

    assert (SEP : M0 + 16 + on <= A' \/ A' + n <= M0 + 16).
    { assert (APch : chunk_apart AL ach ch).
      { pose proof (live_fop AL E AO s1' _ m1 HR1) as FOP. unfold live_chunks in FOP. rewrite EL1' in FOP. cbn [map app] in FOP.
        inversion FOP as [|x0 l0 FA0 _]; subst. rewrite map_app in FA0. apply Forall_app in FA0 as [_ FA0]. cbn [map] in FA0. apply Forall_cons_iff in FA0 as [APx _]. exact APx. }
      assert (WFA : qchunk_wf ach).
      { destruct HR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFL1 & _). unfold live_chunks in WFL1. rewrite EL1 in WFL1. cbn [map fst] in WFL1.
        apply Forall_cons_iff in WFL1 as [W0 _]. exact W0. }
      assert (LRA : lr_ok (ach, n)).
      { destruct HR1 as (_ & LOK1 & _). rewrite EL1 in LOK1. apply Forall_cons_iff in LOK1 as [L0 _]. exact L0. }
      unfold lr_ok in LRA. cbn [fst snd] in LRA.
      destruct (chunk_apart_users AL ach ch WFA WFC APch) as [CA|CA]; rewrite <- EA' in CA; unfold lc_user in CA; fold M in CA; rewrite <- HM0 in CA; fold on in CA;
        [right| left]; clear - CA LRA NR; lia. }
    do 3 zstep.
    zstep.
    eapply evt_cut.
    { eapply (memcpy_spec_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc m1 A' (M0 + 16) k src (firstn (Z.to_nat k) njunk));
        [ exact SRC | exact LSRC | exact DST | clear - SEP KR; lia | assumption | clear - AP0 APC ACR NR; lia | clear - MR ACR HM0 N1; lia | clear - KR NR; unfold A0_MAXREQ in NR; lia ]. }
    cbv beta. unfold memcpy_post_z. intros msC (c0 & c1 & c2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & c3 & c4 & c5 & c6 & m2 & -> & MUc & WMc & MIc & DSTc & SRCc).

    replace (ret_pc (Z_to_bv 64 213360)) with (Z_to_bv 64 213360) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

    assert (LQ0 : lo <= q0) by (clear - LQ1 QQ0; lia).
    destruct (copy_frame s1' _ m1 m2 st ach n (bs_live s) A' k q0 lo HR1 MI1 EL1 EA' ltac:(left; reflexivity) ltac:(clear - KR; lia) MUc WMc CLO LQ0)
      as (HR2 & AE2f & RF2f & STK2f & AP2).
    pose proof (AE2f AE1) as AE2. pose proof (RF2f RF1) as RF2. pose proof (STK2f _ _ STK1 CLO ltac:(clear - LQ1; lia)) as STK2. clear AE2f RF2f STK2f.
    assert (DJc : forall A0 k0, alloc_ceiling <= A0 -> disjoint_from [(A', A' + k)] A0 k0) by (intros A0 k0 HA0; cbn [disjoint_from]; clear - HA0 APC KR; lia).
    eapply (rw_cells_transport_m _ m1 m2) in FR; [| exact MUc| apply DJc; clear - CLO LQ1; lia].
    eapply (rw_cells_transport_m _ m1 m2) in SOBJ0; [| exact MUc| apply DJc; clear - CLO LQ1 QSTK; lia].
    eapply (u64arr_transport_m _ m1 m2) in BUF0; [| exact MUc| apply DJc; clear - CLO LQ1 QTR; lia].
    eapply (rw_cells_transport_m _ m1 m2) in NREST; [| exact MUc| cbn [disjoint_from]; clear; lia].
    pose proof (cb_join m2 A' _ _ _ _ DSTc ltac:(rewrite Z2Nat.id by (clear - KR; lia); exact NREST)) as NB2.
    replace (Z.to_nat k + (Z.to_nat n - Z.to_nat k))%nat with (Z.to_nat n) in NB2 by (clear - KR; lia).
    pose proof (law_blocks_nodup AL E AO s1' _ m2 HR2) as NDK2.
    do 6 zstep.
    zstep.
    lz_here.
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      rewrite <- EX1, <- EQ1. replace H1 with (bs_H s1') by (clear - GH1; unfold bs_ghost in GH1; congruence).
      rewrite HM0.
      eapply (dealloc_L8_at gp F_ fc (q' - 48) lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1' _ m2 st ch oldn ((ach, n) :: l1) l2 tr STK TR ws);
        [ exact HR2 | replace (bs_H s1') with H1 by (clear - GH1; unfold bs_ghost in GH1; congruence); exact MC0 | assumption | exact AE2 | exact RF2 | exact EL1' | exact (proj1 (NoDup_ListNoDup _) NDK2) | exact STK2 | exact CLO | clear - LOQD; lia | clear - QH; lia
        | clear - Q16; Z.div_mod_to_equations; lia | exact TRIN | exact SOBJ0 | clear - QSTK; lia | exact STKH | exact BUF0 | exact TRW | exact LENW | clear - QTR; lia | exact TRH ]. }

    intros u H3 ms3 [PO MC3]. unfold dl8_post in PO.
    destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m3 & W3 & hs3 & total3 & -> & MI3 & STK3 & AE3 & RF3 & AP3 & BLK3 & HR3 & MUW3 & ABV3).
    clean_ms_mem MC3.
    eapply (rw_cells_transport_m _ m2 m3) in FR; [| exact MUW3| apply ABV3; clear; lia].
    lz_go.
    replace (ret_pc (Z_to_bv 64 213388)) with (Z_to_bv 64 213388) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.
    do 6 zstep.
    zstep. replace (q' - 48 + 48) with q' by (clear; lia). zstep.
    release_frame FR STK3 q'.

    assert (WFA : qchunk_wf ach).
    { destruct HR1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFL1 & _). unfold live_chunks in WFL1. rewrite EL1 in WFL1. cbn [map fst] in WFL1.
      apply Forall_cons_iff in WFL1 as [W0 _]. exact W0. }
    assert (LRA : lr_ok (ach, n)).
    { destruct HR1 as (_ & LOK1 & _). rewrite EL1 in LOK1. apply Forall_cons_iff in LOK1 as [L0 _]. exact L0. }
    unfold lr_ok in LRA. cbn [fst snd] in LRA.
    pose proof WFA as (RZ16a & _ & NA1 & RZNa & _).
    assert (RUa : qc_n ach <= rup8 (qc_n ach)) by (unfold rup8; clear - NA1; Z.div_mod_to_equations; lia).
    assert (NB3 : rw_cells asegs m3 A' [CB (Z.to_nat n) (src ++ firstn (Z.to_nat n - Z.to_nat k) (skipn (Z.to_nat k) njunk))]).
    { apply (BLK3 (ach, n)); [left; reflexivity| | | exact NB2]; cbn [fst cells_size csize]; rewrite EA'; unfold lc_user, qc_hdr.
      - clear - RZ16a. lia.
      - rewrite Nat.add_0_r, Z2Nat.id by (clear - NR; lia). clear - RZNa RUa LRA NR. lia. }
    assert (NEQ : Z.eqb A' (lc_user AL ch) = false).
    { apply Z.eqb_neq. unfold lc_user. fold M. rewrite <- HM0. clear - SEP NR N1. lia. }
    assert (HR3' : RHEAP_B AL E (dl8_state s1' ch ((ach, n) :: l1) l2 H3 hs3 total3) ((A', A', n) :: lb_remove Z.eqb (lc_user AL ch) LB) m3).
    { rewrite lb_remove_filter in HR3 |- *. cbn [List.filter blk_id fst] in HR3. rewrite NEQ in HR3. cbn [negb] in HR3. exact HR3. }

    set (rest := firstn (Z.to_nat n - Z.to_nat k) (skipn (Z.to_nat k) njunk)) in *.
    assert (CONT : exists junkF, src ++ rest = firstn (Z.to_nat (Z.min n oldn)) old ++ junkF).
    { destruct LR as [LRe|[LR0 LR1]].
      - assert (UBO : ub = old).
        { destruct UB as [[_ BAu] _]. destruct OLD1 as [[WFo BAo] _]. cbn [cells_bytes cbytes] in BAu, BAo. rewrite app_nil_r in BAu, BAo.
          rewrite <- HM0 in BAo. apply (bytes_at_det m1 (M0 + 16) ub old BAu BAo). rewrite LUB, <- LRe. symmetry. exact (proj1 WFo). }
        exists rest. unfold src. rewrite UBO, LRe, <- EK. reflexivity.
      - exists (src ++ rest). rewrite LR0. replace (Z.min n 0) with 0 by (clear - NR; lia). reflexivity. }
    destruct CONT as (junkF & CONT). rewrite CONT in NB3.
    lz_ret. apply evt_done. unfold rl8_post.
    exists v0, v1, v2, (wz A'), e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m3, ([(q' - 80, q'); (THR + 2800, THR + 3168)] ++ W1 ++ [(A', A' + k)] ++ W3).
    split; [reflexivity|].
    split; [exact (munch_joinP _ _ mW mT m3 MU4 (munch_joinP _ _ mT m1 m3 MUW1 (munch_joinP _ _ m1 m2 m3 MUc MUW3)))|].
    split.
    { intros B0 k0 HB0. apply disjoint_from_app. split; [cbn [disjoint_from]; clear - HB0 T4 CLO LQ1; lia|].
      apply disjoint_from_app. split; [apply ABV1; clear - HB0; lia|].
      apply disjoint_from_app. split; [apply DJc; clear - HB0 CLO LQ1; lia| apply ABV3; clear - HB0; lia]. }
    split; [exact STK3|].
    unfold rl8_cpost. exists s1', ach, hs3, total3, A', junkF, m2.
    split; [reflexivity|]. split; [exact EX1|]. split; [exact EQ1|]. split; [exact ENS1|].
    split; [clear - GH1; unfold bs_ghost in GH1; congruence|]. split; [exact EL1|]. split; [exact HR2|].
    split; [exact MI3|]. split; [exact AE3|]. split; [exact RF3|].
    split.
    { intros LBk HB.
      assert (HB0 : forall b, In b LBk -> exists r0, In r0 (bs_live s) /\ blk_addr b = lc_user AL (fst r0) /\ blk_size b = snd r0).
      { intros b Hb. destruct (HB b Hb) as (r0 & Hr0 & E1 & E2). exists r0. split; [| split; assumption]. rewrite EL. apply in_app_or in Hr0 as [Hr0|Hr0]; apply in_or_app; [left| right; right]; exact Hr0. }
      assert (HB3 : forall b, In b LBk -> exists r0, In r0 (((ach, n) :: l1) ++ l2) /\ blk_addr b = lc_user AL (fst r0) /\ blk_size b = snd r0).
      { intros b Hb. destruct (HB b Hb) as (r0 & Hr0 & E1 & E2). exists r0. split; [| split; assumption]. right. exact Hr0. }
      eapply apres_trans; [exact (AP1 LBk HB0)|]. eapply apres_trans; [exact (AP2 LBk HB0)|].
      intros a Ha AC. apply (AP3 LBk HB3 a Ha). destruct AC as [AC|AC]; [left; clear - AC QQ0; lia| right; exact AC]. }
    split; [exact HR3'|]. split; [exact NB3|].
    exact (law_block_shadow AL E _ _ m3 (A', A', n) HR3' ltac:(left; reflexivity)).
  Qed.
End REALLOCATE.

#[using="AO"] Lemma rl_cpre_frame : forall s (m m' : mem) lo sa sb,
  alloc_ceiling <= lo -> lo <= sa -> sa <= sb -> rl_cpre s m -> munch [(sa, sb)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> rl_cpre s m'.
Proof.
  intros s m m' lo sa sb CLO LSA SAB (INV & AENV & TE2 & HKE & RD & IA) MU WM MI'.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  pose proof INV as (_ & _ & _ & _ & _ & TE & _).
  assert (TE' : thread_env L m').
  { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LSA CLO T2 T4. lia. }
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36. layout_apart_fact AO 2%nat 3%nat A23.
  assert (DJ : forall A k, A + k <= lo -> disjoint_from [(sa, sb)] A k) by (intros A k D1; cbn [disjoint_from]; clear - D1 LSA; lia).
  unfold rl_cpre.
  split.
  { apply (dr_inv_frame_i AL E (bs_X s) (bs_H s) m m' _ _ _ lo [(sa, sb)] AO LOH CLO INV MU WM MI' TE'). constructor; [| constructor]. left. cbn [fst]. exact LSA. }
  split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MU| cbn [cells_size csize Nat.add]; apply DJ; clear - LOH T3; lia])|].
  split; [eapply (thread_env2_frame_m AL _ m m' TE2 MU); apply DJ; clear - LOH CLO T1 T2 T3 T4 T5 A23; lia|].
  split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MU| cbn [cells_size csize Nat.add]; apply DJ; clear - LOH T3; lia]|].
  split; [eapply (RDEPOT_frame_m AL _ _ _ m m' DLO SWB RD MU); apply DJ; clear - LOH CLO N1d N2d S1d S2d A35 A36 T3; lia|].
  assert (TRC : forall A cs, rw_cells asegs m A cs -> 740096 <= A -> A + Z.of_nat (cells_size cs) <= 1323916 -> rw_cells asegs m' A cs).
  { intros A cs C0 H1 H2x. eapply rw_cells_transport_m; [exact C0| exact MU|]. apply DJ; clear - H1 H2x LOH; lia. }
  destruct IA as (FL & [j0 C0] & [j2 [C2x Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
  split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; cbn [cells_size csize Nat.add]; clear; lia]|].
  split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
  split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2x| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
  split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
  split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
  exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia].
Qed.

Section AREALLOC.
  Variable ART : Type.
  Variable ATREE : itree nodeL (exc ART).
  Variable AX : ART -> pstate.
  Variables (dn ASTK : Z).
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (qa q0 lo : Z).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQA : lo <= qa - 64 - ASTK.
  Hypothesis LOQD : lo <= qa - 64 - DEALLOC_STACK.
  Hypothesis QQ0 : qa <= q0.
  Hypothesis Q0H : q0 <= 2^47.
  Hypothesis Q16 : qa mod 16 = 0.

  #[using="AO SWIN_LO FSBE STAT CLO LOQA LOQD QQ0 Q0H Q16"] Theorem asan_realloc_L8 : forall (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (s : astB) (LB : list (block Z)) (st : fsstate FI) (ch : qchunk) (oldn : Z) (l1 l2 : list (qchunk * Z)) (n : Z) (tr : list Z) (old : list byte)
        (m0 mW : mem) (FT0 : list (Z * Z)) (STK TR : Z) (ws : list word),
    RHEAP_B AL E s LB m0 -> mem_inv asegs m0 -> asan_env asegs m0 -> RFAKE FI st m0 ->
    bs_live s = l1 ++ (ch, oldn) :: l2 -> rw_cells asegs m0 (qc_hdr AL ch + 16) [CB (Z.to_nat oldn) old] ->
    munch FT0 m0 mW -> wmono asegs m0 mW -> Forall (fclass AL lo q0) FT0 ->
    mclean (bs_H s) mW -> stk asegs mW lo qa -> mem_inv asegs mW -> rl_cpre s mW ->
    rw_cells asegs mW STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> qa <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs mW TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> qa <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n tr q0 lo ->
    0 < n <= A0_MAXREQ -> In tr A0_TRACES ->
    implA (bs_H s) (rl8_tree ATREE AX (bs_quar s) ch)
      (rl8_post AX dn gp F_ fc q0 lo qa ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st ch l1 l2 n oldn old m0 mW)
      (MS (mkR ra (wz qa) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (qc_hdr AL ch + 16)) (wz n) (wz STK) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz asan_realloc_entry) fc None mW (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s LB st ch oldn l1 l2 n tr old m0 mW FT0 STK TR ws
           HR MI AE RF EL OLD0 MU0 WM0 FC0 MC ST MIW CPW SOBJ QSTK STKH BUF TRW LENW QTR TRH ALLOC NR TRIN.
    unfold asan_realloc_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    assert (DS : 96 <= DEALLOC_STACK) by (vm_compute; discriminate).
    assert (QH : qa <= 2^47) by (clear - QQ0 Q0H; lia).
    assert (LQ1 : lo <= qa - 64 - 96) by (clear - LOQD DS; lia).
    destruct (free_pre_at AL E s LB m0 ch oldn l1 l2 HR MI EL) as (INV0 & HK & WFC & _).
    pose proof INV0 as (RP0 & _ & RS0 & _).
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL (bs_X s) m0 ch AO RP0 RS0 HK) as (GB8 & GS8 & GS32 & GLO & GHI & GBAND).
    assert (RU0 : 0 <= rup8 (qc_n ch) /\ qc_n ch <= rup8 (qc_n ch)) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    assert (MR : 6328320 <= qc_hdr AL ch /\ qc_hdr AL ch + 16 + qc_n ch <= alloc_ceiling) by (unfold qc_hdr; clear - GLO GHI RZ16 RZN RU0 N1; Z.div_mod_to_equations; lia).
    clear INV0 RP0 RS0 HK GB8 GS8 GS32 GLO GHI GBAND.
    pose proof SOBJ as SOBJ0. hide SOBJ0. pose proof BUF as BUF0. hide BUF0. pose proof CPW as CPW0. hide CPW0. clear CPW.
    hide MU0. hide WM0. hide OLD0.
    pose proof (munch_refl [(qa - 16, qa)] mW) as MU. pose proof (wmono_refl asegs mW) as WM.
    lz_go.
    zstep. carve_frame 16%nat ST.
    zstep.
    do 2 zstep.
    zstep. if_cases KP; zify_cond KP. { exfalso. clear - KP MR ACR N1. rewrite ?Z.mod_small in KP by lia. lia. } clear KP.
    zstep.
    zstep. if_cases KN; zify_cond KN; [| exfalso; clear - KN NR; unfold A0_MAXREQ in NR; rewrite ?Z.mod_small in KN by lia; lia]. clear KN.
    do 2 zstep.
    do 2 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (qa + -16) with (qa - 16) in * by lia.
    lz_here.

    unhide MU0. unhide WM0. unhide CPW0. unhide SOBJ0. unhide BUF0. unhide OLD0.
    assert (MIA : mem_inv asegs mA) by assumption.
    pose proof (rl_cpre_frame s mW mA lo (qa - 16) qa CLO ltac:(clear - LQ1; lia) ltac:(clear; lia) CPW0 MU WM MIA) as CPA.
    eapply (rw_cells_transport_m _ mW mA) in SOBJ0; [| exact MU| cbn [cells_size csize Nat.add disjoint_from]; clear - QSTK; lia].
    eapply (u64arr_transport_m _ mW mA) in BUF0; [| exact MU| cbn [disjoint_from]; clear - QTR; lia].
    set (FT1 := FT0 ++ [(qa - 16, qa)]).
    assert (MU1 : munch FT1 m0 mA) by (unfold FT1; exact (munch_joinP _ _ m0 mW mA MU0 MU)).
    pose proof (wmono_trans asegs _ _ _ WM0 WM) as WM1.
    assert (FC1 : Forall (fclass AL lo q0) FT1).
    { unfold FT1. apply Forall_app. split; [exact FC0|]. constructor; [| constructor]. left. unfold sub_iv. cbn [fst snd]. clear - LQ1 QQ0. lia. }
    rewrite <- (ebind_ret_r (rl8_tree ATREE AX (bs_quar s) ch)).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (reallocate_L8 ART ATREE AX dn ASTK gp F_ fc (qa - 16) q0 lo CLO ltac:(clear - LOQA; lia) ltac:(clear - LOQD; lia) ltac:(clear - QQ0; lia) Q0H
                ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s LB st ch oldn l1 l2 n tr old m0 mA FT1 STK TR ws);
        [ exact HR | exact MI | exact AE | exact RF | exact EL | exact OLD0 | exact MU1 | exact WM1 | exact FC1 | eassumption | exact ST | exact CPA
        | exact SOBJ0 | clear - QSTK; lia | exact STKH | exact BUF0 | exact TRW | exact LENW | clear - QTR; lia | exact TRH | exact ALLOC | exact NR | exact TRIN ]. }
    intros r H3 ms3 [PO MC3]. unfold rl8_post in PO.
    destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m3 & W3 & -> & MUW3 & ABV3 & STK3 & CP).
    clean_ms_mem MC3.
    eapply (rw_cells_transport_m _ mA m3) in FR; [| exact MUW3| apply ABV3; clear; lia].
    pose proof CP as (s1' & ach & hs3 & total3 & A' & junkF & m1 & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR3 & _).
    destruct (law_block_range AL E AO FI FSBE _ _ m3 (A', A', n) HR3 ltac:(left; reflexivity)) as (AP0 & _ & _ & APC & _).
    unfold blk_addr, blk_size in AP0, APC. cbn [fst snd] in AP0, APC.
    lz_go.
    replace (ret_pc (Z_to_bv 64 213116)) with (Z_to_bv 64 213116) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. if_cases KA; zify_cond KA. { exfalso. clear - KA AP0 APC ACR NR. rewrite ?Z.mod_small in KA by lia. lia. } clear KA.
    zstep.
    zstep. replace (qa - 16 + 16) with qa by (clear; lia). zstep.
    release_frame FR STK3 qa.
    lz_ret. apply evt_done. unfold rl8_post.
    exists v0, v1, v2, (wz A'), e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m3, ([(qa - 16, qa)] ++ W3).
    split; [reflexivity|].
    split; [exact (munch_joinP _ _ mW mA m3 MU MUW3)|].
    split; [intros B0 k0 HB0; apply disjoint_from_app; split; [cbn [disjoint_from]; clear - HB0; lia| apply ABV3; clear - HB0; lia]|].
    split; [exact STK3|]. exact CP.
  Qed.

  Definition rn8_cpost (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (m0 : mem)
      : mem -> ART -> (word -> bool) -> word -> mem -> Prop :=
    fun _ r H1 a0 m1 => exists s1' (A' : Z) (junk : list byte),
      a0 = wz A'
      /\ bs_ghost s1' = (H1, bs_pages s) /\ bs_X s1' = AX r /\ bs_quar s1' = bs_quar s /\ bs_nsec s1' = bs_nsec s + dn
      /\ (exists ach, bs_live s1' = (ach, n) :: bs_live s /\ A' = lc_user AL ach)
      /\ mem_inv asegs m1 /\ asan_env asegs m1 /\ RFAKE FI st m1
      /\ (forall LBk : list (block (am_K FI AI)),
            (forall b, In b LBk -> exists r0, In r0 (bs_live s) /\ blk_addr b = lc_user AL (fst r0) /\ blk_size b = snd r0) -> apres FI AI LBk q0 m0 m1)
      /\ RHEAP_B AL E s1' ((A', A', n) :: LB) m1
      /\ rw_cells asegs m1 A' [CB (Z.to_nat n) junk] /\ rw_cells asegs m1 (sh A') (shadow_cells (block_shadow n))
      /\ wmono asegs m0 m1.

  Definition rn8_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (m0 mW : mem)
      : ART -> (word -> bool) -> machine_state -> Prop :=
    fun r H1 ms1 => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 W,
      ms1 = MS (mkR ra (wz qa) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch W mW m1 /\ (forall B k, qa <= B -> disjoint_from W B k) /\ stk asegs m1 lo qa
      /\ rn8_cpost s LB st n m0 mW r H1 a0 m1.

  #[using="AO FSBE CLO LOQA LOQD QQ0 Q0H Q16"] Theorem asan_realloc_null_L8 : forall (ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (tr : list Z)
        (m0 mW : mem) (FT0 : list (Z * Z)) (STK TR : Z) (ws : list word),
    RHEAP_B AL E s LB m0 -> mem_inv asegs m0 -> asan_env asegs m0 -> RFAKE FI st m0 ->
    munch FT0 m0 mW -> wmono asegs m0 mW -> Forall (fclass AL lo q0) FT0 ->
    mclean (bs_H s) mW -> stk asegs mW lo qa -> mem_inv asegs mW -> rl_cpre s mW ->
    rw_cells asegs mW STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> qa <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs mW TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> qa <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n tr q0 lo ->
    0 <= n <= A0_MAXREQ ->
    implA (bs_H s) ATREE
      (rn8_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st n m0 mW)
      (MS (mkR ra (wz qa) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) (wz n) (wz STK) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz asan_realloc_entry) fc None mW (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s LB st n tr m0 mW FT0 STK TR ws
           HR MI AE RF MU0 WM0 FC0 MC ST MIW CPW SOBJ QSTK STKH BUF TRW LENW QTR TRH ALLOC NR.
    unfold asan_realloc_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    assert (DS : 96 <= DEALLOC_STACK) by (vm_compute; discriminate).
    assert (QH : qa <= 2^47) by (clear - QQ0 Q0H; lia).
    assert (LQ1 : lo <= qa - 64 - 96) by (clear - LOQD DS; lia).
    pose proof SOBJ as SOBJ0. hide SOBJ0. pose proof BUF as BUF0. hide BUF0. pose proof CPW as CPW0. hide CPW0. clear CPW.
    hide MU0. hide WM0.
    pose proof (munch_refl [(qa - 16, qa)] mW) as MU. pose proof (wmono_refl asegs mW) as WM.
    lz_go.
    zstep. carve_frame 16%nat ST.
    zstep.
    do 2 zstep.
    zstep. lit_branch.
    do 7 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (qa + -16) with (qa - 16) in * by lia.
    lz_here.
    unhide MU0. unhide WM0. unhide CPW0. unhide SOBJ0. unhide BUF0.
    assert (MIA : mem_inv asegs mA) by assumption.
    pose proof (rl_cpre_frame s mW mA lo (qa - 16) qa CLO ltac:(clear - LQ1; lia) ltac:(clear; lia) CPW0 MU WM MIA) as (INVA & AENVA & TE2A & HKEA & RDA & IAA).
    eapply (rw_cells_transport_m _ mW mA) in SOBJ0; [| exact MU| cbn [cells_size csize Nat.add disjoint_from]; clear - QSTK; lia].
    eapply (u64arr_transport_m _ mW mA) in BUF0; [| exact MU| cbn [disjoint_from]; clear - QTR; lia].
    set (FT1 := FT0 ++ [(qa - 16, qa)]).
    assert (MU1 : munch FT1 m0 mA) by (unfold FT1; exact (munch_joinP _ _ m0 mW mA MU0 MU)).
    pose proof (wmono_trans asegs _ _ _ WM0 WM) as WM1.
    assert (FC1 : Forall (fclass AL lo q0) FT1).
    { unfold FT1. apply Forall_app. split; [exact FC0|]. constructor; [| constructor]. left. unfold sub_iv. cbn [fst snd]. clear - LQ1 QQ0. lia. }
    rewrite <- (ebind_ret_r ATREE).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (ALLOC gp F_ fc (qa - 16) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 mA FT1 STK TR ws);
        [ exact HR | exact MI | exact AE | exact RF | exact MU1 | exact WM1 | exact FC1 | eassumption | exact ST | exact INVA | exact AENVA | exact TE2A | exact HKEA | exact RDA
        | exists true; exact IAA | exact SOBJ0 | clear - QSTK; lia | exact STKH | exact BUF0 | exact TRW | exact LENW | clear - QTR; lia | exact TRH
        | clear - LOQA; lia | clear - QQ0; lia | exact Q0H | clear - Q16; Z.div_mod_to_equations; lia ]. }
    intros r H1 ms1 [PO MC1]. unfold al8_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & s1' & A' & njunk & W1 & -> & GH1 & EX1 & EQ1 & ENS1 & ELA & MI1 & STK1 & AE1 & RF1 & AP1 & BLK1 & HR1 & NB1 & NSH1 & WMo1 & MUW1 & ABV1).
    clean_ms_mem MC1.
    eapply (rw_cells_transport_m _ mA m1) in FR; [| exact MUW1| apply ABV1; clear; lia].
    destruct (law_block_range AL E AO FI FSBE _ _ m1 (A', A', n) HR1 ltac:(left; reflexivity)) as (AP0 & _ & _ & APC & _).
    unfold blk_addr, blk_size in AP0, APC. cbn [fst snd] in AP0, APC.
    lz_go.
    replace (ret_pc (Z_to_bv 64 213080)) with (Z_to_bv 64 213080) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. if_cases KA; zify_cond KA; [| exfalso; clear - KA AP0 APC ACR NR; rewrite ?Z.mod_small in KA by lia; lia]. clear KA.
    zstep.
    zstep. replace (qa - 16 + 16) with qa by (clear; lia). zstep.
    release_frame FR STK1 qa.
    lz_ret. apply evt_done. unfold rn8_post.
    exists u0, u1, u2, (wz A'), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, ([(qa - 16, qa)] ++ W1).
    split; [reflexivity|].
    split; [exact (munch_joinP _ _ mW mA m1 MU MUW1)|].
    split; [intros B0 k0 HB0; apply disjoint_from_app; split; [cbn [disjoint_from]; clear - HB0; lia| apply ABV1; clear - HB0; lia]|].
    split; [exact STK1|].
    unfold rn8_cpost. exists s1', A', njunk.
    split; [reflexivity|]. split; [exact GH1|]. split; [exact EX1|]. split; [exact EQ1|]. split; [exact ENS1|]. split; [exact ELA|].
    split; [exact MI1|]. split; [exact AE1|]. split; [exact RF1|]. split; [exact AP1|]. split; [exact HR1|]. split; [exact NB1|]. split; [exact NSH1|]. exact WMo1.
  Qed.
End AREALLOC.

Notation WNR lo q := [(lo, q); (1323912, 1323912 + 4); (740096, 740096 + 8 + 262144); (1002304, 1268488 + 40); (THR + 3168, THR + 3169)].

Definition rl_icpre (s : astB) (lo q : Z) (m : mem) : mem -> Prop :=
  fun mW => munch (WNR lo q) m mW /\ wmono asegs m mW /\ mem_inv asegs mW /\ rl_cpre s mW.

#[using="Type"] Lemma wnr_fclass : forall lo q, Forall (fclass AL lo q) (WNR lo q).
Proof.
  intros lo q. repeat (apply Forall_cons || apply Forall_nil).
  - left. unfold sub_iv. cbn [fst snd]. lia.
  - right. left. unfold iastat. cbn [fst snd]. lia.
  - right. left. unfold iastat. cbn [fst snd]. lia.
  - right. left. unfold iastat. cbn [fst snd]. lia.
  - right. right. left. reflexivity.
Qed.

#[using="AO"] Lemma rl_cpre_front : forall s LB (m mW : mem) lo q,
  RHEAP_B AL E s LB m -> mem_inv asegs m -> alloc_ceiling <= lo -> lo <= q ->
  munch (WNR lo q) m mW -> wmono asegs m mW -> mem_inv asegs mW -> thread_env L mW -> ia_cells 262144 262728 true mW ->
  rl_cpre s mW.
Proof.
  intros s LB m mW lo q HR MI CLO LQ MUW WMW MIW TEW IAW.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  pose proof HR as (_ & _ & _ & INVB & _ & _ & _ & _ & _ & _ & RD & _ & _ & _ & _ & _ & _ & TE2 & HKE & _ & AENV & _).
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV.
  pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  assert (FZ : Forall (izone AL lo) (WNR lo q)).
  { unfold izone, iastat. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd];
      [left; clear; lia| right; left; clear; lia| right; left; clear; lia| right; left; clear; lia| right; right; reflexivity]. }
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36. layout_apart_fact AO 2%nat 3%nat A23.
  assert (DJT : forall A k, A + k <= lo -> (A + k <= 740096 \/ (1268528 <= A /\ A + k <= 1323912) \/ 1323916 <= A) -> (A + k <= THR + 3168 \/ THR + 3169 <= A) ->
                disjoint_from (WNR lo q) A k)
    by (intros A k D1 D2 D3; cbn [disjoint_from]; clear - D1 D2 D3; lia).
  unfold rl_cpre.
  split; [exact (dr_inv_frame_i AL E (bs_X s) (bs_H s) m mW _ _ _ lo _ AO LOH CLO INV MUW WMW MIW TEW FZ)|].
  split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MUW| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia])|].
  split; [eapply (thread_env2_frame_m AL _ m mW TE2 MUW); apply DJT; clear - LOH CLO T1 T2 T3 T4 T5 A23; lia|].
  split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MUW| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia]|].
  split; [| exact IAW].
  eapply (RDEPOT_frame_m AL _ _ _ m mW DLO SWB RD MUW); apply DJT; clear - LOH CLO N1d N2d S1d S2d A35 A36 T3; lia.
Qed.

Section RWALK.
  Variable ART : Type.
  Variable ATREE : itree nodeL (exc ART).
  Variable AX : ART -> pstate.
  Variables (dn ASTK : Z).
  Hypothesis ASTK_LE : ASTK <= 1888.

  #[using="AO SWIN_LO FSBE STAT ASTK_LE"] Lemma realloc_walk : forall (gp s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
      (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) s LB (m : mem) (st : fsstate FI) k A oldn n (old : list byte) ras,
    RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m -> In (k, A, oldn) LB ->
    rw_cells asegs m A [CB (Z.to_nat oldn) old] ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top L ->
    fpchain m (at_top L) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
    0 < n <= A0_MAXREQ ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n (realloc_tr ra ras) q lo ->
    exists ch l1 l2, bs_live s = l1 ++ (ch, oldn) :: l2 /\ A = qc_hdr AL ch + 16 /\ k = A /\
      implA (bs_H s) (rl8_tree ATREE AX (bs_quar s) ch)
        (ricpt_post L gp s7 s8 s9 s10 s11 F_ fc q lo 262144 ra ART (rl8_cpost AX dn q s LB st ch l1 l2 n oldn old m) s0 s1 s2 s3 s4 s5 s6 m)
        (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F_ (wz realloc_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros gp s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 s LB m st k A oldn n old ras
           HR MC MI AE RF HIN OLD ST CLO LOQ Q16 QTOP CH TRIN NR ALLOC.
    destruct (free_pre AL E s LB m k A oldn HR MI HIN) as (ch & l1 & l2 & EL & EA & EK & INV & HK & WFC & _).
    exists ch, l1, l2. split; [exact EL|]. split; [exact EA|]. split; [exact EK|]. subst A.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    destruct (traces_ok _ _ _ TRIN) as (LRAS & NPC & RA4 & RANE & RNG).
    pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRE & _ & (inited & IA) & _).
    pose proof INV as (RP & _ & RS & _ & _ & TE & _).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    assert (DSV : DEALLOC_STACK <= 1888) by (vm_compute; discriminate).
    pose proof WFC as (RZ16 & RZM & N1 & RZN & _).
    destruct (pchunk_geo AL (bs_X s) m ch AO RP RS HK) as (_ & _ & _ & GLO & GHI & _).
    assert (RU0 : 0 <= rup8 (qc_n ch)) by (unfold rup8; clear - N1; Z.div_mod_to_equations; lia).
    eapply (realloc_icpt_spec L TLO gp s7 s8 s9 s10 s11 F_ fc q lo LOH CLO LOQ QTOP Q16 262144 262728 eq_refl eq_refl ra ras ART
              (rl8_tree ATREE AX (bs_quar s) ch) (bs_H s) (qc_hdr AL ch + 16) n (rl_icpre s lo q m) (rl8_cpost AX dn q s LB st ch l1 l2 n oldn old m));
      [ | exact MC | exact ST | exact MI | exact TE | exact TRE | exact IA | exact CH | exact LRAS | exact NPC | exact RA4 | exact RANE
      | right; unfold qc_hdr; clear - GLO GHI RZ16 RZN RU0 N1 ACR; lia | ].
    - intros ra' u0 u1 u2 r0 r1 b3 b4 b5 b6 b7 r2 r3 r4 r5 r6 u3 u4 u5 u6 mW ws MCW STW SOBJ BUF LWS TRW (MUW & WMW & MIW & CPW).
      eapply implA_mono.
      + eapply (asan_realloc_L8 ART ATREE AX dn ASTK gp F_ fc (q - 2144) q lo CLO ltac:(clear - LOQ ASTK_LE; lia) ltac:(clear - LOQ DSV; lia) ltac:(clear; lia) QH
                  ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                  ra' u0 u1 u2 r0 r1 b3 b4 b5 b6 b7 r2 r3 r4 r5 r6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s LB st ch oldn l1 l2 n (realloc_tr ra ras) old m mW (WNR lo q)
                  (q - 2136) (q - 2136 + 16) ws);
          [ exact HR | exact MI | exact AE | exact RF | exact EL | exact OLD | exact MUW | exact WMW | apply wnr_fclass | exact MCW | exact STW | exact MIW | exact CPW
          | exact SOBJ | clear; lia | clear - QH; lia | exact BUF | exact TRW | rewrite LWS; unfold realloc_tr; cbn [length]; clear - LRAS; lia | clear; lia
          | rewrite LWS; clear - QH; lia | exact ALLOC | exact NR | exact TRIN ].
      + intros r H' ms' PO. exact PO.
    - intros mW MUW WMW MIW TEW IAW. unfold rl_icpre.
      split; [exact MUW|]. split; [exact WMW|]. split; [exact MIW|].
      exact (rl_cpre_front s LB m mW lo q HR MI CLO ltac:(clear - LOQ; lia) MUW WMW MIW TEW IAW).
  Qed.

  #[using="AO FSBE ASTK_LE"] Lemma realloc_null_walk : forall (gp s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
      (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) s LB (m : mem) (st : fsstate FI) n ras,
    RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top L ->
    fpchain m (at_top L) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
    0 <= n <= A0_MAXREQ ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n (realloc_tr ra ras) q lo ->
    implA (bs_H s) ATREE
      (ricpt_post L gp s7 s8 s9 s10 s11 F_ fc q lo 262144 ra ART (rn8_cpost ART AX dn q s LB st n m) s0 s1 s2 s3 s4 s5 s6 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) (wz n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz realloc_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros gp s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 s LB m st n ras
           HR MC MI AE RF ST CLO LOQ Q16 QTOP CH TRIN NR ALLOC.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    destruct (traces_ok _ _ _ TRIN) as (LRAS & NPC & RA4 & RANE & RNG).
    pose proof HR as (_ & _ & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRE & _ & (inited & IA) & _).
    pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (_ & _ & _ & _ & _ & TE & _).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    assert (DSV : DEALLOC_STACK <= 1888) by (vm_compute; discriminate).
    eapply (realloc_icpt_spec L TLO gp s7 s8 s9 s10 s11 F_ fc q lo LOH CLO LOQ QTOP Q16 262144 262728 eq_refl eq_refl ra ras ART
              ATREE (bs_H s) 0 n (rl_icpre s lo q m) (rn8_cpost ART AX dn q s LB st n m));
      [ | exact MC | exact ST | exact MI | exact TE | exact TRE | exact IA | exact CH | exact LRAS | exact NPC | exact RA4 | exact RANE | left; reflexivity | ].
    - intros ra' u0 u1 u2 r0 r1 b3 b4 b5 b6 b7 r2 r3 r4 r5 r6 u3 u4 u5 u6 mW ws MCW STW SOBJ BUF LWS TRW (MUW & WMW & MIW & CPW).
      eapply implA_mono.
      + eapply (asan_realloc_null_L8 ART ATREE AX dn ASTK gp F_ fc (q - 2144) q lo CLO ltac:(clear - LOQ ASTK_LE; lia) ltac:(clear - LOQ DSV; lia) ltac:(clear; lia) QH
                  ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                  ra' u0 u1 u2 r0 r1 b3 b4 b5 b6 b7 r2 r3 r4 r5 r6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s LB st n (realloc_tr ra ras) m mW (WNR lo q)
                  (q - 2136) (q - 2136 + 16) ws);
          [ exact HR | exact MI | exact AE | exact RF | exact MUW | exact WMW | apply wnr_fclass | exact MCW | exact STW | exact MIW | exact CPW
          | exact SOBJ | clear; lia | clear - QH; lia | exact BUF | exact TRW | rewrite LWS; unfold realloc_tr; cbn [length]; clear - LRAS; lia | clear; lia
          | rewrite LWS; clear - QH; lia | exact ALLOC | exact NR ].
      + intros r H' ms' PO. exact PO.
    - intros mW MUW WMW MIW TEW IAW. unfold rl_icpre.
      split; [exact MUW|]. split; [exact WMW|]. split; [exact MIW|].
      exact (rl_cpre_front s LB m mW lo q HR MI CLO ltac:(clear - LOQ; lia) MUW WMW MIW TEW IAW).
  Qed.
End RWALK.

End RAL8.

