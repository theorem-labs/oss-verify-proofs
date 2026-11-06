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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P F_alloc_M
                        F_malloc_icpt F_malloc_top ALedger AHeap2 AHeapB AFreeF AFreeZ AFreeL8 AAllocF AMallocP AMallocL8 AAllocL8 AHeapLaws.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section MGL8.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis AO : alayout_ok AL.
Hypothesis FSBE : FSB FI = al_fsb AL.

Definition ma_cpre (s : astB) (mW : mem) : Prop :=
  dr_inv AL E (bs_X s) (bs_H s) mW (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s)
  /\ alloc_env mW /\ thread_env2 AL mW /\ hooks_env mW /\ RDEPOT D (bs_depot s) (bs_dtotal s) mW /\ (exists inited, ia_cells 262144 262728 inited mW).

#[using="Type"] Lemma ia_cells_band : forall (m m' : mem) inited,
  (forall A cs, rw_cells asegs m A cs -> 743232 <= A -> A + Z.of_nat (cells_size cs) <= 1327052 -> rw_cells asegs m' A cs) ->
  ia_cells 262144 262728 inited m -> ia_cells 262144 262728 inited m'.
Proof.
  intros m m' inited TRC IA.
  destruct IA as (FL & [j0 C0] & [j2 [C2x Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_cells.
  split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; destruct inited; cbn [cells_size csize Nat.add]; clear; lia]|].
  split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
  split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2x| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
  split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
  split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
  exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia].
Qed.

#[using="AO"] Lemma ma_cpre_frame : forall s (m m' : mem) lo W,
  alloc_ceiling <= lo -> ma_cpre s m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> thread_env L m' ->
  Forall (fun iv => lo <= fst iv \/ iv = (THR + 3168, THR + 3169)) W -> ma_cpre s m'.
Proof.
  intros s m m' lo W CLO (INV & AENV & TE2 & HKE & RD & (inited & IA)) MU WM MI' TE' FW.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36. layout_apart_fact AO 2%nat 3%nat A23.
  assert (FZ : Forall (izone AL lo) W).
  { eapply Forall_impl; [| exact FW]. intros iv [H1|H1]; unfold izone; [left; exact H1| right; right; exact H1]. }
  assert (DJT : forall A k, A + k <= lo -> (A + k <= THR + 3168 \/ THR + 3169 <= A) -> disjoint_from W A k).
  { intros A k D1 D3. apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [a b] [H1|H1]; cbn [fst snd] in *; [left; clear - H1 D1; lia|].
    inversion H1; subst. clear - D3. lia. }
  unfold ma_cpre.
  split; [exact (dr_inv_frame_i AL E (bs_X s) (bs_H s) m m' _ _ _ lo _ AO LOH CLO INV MU WM MI' TE' FZ)|].
  split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia])|].
  split; [eapply (thread_env2_frame_m AL _ m m' TE2 MU); apply DJT; clear - LOH CLO T1 T2 T3 T4 T5 A23; lia|].
  split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia]|].
  split; [eapply (RDEPOT_frame_m AL _ _ _ m m' DLO SWB RD MU); apply DJT; clear - LOH CLO N1d N2d S1d S2d A35 A36 T3; lia|].
  exists inited. apply (ia_cells_band m m' inited); [| exact IA].
  intros A cs C0 H1 H2x. eapply rw_cells_transport_m; [exact C0| exact MU|]. apply DJT; clear - H1 H2x LOH T3; lia.
Qed.

Section AMALLOC.
  Variable ART : Type.
  Variable ATREE : itree nodeL (exc ART).
  Variable AX : ART -> pstate.
  Variables (dn ASTK : Z).
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (qa q0 lo : Z).
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis ASTK0 : 0 <= ASTK.
  Hypothesis LOQA : lo <= qa - 16 - ASTK.
  Hypothesis QQ0 : qa <= q0.
  Hypothesis Q0H : q0 <= 2^47.
  Hypothesis Q16 : qa mod 16 = 0.

  Definition ma8_cpost (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (m0 : mem)
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

  Definition ma8_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (m0 mW : mem)
      : ART -> (word -> bool) -> machine_state -> Prop :=
    fun r H1 ms1 => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 W,
      ms1 = MS (mkR ra (wz qa) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch W mW m1 /\ (forall B k, qa <= B -> disjoint_from W B k) /\ stk asegs m1 lo qa
      /\ ma8_cpost s LB st n m0 mW r H1 a0 m1.

  #[using="AO FSBE CLO ASTK0 LOQA QQ0 Q0H Q16"] Theorem asan_malloc_L8 : forall (ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (s : astB) (LB : list (block Z)) (st : fsstate FI) (n : Z) (tr : list Z)
        (m0 mW : mem) (FT0 : list (Z * Z)) (STK TR : Z) (ws : list word),
    RHEAP_B AL E s LB m0 -> mem_inv asegs m0 -> asan_env asegs m0 -> RFAKE FI st m0 ->
    munch FT0 m0 mW -> wmono asegs m0 mW -> Forall (fclass AL lo q0) FT0 ->
    mclean (bs_H s) mW -> stk asegs mW lo qa -> mem_inv asegs mW -> ma_cpre s mW ->
    rw_cells asegs mW STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] -> qa <= STK -> STK + 16 <= 2^47 ->
    u64arr asegs mW TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> qa <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n tr q0 lo ->
    0 <= n <= A0_MAXREQ ->
    implA (bs_H s) ATREE
      (ma8_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB st n m0 mW)
      (MS (mkR ra (wz qa) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) (wz STK) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz F_malloc_icpt.asan_malloc_entry) fc None mW (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s LB st n tr m0 mW FT0 STK TR ws
           HR MI AE RF MU0 WM0 FC0 MC ST MIW CPW SOBJ QSTK STKH BUF TRW LENW QTR TRH ALLOC NR.
    unfold F_malloc_icpt.asan_malloc_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    assert (QH : qa <= 2^47) by (clear - QQ0 Q0H; lia).
    assert (LQ1 : lo <= qa - 16) by (clear - LOQA ASTK0; lia).
    pose proof SOBJ as SOBJ0. hide SOBJ0. pose proof BUF as BUF0. hide BUF0. pose proof CPW as CPW0. hide CPW0. clear CPW.
    hide MU0. hide WM0.
    pose proof (munch_refl [(qa - 16, qa)] mW) as MU. pose proof (wmono_refl asegs mW) as WM.
    lz_go.
    zstep. carve_frame 16%nat ST.
    zstep. zstep.
    do 7 zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (qa + -16) with (qa - 16) in * by lia.
    lz_here.
    unhide MU0. unhide WM0. unhide CPW0. unhide SOBJ0. unhide BUF0.
    assert (MIA : mem_inv asegs mA) by assumption.
    assert (TEA : thread_env L mA).
    { destruct CPW0 as (INVW & _). pose proof INVW as (_ & _ & _ & _ & _ & TEW & _).
      pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
      eapply thread_env_frame; [exact TEW| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - LOH LQ1 CLO T2 T4. lia. }
    pose proof (ma_cpre_frame s mW mA lo [(qa - 16, qa)] CLO CPW0 MU WM MIA TEA ltac:(constructor; [left; cbn [fst]; exact LQ1| constructor])) as (INVA & AENVA & TE2A & HKEA & RDA & IAA).
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
        | exact IAA | exact SOBJ0 | clear - QSTK; lia | exact STKH | exact BUF0 | exact TRW | exact LENW | clear - QTR; lia | exact TRH
        | clear - LOQA; lia | clear - QQ0; lia | exact Q0H | clear - Q16; Z.div_mod_to_equations; lia ]. }
    intros r H1 ms1 [PO MC1]. unfold al8_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & s1' & A' & njunk & W1 & -> & GH1 & EX1 & EQ1 & ENS1 & ELA & MI1 & STK1 & AE1 & RF1 & AP1 & BLK1 & HR1 & NB1 & NSH1 & WMo1 & MUW1 & ABV1).
    clean_ms_mem MC1.
    eapply (rw_cells_transport_m _ mA m1) in FR; [| exact MUW1| apply ABV1; clear; lia].
    destruct (law_block_range AL E AO FI FSBE _ _ m1 (A', A', n) HR1 ltac:(left; reflexivity)) as (AP0 & _ & _ & APC & _).
    unfold blk_addr, blk_size in AP0, APC. cbn [fst snd] in AP0, APC.
    lz_go.
    replace (ret_pc (Z_to_bv 64 210448)) with (Z_to_bv 64 210448) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep. if_cases KA; zify_cond KA. { exfalso. clear - KA AP0 APC ACR NR. rewrite ?Z.mod_small in KA by lia. lia. } clear KA.
    zstep. zstep.
    zstep. replace (qa - 16 + 16) with qa by (clear; lia). zstep.
    release_frame FR STK1 qa.
    lz_ret. apply evt_done. unfold ma8_post.
    exists u0, u1, u2, (wz A'), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, ([(qa - 16, qa)] ++ W1).
    split; [reflexivity|].
    split; [exact (munch_joinP _ _ mW mA m1 MU MUW1)|].
    split; [intros B0 k0 HB0; apply disjoint_from_app; split; [cbn [disjoint_from]; clear - HB0; lia| apply ABV1; clear - HB0; lia]|].
    split; [exact STK1|].
    unfold ma8_cpost. exists s1', A', njunk.
    split; [reflexivity|]. split; [exact GH1|]. split; [exact EX1|]. split; [exact EQ1|]. split; [exact ENS1|]. split; [exact ELA|].
    split; [exact MI1|]. split; [exact AE1|]. split; [exact RF1|]. split; [exact AP1|]. split; [exact HR1|]. split; [exact NB1|]. split; [exact NSH1|]. exact WMo1.
  Qed.
End AMALLOC.

Notation WNM lo q := [(lo, q); (THR + 3168, THR + 3169)].

Definition ma_icpre (s : astB) (lo q : Z) (m : mem) : mem -> Prop :=
  fun mW => munch (WNM lo q) m mW /\ wmono asegs m mW /\ mem_inv asegs mW /\ ma_cpre s mW.

#[using="Type"] Lemma wnm_fclass : forall lo q, Forall (fclass AL lo q) (WNM lo q).
Proof.
  intros lo q. repeat (apply Forall_cons || apply Forall_nil).
  - left. unfold sub_iv. cbn [fst snd]. lia.
  - right. right. left. reflexivity.
Qed.

#[using="Type"] Lemma ma_cpre_of_heap : forall s LB (m : mem), RHEAP_B AL E s LB m -> mem_inv asegs m -> ma_cpre s m.
Proof.
  intros s LB m HR MI.
  pose proof HR as (_ & _ & _ & INVB & _ & _ & _ & _ & _ & _ & RD & _ & _ & _ & _ & _ & _ & TE2 & HKE & _ & AENV & IA & _).
  unfold ma_cpre. split; [exact (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI)|]. tauto.
Qed.

Section MWALK.
  Variable ART : Type.
  Variable ATREE : itree nodeL (exc ART).
  Variable AX : ART -> pstate.
  Variables (dn ASTK : Z).
  Hypothesis ASTK0 : 0 <= ASTK.
  Hypothesis ASTK_LE : ASTK <= 1888.

  #[using="AO FSBE ASTK0 ASTK_LE"] Lemma malloc_walk : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) s LB (m : mem) (st : fsstate FI) n ras,
    RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top L ->
    fpchain m (at_top L) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
    0 <= n <= A0_MAXREQ ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n (malloc_tr ra ras) q lo ->
    implA (bs_H s) ATREE
      (micpt_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra ART (ma8_cpost ART AX dn q s LB st n m) s0 s1 s2 s3 s4 s5 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz malloc_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m st n ras
           HR MC MI AE RF ST CLO LOQ Q16 QTOP CH TRIN NR ALLOC.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    destruct (malloc_traces_ok _ _ TRIN) as (LRAS & NPC & RA4 & RANE & RNG).
    pose proof HR as (_ & _ & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRE & _).
    pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (_ & _ & _ & _ & _ & TE & _).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
    eapply (malloc_icpt_spec L TLO gp s6 s7 s8 s9 s10 s11 F_ fc q lo LOH CLO LOQ QTOP Q16 ra ras ART ATREE (bs_H s) n
              (ma_icpre s lo q m) (ma8_cpost ART AX dn q s LB st n m));
      [ | exact MC | exact ST | exact MI | exact TE | exact TRE | exact CH | exact LRAS | exact NPC | exact RA4 | exact RANE | ].
    - intros ra' u0 u1 u2 r0 r1 b2 b3 b4 b5 b6 b7 r2 r3 r4 r5 u3 u4 u5 u6 mW ws MCW STW SOBJ BUF LWS TRW (MUW & WMW & MIW & CPW).
      eapply implA_mono.
      + eapply (asan_malloc_L8 ART ATREE AX dn ASTK gp F_ fc (q - 2128) q lo CLO ASTK0 ltac:(clear - LOQ ASTK_LE; lia) ltac:(clear; lia) QH
                  ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                  ra' u0 u1 u2 r0 r1 b2 b3 b4 b5 b6 b7 r2 r3 r4 r5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s LB st n (malloc_tr ra ras) m mW (WNM lo q)
                  (q - 2128) (q - 2128 + 16) ws);
          [ exact HR | exact MI | exact AE | exact RF | exact MUW | exact WMW | apply wnm_fclass | exact MCW | exact STW | exact MIW | exact CPW
          | exact SOBJ | clear; lia | clear - QH; lia | exact BUF | exact TRW | rewrite LWS; unfold malloc_tr; cbn [length]; clear - LRAS; lia | clear; lia
          | rewrite LWS; clear - QH; lia | exact ALLOC | exact NR ].
      + intros r H' ms' PO. exact PO.
    - intros mW MUW WMW MIW TEW. unfold ma_icpre.
      split; [exact MUW|]. split; [exact WMW|]. split; [exact MIW|].
      eapply (ma_cpre_frame s m mW lo (WNM lo q) CLO (ma_cpre_of_heap s LB m HR MI) MUW WMW MIW TEW).
      constructor; [left; cbn [fst]; clear; lia|]. constructor; [right; reflexivity| constructor].
  Qed.

  #[using="AO FSBE ASTK0 ASTK_LE"] Lemma malloc_walk_top : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) s LB (m : mem) (st : fsstate FI) n,
    RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> at_top L <= q + 16 -> q <= alloc_ceiling + 8388608 ->
    0 <= n <= A0_MAXREQ ->
    al8_stmt AL E FI AI ATREE AX dn ASTK s LB st n [PC0_MALLOC] q lo ->
    implA (bs_H s) ATREE
      (micpt_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra ART (ma8_cpost ART AX dn q s LB st n m) s0 s1 s2 s3 s4 s5 m)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz malloc_icpt_entry) fc None m (seg_rom asegs)).
  Proof.
    intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m st n
           HR MC MI AE RF ST CLO LOQ Q16 QTOP QSP NR ALLOC.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
    pose proof HR as (_ & _ & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRE & _).
    pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (_ & _ & _ & _ & _ & TE & _).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    assert (QH : q <= 2^47) by (clear - QSP ACR; change (2^47) with 140737488355328; lia).
    eapply (malloc_top_spec L TLO gp s6 s7 s8 s9 s10 s11 F_ fc q lo LOH CLO LOQ QTOP QSP ra ART ATREE (bs_H s) n
              (ma_icpre s lo q m) (ma8_cpost ART AX dn q s LB st n m));
      [ | exact MC | exact ST | exact MI | exact TE | exact TRE | ].
    - intros ra' u0 u1 u2 r0 r1 b2 b3 b4 b5 b6 b7 r2 r3 r4 r5 u3 u4 u5 u6 mW ws MCW STW SOBJ BUF LWS TRW (MUW & WMW & MIW & CPW).
      eapply implA_mono.
      + eapply (asan_malloc_L8 ART ATREE AX dn ASTK gp F_ fc (q - 2128) q lo CLO ASTK0 ltac:(clear - LOQ ASTK_LE; lia) ltac:(clear; lia) QH
                  ltac:(clear - Q16; Z.div_mod_to_equations; lia)
                  ra' u0 u1 u2 r0 r1 b2 b3 b4 b5 b6 b7 r2 r3 r4 r5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 s LB st n [PC0_MALLOC] m mW (WNM lo q)
                  (q - 2128) (q - 2128 + 16) ws);
          [ exact HR | exact MI | exact AE | exact RF | exact MUW | exact WMW | apply wnm_fclass | exact MCW | exact STW | exact MIW | exact CPW
          | exact SOBJ | clear; lia | clear - QH; lia | exact BUF | exact TRW | rewrite LWS; cbn [length]; clear; lia | clear; lia
          | rewrite LWS; clear - QH; lia | exact ALLOC | exact NR ].
      + intros r H' ms' PO. exact PO.
    - intros mW MUW WMW MIW TEW. unfold ma_icpre.
      split; [exact MUW|]. split; [exact WMW|]. split; [exact MIW|].
      eapply (ma_cpre_frame s m mW lo (WNM lo q) CLO (ma_cpre_of_heap s LB m HR MI) MUW WMW MIW TEW).
      constructor; [left; cbn [fst]; clear; lia|]. constructor; [right; reflexivity| constructor].
  Qed.

  #[using="Type"] Lemma malloc_conv : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z) (ra s0 s1 s2 s3 s4 s5 : word)
      s LB (m : mem) (st : fsstate FI) n r H' ms',
    micpt_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra ART (ma8_cpost ART AX dn q s LB st n m) s0 s1 s2 s3 s4 s5 m r H' ms' ->
    exists s1' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A : Z) (junk : list byte),
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ bs_ghost s1' = (H', bs_pages s) /\ bs_X s1' = AX r /\ bs_quar s1' = bs_quar s /\ bs_nsec s1' = bs_nsec s + dn
      /\ (exists ach, bs_live s1' = (ach, n) :: bs_live s /\ A = lc_user AL ach)
      /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
      /\ (forall LBk : list (block (am_K FI AI)),
            (forall b, In b LBk -> exists r0, In r0 (bs_live s) /\ blk_addr b = lc_user AL (fst r0) /\ blk_size b = snd r0) -> apres FI AI LBk q m m')
      /\ RHEAP_B AL E s1' ((A, A, n) :: LB) m'
      /\ rw_cells asegs m' A [CB (Z.to_nat n) junk] /\ rw_cells asegs m' (sh A) (shadow_cells (block_shadow n))
      /\ wmono asegs m m'.
  Proof.
    intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m st n r H' ms' POST.
    destruct POST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & mW & m' & W & EMS & MUW & WMW & MU & ABV & STK' & CP).
    destruct CP as (s1' & A' & junk & -> & GH & EX & EQ & ENS & ELA & MI' & AE' & RF' & AP' & HR' & NB & NSH & WMo).
    exists s1', t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', A', junk.
    split; [exact EMS|]. split; [exact GH|]. split; [exact EX|]. split; [exact EQ|]. split; [exact ENS|]. split; [exact ELA|].
    split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|]. split; [exact AP'|]. split; [exact HR'|].
    split; [exact NB|]. split; [exact NSH| exact WMo].
  Qed.
End MWALK.

End MGL8.
