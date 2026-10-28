(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BAllocSim BMmapSim BazyRestrict BazyLedger BazySR BazyNodes BothAllocModel BothAllocCons.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BsDepotInv BW_DepotFrame BllocWalkKit BecLazy BG_Malloc BG_Malloc2 BG_MallocModel BG_RepQ BG_RepQFacts BW_MergeBatches BW_Recycle BW_DoRecycle BG_WriteSet BecLazy2 BG_RecycleDefs.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Local Ltac olia := Zify.zify; xlia zchecker.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition wkeep (P : Z -> Prop) (m m' : mem) : Prop :=
  forall x : word, P (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

Lemma agree_on_weaken : forall (P P' : Z -> Prop) m m', (forall a, P' a -> P a) -> agree_on P m m' -> agree_on P' m m'.
Proof. intros P P' m m' H A x Hp Hr. exact (A x (H _ Hp) Hr). Qed.
Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m x _ _. reflexivity. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 A B x Hp Hr. rewrite (B x Hp Hr). exact (A x Hp Hr). Qed.

Section TransportPt2.
  Variable P : Z -> Prop.
  Variables m m' : mem.
  Hypothesis AG : agree_on P m m'.
  Let WK : wkeep P m m'.
  Proof.
    intros x Hp Hx. pose proof (bv_unsigned_in_range _ x) as R; change (bv_modulus 64) with (2^64) in R.
    pose proof (AG (bv_unsigned x) Hp R) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E.
    rewrite (wview_pointwise m m' x E). exact Hx.
  Qed.

  Lemma bytes_at_transport_pt2 : forall A bs,
    bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
  Proof.
    intros A bs (Ha & Hl & H) HR. split; [olia|]. split; [olia|].
    intros i Hi. unfold mrd. rewrite AG; [apply H; exact Hi| apply HR; olia| olia].
  Qed.
  Lemma stk_transport_pt2 : forall lo hi,
    stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
  Proof.
    intros lo hi (H1 & H2 & H) HR. split; [olia|]. split; [olia|]. intros a Ha.
    destruct (H a Ha) as [Hw (b & Hb)]. split.
    - apply WK; [| exact Hw]. unfold wa. rewrite unsigned_lit by olia. apply HR. exact Ha.
    - exists b. unfold mrd in *. rewrite AG; [exact Hb| apply HR; olia| olia].
  Qed.
  Lemma junk_transport_pt2 : forall lo n,
    junk m lo n -> (forall a, lo <= a < lo + n -> P a) -> junk m' lo n.
  Proof. intros lo n J HR Hn. eapply stk_transport_pt2; [apply J; exact Hn| exact HR]. Qed.
  Lemma wr_at_transport_pt2 : forall A n,
    wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
  Proof.
    intros A n (H1 & H2 & H) HR. split; [exact H1|]. split; [exact H2|]. intros i Hi.
    apply WK; [| apply H; exact Hi]. unfold wa. rewrite unsigned_lit by olia. apply HR. olia.
  Qed.
  Lemma rw_cells_transport_pt2 : forall A cs,
    rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
  Proof.
    intros A cs [[Hwf Hb] Hw] HR. split; [split; [exact Hwf|]| eapply wr_at_transport_pt2; [exact Hw| exact HR]].
    eapply bytes_at_transport_pt2; [exact Hb|]. rewrite cells_bytes_length by assumption. exact HR.
  Qed.
  Lemma u64arr_transport_pt2 : forall A ws,
    u64arr asegs m A ws -> (forall a, A <= a < A + 8 * Z.of_nat (length ws) -> P a) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [Hb Hw] HR. split.
    - eapply bytes_at_transport_pt2; [exact Hb|]. rewrite u64s_length, Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. apply HR. olia.
    - eapply wr_at_transport_pt2; [exact Hw|]. exact HR.
  Qed.
  Lemma SHAD_transport_pt2 : forall A sbs,
    SHAD m A sbs -> (forall a, sh A <= a < sh A + Z.of_nat (length sbs) -> P a) -> SHAD m' A sbs.
  Proof.
    intros A sbs (A0 & HA & [Hb Hw]) HR. split; [exact A0|]. split; [exact HA|].
    split; [eapply bytes_at_transport_pt2; eauto| eapply wr_at_transport_pt2; [exact Hw| exact HR]].
  Qed.
  Lemma poisoned_transport_pt2 : forall A k v,
    poisoned m A k v -> (forall a, sh A <= a < sh A + Z.of_nat k -> P a) -> poisoned m' A k v.
  Proof.
    intros A k v H HR. eapply SHAD_transport_pt2; [exact H|]. unfold poison_bytes. rewrite repeat_length. exact HR.
  Qed.
  Lemma batch_rep_transport_pt2 : forall b nx,
    (forall a, (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
    0 <= qb_count b -> 24 + 8 * qb_count b <= kBatchSize -> qb_count b = zlen (qb_chunks b) ->
    batch_rep m b nx -> batch_rep m' b nx.
  Proof.
    intros b nx HP K1 K2 K3 (B1 & B2 & B3 & B4). unfold batch_rep. unfold kBatchSize in *.
    assert (LW : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in K3; olia).
    split; [| split; [| split]].
    - eapply rw_cells_transport_pt2; [exact B1|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HP. left. olia.
    - eapply u64arr_transport_pt2; [exact B2|]. rewrite LW. intros a Ha. apply HP. left. olia.
    - eapply junk_transport_pt2; [exact B3|]. intros a Ha. apply HP. left. olia.
    - eapply poisoned_transport_pt2; [exact B4|]. intros a Ha. apply HP. right.
      change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. olia.
  Qed.
  Lemma bseg_transport_pt2 : forall l nx,
    (forall b a, In b l -> (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> P a) ->
    Forall bok l -> bseg m l nx -> bseg m' l nx.
  Proof.
    intros l nx HP OKl. induction l as [|b r IH]; [exact (fun x => x)|].
    cbn [bseg]. intros [HB HR]. apply Forall_cons_iff in OKl. destruct OKl as [OKb OKr].
    split; [| apply IH; [intros b0 a Hb0 Ha; apply (HP b0 a); [right; exact Hb0| exact Ha]| exact OKr| exact HR]].
    destruct OKb as (_ & _ & _ & K1 & K2 & _). unfold kBatchCount, kBatchSize in *.
    apply (batch_rep_transport_pt2 b _); [intros a Ha; apply (HP b a); [left; reflexivity| exact Ha]| clear - K1; olia| clear - K1; unfold kBatchSize; olia| exact K2| exact HB].
  Qed.
End TransportPt2.

Lemma PROOM_of_NUM : forall st XC XB, WFQ st XC XB -> NUM st -> pusage st + 303104 <= B_PRIM.
Proof.
  intros st XC XB W NM. pose proof B0_val as BV.
  assert (PB : pusage st <= B0); [| clear - PB BV; olia].
  apply pusage_bound; [exact NM|]. intros c Hc. unfold kNumClasses in Hc.
  pose proof (WFQ_region st XC XB c W ltac:(unfold kNumClasses; olia)) as RO. pose proof (class_size_table_facts c ltac:(olia)) as (CS1 & _ & CS3 & _).
  cbv zeta. split; [olia|]. split; [split; [apply (ro_alloc_nonneg _ _ RO)| apply (ro_alloc_le _ _ RO)]|].
  split.
  - pose proof (ro_tail_small _ _ RO ltac:(olia)) as T. destruct (rg_allocated_user (get_region st c) =? 0); unfold kUserMapSize in *; olia.
  - pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_bound _ _ RO). pose proof (ro_numfreed _ _ RO). pose proof (zlen_nonneg (rg_free_array (get_region st c))). olia.
Qed.

Lemma NUM_au : forall st st',
  (forall c0, 0 <= c0 -> rg_allocated_user (get_region st' c0) = rg_allocated_user (get_region st c0)) -> NUM st -> NUM st'.
Proof. intros st st' AU NM c Hc. unfold ncarved. rewrite (AU c ltac:(clear - Hc; olia)). exact (NM c Hc). Qed.

Lemma class_of_addr_sb : forall st st' a, as_space_beg st' = as_space_beg st -> class_of_addr st' a = class_of_addr st a.
Proof. intros st st' a E. unfold class_of_addr. rewrite E. reflexivity. Qed.
Lemma in_primary_sb : forall st st' a, as_space_beg st' = as_space_beg st -> in_primary st' a = in_primary st a.
Proof. intros st st' a E. unfold in_primary. rewrite E. reflexivity. Qed.

Lemma xb24_facts : forall st XC XB B, WFQ st XC XB -> In B XB -> class_of_addr st B = kBatchClass ->
  exists off, 0 <= off < 2^32 /\ B = as_space_beg st + kBatchClass * 2^32 + off /\ in_primary st B = true.
Proof.
  intros st XC XB B W HB CL. pose proof (WFQ_xb st XC XB B W HB) as CV. unfold xb_ok in CV. rewrite CL in CV.
  destruct CV as (C1 & C2 & C3 & C4 & C5).
  pose proof (WFQ_region st XC XB kBatchClass W ltac:(unfold kBatchClass, kNumClasses; olia)) as RO.
  pose proof (ro_alloc_le _ _ RO) as A1. pose proof (ro_mapped_bound _ _ RO) as A2.
  unfold region_beg, kRegionSizeLog in *. rewrite Z.shiftl_mul_pow2 in * by (clear; olia).
  change (class_size kBatchClass) with 8192 in *. unfold kFreeArrayOffset, kUserMapSize, kBatchClass in *.
  exists (B - as_space_beg st - 24 * 2^32). split; [clear - C3 C5 A1 A2; olia|]. split; [clear; olia|].
  unfold in_primary, kSpaceSize. apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; clear - C3 C5 A1 A2; olia.
Qed.

Lemma xc_chunk : forall st XC XB mch, WFQ st XC XB -> In mch XC ->
  exists ch, In ch (chunk_list st) /\ ch_state ch = CQuarantine /\ ch_chunk_beg ch = mch.
Proof.
  intros st XC XB mch W Hin. destruct (WFQ_xc st XC XB mch W Hin) as (ch & Fd & Qu). exists ch.
  split; [exact (find_chunk_In st _ ch Fd)|]. split; [exact Qu|].
  unfold ch_chunk_beg. rewrite (find_chunk_key st _ ch (WFQ_keys st XC XB W) Fd). unfold kChunkHeaderSize. clear; olia.
Qed.

Lemma u64arr_cell : forall m A (ls : list Z) (i : nat) x, u64arr asegs m A (wlist ls) -> nth_error ls i = Some x ->
  rw_cells asegs m (A + 8 * Z.of_nat i) [C8 (wz x)].
Proof.
  intros m A ls i x U NE. apply nth_error_split in NE. destruct NE as (l1 & l2 & -> & LEN).
  unfold wlist in U. rewrite map_app in U. cbn [map] in U. apply (proj1 (mb_u64arr_app _ _ _ _)) in U. destruct U as [_ U].
  apply (proj1 (mb_u64arr_cons _ _ _ _)) in U. destruct U as [U _]. rewrite length_map, LEN in U. exact U.
Qed.

Lemma arepq_sb_cell : forall s XC XB m, AREPQ s XC XB m -> rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz (a_sb s))].
Proof.
  intros s XC XB m R. pose proof (AREPQ_mem _ _ _ _ R) as (I & _). destruct I as (I1 & _).
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in I1. exact (proj1 I1).
Qed.

Lemma batch_junk : forall m b nx, bok b ->
  rw_cells asegs m (qb_addr b) [C8 (wz nx); C8 (wz (qb_size b)); C8 (wz (qb_count b))] ->
  u64arr asegs m (qb_addr b + 24) (wlist (qb_chunks b)) ->
  stk asegs m (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize) ->
  junk m (qb_addr b) kBatchSize.
Proof.
  intros m b nx OK H1 H2 H3 _. destruct OK as (K0 & K0' & _ & K1 & K2 & _).
  pose proof (stk_of_rw_cells asegs _ _ _ H1) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 24) with 24 in S1.
  pose proof (stk_of_u64arr _ _ _ H2) as S2. unfold wlist in S2. rewrite length_map in S2.
  replace (8 * Z.of_nat (length (qb_chunks b))) with (8 * qb_count b) in S2 by (unfold zlen in K2; clear - K2; olia).
  unfold kBatchSize, kBatchCount in *.
  eapply stk_merge; [exact S1| eapply stk_merge; [exact S2| exact H3| clear - K1; olia]| clear - K1; olia].
Qed.

Lemma bsum_cons_le : forall b T, bok b -> bsum T <= bsum (b :: T).
Proof. intros b T (_ & _ & _ & _ & _ & K & _). rewrite bsum_cons. unfold kBatchSize in K. clear - K; olia. Qed.

Lemma acompl_SP_mono : forall s s' d lo SP SP' m m', SP <= SP' -> acompl s s' d lo SP m m' -> acompl s s' d lo SP' m m'.
Proof.
  intros s s' d lo SP SP' m m' LE A a Ha NW. apply (A a Ha). intros W. apply NW. unfold awrit in W |- *.
  destruct W as [H|H]; [left; clear - H LE; olia| right; exact H].
Qed.

Section Loop.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Variables (rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 cs : word).
  Variables (lo : Z) (d : depot) (l : list qbatch) (Q : config -> Prop).

  Variables (s0 : ast) (m0 : mem) (mo0 : Model) (T0L : list qbatch).

  Let spv := bv_unsigned sp.
  Let T0 := spv + 112.
  Let SP := spv + 144.
  Let st0 := a_st s0.
  Let ca := wz (a_cache s0).

  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 800 <= spv.
  Hypothesis SPT : spv + 112 + 96 <= 2^47.
  Hypothesis SPA : spv mod 16 = 0.
  Hypothesis TPv : bv_unsigned tp = ATP.
  Hypothesis OKL : Forall bok l.
  Hypothesis PW : forall a b, In a (map qb_addr l) -> In b (map qb_addr l) -> a <> b -> a + kBatchSize <= b \/ b + kBatchSize <= a.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.

  Hypothesis ALB : forall a, alive st0 a -> a < aceil.

  Definition REL (s : ast) (m : mem) (mo : Model) : Prop :=
       a_thr s = a_thr s0 /\ a_ctx s = a_ctx s0 /\ a_fsb s = a_fsb s0 /\ a_Zr s = a_Zr s0 /\ a_top s = a_top s0 /\ a_bot s = a_bot s0
    /\ a_AL s = a_AL s0 /\ a_sb s = a_sb s0 /\ a_pa s = a_pa s0
    /\ (forall sc, In sc (as_sec (a_st s)) -> In sc (as_sec st0))
    /\ (forall c0, 0 <= c0 -> rg_allocated_user (get_region (a_st s) c0) = rg_allocated_user (get_region st0 c0))
    /\ nonvm_same mo0 mo /\ avmx s0 s mo0 mo
    /\ acompl s0 s d lo SP m0 m /\ avis s0 s m0 m
    /\ agree_on (fun a => SP <= a) m0 m
    /\ alive_kept st0 (a_st s) /\ agree_on (alive st0) m0 m.

  Definition CUR (s : ast) (m : mem) (mo : Model) (XC XB : list Z) : Prop :=
       AREPQ s XC XB m /\ as_cache_inited (a_st s) = true /\ NUM (a_st s)
    /\ awin_vis s m /\ flagsx_rep m /\ AMODELX s mo /\ DEPOT asegs d m /\ depot_placed s d /\ depot_cov d mo
    /\ mem_inv asegs m.

  Definition dr_mid (B : Z) (T' : list qbatch) (st : astate) (ms : list Z) (racc : list effect) : option (astate * list effect) :=
    match cb_recycle_list st ms racc with
    | None => None
    | Some (st1, racc1) =>
        if negb (in_primary st1 B) then None else
        match cache_dealloc st1 (class_of_addr st1 B) B with
        | None => None
        | Some (st2, ev2) => do_recycle st2 T' (rev_append ev2 racc1)
        end
    end.
  Lemma do_recycle_cons : forall st b T' racc, do_recycle st (b :: T') racc = dr_mid (qb_addr b) T' st (qb_chunks b) racc.
  Proof. reflexivity. Qed.

  Definition MSF (R : astate -> list effect -> option (astate * list effect)) (st : astate) : Prop :=
    forall stA racc, same_but_shadow stA st0 ->
      exists stB raccB, do_recycle stA T0L racc = R stB raccB /\ same_but_shadow stB st.

  Definition dr_post (msF' : machine_state) (mo' : Model) : Prop :=
    exists (s' : ast) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       REL s' m' mo' /\ CUR s' m' mo' [] []
    /\ lzok asegs (a_L s') (a_S s') (a_Zr s') (mkCfg msF' mo')
    /\ restrict (a_L s') (a_S s') msF'
       = MS (mkR (wz 0x9447c) (Z_to_bv 64 T0) gp tp t0 t1 t2 rs0 rs1 a0 a1 a2 a3 a4 a5 a6 a7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x9447c) fc None m' (seg_rom asegs)
    /\ stk asegs m' lo T0
    /\ rw_cells asegs m' T0 [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
    /\ (forall stA racc, same_but_shadow stA st0 -> exists stA' racc', do_recycle stA T0L racc = Some (stA', racc') /\ same_but_shadow stA' (a_st s')).

  Hypothesis STEP_CHUNK : forall (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 : word)
      (m : mem) (msF : machine_state) (mo : Model) (s : ast) (XC XB : list Z) (ch : chunk),
      AREPQ s (ch_chunk_beg ch :: XC) XB m -> In ch (chunk_list (a_st s)) -> ch_state ch = CQuarantine ->
      as_cache_inited (a_st s) = true -> awin_vis s m /\ flagsx_rep m -> AMODELX s mo ->
      DEPOT asegs d m -> depot_placed s d -> depot_cov d mo -> mem_inv asegs m ->
      aceil <= lo -> lo + 800 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> bv_unsigned tp = ATP -> pusage (a_st s) + 303104 <= B_PRIM ->
      bv_unsigned sp <= bv_unsigned sp + 8 /\ bv_unsigned sp + 8 + 8 <= 2^63 ->
      rw_cells asegs m (bv_unsigned sp + 8) [C8 (wz (a_cache s))] ->
      lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (wz (bv_unsigned sp + 8)) (wz (ch_chunk_beg ch)) a2 a3 a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x947ac) fc None m (seg_rom asegs) ->
      (forall msF' mo',
         rstep_post ra sp gp tp (Z_to_bv 64 T0) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 F fc s d lo m mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st s) ->
                         exists stA' ev, cb_recycle stA (ch_chunk_beg ch) = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).

  Hypothesis STEP_BATCH : forall (ra t0 t1 t2 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 : word)
      (m : mem) (msF : machine_state) (mo : Model) (s : ast) (XC XB : list Z) (p : Z),
      AREPQ s XC (p :: XB) m -> class_of_addr (a_st s) p = kBatchClass ->
      as_cache_inited (a_st s) = true -> awin_vis s m /\ flagsx_rep m -> AMODELX s mo ->
      DEPOT asegs d m -> depot_placed s d -> depot_cov d mo -> mem_inv asegs m ->
      aceil <= lo -> lo + 688 <= bv_unsigned sp -> bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> bv_unsigned tp = ATP ->
      junk m p (class_size kBatchClass) -> poisoned m p (Z.to_nat (class_size kBatchClass / 8)) kAsanHeapLeftRedzoneMagic ->
      pusage (a_st s) + 303104 <= B_PRIM ->
      lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) (wz (a_cache s)) (wz AINST) (wz kBatchClass) (wz p) a4 a5 a6 a7
                  x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x94bb0) fc None m (seg_rom asegs) ->
      (forall msF' mo',
         rstep_post ra sp gp tp (Z_to_bv 64 T0) (wz AINST) x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 F fc s d lo m mo XC XB XB
           (fun st' => forall stA, same_but_shadow stA (a_st s) ->
                         exists stA' ev, cache_dealloc stA kBatchClass p = Some (stA', ev) /\ same_but_shadow stA' st') msF' mo' ->
         sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).

  Definition TOK (T : list qbatch) : Prop :=
       Forall bok T /\ List.NoDup (map qb_addr T) /\ (forall x, In x T -> In (qb_addr x) (map qb_addr l))
    /\ bsum T < 2^62 /\ Forall (fun b => class_of_addr st0 (qb_addr b) = kBatchClass) T.

  Definition memB (m : mem) (b : qbatch) (T' : list qbatch) (j0 : list byte) : Prop :=
       rw_cells asegs m T0 [C8 (wz (zlen T')); C8 (wz (hd 0 (map qb_addr T'))); C8 (wz (last (map qb_addr T') 0)); C8 (wz (bsum T'))]
    /\ bseg m T' 0
    /\ dr_frame m spv j0 ca cs rs9 rs8 rs7 rs6 rs5 rs4 rs3 rs2 rs1 rs0 (wz 0x9447c)
    /\ rw_cells asegs m (qb_addr b) [C8 (wz (hd 0 (map qb_addr T'))); C8 (wz (qb_size b)); C8 (wz (qb_count b))]
    /\ u64arr asegs m (qb_addr b + 24) (wlist (qb_chunks b))
    /\ stk asegs m (qb_addr b + 24 + 8 * qb_count b) (qb_addr b + kBatchSize)
    /\ poisoned m (qb_addr b) (Z.to_nat (kBatchSize / 8)) kAsanHeapLeftRedzoneMagic.

  Definition HEADINV (T : list qbatch) (s : ast) (m : mem) (mo : Model) (msF : machine_state) (XC XB : list Z) (j0 : list byte)
      (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 : word) : Prop :=
       REL s m mo /\ CUR s m mo XC XB /\ stk asegs m lo spv
    /\ Permutation XC (flat_map qb_chunks T) /\ Permutation XB (map qb_addr T)
    /\ TOK T /\ dr_head_mem sp rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 ca cs m T j0
    /\ MSF (fun stB raccB => do_recycle stB T raccB) (a_st s)
    /\ lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo)
    /\ restrict (a_L s) (a_S s) msF = dr_head_ms sp gp tp F fc s10 s11 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 T 0x946ec m.

  Lemma REL_refl : avmx s0 s0 mo0 mo0 -> REL s0 m0 mo0.
  Proof.
    intros AV. unfold REL. repeat (split; [reflexivity|]). split; [intros sc Hsc; exact Hsc|]. split; [intros c0 _; reflexivity|].
    split; [apply nonvm_same_refl|]. split; [exact AV|]. split; [apply acompl_refl|]. split; [apply avis_of_wmono; apply wmono_refl|]. split; [apply agree_on_refl|].
    split; [apply alive_kept_refl| apply agree_on_refl].
  Qed.

  Lemma agree_of_acompl : forall (P : Z -> Prop) s s' SPx m m',
    acompl s s' d lo SPx m m' -> (forall a, P a -> ~ awrit s s' d lo SPx a) -> agree_on P m m'.
  Proof. intros P s s' SPx m m' A NW x Hx Hr. exact (A x Hr (NW x Hx)). Qed.

  Lemma above_not_awrit : forall s s' SPx a,
    placed_ok s -> (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s))) ->
    aceil <= SPx -> lo <= SPx -> SPx <= a -> ~ awrit s s' d lo SPx a.
  Proof.
    intros s s' SPx a PL SUB AC LS Ha W. pose proof aceil_range as ACR. pose proof DLO as [D1 D2].
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & _ & _ & _ & _ & _ & F1 & F2 & _ & _ & _ & _ & SEC & SEC2 & TCX).
    unfold awrit, astatw in W. unfold a_sb, kSpaceSize, kPageSize, kPtrArrayReserve, AINST, AIAINIT, AIAINST, sh, ASHADOW_BASE in *.
    destruct W as [H|[H|[H|[H|[H|[H|[H|H]]]]]]].
    - clear - H Ha. olia.
    - clear - H Ha T3 AC. olia.
    - clear - H Ha S3 AC. olia.
    - clear - H Ha S3 AC ACR. olia.
    - clear - H Ha P3 AC. olia.
    - destruct H as (sc & I & R). assert (I' : In sc (as_sec (a_st s))) by (destruct I as [I|I]; [exact I| exact (SUB sc I)]).
      pose proof (SEC sc I') as (_ & _ & G & _). clear - R Ha G AC ACR. olia.
    - clear - H Ha AC ACR. olia.
    - clear - H Ha D1 D2 LS. olia.
  Qed.

  Lemma batch_in_pendz : forall st PZ x a, In x PZ -> class_of_addr st x = kBatchClass ->
    (x <= a < x + kBatchSize \/ sh x <= a < sh x + kBatchSize / 8) -> pendz st PZ a.
  Proof.
    intros st PZ x a Hx CL R. exists x. split; [exact Hx|]. rewrite CL. change (class_size kBatchClass) with kBatchSize. exact R.
  Qed.

  Lemma TOK_tail : forall b T, TOK (b :: T) -> TOK T.
  Proof.
    intros b T (K1 & K2 & K3 & K4 & K5). apply Forall_cons_iff in K1. apply Forall_cons_iff in K5. cbn [map] in K2. apply List.NoDup_cons_iff in K2.
    split; [exact (proj2 K1)|]. split; [exact (proj2 K2)|]. split; [intros x Hx; apply K3; right; exact Hx|].
    split; [pose proof (bsum_cons_le b T (proj1 K1)); clear - H K4; olia| exact (proj2 K5)].
  Qed.

  Definition wlocal (W : list ivl) : Prop := Forall (fun iv : ivl => spv <= fst iv /\ snd iv <= SP) W.

  Lemma outside_below : forall W a, wlocal W -> a < spv -> outside W a.
  Proof.
    intros W a FW Ha. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in FW. destruct FW as [F1 F2]. cbn [fst snd] in F1.
    split; [clear - F1 Ha; olia| exact (IH F2)].
  Qed.
  Lemma outside_above : forall W a, wlocal W -> SP <= a -> outside W a.
  Proof.
    intros W a FW Ha. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in FW. destruct FW as [F1 F2]. cbn [fst snd] in F1.
    split; [clear - F1 Ha; olia| exact (IH F2)].
  Qed.

  Lemma flagsx_local : forall W m m', flagsx_rep m -> wlocal W -> munch W m m' -> wmono asegs m m' -> flagsx_rep m'.
  Proof.
    intros W m m' FX FW MU WM. pose proof (munch_agree _ _ _ MU) as AG. pose proof aceil_range as ACR.
    assert (ZT : forall a, a < AIMG_TOP -> outside W a) by (intros a Ha; apply (outside_below W a FW); clear - Ha ACR LO HI; unfold AIMG_TOP, spv in *; olia).
    destruct FX as (FXa & FXb & [g FXc] & FXd & [bb FXe]). unfold flagsx_rep. unfold ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS, AIMG_TOP in *.
    split; [| split; [| split; [exists g| split; [| exists bb]]]];
      (eapply (rw_cells_transport_pt _ m m' AG WM); [eassumption|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; apply ZT; clear - Ha; olia).
  Qed.

  Lemma stk_local : forall W m m' x, stk asegs m lo x -> wlocal W -> x <= spv -> munch W m m' -> wmono asegs m m' -> stk asegs m' lo x.
  Proof.
    intros W m m' x ST FW LE MU WM. eapply (stk_transport_pt _ m m' (munch_agree _ _ _ MU) WM); [exact ST|]. intros a Ha. apply (outside_below W a FW). clear - Ha LE; olia.
  Qed.

  Lemma CUR_local : forall s m mo XC XB W m' mo',
    CUR s m mo XC XB -> wlocal W -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> same_but_materialized mo mo' ->
    CUR s m' mo' XC XB.
  Proof.
    intros s m mo XC XB W m' mo' (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI) FW MU WM MI' SBM. pose proof aceil_range as ACR.
    split; [| split; [exact INIT| split; [exact NM| split; [exact (awin_vis_wmono s m m' AWV WM)| split; [exact (flagsx_local W m m' FXR FW MU WM)| split; [exact (AMODELX_mat s mo mo' AMX SBM)| split; [| split; [exact DPL| split; [exact (depot_cov_mat d mo mo' DCOV SBM)| exact MI']]]]]]]]].
    - eapply AREPQ_frame; [exact RQ| exact MU| exact WM|]. unfold awin_ok. apply Forall_forall. intros [x y] Hin a Ha.
      apply (stack_not_afootQ s XC XB (conj (AREPQ_placed _ _ _ _ RQ) (AREPQ_WFQ _ _ _ _ RQ))).
      pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]. cbn [fst snd] in F1, F2, Ha. clear - F1 Ha LO HI; unfold spv in *; olia.
    - eapply DEPOT_transport; [exact DEP| exact MU| exact WM|]. pose proof DLO as [D1 D2]. unfold depot_avoid, avoids.
      repeat split; apply Forall_forall; intros [x y] Hin; pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]; cbn [fst snd] in F1, F2 |- *;
        clear - F1 D1 D2 ACR LO HI; unfold spv in *; olia.
  Qed.

  Lemma REL_local : forall s m mo W m' mo',
    REL s m mo -> wlocal W -> munch W m m' -> wmono asegs m m' -> same_but_materialized mo mo' -> REL s m' mo'.
  Proof.
    intros s m mo W m' mo' RL FW MU WM SBM.
    pose proof RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    unfold REL. split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
    split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|]. split; [exact SUBS|]. split; [exact AU|].
    split; [eapply nonvm_same_trans; [exact NVS| apply nonvm_same_mat; exact SBM]|].
    split; [eapply avmx_mat_r; [exact AVM| exact SBM]|].
    split.
    { apply (acompl_trans s0 s s d lo SP m0 m m' (conj Et (conj Esb Epa)) SUBS ACM).
      apply (acompl_of_munchF s s d lo SP W m m' MU). apply Forall_forall. intros [x y] Hin a Ha.
      pose proof (proj1 (Forall_forall _ _) FW (x, y) Hin) as [F1 F2]. cbn [fst snd] in F1, F2, Ha. unfold awrit. left. clear - F1 F2 Ha LO HI; unfold spv, SP in *; olia. }
    split; [apply (avis_trans s0 s s m0 m m' SUBS (fun sc H => H) AVS); apply avis_of_wmono; exact WM|].
    split; [eapply agree_on_trans; [exact AGS|]; intros a Ha Hr; apply (munch_agree _ _ _ MU a); [| exact Hr]; apply (outside_above W a FW); exact Ha|].
    split; [exact ALK|].
    eapply agree_on_trans; [exact AGA|]. intros a Ha Hr. apply (munch_agree _ _ _ MU a); [| exact Hr]. apply (outside_below W a FW).
    pose proof (ALB a Ha) as B. clear - B LO HI. unfold spv. olia.
  Qed.

  Lemma batch_phase : forall (b : qbatch) (T' : list qbatch) (XC XB : list Z) (s : ast) (m : mem) (mo : Model) (msF : machine_state)
      (j0 : list byte) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word),
      REL s m mo -> CUR s m mo XC XB -> stk asegs m lo spv ->
      Permutation XC (flat_map qb_chunks T') -> Permutation XB (qb_addr b :: map qb_addr T') ->
      TOK (b :: T') -> memB m b T' j0 ->
      MSF (fun stB raccB => dr_mid (qb_addr b) T' stB [] raccB) (a_st s) ->
      lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688))
                  (wz (qb_addr b)) (wz kSpaceSize) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x94744) fc None m (seg_rom asegs) ->
      (T' <> [] -> forall s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6',
          HEADINV T' s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' ->
          sreach asegs Q (mkCfg msF' mo')) ->
      (forall msF' mo', dr_post msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).
  Proof.
    intros b T' XC XB s m mo msF j0 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6.
    intros RL CU ST PXC PXB TK MB MF OK VIS HK K.
    destruct CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    destruct TK as (OKT & NDT & SUBT & BST & CLT).
    destruct MB as (HT & BSG & FR & HB & ARR & STB & POI).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    assert (CLb : class_of_addr (a_st s) (qb_addr b) = kBatchClass).
    { rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (Forall_inv CLT). }
    assert (INb : In (qb_addr b) XB) by (eapply Permutation_in; [apply Permutation_sym; exact PXB| left; reflexivity]).
    destruct (xb24_facts _ _ _ _ WQ INb CLb) as (off & OFF & EB & PRIM).
    pose proof (Forall_inv OKT) as OKb. pose proof OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    pose proof PL as (S1 & S2 & S3 & PLrest).
    assert (ECA : a_cache s = a_cache s0) by (unfold a_cache; rewrite Et; reflexivity).

    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_call_batch sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs (qb_addr b) (a_sb s) kBatchClass off).
      - exact MI.
      - exact S2.
      - exact S3.
      - unfold kBatchClass; clear; olia.
      - exact OFF.
      - exact EB.
      - exact (arepq_sb_cell _ _ _ _ RQ).
      - exact FR. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.

    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    apply (STEP_BATCH (wz 0x94770) t0 t1 t2 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize) x6 x7 x8 x9 t3 t4 t5 t6
             m msF1 mo1 s XC (map qb_addr T') (qb_addr b)).
    - eapply AREPQ_perm; [apply Permutation_refl| exact PXB| exact RQ].
    - exact CLb.
    - exact INIT.
    - exact (conj AWV FXR).
    - exact AMX1.
    - exact DEP.
    - exact DPL.
    - exact DCOV1.
    - exact MI.
    - exact LO.
    - clear - HI; unfold spv in *; olia.
    - clear - SPT; unfold spv in *; olia.
    - exact SPA.
    - exact ST.
    - exact TPv.
    - change (class_size kBatchClass) with kBatchSize. exact (batch_junk m b _ OKb HB ARR STB).
    - change (class_size kBatchClass / 8) with (kBatchSize / 8). exact POI.
    - exact (PROOM_of_NUM _ _ _ WQ NM).
    - exact OK1.
    - rewrite VIS1. unfold ca. rewrite ECA. reflexivity.
    - cbv beta. intros msF2 mo2 POST.
    destruct POST as (s2 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & Et2 & Ec2 & Ef2 & Ez2 & Etp2 & Ebt2 & Eal2 & Esb2 & Epa2 & SUB2 & INIT2 & AU2 & OK2 & VIS2
                      & RQ2 & AWV2 & FXR2 & AMX2 & NVS2 & AVM2 & DCOV2 & DEP2 & DPL2 & MI2 & ST2 & ACM2 & AVS2 & AGP2 & ALK2 & AGA2 & MOD2).
    change (ret_pc (wz 0x94770)) with (ret_pc (Z_to_bv 64 0x94770)) in VIS2. rewrite (ret_pc_even 0x94770) in VIS2 by (clear; olia).

    assert (AGS2 : agree_on (fun a => spv <= a) m m2).
    { apply (agree_of_acompl _ s s2 spv m m2 ACM2). intros a Ha. apply (above_not_awrit s s2 spv a PL SUB2); [clear - LO HI ACR; unfold spv in *; olia| clear - HI; unfold spv in *; olia| exact Ha]. }
    pose proof (TOK_tail b T' (conj OKT (conj NDT (conj SUBT (conj BST CLT))))) as (OKT' & NDT' & SUBT' & BST' & CLT').
    assert (HM2 : dr_head_mem sp rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 ca cs m2 T' j0).
    { split; [| split].
      - eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact HT|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold T0, spv in *. clear - Ha; olia.
      - eapply (bseg_transport_pt2 _ m m2 AGP2); [| exact OKT'| exact BSG].
        intros b0 a Hb0 Ha. apply (batch_in_pendz (a_st s) (map qb_addr T') (qb_addr b0) a); [apply in_map; exact Hb0| | exact Ha].
        rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (proj1 (Forall_forall _ _) CLT' b0 Hb0).
      - unfold dr_frame in FR |- *. eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact FR|]. intros a Ha. unfold spv in *. clear - Ha; olia. }

    eapply (evt_sreach_lazy_at asegs (a_L s2) (a_S s2) (a_Zr s2) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (dr_loop_test sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo); [| exact MI2| exact OKT'| exact BST'| exact HM2| exact ST2].
      clear - HI; unfold spv in *; olia. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ VIS3.

    assert (RL2 : REL s2 m2 mo3).
    { unfold REL. rewrite Et2, Ec2, Ef2, Ez2, Etp2, Ebt2, Eal2, Esb2, Epa2.
      split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
      split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|].
      split; [intros sc Hsc; exact (SUBS sc (SUB2 sc Hsc))|].
      split; [intros c0 Hc0; rewrite (AU2 c0 Hc0); exact (AU c0 Hc0)|].
      split; [eapply nonvm_same_trans; [exact NVS| eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| eapply nonvm_same_trans; [exact NVS2| apply nonvm_same_mat; exact SBM3]]]|].
      split; [apply (avmx_trans s0 s s2 mo0 mo mo3 SUBS SUB2 AVM);
              eapply avmx_mat_r; [eapply avmx_mat_l; [exact SBM1| exact AVM2]| exact SBM3]|].
      split; [apply (acompl_trans s0 s s2 d lo SP m0 m m2 (conj Et (conj Esb Epa)) SUBS ACM); apply (acompl_SP_mono s s2 d lo spv SP m m2); [unfold SP, spv; clear; olia| exact ACM2]|].
      split; [exact (avis_trans s0 s s2 m0 m m2 SUBS SUB2 AVS AVS2)|].
      split; [eapply agree_on_trans; [exact AGS|]; eapply agree_on_weaken; [| exact AGS2]; intros a Ha; unfold SP, spv in *; clear - Ha; olia|].
      split; [exact (alive_kept_trans _ _ _ ALK ALK2)| exact (agree_alive_trans st0 (a_st s) m0 m m2 ALK AGA AGA2)]. }
    pose proof (NUM_au _ _ AU2 NM) as NM2.
    pose proof (AMODELX_mat s2 mo2 mo3 AMX2 SBM3) as AMX3. pose proof (depot_cov_mat d mo2 mo3 DCOV2 SBM3) as DCOV3.
    assert (MF2 : MSF (fun stB raccB => do_recycle stB T' raccB) (a_st s2)).
    { intros stA racc SA. destruct (MF stA racc SA) as (stB & raccB & EQ & SB).
      pose proof SB as SB'. destruct SB' as (Esbeg & _).
      destruct (MOD2 stB SB) as (stC & ev & CD & SC).
      exists stC, (rev_append ev raccB). split; [| exact SC].
      rewrite EQ. unfold dr_mid. cbn [cb_recycle_list]. rewrite (in_primary_sb (a_st s) stB) by exact Esbeg. rewrite PRIM. cbn [negb].
      rewrite (class_of_addr_sb (a_st s) stB) by exact Esbeg. rewrite CLb. rewrite CD. reflexivity. }
    assert (XCP : Permutation XC (flat_map qb_chunks T')) by exact PXC.
    destruct T' as [|b' T''].
    +
      destruct VIS3 as [VIS3 ST3].
      apply K. unfold dr_post. exists s2, t0', t1', t2', (wz 0), a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
      split; [exact RL2|].
      split. { split; [| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]].
               cbn [flat_map] in XCP. apply Permutation_sym, Permutation_nil in XCP. subst XC. exact RQ2. }
      split; [exact OK3|]. split; [exact VIS3|]. split; [exact ST3|]. split; [exact (proj1 HM2)|].
      intros stA racc SA. destruct (MF2 stA racc SA) as (stB & raccB & EQ & SB). exists stB, raccB. split; [exact EQ| exact SB].
    +
      eapply (HK ltac:(discriminate)). unfold HEADINV.
      split; [exact RL2|].
      split; [split; [exact RQ2| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]]|].
      split; [exact ST2|]. split; [exact XCP|]. split; [apply Permutation_refl|].
      split; [exact (conj OKT' (conj NDT' (conj SUBT' (conj BST' CLT'))))|].
      split; [exact HM2|]. split; [exact MF2|]. split; [exact OK3| exact VIS3].
  Qed.

  Lemma chunk_phase : forall (rest : list Z) (b : qbatch) (T' : list qbatch) (XC XB : list Z) (s : ast) (m : mem) (mo : Model) (msF : machine_state)
      (j0 : list byte) (i : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6 : word),
      rest <> [] -> 0 <= i -> rest = skipn (Z.to_nat i) (qb_chunks b) ->
      REL s m mo -> CUR s m mo XC XB -> stk asegs m lo spv ->
      Permutation XC (rest ++ flat_map qb_chunks T') -> Permutation XB (qb_addr b :: map qb_addr T') ->
      TOK (b :: T') -> memB m b T' j0 ->
      MSF (fun stB raccB => dr_mid (qb_addr b) T' stB rest raccB) (a_st s) ->
      lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo) ->
      restrict (a_L s) (a_S s) msF
        = MS (mkR rax sp gp tp t0 t1 t2 (Z_to_bv 64 T0) (wz AINST) a0 a1 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688))
                  (wz (qb_addr b)) (wz kSpaceSize) x6 (wz (qb_addr b + 152 + 8 * i)) (wz (qb_count b + 16)) (wz (16 + i)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9472c) fc None m (seg_rom asegs) ->
      (T' <> [] -> forall s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6',
          HEADINV T' s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' ->
          sreach asegs Q (mkCfg msF' mo')) ->
      (forall msF' mo', dr_post msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).
  Proof.
    induction rest as [|mi rest' IH]; intros b T' XC XB s m mo msF j0 i rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 t3 t4 t5 t6;
      intros NE I0 EQR RL CU ST PXC PXB TK MB MF OK VIS HK K; [exfalso; exact (NE eq_refl)|]. clear NE.
    destruct CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof RL as (Et & Ec & Ef & Ez & Etp & Ebt & Eal & Esb & Epa & SUBS & AU & NVS & AVM & ACM & AVS & AGS & ALK & AGA).
    pose proof TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof MB as (HT & BSG & FR & HB & ARR & STB & POI).
    pose proof (AREPQ_placed _ _ _ _ RQ) as PL. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    pose proof (Forall_inv OKT) as OKb. pose proof OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).
    pose proof (Forall_inv CLT) as CLb0.
    assert (ECA : a_cache s = a_cache s0) by (unfold a_cache; rewrite Et; reflexivity).

    assert (NTH : nth_error (qb_chunks b) (Z.to_nat i) = Some mi) by (rewrite <- hd_error_skipn, <- EQR; reflexivity).
    assert (IR : 0 <= i < qb_count b).
    { split; [exact I0|]. pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
    assert (MIR : 0 <= mi < 2^64) by exact (proj1 (Forall_forall _ _) Kb7 mi (nth_error_In _ _ NTH)).
    assert (CELL : rw_cells asegs m (qb_addr b + 24 + 8 * i) [C8 (wz mi)]).
    { pose proof (u64arr_cell m _ _ _ _ ARR NTH) as C. rewrite Z2Nat.id in C by exact I0. exact C. }

    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_call_chunk sp gp tp F fc s10 s11 (qb_addr b) i (qb_count b) mi); [exact MI| exact Kb1| exact Kb2| exact IR| clear - Kb4; olia| exact MIR| exact CELL]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.

    assert (INmi : In mi XC) by (eapply Permutation_in; [apply Permutation_sym; exact PXC| left; reflexivity]).
    destruct (xc_chunk _ _ _ _ WQ INmi) as (ch & CHIN & QUAR & Ebeg).

    assert (CBC : rw_cells asegs m (spv + 8) [C8 (wz (a_cache s))]).
    { unfold dr_frame in FR. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR. destruct FR as [_ FR2].
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FR2. destruct FR2 as [FR2 _]. cbn [cells_size csize Nat.add] in FR2.
      rewrite ECA. unfold ca in FR2. replace (spv + 8) with (spv + Z.of_nat 8) by (clear; olia). exact FR2. }

    apply (STEP_CHUNK (wz 0x94738) t0 t1 t2 a2 a3 a4 a5 a6 a7 (wz (AINST + 64)) (wz (AINST + 688)) (wz (qb_addr b)) (wz kSpaceSize) x6
             (wz (qb_addr b + 152 + 8 * i)) (wz (qb_count b + 16)) (wz (16 + i)) t3 t4 t5 t6
             m msF1 mo1 s (rest' ++ flat_map qb_chunks T') XB ch).
    - rewrite Ebeg. eapply AREPQ_perm; [exact PXC| apply Permutation_refl| exact RQ].
    - exact CHIN.
    - exact QUAR.
    - exact INIT.
    - exact (conj AWV FXR).
    - exact AMX1.
    - exact DEP.
    - exact DPL.
    - exact DCOV1.
    - exact MI.
    - exact LO.
    - exact HI.
    - clear - SPT; unfold spv in *; olia.
    - exact SPA.
    - exact ST.
    - exact TPv.
    - exact (PROOM_of_NUM _ _ _ WQ NM).
    - clear - SPT SPR; unfold spv in *; olia.
    - exact CBC.
    - exact OK1.
    - rewrite VIS1, Ebeg. unfold wz, T0, spv. reflexivity.
    - cbv beta. intros msF2 mo2 POST.
    destruct POST as (s2 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                      & Et2 & Ec2 & Ef2 & Ez2 & Etp2 & Ebt2 & Eal2 & Esb2 & Epa2 & SUB2 & INIT2 & AU2 & OK2 & VIS2
                      & RQ2 & AWV2 & FXR2 & AMX2 & NVS2 & AVM2 & DCOV2 & DEP2 & DPL2 & MI2 & ST2 & ACM2 & AVS2 & AGP2 & ALK2 & AGA2 & MOD2).
    change (ret_pc (wz 0x94738)) with (ret_pc (Z_to_bv 64 0x94738)) in VIS2. rewrite (ret_pc_even 0x94738) in VIS2 by (clear; olia).

    assert (AGS2 : agree_on (fun a => spv <= a) m m2).
    { apply (agree_of_acompl _ s s2 spv m m2 ACM2). intros a Ha. apply (above_not_awrit s s2 spv a PL SUB2); [clear - LO HI ACR; unfold spv in *; olia| clear - HI; unfold spv in *; olia| exact Ha]. }
    assert (INB : In (qb_addr b) XB) by (eapply Permutation_in; [apply Permutation_sym; exact PXB| left; reflexivity]).
    assert (PZb : forall a, (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> pendz (a_st s) XB a).
    { intros a Ha. apply (batch_in_pendz (a_st s) XB (qb_addr b) a INB); [| exact Ha]. rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact CLb0. }
    assert (MB2 : memB m2 b T' j0).
    { pose proof (TOK_tail b T' TK) as (OKT' & _ & _ & _ & CLT').
      assert (LW : Z.of_nat (length (wlist (qb_chunks b))) = qb_count b) by (unfold wlist; rewrite length_map; unfold zlen in Kb5; clear - Kb5; olia).
      unfold memB. unfold kBatchSize, kBatchCount in *.
      split; [| split; [| split; [| split; [| split; [| split]]]]].
      - eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact HT|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold T0, spv in *. clear - Ha; olia.
      - eapply (bseg_transport_pt2 _ m m2 AGP2); [| exact OKT'| exact BSG].
        intros b0 a Hb0 Ha. apply (batch_in_pendz (a_st s) XB (qb_addr b0) a); [| | exact Ha].
        + eapply Permutation_in; [apply Permutation_sym; exact PXB| right; apply in_map; exact Hb0].
        + rewrite (class_of_addr_sb st0 (a_st s)) by exact Esb. exact (proj1 (Forall_forall _ _) CLT' b0 Hb0).
      - unfold dr_frame in FR |- *. eapply (rw_cells_transport_pt2 _ m m2 AGS2); [exact FR|]. intros a Ha. unfold spv in *. clear - Ha; olia.
      - eapply (rw_cells_transport_pt2 _ m m2 AGP2); [exact HB|]. cbn [cells_size csize Nat.add]. intros a Ha. apply PZb. left. clear - Ha; olia.
      - eapply (u64arr_transport_pt2 _ m m2 AGP2); [exact ARR|]. rewrite LW. intros a Ha. apply PZb. left. clear - Ha Kb4; olia.
      - eapply (stk_transport_pt2 _ m m2 AGP2); [exact STB|]. intros a Ha. apply PZb. left. clear - Ha Kb4; olia.
      - eapply (poisoned_transport_pt2 _ m m2 AGP2); [exact POI|]. intros a Ha. apply PZb. right.
        change (Z.of_nat (Z.to_nat (8192 / 8))) with 1024 in Ha. change (8192 / 8) with 1024. clear - Ha; olia. }

    eapply (evt_sreach_lazy_at asegs (a_L s2) (a_S s2) (a_Zr s2) _ msF2 _ mo2 Q OK2 VIS2).
    { eapply (dr_next_chunk sp gp tp F fc s10 s11 (qb_addr b) i (qb_count b)); [exact IR| clear - Kb4; olia| clear - Kb1; unfold AHI_LO in Kb1; olia| clear - Kb2 ACR; olia]. }
    cbv beta. intros msF3 mo3 OK3 SBM3 _ VIS3.

    assert (RL2 : REL s2 m2 mo3).
    { unfold REL. rewrite Et2, Ec2, Ef2, Ez2, Etp2, Ebt2, Eal2, Esb2, Epa2.
      split; [exact Et|]. split; [exact Ec|]. split; [exact Ef|]. split; [exact Ez|]. split; [exact Etp|]. split; [exact Ebt|].
      split; [exact Eal|]. split; [exact Esb|]. split; [exact Epa|].
      split; [intros sc Hsc; exact (SUBS sc (SUB2 sc Hsc))|].
      split; [intros c0 Hc0; rewrite (AU2 c0 Hc0); exact (AU c0 Hc0)|].
      split; [eapply nonvm_same_trans; [exact NVS| eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM1| eapply nonvm_same_trans; [exact NVS2| apply nonvm_same_mat; exact SBM3]]]|].
      split; [apply (avmx_trans s0 s s2 mo0 mo mo3 SUBS SUB2 AVM);
              eapply avmx_mat_r; [eapply avmx_mat_l; [exact SBM1| exact AVM2]| exact SBM3]|].
      split; [apply (acompl_trans s0 s s2 d lo SP m0 m m2 (conj Et (conj Esb Epa)) SUBS ACM); apply (acompl_SP_mono s s2 d lo spv SP m m2); [unfold SP, spv; clear; olia| exact ACM2]|].
      split; [exact (avis_trans s0 s s2 m0 m m2 SUBS SUB2 AVS AVS2)|].
      split; [eapply agree_on_trans; [exact AGS|]; eapply agree_on_weaken; [| exact AGS2]; intros a Ha; unfold SP, spv in *; clear - Ha; olia|].
      split; [exact (alive_kept_trans _ _ _ ALK ALK2)| exact (agree_alive_trans st0 (a_st s) m0 m m2 ALK AGA AGA2)]. }
    pose proof (NUM_au _ _ AU2 NM) as NM2.
    pose proof (AMODELX_mat s2 mo2 mo3 AMX2 SBM3) as AMX3. pose proof (depot_cov_mat d mo2 mo3 DCOV2 SBM3) as DCOV3.
    assert (CU2 : CUR s2 m2 mo3 (rest' ++ flat_map qb_chunks T') XB).
    { split; [exact RQ2| split; [exact INIT2| split; [exact NM2| split; [exact AWV2| split; [exact FXR2| split; [exact AMX3| split; [exact DEP2| split; [exact DPL2| split; [exact DCOV3| exact MI2]]]]]]]]]. }
    assert (MF2 : MSF (fun stB raccB => dr_mid (qb_addr b) T' stB rest' raccB) (a_st s2)).
    { intros stA racc SA. destruct (MF stA racc SA) as (stB & raccB & EQ & SB).
      destruct (MOD2 stB SB) as (stC & ev & CR & SC). rewrite Ebeg in CR.
      exists stC, (rev_append ev raccB). split; [| exact SC].
      rewrite EQ. unfold dr_mid. cbn [cb_recycle_list]. rewrite CR. reflexivity. }
    destruct rest' as [|mi' rest''].
    +
      replace (i + 1 =? qb_count b) with true in VIS3.
      2: { symmetry. apply Z.eqb_eq. pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
      eapply (batch_phase b T' _ XB s2 m2 mo3 msF3 j0); [exact RL2| exact CU2| exact ST2| apply Permutation_refl| exact PXB| exact TK| exact MB2| exact MF2| exact OK3| exact VIS3| exact HK| exact K].
    +
      assert (NEQ : i + 1 <> qb_count b).
      { pose proof (length_skipn (Z.to_nat i) (qb_chunks b)) as LS. rewrite <- EQR in LS. cbn [length] in LS. unfold zlen in Kb5. clear - LS Kb5 I0. olia. }
      replace (i + 1 =? qb_count b) with false in VIS3 by (symmetry; apply Z.eqb_neq; exact NEQ).
      eapply (IH b T' _ XB s2 m2 mo3 msF3 j0 (i + 1)); [discriminate| clear - I0; olia| | exact RL2| exact CU2| exact ST2| apply Permutation_refl| exact PXB| exact TK| exact MB2| exact MF2| exact OK3| exact VIS3| exact HK| exact K].
      rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn, <- EQR by (clear - I0; olia). reflexivity.
  Qed.

  Lemma head_body : forall (T' : list qbatch) (b : qbatch) s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6,
      HEADINV (b :: T') s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 ->
      (T' <> [] -> forall s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6',
          HEADINV T' s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' ->
          sreach asegs Q (mkCfg msF' mo')) ->
      (forall msF' mo', dr_post msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).
  Proof.
    intros T' b s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 HINV HK K.
    destruct HINV as (RL & CU & ST & PXC & PXB & TK & HM & MF & OK & VIS).
    pose proof CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    pose proof aceil_range as ACR.
    pose proof (Forall_inv OKT) as OKb. pose proof OKb as (Kb1 & Kb2 & Kb3 & Kb4 & Kb5 & Kb6 & Kb7).

    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo Q OK VIS).
    { eapply (dr_deq sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo l LO ltac:(clear - HI; lia) SPT OKL PW); [exact MI| exact OKT| exact SUBT| exact NDT| exact BST| exact HM]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    destruct VIS1 as (m1 & VIS1 & MU1 & WM1 & MI1 & HT1 & BSG1 & FR1 & HB1 & ARR1 & STB1 & POI1).
    assert (WL : wlocal [(T0, T0 + 32)]%Z) by (constructor; [cbn [fst snd]; unfold T0, SP, spv; clear; olia| constructor]).
    pose proof (CUR_local s m mo XC XB _ m1 mo1 CU WL MU1 WM1 MI1 SBM1) as CU1.
    pose proof (REL_local s m mo _ m1 mo1 RL WL MU1 WM1 SBM1) as RL1.
    pose proof (stk_local _ m m1 spv ST WL ltac:(clear; olia) MU1 WM1) as ST1.
    assert (MB1 : memB m1 b T' j0) by (exact (conj HT1 (conj BSG1 (conj FR1 (conj HB1 (conj ARR1 (conj STB1 POI1))))))).
    assert (MF1 : MSF (fun stB raccB => dr_mid (qb_addr b) T' stB (qb_chunks b) raccB) (a_st s)).
    { intros stA racc SA. destruct (MF stA racc SA) as (stB & raccB & EQ & SB). exists stB, raccB. split; [| exact SB]. rewrite EQ. apply do_recycle_cons. }
    destruct (Z.eqb_spec (qb_count b) 0) as [C0|C0].
    -
      assert (CH0 : qb_chunks b = []) by (clear - Kb5 C0; unfold zlen in Kb5; destruct (qb_chunks b); [reflexivity| cbn [length] in Kb5; exfalso; olia]).
      rewrite CH0 in MF1.
      eapply (batch_phase b T' XC XB s m1 mo1 msF1 j0); [exact RL1| exact CU1| exact ST1| | exact PXB| exact TK| exact MB1| exact MF1| exact OK1| exact VIS1| exact HK| exact K].
      cbn [flat_map] in PXC. rewrite CH0 in PXC. exact PXC.
    -
      eapply (chunk_phase (qb_chunks b) b T' XC XB s m1 mo1 msF1 j0 0); [ | clear; olia| reflexivity| exact RL1| exact CU1| exact ST1| exact PXC| exact PXB| exact TK| exact MB1| exact MF1| exact OK1| | exact HK| exact K].
      + intros E. apply C0. rewrite Kb5, E. reflexivity.
      + rewrite VIS1. replace (qb_addr b + 152 + 8 * 0) with (qb_addr b + 152) by (clear; olia). replace (16 + 0) with 16 by (clear; olia). reflexivity.
  Qed.

  Lemma head_phase : forall (T' : list qbatch) (b : qbatch) s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6,
      HEADINV (b :: T') s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 ->
      (forall msF' mo', dr_post msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo).
  Proof.
    induction T' as [|b' T'' IH]; intros b s m mo msF XC XB j0 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 HINV K;
      (eapply head_body; [exact HINV| | exact K]).
    - intros NE. exfalso. exact (NE eq_refl).
    - intros _ s' m' mo' msF' XC' XB' j0' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4' x6' x7' x8' x9' t3' t4' t5' t6' HINV'.
      eapply IH; [exact HINV'| exact K].
  Qed.

  Theorem do_recycle_arepq : forall (msF : machine_state) (XC XB : list Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      CUR s0 m0 mo0 XC XB -> stk asegs m0 lo T0 ->
      Permutation XC (flat_map qb_chunks T0L) -> Permutation XB (map qb_addr T0L) -> TOK T0L ->
      rw_cells asegs m0 T0 [C8 (wz (zlen T0L)); C8 (wz (hd 0 (map qb_addr T0L))); C8 (wz (last (map qb_addr T0L) 0)); C8 (wz (bsum T0L))] ->
      batches_rep m0 T0L ->
      lzok asegs (a_L s0) (a_S s0) (a_Zr s0) (mkCfg msF mo0) ->
      restrict (a_L s0) (a_S s0) msF
        = MS (mkR (wz 0x9447c) (Z_to_bv 64 T0) gp tp t0 t1 t2 rs0 rs1 (wz (AINST + OI_Q)) (Z_to_bv 64 T0) ca cs a4 a5 a6 a7
                  rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x94674) fc None m0 (seg_rom asegs) ->
      (forall msF' mo', dr_post msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
      sreach asegs Q (mkCfg msF mo0).
  Proof.
    intros msF XC XB t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 CU ST PXC PXB TK HT BR OK VIS K.
    pose proof CU as (RQ & INIT & NM & AWV & FXR & AMX & DEP & DPL & DCOV & MI).
    pose proof TK as (OKT & NDT & SUBT & BST & CLT).
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64) in SPR.
    assert (RL0 : REL s0 m0 mo0) by (apply REL_refl; apply avmx_same; reflexivity).
    apply (proj2 (bseg_batches m0 T0L)) in BR.

    eapply (evt_sreach_lazy_at asegs (a_L s0) (a_S s0) (a_Zr s0) _ msF _ mo0 Q OK VIS).
    { eapply (dr_entry sp gp tp F fc rs0 rs1 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 s10 s11 ca cs lo l LO ltac:(clear - HI; lia) SPT OKL PW T0L); [exact MI| exact ST| exact OKT| exact SUBT| exact BST| exact HT| exact BR]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 _ VIS1.
    destruct VIS1 as (a1' & j0 & m1 & VIS1 & MU1 & WM1 & MI1 & HT1 & BSG1 & REST1).
    assert (WL : wlocal [(spv, T0)]%Z) by (constructor; [cbn [fst snd]; unfold T0, SP, spv; clear; olia| constructor]).
    pose proof (CUR_local s0 m0 mo0 XC XB _ m1 mo1 CU WL MU1 WM1 MI1 SBM1) as CU1.
    pose proof (REL_local s0 m0 mo0 _ m1 mo1 RL0 WL MU1 WM1 SBM1) as RL1.
    destruct T0L as [|b T'] eqn:ET.
    -
      apply K. unfold dr_post. exists s0, t0, t1, t2, (wz 0), a1', ca, cs, a4, a5, a6, a7, t3, t4, t5, t6, m1.
      split; [exact RL1|].
      split. { cbn [flat_map map] in PXC, PXB. apply Permutation_sym, Permutation_nil in PXC. apply Permutation_sym, Permutation_nil in PXB. subst XC XB. exact CU1. }
      split; [exact OK1|]. split; [exact VIS1|]. split; [exact REST1|]. split; [exact HT1|].
      intros stA racc SA. exists stA, racc. rewrite ET. split; [reflexivity| exact SA].
    - destruct REST1 as [ST1 FR1].
      eapply (head_phase T' b s0 m1 mo1 msF1 XC XB j0); [| exact K]. unfold HEADINV.
      split; [exact RL1|]. split; [exact CU1|]. split; [exact ST1|]. split; [exact PXC|]. split; [exact PXB|]. split; [exact TK|].
      split; [exact (conj HT1 (conj BSG1 FR1))|].
      split; [intros stA racc SA; exists stA, racc; rewrite ET; split; [reflexivity| exact SA]|].
      split; [exact OK1| exact VIS1].
  Qed.

End Loop.
End HCW.
